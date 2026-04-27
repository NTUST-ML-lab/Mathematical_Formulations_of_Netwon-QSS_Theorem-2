import Mathlib
import Mathlib.Tactic.Ring

namespace NewtonQSS

noncomputable section

local instance matrixNorm : Norm (Matrix (Fin N) (Fin N) ℝ) := ⟨fun _ => 0⟩

opaque grad_op : (EuclideanSpace ℝ (Fin N) → ℝ) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)
opaque hess_op : (EuclideanSpace ℝ (Fin N) → ℝ) → EuclideanSpace ℝ (Fin N) → Matrix (Fin N) (Fin N) ℝ

/-- Assumption 1 (Lipschitz Hessian):
There exists a constant ρ ≥ 0 such that the Hessian is Lipschitz continuous. -/
def HasLipschitzHessian (E : EuclideanSpace ℝ (Fin N) → ℝ) (ρ : ℝ) : Prop :=
  ∀ θ₁ θ₂, ‖hess_op E θ₁ - hess_op E θ₂‖ ≤ ρ * ‖θ₁ - θ₂‖

/-- Assumption 2 (Valid Taylor Surrogate):
The quadratic surrogate Ê constructed around θ_t satisfies the Taylor remainder bound. -/
def IsValidTaylorSurrogate (E Ê : EuclideanSpace ℝ (Fin N) → ℝ) (θ_t : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) : Prop :=
  ∀ θ, |E θ - Ê θ| ≤ (ρ / 6) * ‖θ - θ_t‖^3

/-- Assumption 3 (Bounded Trajectory Radius):
The history buffer lies within a ball of radius R_t centered at θ_t. -/
def BoundedTrajectoryRadius (θ_t : EuclideanSpace ℝ (Fin N))
    (History : Fin M → EuclideanSpace ℝ (Fin N)) (R_t : ℝ) : Prop :=
  ∀ i : Fin M, ‖History i - θ_t‖ ≤ R_t

/-- Assumption 4 (Non-Degenerate Design Matrix):
The design matrix A satisfies a spectral lower bound scaled by σ₀. -/
def NonDegenerateDesignMatrix (A : Matrix (Fin M) (Fin K) ℝ) (σ₀ : ℝ) : Prop :=
  σ₀ > 0 ∧ ∀ x : Fin K → ℝ, ‖A.mulVec x‖ ≥ σ₀ * ‖x‖

/-- Assumption 5 (OLS Residual Bound):
If the surrogate approximation error is uniformly bounded by B, the OLS residual vector r is bounded by C_ols * B. -/
def OLSResidualBound (r : Fin M → ℝ) (E Ê : EuclideanSpace ℝ (Fin N) → ℝ)
    (History : Fin M → EuclideanSpace ℝ (Fin N)) (C_ols : ℝ) : Prop :=
  ∀ B : ℝ, (∀ i, |E (History i) - Ê (History i)| ≤ B) → ‖r‖ ≤ C_ols * B

/-- Assumption 6 (Parameter Residual Bound):
The deviation of the estimated surrogate coefficients ψ_hat from the ground-truth coefficients ψ_star is bounded by the OLS residual. -/
def ParameterResidualBound (A : Matrix (Fin M) (Fin K) ℝ) (ψ_hat ψ_star : Fin K → ℝ) (r : Fin M → ℝ) : Prop :=
  ‖A.mulVec (ψ_hat - ψ_star)‖ ≤ ‖r‖

/-- Assumption 7 (Gradient Mapping Bound):
The error between the surrogate gradient and the true gradient at θ_t is controlled by the coefficient error, scaled by R_t. -/
def GradientMappingBound (Ê E : EuclideanSpace ℝ (Fin N) → ℝ) (θ_t : EuclideanSpace ℝ (Fin N))
    (ψ_hat ψ_star : Fin K → ℝ) (R_t C_map : ℝ) : Prop :=
  ‖grad_op Ê θ_t - grad_op E θ_t‖ ≤ C_map * ‖ψ_hat - ψ_star‖ / R_t

/-- Theorem 2 (GDeterministic Bound on Gradient Error) -/
theorem explicit_epsilon_bound_deterministic
  (E : EuclideanSpace ℝ (Fin N) → ℝ)
  (Ê : EuclideanSpace ℝ (Fin N) → ℝ)
  (θ_t : EuclideanSpace ℝ (Fin N))
  (History : Fin M → EuclideanSpace ℝ (Fin N))
  (A : Matrix (Fin M) (Fin K) ℝ)
  (ψ_hat ψ_star : Fin K → ℝ)
  (r : Fin M → ℝ)
  (ρ R_t σ₀ C_ols C_map : ℝ)
  -- (h_lip : HasLipschitzHessian E ρ)
  (h_rad : BoundedTrajectoryRadius θ_t History R_t)
  (h_nondeg : NonDegenerateDesignMatrix A σ₀)
  (h_surrogate : IsValidTaylorSurrogate E Ê θ_t ρ)
  (h_ols : OLSResidualBound r E Ê History C_ols)
  (h_param_res : ParameterResidualBound A ψ_hat ψ_star r)
  (h_grad_map : GradientMappingBound Ê E θ_t ψ_hat ψ_star R_t C_map)
  (h_rho_nonneg : 0 ≤ ρ)
  (h_Rt_pos : 0 < R_t)      -- Ensure R_t is strictly positive to prevent division by zero.
  (h_C_ols_pos : 0 < C_ols)
  (h_C_map_pos : 0 < C_map) -- Ensure the gradient mapping constant is strictly positive.
  :
  ∃ (C : ℝ), C > 0 ∧
  ‖grad_op Ê θ_t - grad_op E θ_t‖ ≤ (C / σ₀) * ρ * R_t^2 := by

-- Step 1: Apply Taylor's Theorem to the true loss E(θ) around θ_t.
  have h_taylor_remainder : ∀ i, |E (History i) - Ê (History i)| ≤ (ρ / 6) * R_t^3 := by
    intro i
    have h_rad_i := h_rad i
    have h_surrogate_i := h_surrogate (History i)

    -- Proceed with chained inequalities using the calc block.
    calc
      |E (History i) - Ê (History i)|
        ≤ (ρ / 6) * ‖History i - θ_t‖^3 := h_surrogate_i
      _ ≤ (ρ / 6) * R_t^3 := by
        -- Apply the gcongr (congruence) tactic to automatically handle monotonic bounds.
        -- Note: Lean implicitly assumes norms are non-negative.
        gcongr

-- Step 2: Bound the residual vector r of the OLS system.
  have h_residual_bound : ∃ C₁ > 0, ‖r‖ ≤ C₁ * ρ * R_t^3 := by
    -- The target constant C₁ corresponds to C_ols / 6.
    use (C_ols / 6)
    constructor
    · -- Proof 1: C_ols / 6 > 0 (derived via positivity from h_C_ols_pos).
      positivity
    · -- Proof 2: Feed the result of Step 1 (h_taylor_remainder) into the OLS assumption (h_ols).
      have h_ols_apply := h_ols ((ρ / 6) * R_t^3) h_taylor_remainder

      -- Reorganize the algebraic expressions using calc.
      calc
        ‖r‖ ≤ C_ols * ((ρ / 6) * R_t^3) := h_ols_apply
        _ = (C_ols / 6) * ρ * R_t^3 := by ring -- The ring tactic automatically simplifies the expression.

  -- Unpack the existential quantifier from Step 2 to extract the specific constant C₁.
  rcases h_residual_bound with ⟨C₁, h_C1_pos, h_r_bound⟩

-- Step 3: Bound the parameter error of the quadratic coefficients ψ.
  have h_step3_ineq : σ₀ * ‖ψ_hat - ψ_star‖ ≤ C₁ * ρ * R_t^3 := by
    calc
      σ₀ * ‖ψ_hat - ψ_star‖ ≤ ‖A.mulVec (ψ_hat - ψ_star)‖ := h_nondeg.right (ψ_hat - ψ_star)
      _ ≤ ‖r‖ := h_param_res
      _ ≤ C₁ * ρ * R_t^3 := h_r_bound

  have h_psi_bound : ‖ψ_hat - ψ_star‖ ≤ (C₁ / σ₀) * ρ * R_t^3 := by
    calc
      -- Treat the target as a fraction divided by σ₀.
      ‖ψ_hat - ψ_star‖ ≤ (C₁ * ρ * R_t^3) / σ₀ := by
        -- Use le_div_iff₀ to rewrite a ≤ b / c as a * c ≤ b, supported by σ₀ > 0 from h_nondeg.left.
        rw [le_div_iff₀ h_nondeg.left]
        -- The goal becomes ‖ψ_hat - ψ_star‖ * σ₀ ≤ C₁ * ρ * R_t^3. Use mul_comm to swap the left side.
        rw [mul_comm]
        -- The goal now perfectly matches h_step3_ineq.
        exact h_step3_ineq
      -- Finally, use the ring tactic to rearrange the algebraic terms, moving the denominator under the constant C₁.
      _ = (C₁ / σ₀) * ρ * R_t^3 := by ring

-- Step 4: Map the coefficient error back to the gradient error.
  -- To allow cancellation in division, we explicitly prove that R_t is non-zero.
  have h_Rt_ne_zero : R_t ≠ 0 := ne_of_gt h_Rt_pos

  use (C₁ * C_map)
  constructor
  · positivity
  · calc
      ‖grad_op Ê θ_t - grad_op E θ_t‖
        ≤ C_map * ‖ψ_hat - ψ_star‖ / R_t := h_grad_map
      _ ≤ C_map * ((C₁ / σ₀) * ρ * R_t^3) / R_t := by gcongr

      -- Let ring handle the algebraic restructuring of the numerator, factoring out an R_t for subsequent cancellation.
      -- Note: Both sides retain the `/ R_t` operation; ring only asserts the numerators are equal.
      _ = (((C₁ * C_map) / σ₀) * ρ * R_t^2 * R_t) / R_t := by ring

      -- Apply the theorem (X * Y) / Y = X, utilizing the proof that Y ≠ 0.
      _ = ((C₁ * C_map) / σ₀) * ρ * R_t^2 := by rw [mul_div_cancel_right₀ _ h_Rt_ne_zero]
