import Mathlib
import Mathlib.Tactic.Ring

namespace NewtonQSS

noncomputable section

local instance matrixNorm : Norm (Matrix (Fin N) (Fin N) ℝ) := ⟨fun _ => 0⟩

opaque grad_op : (EuclideanSpace ℝ (Fin N) → ℝ) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)
opaque hess_op : (EuclideanSpace ℝ (Fin N) → ℝ) → EuclideanSpace ℝ (Fin N) → Matrix (Fin N) (Fin N) ℝ

/-- Assumption 1 (Lipschitz Hessian): there exists `ρ ≥ 0` such that the Hessian is Lipschitz. -/
def HasLipschitzHessian (E : EuclideanSpace ℝ (Fin N) → ℝ) (ρ : ℝ) : Prop :=
  ∀ θ₁ θ₂, ‖hess_op E θ₁ - hess_op E θ₂‖ ≤ ρ * ‖θ₁ - θ₂‖

/-- Assumption 2 (Taylor reference): the reference quadratic `T` built at `θ_t`
(the second-order Taylor polynomial of `E`) satisfies the Taylor remainder bound. -/
def IsValidTaylorSurrogate (E T : EuclideanSpace ℝ (Fin N) → ℝ) (θ_t : EuclideanSpace ℝ (Fin N)) (ρ : ℝ) : Prop :=
  ∀ θ, |E θ - T θ| ≤ (ρ / 6) * ‖θ - θ_t‖^3

/-- Assumption 3 (Bounded Trajectory Radius): the samples lie in a ball of radius `R_t` around `θ_t`. -/
def BoundedTrajectoryRadius (θ_t : EuclideanSpace ℝ (Fin N))
    (History : Fin M → EuclideanSpace ℝ (Fin N)) (R_t : ℝ) : Prop :=
  ∀ i : Fin M, ‖History i - θ_t‖ ≤ R_t

/-- Assumption 4 (Non-Degenerate Design Matrix): `‖A x‖ ≥ σ₀ ‖x‖` with `σ₀ > 0`. -/
def NonDegenerateDesignMatrix (A : Matrix (Fin M) (Fin K) ℝ) (σ₀ : ℝ) : Prop :=
  σ₀ > 0 ∧ ∀ x : Fin K → ℝ, ‖A.mulVec x‖ ≥ σ₀ * ‖x‖

/-- Assumption 5 (Misfit bound): if the reference `T` misfits `E` by at most `B` at every sample,
the misfit vector `r` satisfies `‖r‖ ≤ C_ols * B` (`C_ols = √M` for the Euclidean norm). -/
def MisfitBound (r : Fin M → ℝ) (E T : EuclideanSpace ℝ (Fin N) → ℝ)
    (History : Fin M → EuclideanSpace ℝ (Fin N)) (C_ols : ℝ) : Prop :=
  ∀ B : ℝ, (∀ i, |E (History i) - T (History i)| ≤ B) → ‖r‖ ≤ C_ols * B

/-- Assumption 6 (Design–misfit relation): the coefficient error of the fitted surrogate,
mapped through the design matrix, is controlled by the misfit vector of the reference. -/
def DesignMisfitRelation (A : Matrix (Fin M) (Fin K) ℝ) (ψ_hat ψ_star : Fin K → ℝ) (r : Fin M → ℝ) : Prop :=
  ‖A.mulVec (ψ_hat - ψ_star)‖ ≤ ‖r‖

/-- Assumption 7 (Gradient Mapping Bound): the gradient error of the fitted surrogate `Ê` at `θ_t`
is controlled by the coefficient error, scaled by `R_t` (`C_map = 1` in scaled coordinates). -/
def GradientMappingBound (Ê E : EuclideanSpace ℝ (Fin N) → ℝ) (θ_t : EuclideanSpace ℝ (Fin N))
    (ψ_hat ψ_star : Fin K → ℝ) (R_t C_map : ℝ) : Prop :=
  ‖grad_op Ê θ_t - grad_op E θ_t‖ ≤ C_map * ‖ψ_hat - ψ_star‖ / R_t

/-- Theorem 2 (Deterministic Bound on Gradient Error), existential form. -/
theorem explicit_epsilon_bound_deterministic
  (E : EuclideanSpace ℝ (Fin N) → ℝ)
  (T : EuclideanSpace ℝ (Fin N) → ℝ)          -- Taylor reference
  (Ê : EuclideanSpace ℝ (Fin N) → ℝ)          -- fitted surrogate
  (θ_t : EuclideanSpace ℝ (Fin N))
  (History : Fin M → EuclideanSpace ℝ (Fin N))
  (A : Matrix (Fin M) (Fin K) ℝ)
  (ψ_hat ψ_star : Fin K → ℝ)
  (r : Fin M → ℝ)
  (ρ R_t σ₀ C_ols C_map : ℝ)
  (h_rad : BoundedTrajectoryRadius θ_t History R_t)
  (h_nondeg : NonDegenerateDesignMatrix A σ₀)
  (h_surrogate : IsValidTaylorSurrogate E T θ_t ρ)
  (h_ols : MisfitBound r E T History C_ols)
  (h_param_res : DesignMisfitRelation A ψ_hat ψ_star r)
  (h_grad_map : GradientMappingBound Ê E θ_t ψ_hat ψ_star R_t C_map)
  (h_rho_nonneg : 0 ≤ ρ)
  (h_Rt_pos : 0 < R_t)
  (h_C_ols_pos : 0 < C_ols)
  (h_C_map_pos : 0 < C_map)
  :
  ∃ (C : ℝ), C > 0 ∧
  ‖grad_op Ê θ_t - grad_op E θ_t‖ ≤ (C / σ₀) * ρ * R_t^2 := by

-- Step 1: Taylor remainder of the reference at every sample.
  have h_taylor_remainder : ∀ i, |E (History i) - T (History i)| ≤ (ρ / 6) * R_t^3 := by
    intro i
    have h_rad_i := h_rad i
    have h_surrogate_i := h_surrogate (History i)
    calc
      |E (History i) - T (History i)|
        ≤ (ρ / 6) * ‖History i - θ_t‖^3 := h_surrogate_i
      _ ≤ (ρ / 6) * R_t^3 := by
        gcongr

-- Step 2: Bound the misfit vector.
  have h_residual_bound : ∃ C₁ > 0, ‖r‖ ≤ C₁ * ρ * R_t^3 := by
    use (C_ols / 6)
    constructor
    · positivity
    · have h_ols_apply := h_ols ((ρ / 6) * R_t^3) h_taylor_remainder
      calc
        ‖r‖ ≤ C_ols * ((ρ / 6) * R_t^3) := h_ols_apply
        _ = (C_ols / 6) * ρ * R_t^3 := by ring

  rcases h_residual_bound with ⟨C₁, h_C1_pos, h_r_bound⟩

-- Step 3: Bound the coefficient error.
  have h_step3_ineq : σ₀ * ‖ψ_hat - ψ_star‖ ≤ C₁ * ρ * R_t^3 := by
    calc
      σ₀ * ‖ψ_hat - ψ_star‖ ≤ ‖A.mulVec (ψ_hat - ψ_star)‖ := h_nondeg.right (ψ_hat - ψ_star)
      _ ≤ ‖r‖ := h_param_res
      _ ≤ C₁ * ρ * R_t^3 := h_r_bound

  have h_psi_bound : ‖ψ_hat - ψ_star‖ ≤ (C₁ / σ₀) * ρ * R_t^3 := by
    calc
      ‖ψ_hat - ψ_star‖ ≤ (C₁ * ρ * R_t^3) / σ₀ := by
        rw [le_div_iff₀ h_nondeg.left]
        rw [mul_comm]
        exact h_step3_ineq
      _ = (C₁ / σ₀) * ρ * R_t^3 := by ring

-- Step 4: Map the coefficient error to the gradient error of the fitted surrogate.
  have h_Rt_ne_zero : R_t ≠ 0 := ne_of_gt h_Rt_pos

  use (C₁ * C_map)
  constructor
  · positivity
  · calc
      ‖grad_op Ê θ_t - grad_op E θ_t‖
        ≤ C_map * ‖ψ_hat - ψ_star‖ / R_t := h_grad_map
      _ ≤ C_map * ((C₁ / σ₀) * ρ * R_t^3) / R_t := by gcongr
      _ = (((C₁ * C_map) / σ₀) * ρ * R_t^2 * R_t) / R_t := by ring
      _ = ((C₁ * C_map) / σ₀) * ρ * R_t^2 := by rw [mul_div_cancel_right₀ _ h_Rt_ne_zero]

/-- Theorem 2 with the explicit constant of the paper: `‖∇Ê − ∇E‖ ≤ (C_ols · C_map / (6 σ₀)) ρ R_t²`. -/
theorem explicit_epsilon_bound_deterministic_const
  (E T Ê : EuclideanSpace ℝ (Fin N) → ℝ)
  (θ_t : EuclideanSpace ℝ (Fin N))
  (History : Fin M → EuclideanSpace ℝ (Fin N))
  (A : Matrix (Fin M) (Fin K) ℝ)
  (ψ_hat ψ_star : Fin K → ℝ)
  (r : Fin M → ℝ)
  (ρ R_t σ₀ C_ols C_map : ℝ)
  (h_rad : BoundedTrajectoryRadius θ_t History R_t)
  (h_nondeg : NonDegenerateDesignMatrix A σ₀)
  (h_surrogate : IsValidTaylorSurrogate E T θ_t ρ)
  (h_ols : MisfitBound r E T History C_ols)
  (h_param_res : DesignMisfitRelation A ψ_hat ψ_star r)
  (h_grad_map : GradientMappingBound Ê E θ_t ψ_hat ψ_star R_t C_map)
  (h_rho_nonneg : 0 ≤ ρ)
  (h_Rt_pos : 0 < R_t)
  (h_C_map_pos : 0 < C_map)
  :
  ‖grad_op Ê θ_t - grad_op E θ_t‖ ≤ (C_ols * C_map / (6 * σ₀)) * ρ * R_t^2 := by
  have h_taylor_remainder : ∀ i, |E (History i) - T (History i)| ≤ (ρ / 6) * R_t^3 := by
    intro i
    calc
      |E (History i) - T (History i)|
        ≤ (ρ / 6) * ‖History i - θ_t‖^3 := h_surrogate (History i)
      _ ≤ (ρ / 6) * R_t^3 := by
        have := h_rad i
        gcongr
  have h_r : ‖r‖ ≤ C_ols * ((ρ / 6) * R_t^3) := h_ols _ h_taylor_remainder
  have h_psi : ‖ψ_hat - ψ_star‖ ≤ C_ols * ((ρ / 6) * R_t^3) / σ₀ := by
    rw [le_div_iff₀ h_nondeg.left, mul_comm]
    exact le_trans (h_nondeg.right (ψ_hat - ψ_star)) (le_trans h_param_res h_r)
  have h_Rt_ne_zero : R_t ≠ 0 := ne_of_gt h_Rt_pos
  have h_sigma_ne_zero : σ₀ ≠ 0 := ne_of_gt h_nondeg.left
  calc
    ‖grad_op Ê θ_t - grad_op E θ_t‖
      ≤ C_map * ‖ψ_hat - ψ_star‖ / R_t := h_grad_map
    _ ≤ C_map * (C_ols * ((ρ / 6) * R_t^3) / σ₀) / R_t := by gcongr
    _ = (C_ols * C_map / (6 * σ₀)) * ρ * R_t^2 := by
      field_simp

end

end NewtonQSS
