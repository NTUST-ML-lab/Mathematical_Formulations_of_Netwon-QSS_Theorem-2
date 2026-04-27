# Newton-QSS: Formal Verification of Gradient Approximation Error

This repository contains the machine-checked formalization for the core theoretical guarantee of the **Newton-QSS**. Specifically, it provides the interactive theorem prover code for the **Deterministic Bound on Gradient Error** (detailed in Section 4.4.3 of our paper).

## Overview

When substituting exact second-order optimization with a trajectory-based quadratic surrogate, it is crucial to mathematically guarantee that the surrogate gradient does not deviate significantly from the true gradient. This repository provides a rigorous proof that the gradient approximation error is strictly bounded and decays quadratically with the trajectory radius.

To ensure absolute mathematical rigor, the dimensional reduction, the applications of Taylor's Theorem, and the Ordinary Least Squares (OLS) residual bounds have been formally machine-checked using the [Lean 4](https://leanprover.github.io/) theorem prover.

## Formalized Assumptions

The Lean 4 codebase (`Theorem-2.lean`) defines the following regularity conditions, directly mirroring the mathematical assumptions in the paper:

1. **`HasLipschitzHessian`**: The true objective function possesses a Lipschitz continuous Hessian with constant $\rho \ge 0$.
2. **`IsValidTaylorSurrogate`**: The constructed surrogate satisfies the Taylor remainder bound derived from the Lipschitz Hessian.
3. **`BoundedTrajectoryRadius`**: Historical exploration states (the trajectory buffer) lie within a local ball of radius $R_t$.
4. **`NonDegenerateDesignMatrix`**: The OLS design matrix maintains a strict spectral lower bound, $\sigma_0 > 0$.
5. **`OLSResidualBound`**: The OLS projection residual is bounded by the surrogate's maximum pointwise approximation error.
6. **`ParameterResidualBound`**: The surrogate coefficient deviation is constrained by the OLS residual.
7. **`GradientMappingBound`**: The final gradient error mapping is controlled by the coefficient deviation scaled by $R_t$.

## The Main Theorem

The core theoretical result, formalized as `explicit_epsilon_bound_deterministic` in the code, proves that under the aforementioned assumptions, there exists a constant $C > 0$ such that:

$$\|\nabla \hat{E}(\theta_t) - \nabla E(\theta_t)\| \le \left(\frac{C}{\sigma_0}\right) \cdot \rho \cdot R_t^2$$

**Key Insights Verified in Lean:**
* **Quadratic Decay:** The theorem formally verifies that the error decays quadratically ($\mathcal{O}(R_t^2)$) as the optimization trajectory approaches a minimum and the sampling radius shrinks.
* **Degeneracy Penalty:** The error bound explicitly scales inversely with the trajectory condition number $\sigma_0$. This mathematical reality (where $\sigma_0 \rightarrow 0$ causes the error to explode) provides the theoretical justification for the trajectory stabilization and regularization techniques employed in Newton-QSS.

## Verification Environment

The proof leverages `Mathlib.Tactic.Ring` for algebraic simplifications and standard `gcongr` tactics for monotonic inequalities.

* **Language:** Lean 4
* **Dependencies:** Mathlib
* **Tested Environment:** Developed and verified on Kubuntu 24.02.

### How to Build and Verify

To verify the proofs locally, ensure you have the Lean 4 toolchain installed, then run:

```bash
# Clone the repository
git clone <your-repo-url>
cd <your-repo-directory>

# Fetch Mathlib dependencies and build the proof
lake build
```