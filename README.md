# Newton-QSS: Formal Verification of Gradient Approximation Error

This repository contains a Lean 4 formalization of the argument behind **Theorem 2 (Deterministic Bound on Gradient Error)** in the paper *Newton-QSS: Trajectory-Induced Quadratic Subspace Updates and Compatibility Conditions for Base Optimizers*. In the current manuscript, the theorem is in Section 4.4.3 and its full proof is in Appendix D.3. Section numbers may change between versions.

Theorem 2 bounds the gradient error of the quadratic surrogate $\hat{E}$ fitted to recent trajectory samples of one parameter block:

$$\lVert \nabla \hat{E}(\theta_{t,b}) - \nabla E_b(\theta_{t,b}) \rVert \le \left(\frac{C_{\mathrm{ols}}\, C_{\mathrm{map}}}{6\sigma_0}\right) \rho R_t^2, \qquad C_{\mathrm{ols}} = \sqrt{M}, \quad C_{\mathrm{map}} = 1.$$

The whole formalization is in `Theorem2.lean`.

## What is verified

Lean checks the derivation from a set of hypotheses to the bound, with the explicit constant $C_{\mathrm{ols}} C_{\mathrm{map}} / (6\sigma_0)$. The hypotheses (the Taylor remainder bound, the misfit-vector bound, the design–misfit relation and the gradient mapping) are stated as definitions and passed to the theorem. Appendix D.3 of the paper proves them on paper with $C_{\mathrm{ols}} = \sqrt{M}$ and $C_{\mathrm{map}} = 1$. The formalization verifies the derivation, not the modelling. Whether a given training trajectory satisfies the assumptions, in particular exact loss values and a non-degenerate design, is an empirical question.

The following steps are **not** formalized:

- **Taylor's theorem.** The step from a Lipschitz Hessian to the remainder bound enters as the hypothesis `IsValidTaylorSurrogate`. `HasLipschitzHessian` is stated for reference only. It is not a hypothesis of either theorem, and the matrix norm it uses is a local placeholder instance that always returns 0.
- **The coordinate change and the feature map.** `grad_op` and `hess_op` are opaque symbols, not Mathlib's `gradient` or `fderiv`. The centred, $R_t$-scaled design matrix enters only through `NonDegenerateDesignMatrix` and `GradientMappingBound`.
- **Corollary 1 (inexact loss values)** and the EMA that the training runs apply across several fits.

## Notation

| Lean | Paper | Meaning |
|---|---|---|
| `E` | $E_b$ | block objective (other parameters held fixed) |
| `T` | $T_2$ | second-order Taylor polynomial of $E_b$ at $\theta_{t,b}$ (the reference) |
| `Ê` | $\hat{E}$ | fitted quadratic surrogate |
| `θ_t` | $\theta_{t,b}$ | expansion point |
| `History i` | $\theta_b^{(i)}$ | $i$-th trajectory sample |
| `N` | $m$ | block dimension |
| `M` | $M$ | number of samples |
| `K` | $(m+1)(m+2)/2$ | number of quadratic coefficients ($K = M$ for interpolation, $K < M$ for least squares) |
| `A` | $\tilde{A}$ | design matrix in centred, $R_t$-scaled coordinates |
| `ψ_hat`, `ψ_star` | $\hat{\psi}$, $\psi^*$ | coefficients of $\hat{E}$ and of $T_2$ |
| `r` | $\boldsymbol{\zeta}$ | misfit of $T_2$ at the samples, $\zeta_i = E_b(\theta_b^{(i)}) - T_2(\theta_b^{(i)})$ |
| `ρ`, `R_t`, `σ₀` | $\rho$, $R_t$, $\sigma_0$ | Hessian Lipschitz constant, sample radius, smallest singular value of $\tilde{A}$ |
| `C_ols`, `C_map` | $\sqrt{M}$, $1$ | constants of the misfit bound and the gradient mapping |

## Hypotheses

| Lean definition | Statement | Paper |
|---|---|---|
| `BoundedTrajectoryRadius θ_t History R_t` | $\lVert \theta_i - \theta_t \rVert \le R_t$ for all $i$ | Assumption 5(ii) |
| `NonDegenerateDesignMatrix A σ₀` | $\sigma_0 > 0$ and $\lVert A x \rVert \ge \sigma_0 \lVert x \rVert$ for all $x$ | Assumption 5(iii) |
| `IsValidTaylorSurrogate E T θ_t ρ` | $\lvert E(\theta) - T(\theta) \rvert \le \frac{\rho}{6} \lVert \theta - \theta_t \rVert^3$ | Taylor's theorem under Assumption 5(i) |
| `MisfitBound r E T History C_ols` | if $\lvert E(\theta_i) - T(\theta_i) \rvert \le B$ for all $i$, then $\lVert r \rVert \le C_{\mathrm{ols}} B$ | $\lVert \boldsymbol{\zeta} \rVert \le \sqrt{M} \max_i \lvert \zeta_i \rvert$ |
| `DesignMisfitRelation A ψ_hat ψ_star r` | $\lVert A(\hat{\psi} - \psi^*) \rVert \le \lVert r \rVert$ | $\tilde{A}(\hat{\psi} - \psi^*) = \boldsymbol{\zeta}$ under exact values, Assumption 5(iv); a projection of $\boldsymbol{\zeta}$ for least squares |
| `GradientMappingBound Ê E θ_t ψ_hat ψ_star R_t C_map` | $\lVert \nabla \hat{E}(\theta_t) - \nabla E(\theta_t) \rVert \le C_{\mathrm{map}} \lVert \hat{\psi} - \psi^* \rVert / R_t$ | chain rule in scaled coordinates, $C_{\mathrm{map}} = 1$ |
| `HasLipschitzHessian E ρ` | $\lVert \nabla^2 E(\theta_1) - \nabla^2 E(\theta_2) \rVert \le \rho \lVert \theta_1 - \theta_2 \rVert$ | Assumption 5(i); not used by the theorems |

`IsValidTaylorSurrogate` is stated for all $\theta$. The paper derives the remainder bound only on the ball of radius $R_t$, and the proof uses it only at the samples.

Both theorems also take the scalar conditions $\rho \ge 0$, $R_t > 0$ and $C_{\mathrm{map}} > 0$. The existential form also takes $C_{\mathrm{ols}} > 0$.

## Theorems

**`explicit_epsilon_bound_deterministic`** (existential form):

$$\exists\, C > 0, \quad \lVert \nabla \hat{E}(\theta_t) - \nabla E(\theta_t) \rVert \le \frac{C}{\sigma_0}\, \rho R_t^2,$$

with witness $C = C_{\mathrm{ols}} C_{\mathrm{map}} / 6$.

**`explicit_epsilon_bound_deterministic_const`** (explicit constant, as stated in the paper):

$$\lVert \nabla \hat{E}(\theta_t) - \nabla E(\theta_t) \rVert \le \frac{C_{\mathrm{ols}}\, C_{\mathrm{map}}}{6\sigma_0}\, \rho R_t^2.$$

Both proofs have the same four steps:

1. **Taylor remainder at the samples.** $\lvert E(\theta_i) - T(\theta_i) \rvert \le \rho R_t^3 / 6$, from `IsValidTaylorSurrogate` and `BoundedTrajectoryRadius`.
2. **Misfit vector.** $\lVert r \rVert \le C_{\mathrm{ols}}\, \rho R_t^3 / 6$, from `MisfitBound`.
3. **Coefficient error.** $\sigma_0 \lVert \hat{\psi} - \psi^* \rVert \le \lVert A(\hat{\psi} - \psi^*) \rVert \le \lVert r \rVert$, from `NonDegenerateDesignMatrix` and `DesignMisfitRelation`.
4. **Gradient error.** Divide by $R_t$, from `GradientMappingBound`.

## Reading the bound

The bound is conditional (see Remark 1 and Section 4.4.4 of the paper).

- **It covers a single fit to exact values of the block objective.** In training, the recorded epoch losses differ from the block objective by some $\eta$. Corollary 1 of the paper then gives $\frac{\sqrt{M}}{\sigma_0}\left(\frac{\rho R_t^2}{6} + \frac{\eta}{R_t}\right)$. The two terms move in opposite directions as $R_t$ shrinks, so a contracting trajectory does not by itself produce a more accurate surrogate. In the paper's CIFAR-10 diagnostics (Section 5.3.6), the measured error grew as the radius shrank.
- **Both terms scale with $1/\sigma_0$.** A degenerate sample design makes the bound vacuous. The paper does not show that the EMA or soft-thresholding steps of Newton-QSS increase $\sigma_0$.

Earlier versions of this README said that the formalization shows the error decaying quadratically as the trajectory approaches a minimum, and that it justifies the stabilization techniques of Newton-QSS. The bound alone supports neither claim.

## Revision history

**2026-09-25.** The previous version used one function `Ê` both as the Taylor reference (in the remainder and residual hypotheses) and as the fitted surrogate (in the gradient mapping and the conclusion). These are different objects: the interpolating surrogate matches the recorded values and is in general not Taylor-accurate. Changes:

- The Taylor reference has its own symbol `T`. `IsValidTaylorSurrogate E T θ_t ρ` now constrains `T`, and `Ê` appears only in `GradientMappingBound` and the conclusion.
- `OLSResidualBound` is renamed `MisfitBound`. `r` is the misfit of the reference `T` at the samples ($\boldsymbol{\zeta}$ in the paper), not the residual of the fit, which is zero for interpolation.
- `ParameterResidualBound` is renamed `DesignMisfitRelation`.
- The new theorem `explicit_epsilon_bound_deterministic_const` states the explicit constant of the paper.
- The proof script of `explicit_epsilon_bound_deterministic` is otherwise unchanged.

## Building and checking

`lean-toolchain` pins `leanprover/lean4:v4.30.0-rc2`, and `lake-manifest.json` pins Mathlib at `89616f54e87a`.

```bash
git clone https://github.com/NTUST-ML-lab/Mathematical_Formulations_of_Netwon-QSS_Theorem-2.git
cd Mathematical_Formulations_of_Netwon-QSS_Theorem-2
lake exe cache get      # optional: download prebuilt Mathlib instead of compiling it
lake build Theorem2
```

To confirm that neither theorem depends on `sorry`, create a file `Axioms.lean`:

```lean
import Theorem2
#print axioms NewtonQSS.explicit_epsilon_bound_deterministic
#print axioms NewtonQSS.explicit_epsilon_bound_deterministic_const
```

and run `lake env lean Axioms.lean`. Both theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Tested on Kubuntu 24.04 LTS.
