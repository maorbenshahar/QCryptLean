import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.Foundations
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.SpectralSetup
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.MainTheorems

/-!
# Renner thesis Theorem `thm:Hmincondrep` (line 4561) and `cor:Hmincondrepclass` (line 4986)

**Theorem `thm:Hmincondrep`** (Renner 2005, line 4561):

> Let `ρ_{A B} ∈ NN(H_A ⊗ H_B)`, `σ_B ∈ NN(H_B)` be density operators, `n ∈ ℕ`,
> `ε ≥ 0`. Then
> `(1/n) Hmin^ε(ρ_{AB}^⊗n | σ_B^⊗n) ≥ H(ρ_{AB}) - H(ρ_B) - D(ρ_B‖σ_B) - δ`
> where
> `δ := 2 log(rank(ρ_A) + tr(ρ_{AB}² (id_A ⊗ σ_B^{-1})) + 2) · √(log(1/ε)/n + 1)`.

A Chernoff/MGF-style smooth-min-entropy lower bound for tensor powers, proven
via spectral decomposition + the Renner `r_t` function + Birkhoff's theorem +
the projector-sandwich trace bound (`lem:disttracebound`).

**Corollary `cor:Hmincondrepclass`** (line 4986): the specialization to states
classical on the first register (`ρ_{XB}`) with `σ_B = ρ_B`:

> `(1/n) Hmin^ε(ρ_{XB}^⊗n | ρ_B^⊗n) ≥ H(ρ_{XB}) - H(ρ_B) - δ`,
> with `δ := (2 H_max(ρ_X) + 3) · √(log(1/ε)/n + 1)`.

These are the formulas printed at lines 4570–4572 and 4994–4995. The library's
`noiseFactor` instead uses `√((log₂(1/ε)+1)/n)`, the grouping in Renner's application
at lines 6288–6289. Its classical correction `δ_iidAEP_class` uses `2 H_max + 4`.

The classical specialization is used by `thm:Renyisym`'s proof (line 6118), with the
regrouped noise factor at lines 6288–6289.

## Contents

- `CQState.tensorPower` — n-fold CQ tensor (built via `CQState.tensor`).
- `SubDensityOp.tensorPower` — n-fold sub-density tensor (specializing
  `tensorFinProd`).
- `δ_iidAEP_general` and `δ_iidAEP_class` — abstract penalty
  constants. The precise δ formulas (involving `rank`,
  `tr(ρ²·(id⊗σ⁻¹))`, and `H_max`) are recorded in the docstrings.
- `iidAEP` and its classical specialization — the main statements.

The bridging definitions `CQState.toJointDensityOp` and
`quantumMarginalDensityOp` allow `vonNeumannEntropy` to be invoked on
CQ-states.

## Proof strategy (Renner thesis lines 4575–4980)

For `thm:Hmincondrep`:

1. Spectral decomposition of `(id_A ⊗ σ_B)^⊗n` with ordered eigenvalues `q_z`
   and projectors `B_z := ∑_{z' ≥ z} |z'⟩⟨z'|`.
2. β-coefficients with `∑_{z' ≤ z} β_{z'} = q_z`; rewrite
   `(id_A ⊗ σ_B)^⊗n = ∑ β_z B_z`.
3. Construct smoothing witness `ρ̄_{A^n B^n}` via `B_z`-sandwiches of `ρ^⊗n`.
4. Birkhoff (`Mathlib.Analysis.Convex.Birkhoff`) for permutation symmetrization;
   rt-function bounds for the Chernoff/MGF step.
5. `lem:disttracebound` for the trace-norm distance between `ρ̄` and `ρ^⊗n`.

For `cor:Hmincondrepclass`:

1. WLOG `ρ_B` invertible (continuity).
2. `lem:prodpos` ⟹ `tr(ρ²·(id_X ⊗ ρ_B⁻¹)) ≤ 1`.
3. `rank(ρ_X) ≤ 2^H_max(ρ_X)`.
4. Substitute into `iidAEP`'s δ to get `δ ≤ (2 H_max + 3)·√(...)`.
5. `D(ρ_B‖ρ_B) = 0` term drops.
-/
