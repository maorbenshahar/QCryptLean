import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance

/-!
# Fuchs–van-de-Graaf mass-removal barrier

The purified-distance lower bound charged by removing trace mass from a normalized
state.  If `ρ` is a normalized state (`ρ.trace = 1`) and `τ` is a sub-normalized
state, then the **trace deficit** `Δ := ρ.trace - τ.trace` costs at least `√Δ` in
purified distance:

    √(ρ.trace − τ.trace) ≤ P(ρ, τ).

This is the compiled-Lean counterexample core for the accept-move barrier: an
accept step that removes weight `Δ` from a normalized state cannot be charged below
`√Δ` in purified distance, so no accounting can hide that cost below the
Fuchs–van-de-Graaf floor.

## Main statement
- `purifiedDistance_ge_sqrt_traceDeficit`: `√(ρ.trace − τ.trace) ≤ P(ρ, τ)` for
  normalized `ρ`.

## Proof
By the sub-normalized Cauchy–Schwarz bound `fidelity_sq_le_trace_mul_trace`,
`F(ρ, τ)² ≤ ρ.trace · τ.trace = τ.trace` (using `ρ.trace = 1`). Since `ρ` is
normalized the generalized fidelity coincides with the Uhlmann fidelity
(`fidelityGen_eq_fidelity_of_trace_one`), so `F*(ρ, τ)² ≤ τ.trace`. Hence

    P(ρ, τ)² = 1 − F*(ρ, τ)² ≥ 1 − τ.trace = ρ.trace − τ.trace,

and monotonicity of `√` gives the claim.
-/

open Quantum.Operators
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Fuchs–van-de-Graaf mass-removal barrier.**

For a normalized state `ρ` (`ρ.trace = 1`) and a sub-normalized state `τ`, the
purified distance is at least the square root of the trace deficit
`Δ = ρ.trace − τ.trace`:

    √(ρ.trace − τ.trace) ≤ P(ρ, τ).

Removing trace weight `Δ` from a normalized state costs at least `√Δ` in purified
distance; this is the accept-move barrier's lower bound. -/
theorem purifiedDistance_ge_sqrt_traceDeficit {n : ℕ} [NeZero n]
    (ρ τ : SubDensityOp n) (hρ : ρ.trace = 1) :
    Real.sqrt (ρ.trace - τ.trace) ≤ purifiedDistance ρ τ := by
  unfold purifiedDistance
  apply Real.sqrt_le_sqrt
  -- Generalized fidelity equals the Uhlmann fidelity because `ρ` is normalized.
  have hFgen_eq :
      fidelityGen ρ τ =
        Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    fidelityGen_eq_fidelity_of_trace_one ρ τ hρ
  -- Cauchy–Schwarz: `F*(ρ, τ)² ≤ ρ.trace · τ.trace = τ.trace`.
  have hF_sq_le : fidelityGen ρ τ ^ 2 ≤ τ.trace := by
    rw [hFgen_eq]
    calc Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ^ 2
        ≤ ρ.trace * τ.trace := fidelity_sq_le_trace_mul_trace ρ τ
      _ = τ.trace := by rw [hρ, one_mul]
  -- Deficit `ρ.trace − τ.trace = 1 − τ.trace ≤ 1 − F*² = P²`.
  rw [hρ]
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
