import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TraceBoundHelpers
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TraceBoundSpectral

/-!
# Renner thesis Lemma `lem:disttracebound` (line 10045)

**Statement** (Renner 2005):

> Let `ρ, ρ̄ ∈ NN(H)` such that `ρ̄ = P ρ P` for some projector `P` on `H`. Then
> `‖ρ - ρ̄‖₁ ≤ 2 √(tr(ρ) · (tr(ρ) - tr(ρ̄)))`.

i.e., when `ρ̄` is obtained from `ρ` by sandwiching with a projector, the
trace-norm distance is bounded by twice the geometric mean of `tr(ρ)` and the
trace deficit.

**Why we need it.** Used in the proof of `thm:Hmincondrep` (Renner line 4561 —
Chernoff/MGF on the spectral decomposition), and hence `thm:Renyisym` (the AEP needed by the BB84
finite-size chain).

**Proof strategy** (Renner thesis lines 10054–10110, ~50 lines of math):

1. **Pure normalized base case.** If `ρ = |φ⟩⟨φ|` is pure with `|φ⟩` unit, write
   `|φ⟩ = α|a⟩ + β|b⟩` for orthonormal `|a⟩, |b⟩` with `P|a⟩ = |a⟩`, `P|b⟩ = 0`.
   Then `ρ̄ = α²|a⟩⟨a|`, and direct computation gives
   `‖ρ - ρ̄‖₁ ≤ 2β = 2√(1 - tr(ρ̄))`.

2. **Spectral decomposition for general subnormalized `ρ`.** Write
   `ρ = Σ p_x |x⟩⟨x|`. Each `ρ_x = |x⟩⟨x|` is pure normalized; let
   `ρ̄_x = P ρ_x P`. By the base case,
   `‖ρ_x - ρ̄_x‖₁ ≤ 2 √(1 - tr(ρ̄_x))`.

3. **Triangle inequality + Jensen.** Linearity gives
   `ρ̄ = Σ p_x ρ̄_x`, so
   `‖ρ - ρ̄‖₁ ≤ Σ p_x ‖ρ_x - ρ̄_x‖₁ ≤ 2 Σ p_x √(1 - tr(ρ̄_x))`.
   By Jensen (concavity of `√`),
   `Σ p_x √(1 - tr(ρ̄_x)) ≤ √(tr(ρ)) · √(Σ p_x (1 - tr(ρ̄_x))/tr(ρ))
     = √(tr(ρ)) · √((tr(ρ) - tr(ρ̄))/tr(ρ)) = √(tr(ρ)·(tr(ρ) - tr(ρ̄))/tr(ρ))`.
   Multiplying through by 2 finishes.

The non-smooth-quantum-information content is just trace, projector idempotence,
and the trace norm; project conventions match (`P*P = P`, `P† = P`, `traceNorm`).
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Renner `lem:disttracebound`** (line 10045). For a sub-density operator
`ρ` and a Hermitian projector `P`, the trace-norm distance from `ρ` to its
projector sandwich `P ρ P` is bounded by `2 √(tr(ρ)(tr(ρ) - tr(P ρ P)))`.

    The trace inside the square root is real and nonnegative for PSD `ρ` and
    a Hermitian projector `P` (since `P ρ P` is PSD and dominated by `ρ`
    in PSD order, with smaller trace). -/
theorem traceNorm_sub_projector_sandwich_le {n : ℕ} [NeZero n]
    (ρ : SubDensityOp n) (P : Op n)
    (hP_proj : P * P = P) (hP_herm : P† = P) :
    traceNorm (ρ.toOp - P * ρ.toOp * P) ≤
      2 * Real.sqrt (ρ.trace * (ρ.trace - (P * ρ.toOp * P).trace.re)) := by
  classical
  -- 1) PSD bridge: lift `ρ.toPosSemidefOp` into a Mathlib `PosSemidef`.
  have h_psd : Matrix.PosSemidef ρ.toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- 2) Spectral pure-base bound (Helper 3A).
  refine le_trans
    (DistTraceBoundSpectral.traceNorm_sub_projector_sandwich_le_sum_sqrt
      h_psd P hP_proj hP_herm) ?_
  -- 3) Pull the constant `2` out of the sum:
  -- `∑ i, λ_i · (2 · √(1 - …)) = 2 · ∑ i, λ_i · √(1 - …)`.
  have h_sum_const :
      ∑ i, h_psd.1.eigenvalues i *
        (2 * Real.sqrt
          (1 - (Quantum.Operators.quadraticForm P
                  ((h_psd.1.eigenvectorBasis i).ofLp)).re))
      = 2 * ∑ i, h_psd.1.eigenvalues i *
          Real.sqrt
            (1 - (Quantum.Operators.quadraticForm P
                    ((h_psd.1.eigenvectorBasis i).ofLp)).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h_sum_const]
  -- 4) Cancel the leading `2`.
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  -- 5) Cauchy–Schwarz (Helper 3C).
  refine le_trans
    (DistTraceBoundSpectral.cauchySchwarz_sum_sqrt
      Finset.univ
      (fun i => h_psd.1.eigenvalues i)
      (fun i => 1 - (Quantum.Operators.quadraticForm P
                      ((h_psd.1.eigenvectorBasis i).ofLp)).re)
      (fun i => h_psd.eigenvalues_nonneg i)
      (fun i =>
        DistTraceBoundHelpers.one_sub_quadraticForm_nonneg
          hP_proj hP_herm
          ((h_psd.1.eigenvectorBasis i).ofLp)
          (DistTraceBoundSpectral.norm_ofLp_eigenvectorBasis_eq_one
            h_psd.1 i)))
    ?_
  -- 6) Identify the sums under the square roots.
  rw [DistTraceBoundSpectral.sum_eigenvalues_eq_re_trace h_psd.1,
      DistTraceBoundSpectral.sum_eigenvalues_one_sub_quadraticForm_eq_trace_diff
        h_psd hP_proj]
  -- 7) Conclude with `Real.sqrt_mul`. Note `ρ.trace = ρ.toOp.trace.re` by def.
  rw [Real.sqrt_mul ρ.trace_nonneg]
  exact le_refl _

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
