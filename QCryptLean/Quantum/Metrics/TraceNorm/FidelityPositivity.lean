import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.TensorProducts.PSDOrder
import Mathlib.Analysis.Matrix.PosDef

/-!
# Strict positivity of the Uhlmann fidelity against a positive-definite reference

This module supplies `fidelity_pos_of_posDef`: the max-side guarded family of
`bipartiteMaxEntropyOptReal` is nonempty for a positive-definite reference `ς` and a nonzero
state `ρ`, which reduces to `0 < fidelity ρ ς`.

This is the fidelity analogue of the min-side feasibility lemma
`hasDmaxFeasibleLambda_of_posDef_reference`.

## Main statement

- `Quantum.Metrics.fidelity_pos_of_posDef`: `0 < F(A, B)` for `A` positive
  semidefinite with `A ≠ 0` and `B` positive definite.

## Proof of `fidelity_pos_of_posDef`

`F(A, B) = Tr √(√A · B · √A)`. Write `S = √A` and `M = S · B · S`. Since `A ≠ 0`
we have `S ≠ 0`, so `S` acts nontrivially on some vector `u` (i.e. `S u ≠ 0`).
Positive definiteness of `B` then gives `⟨u | M | u⟩ = ⟨S u | B | S u⟩ > 0`, so
`M ≠ 0`. Hence `√M ≠ 0` (a nonzero square root of a nonzero PSD operator), and a
nonzero PSD operator has strictly positive trace (`Matrix.PosSemidef.trace_eq_zero_iff`),
giving `Tr √M ≠ 0`. Combined with `0 ≤ F(A, B)` this yields `0 < F(A, B)`.

This route avoids Löwner-order monotonicity of `Tr ∘ √` (the operator-monotone
square root), which is not available in Mathlib; the strict positivity is
extracted directly from the quadratic form of the sandwiched reference.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- **Strict positivity of fidelity against a positive-definite reference (B-fidpos).**

For a positive-semidefinite operator `A` with `A ≠ 0` and a positive-definite
operator `B`, the Uhlmann fidelity is strictly positive: `0 < F(A, B)`.

This is the fidelity analogue of the min-side feasibility lemma
`hasDmaxFeasibleLambda_of_posDef_reference`; it certifies that the max-side
guarded family in `bipartiteMaxEntropyOptReal` is nonempty for any nonzero state.

Proof: with `S = √A` and `M = S · B · S`, `A ≠ 0` forces `S ≠ 0`, so `S u ≠ 0`
for some `u`; positive definiteness of `B` gives `⟨u | M | u⟩ = ⟨S u | B | S u⟩ > 0`,
so `M ≠ 0`, whence `√M ≠ 0` and `Tr √M ≠ 0`. -/
theorem fidelity_pos_of_posDef {n : ℕ} [NeZero n] (A B : PosSemidefOp n)
    (hA : A.toOp ≠ 0) (hB : B.toOp.PosDef) : 0 < fidelity A B := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have hfid :
      fidelity A B =
        (Matrix.trace
          (CFC.sqrt (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A))).re := rfl
  set S := sqrtPosSemidefOp A with hS
  set M := S * B.toOp * S with hM
  -- `√A` is Hermitian and squares to `A`.
  have hSeq : (Sᴴ : Op n) = S := sqrtPosSemidefOp_isHermitian A
  have hSsq : S * S = A.toOp := sqrtPosSemidefOp_sq A
  -- `M = √A · B · √A` is positive semidefinite.
  have hM_psd : M.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same (posSemidefOp_implies_mathlib B) S
    rw [hSeq] at h
    rwa [hM]
  -- `A ≠ 0` forces `√A ≠ 0`.
  have hS_ne : S ≠ 0 := by
    intro h0
    apply hA
    rw [← hSsq, h0, Matrix.zero_mul]
  -- A nonzero matrix acts nontrivially on some vector.
  obtain ⟨u, hu⟩ : ∃ u, S.mulVec u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hS_ne
    ext i j
    have hj := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using hj
  -- The sandwiched quadratic form is strictly positive by positive definiteness of `B`.
  have hsand : quadraticForm M u = quadraticForm B.toOp (S.mulVec u) := by
    rw [hM]
    exact quadraticForm_sandwich_self_of_isHermitian hSeq B.toOp u
  have hqpos : (0 : ℂ) < quadraticForm M u := by
    rw [hsand]
    simpa [quadraticForm] using hB.dotProduct_mulVec_pos hu
  -- Hence `M ≠ 0`.
  have hM_ne : M ≠ 0 := by
    intro h0
    rw [h0] at hqpos
    simp [quadraticForm] at hqpos
  -- `√M ≠ 0` (a nonzero square root of a nonzero PSD operator).
  have hsqrtM_sq : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM_psd.nonneg
  have hsqrtM_ne : CFC.sqrt M ≠ 0 := by
    intro h0
    apply hM_ne
    rw [← hsqrtM_sq, h0, Matrix.zero_mul]
  have hsqrtM_psd : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg (a := M)).posSemidef
  -- A nonzero PSD operator has nonzero trace.
  have htr_ne : Matrix.trace (CFC.sqrt M) ≠ 0 :=
    fun h0 => hsqrtM_ne (hsqrtM_psd.trace_eq_zero_iff.mp h0)
  have him : (Matrix.trace (CFC.sqrt M)).im = 0 :=
    (Complex.le_def.mp hsqrtM_psd.trace_nonneg).2.symm
  -- Conclude `0 < F(A, B)` from nonnegativity and `Tr √M ≠ 0`.
  refine (fidelity_nonneg_posSemidefOp A B).lt_of_ne (fun hz => ?_)
  apply htr_ne
  have hzre : (Matrix.trace (CFC.sqrt M)).re = 0 := by
    have := hz.symm
    rw [hfid] at this
    exact this
  exact Complex.ext (by simpa using hzre) (by simpa using him)

end Quantum.Metrics

end
