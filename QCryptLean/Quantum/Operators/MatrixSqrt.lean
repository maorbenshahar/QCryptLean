import QCryptLean.Quantum.Operators.Types
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Elementary square-root facts for operators

The continuous functional calculus square root `CFC.sqrt` of a positive-semidefinite
operator, and the two elementary identities that are used all over the library:

* it is positively homogeneous of degree one half, `√(c • A) = √c • √A`;
* it fixes projections, `P² = P ⪰ 0 ⟹ √P = P`.

Both are immediate from uniqueness of the positive square root (`CFC.sqrt_unique`,
`CFC.sqrt_eq_iff`).  They live here — directly above `Types.lean` — so
that consumers do not have to import the geometric-mean, fidelity or smooth-entropy
layers to scale or to take the square root of a projection.

## Main statements

* `Quantum.Operators.sqrt_ofReal_smul` — `√(c • A) = √c • √A` for `0 ≤ c` and `A ⪰ 0`.
* `Matrix.PosSemidef.sqrt_eq_self_of_isIdempotentElem` — `√P = P` for a
  positive-semidefinite idempotent `P`.

Both hypotheses of the second statement are load-bearing: a non-positive idempotent
(for instance a non-Hermitian projection) is not its own positive square root, and a
positive non-idempotent is not either.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-- The CFC square root pulls a nonnegative real scalar out as its real square
root: `√(c • A) = √c • √A` for `0 ≤ c` and positive-semidefinite `A`.

Proof by uniqueness of the positive square root: the right-hand side is positive
semidefinite and its square is `c • (√A · √A) = c • A`. -/
lemma sqrt_ofReal_smul {n : ℕ} {c : ℝ} (hc : 0 ≤ c) {M : Op n} (hM : M.PosSemidef) :
    CFC.sqrt ((Complex.ofReal c) • M) = (Complex.ofReal (Real.sqrt c)) • CFC.sqrt M := by
  have hcC : (0 : ℂ) ≤ (Complex.ofReal c) := by rw [Complex.le_def]; simp [hc]
  have hscC : (0 : ℂ) ≤ (Complex.ofReal (Real.sqrt c)) := by
    rw [Complex.le_def]; exact ⟨by simp [Real.sqrt_nonneg], by simp⟩
  have hLHS_psd : ((Complex.ofReal c) • M).PosSemidef := hM.smul hcC
  have hRHS_psd : ((Complex.ofReal (Real.sqrt c)) • CFC.sqrt M).PosSemidef :=
    (CFC.sqrt_nonneg M).posSemidef.smul hscC
  rw [CFC.sqrt_eq_iff _ _ hLHS_psd.nonneg hRHS_psd.nonneg]
  -- goal: (√c • √M) * (√c • √M) = c • M
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self M hM.nonneg]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]

/-- The CFC square root of `X` commutes with every operator commuting with `X`
(the spectral-calculus commutation pattern: `cfcₙ` applied to a commuting pair). -/
lemma sqrt_commute {n : ℕ} {X Y : Op n} (h : X * Y = Y * X) :
    CFC.sqrt X * Y = Y * CFC.sqrt X := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have hc : Commute X Y := h
  have hswap : Y * CFC.sqrt X = CFC.sqrt X * Y := by
    simp only [CFC.sqrt]
    exact (Commute.cfcₙ_nnreal hc NNReal.sqrt).symm.eq
  exact hswap.symm

end Quantum.Operators

namespace Matrix.PosSemidef

/-- **The square root of a projection is the projection.**

For a positive-semidefinite idempotent `P` (an orthogonal projection) the positive
square root is `P` itself, because `P · P = P` already exhibits `P` as a positive
square root and the positive square root is unique. -/
theorem sqrt_eq_self_of_isIdempotentElem {n : ℕ} {P : Op n} (hP : P.PosSemidef)
    (hidem : IsIdempotentElem P) : CFC.sqrt P = P :=
  CFC.sqrt_unique hidem hP.nonneg

end Matrix.PosSemidef

end -- noncomputable section
