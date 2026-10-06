import QCryptLean.Quantum.Operators.Types
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Principal Submatrices of Density Operators — Hermiticity, positivity, and trace bounds

Reusable operator facts for extracting principal submatrices from density
operators and positive semidefinite matrices.

## Main statements
- `densityOp_submatrix_isHermitian`: a principal submatrix of a density operator is Hermitian.
- `densityOp_submatrix_pos_semidef`: a principal submatrix of a density operator is PSD.
- `trace_re_submatrix_eq_sum_diag_re`: the trace of a principal submatrix is the sum
  of the selected diagonal entries.
- `posSemidef_submatrix_trace_re_le_sum_diag_re`: an injectively indexed principal
  submatrix has trace bounded by the full PSD diagonal sum.
- `densityOp_submatrix_trace_le_one`: an injectively indexed principal submatrix of a
  density operator has trace at most one.
-/

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace Quantum.Operators

/-- A principal submatrix of a density operator is Hermitian. -/
lemma densityOp_submatrix_isHermitian {N m : ℕ} (ρ : DensityOp N)
    (e : Fin m → Fin N) :
    (ρ.toOp.submatrix e e).IsHermitian :=
  (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).isHermitian.submatrix e

/-- A principal submatrix of a density operator has nonnegative real quadratic form. -/
lemma densityOp_submatrix_pos_semidef {N m : ℕ} (ρ : DensityOp N)
    (e : Fin m → Fin N) :
    ∀ x : Fin m → ℂ, 0 ≤ (quadraticForm (ρ.toOp.submatrix e e) x).re := by
  intro x
  have hpsd : (ρ.toOp.submatrix e e).PosSemidef :=
    (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).submatrix e
  have hnn : 0 ≤ star x ⬝ᵥ (ρ.toOp.submatrix e e).mulVec x :=
    hpsd.dotProduct_mulVec_nonneg x
  exact (Complex.nonneg_iff.mp (by simpa [quadraticForm] using hnn)).1

/-- The real trace of a principal submatrix is the sum of the corresponding
ambient diagonal real parts. -/
lemma trace_re_submatrix_eq_sum_diag_re {N m : ℕ}
    (A : Op N) (e : Fin m → Fin N) :
    (A.submatrix e e).trace.re = ∑ i : Fin m, (A (e i) (e i)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Complex.re_sum]

/-- The sum of diagonal real parts of a density operator is one. -/
lemma densityOp_sum_diag_re_eq_one {N : ℕ} (ρ : DensityOp N) :
    (∑ i : Fin N, (ρ.toOp i i).re) = 1 := by
  rw [← hermitian_trace_eq_sum_diag_re ρ.toOp
    ρ.toPosSemidefOp.toHermitianOp.isHermitian]
  simpa using congrArg Complex.re ρ.trace_one

/-- The real trace of an injective principal submatrix of a PSD matrix is bounded
by the full sum of its diagonal real parts. -/
lemma posSemidef_submatrix_trace_re_le_sum_diag_re {N m : ℕ}
    {A : Op N} (hA : A.PosSemidef)
    (e : Fin m → Fin N) (he : Function.Injective e) :
    (A.submatrix e e).trace.re ≤ ∑ j : Fin N, (A j j).re := by
  let emb : Fin m ↪ Fin N := ⟨e, he⟩
  calc
    (A.submatrix e e).trace.re
        = ∑ i : Fin m, (A (e i) (e i)).re :=
            trace_re_submatrix_eq_sum_diag_re A e
    _ = ∑ j ∈ (Finset.univ.map emb), (A j j).re := by
        symm
        simp only [Finset.sum_map]
        rfl
    _ ≤ ∑ j : Fin N, (A j j).re :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun j => psd_diag_re_nonneg A hA j)

/-- The trace of an injectively indexed principal submatrix of a density operator is at most one. -/
lemma densityOp_submatrix_trace_le_one {N m : ℕ} (ρ : DensityOp N)
    (e : Fin m → Fin N) (he : Function.Injective e) :
    (ρ.toOp.submatrix e e).trace.re ≤ 1 := by
  calc
    (ρ.toOp.submatrix e e).trace.re
        ≤ ∑ j : Fin N, (ρ.toOp j j).re :=
          posSemidef_submatrix_trace_re_le_sum_diag_re
            (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) e he
    _ = 1 := densityOp_sum_diag_re_eq_one ρ

end Quantum.Operators

end -- noncomputable section
