import QCryptLean.Quantum.Metrics.TraceNorm.ScalarBlock
import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Scalar block fidelity

Helper facts for one-dimensional scalar-block extensions of positive
semidefinite operators: Hermiticity, positivity, multiplication, trace norm,
square roots, and fidelity.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace Quantum.Metrics

/-- Add a one-dimensional scalar block to the bottom-right corner of a matrix,
viewed on `Fin (n + 1)` through `finSumFinEquiv`. -/
def scalarBlockMatrix {n : ℕ} (A : Op n) (a : ℝ) : Op (n + 1) :=
  (Matrix.fromBlocks A
      (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ)
      ((a : ℂ) • (1 : Op 1))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- A real scalar multiple of the `1×1` identity is the corresponding diagonal matrix. -/
lemma scalarBlock_one_eq_diagonal (a : ℝ) :
    ((a : ℂ) • (1 : Op 1)) =
      Matrix.diagonal (fun _ : Fin 1 => (a : ℂ)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- A real scalar multiple of the `1×1` identity is Hermitian. -/
lemma scalarBlock_one_isHermitian (a : ℝ) :
    (((a : ℂ) • (1 : Op 1))).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp [Complex.conj_ofReal]

/-- A nonnegative real scalar multiple of the `1×1` identity is positive semidefinite. -/
lemma scalarBlock_one_posSemidef (a : ℝ) (ha : 0 ≤ a) :
    (((a : ℂ) • (1 : Op 1))).PosSemidef := by
  rw [scalarBlock_one_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (a : ℂ)
  rw [Complex.nonneg_iff]
  exact ⟨ha, by simp⟩

/-- Multiplication of `1×1` scalar blocks multiplies the underlying real scalars. -/
lemma scalarBlock_one_mul (a b : ℝ) :
    ((a : ℂ) • (1 : Op 1)) *
      ((b : ℂ) • (1 : Op 1)) =
        (((a * b : ℝ) : ℂ) • (1 : Op 1)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Matrix.smul_apply, ← Complex.ofReal_mul]

/-- Adding a real scalar block preserves Hermiticity. -/
lemma scalarBlockMatrix_isHermitian {n : ℕ} {A : Op n}
    (hA : A.IsHermitian) (a : ℝ) :
    (scalarBlockMatrix A a).IsHermitian := by
  unfold scalarBlockMatrix
  apply Matrix.IsHermitian.submatrix
  exact Matrix.IsHermitian.fromBlocks hA (by simp) (scalarBlock_one_isHermitian a)

/-- Adding a nonnegative scalar block to a positive semidefinite operator is
positive semidefinite. -/
lemma scalarBlockMatrix_posSemidef {n : ℕ}
    (A : PosSemidefOp n) (a : ℝ) (ha : 0 ≤ a) :
    (scalarBlockMatrix A.toOp a).PosSemidef := by
  unfold scalarBlockMatrix
  exact (Matrix.PosSemidef.fromBlocks_zero
    (Quantum.Operators.posSemidefOp_implies_mathlib A)
    (scalarBlock_one_posSemidef a ha)).submatrix _

/-- Multiplication of scalar-block matrices is blockwise multiplication. -/
lemma scalarBlockMatrix_mul {n : ℕ} (A B : Op n) (a b : ℝ) :
    scalarBlockMatrix A a * scalarBlockMatrix B b =
      scalarBlockMatrix (A * B) (a * b) := by
  unfold scalarBlockMatrix
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, scalarBlock_one_mul]

/-- Trace norm of a scalar-block matrix is the trace norm of the main block plus the scalar. -/
lemma traceNorm_scalarBlockMatrix {n : ℕ} [NeZero n]
    (M : Op n) (c : ℝ) (hc : 0 ≤ c) :
    traceNorm (scalarBlockMatrix M c) = traceNorm M + c := by
  unfold scalarBlockMatrix
  rw [scalarBlock_one_eq_diagonal c]
  simpa using traceNorm_fromBlocks_scalar M c hc

/-- The positive semidefinite operator `A ⊕ a`, where `a ≥ 0` is a
one-dimensional scalar block. -/
def scalarBlockPosSemidefOp {n : ℕ}
    (A : PosSemidefOp n) (a : ℝ) (ha : 0 ≤ a) : PosSemidefOp (n + 1) where
  toOp := scalarBlockMatrix A.toOp a
  isHermitian := scalarBlockMatrix_isHermitian A.isHermitian a
  pos_semidef := by
    intro x
    have h := (scalarBlockMatrix_posSemidef A a ha).dotProduct_mulVec_nonneg x
    exact (Complex.nonneg_iff.mp h).1

/-- The positive square root of a positive semidefinite operator is positive semidefinite. -/
lemma sqrtPosSemidefOp_posSemidef {n : ℕ} (A : PosSemidefOp n) :
    (sqrtPosSemidefOp A).PosSemidef := by
  unfold sqrtPosSemidefOp
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  exact (CFC.sqrt_nonneg (a := A.toOp)).posSemidef

/-- Square root of a PSD operator with a one-dimensional scalar block. -/
lemma sqrtPosSemidefOp_scalarBlock {n : ℕ}
    (A : PosSemidefOp n) (a : ℝ) (ha : 0 ≤ a) :
    sqrtPosSemidefOp (scalarBlockPosSemidefOp A a ha) =
      scalarBlockMatrix (sqrtPosSemidefOp A) (Real.sqrt a) := by
  unfold sqrtPosSemidefOp
  let : PartialOrder (Op (n + 1)) := Matrix.instPartialOrder
  let : StarOrderedRing (Op (n + 1)) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op (n + 1)) := Matrix.instNonnegSpectrumClass
  refine CFC.sqrt_unique
    (a := (scalarBlockPosSemidefOp A a ha).toOp)
    (b := scalarBlockMatrix (CFC.sqrt A.toOp) (Real.sqrt a)) ?_ ?_
  · rw [scalarBlockMatrix_mul]
    change scalarBlockMatrix (CFC.sqrt A.toOp * CFC.sqrt A.toOp)
        (Real.sqrt a * Real.sqrt a) =
      scalarBlockMatrix A.toOp a
    have hsqrt_sq : CFC.sqrt A.toOp * CFC.sqrt A.toOp = A.toOp := by
      simpa [sqrtPosSemidefOp] using sqrtPosSemidefOp_sq A
    rw [hsqrt_sq]
    congr 1
    exact Real.mul_self_sqrt ha
  · rw [Matrix.nonneg_iff_posSemidef]
    have hsqrtA : (CFC.sqrt A.toOp).PosSemidef := by
      simpa [sqrtPosSemidefOp] using sqrtPosSemidefOp_posSemidef A
    simpa [scalarBlockMatrix] using
      (Matrix.PosSemidef.fromBlocks_zero hsqrtA
        (scalarBlock_one_posSemidef (Real.sqrt a) (Real.sqrt_nonneg a))).submatrix
        finSumFinEquiv.symm

/-- Fidelity of scalar-block extensions splits into the original fidelity plus
the geometric mean of the two scalar blocks. -/
lemma fidelity_scalarBlock {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    fidelity (scalarBlockPosSemidefOp A a ha) (scalarBlockPosSemidefOp B b hb) =
      fidelity A B + Real.sqrt (a * b) := by
  rw [fidelity_eq_traceNorm_sqrtProduct,
    sqrtPosSemidefOp_scalarBlock A a ha,
    sqrtPosSemidefOp_scalarBlock B b hb]
  rw [scalarBlockMatrix_mul]
  have hsqrt_mul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul ha]
  rw [hsqrt_mul]
  rw [traceNorm_scalarBlockMatrix _ _ (Real.sqrt_nonneg _)]
  rw [← fidelity_eq_traceNorm_sqrtProduct A B]

end Quantum.Metrics

end
