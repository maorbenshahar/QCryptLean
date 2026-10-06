import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.TraceNorm.ScalarBlockFidelity
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Fidelity for block-diagonal tensor extensions

This module isolates the metric geometry behind CQ states whose quantum blocks
are all extended by the same normalized maximally mixed register.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-- Append a normalized maximally mixed register to a positive semidefinite
operator. This is the PSD-only analogue of `SubDensityOp.tensorMaxMixed`. -/
def PosSemidefOp.tensorMaxMixed {dE : ℕ} (dR : ℕ) [NeZero dR]
    (A : PosSemidefOp dE) : PosSemidefOp (dE * dR) where
  toOp := A.toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Quantum.TensorProducts.Op.tensor_conjTranspose]
    rw [A.isHermitian]
    congr 1
    exact (DensityOp.maxMixed dR).isHermitian
  pos_semidef := by
    exact Op.tensor_posSemidef A.toOp
      ((1 / (dR : ℂ)) • (1 : Op dR))
      A.isHermitian
      (DensityOp.maxMixed dR).isHermitian
      A.pos_semidef
      (DensityOp.maxMixed dR).pos_semidef

@[simp]
lemma PosSemidefOp.tensorMaxMixed_toOp {dE dR : ℕ} [NeZero dR]
    (A : PosSemidefOp dE) :
    (A.tensorMaxMixed dR).toOp =
      A.toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)) :=
  rfl

end Quantum.Operators

namespace Quantum.Metrics

/-- The block-diagonal PSD operator associated to a family of PSD blocks,
using the same quantum-first reindexing convention as `CQState.toJointDensity`. -/
def cqBlockPosSemidefOp {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (A : X → PosSemidefOp d) : PosSemidefOp (d * Fintype.card X) where
  toOp :=
    Matrix.reindex
      ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
      ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
      (Matrix.blockDiagonal (fun x => (A x).toOp))
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_reindex]
    congr 1
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext x
    exact (A x).isHermitian
  pos_semidef := by
    let e : Fin d × X ≃ Fin (d * Fintype.card X) :=
      (Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv
    have hpsd :
        (Matrix.reindex e e
          (Matrix.blockDiagonal (fun x => (A x).toOp))).PosSemidef := by
      rw [Matrix.reindex_apply]
      exact (Matrix.posSemidef_submatrix_equiv e.symm).mpr
        (Matrix.posSemidef_blockDiagonal fun x =>
          Quantum.Operators.posSemidefOp_implies_mathlib (A x))
    intro v
    have hv := hpsd.dotProduct_mulVec_nonneg v
    exact (Complex.nonneg_iff.mp hv).1

@[simp]
lemma cqBlockPosSemidefOp_toOp {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (A : X → PosSemidefOp d) :
    (cqBlockPosSemidefOp A).toOp =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal (fun x => (A x).toOp)) :=
  rfl

/-- The positive square root of a CQ block-diagonal PSD operator is the
block-diagonal operator of the per-block positive square roots, with the same
quantum-first reindexing as `cqBlockPosSemidefOp`. -/
lemma sqrtPosSemidefOp_cqBlock
    {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (A : X → PosSemidefOp d) :
    sqrtPosSemidefOp (cqBlockPosSemidefOp A) =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal (fun x => sqrtPosSemidefOp (A x))) := by
  let e : Fin d × X ≃ Fin (d * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv
  unfold sqrtPosSemidefOp
  letI : PartialOrder (Op (d * Fintype.card X)) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op (d * Fintype.card X)) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op (d * Fintype.card X)) :=
    Matrix.instNonnegSpectrumClass
  refine CFC.sqrt_unique
    (a := (cqBlockPosSemidefOp A).toOp)
    (b := Matrix.reindex e e
      (Matrix.blockDiagonal (fun x => CFC.sqrt (A x).toOp))) ?_ ?_
  · change Matrix.reindex e e
        (Matrix.blockDiagonal (fun x => CFC.sqrt (A x).toOp)) *
        Matrix.reindex e e
          (Matrix.blockDiagonal (fun x => CFC.sqrt (A x).toOp)) =
      (cqBlockPosSemidefOp A).toOp
    rw [cqBlockPosSemidefOp_toOp]
    simp only [← Matrix.reindexLinearEquiv_apply ℂ ℂ]
    rw [Matrix.reindexLinearEquiv_mul]
    simp only [Matrix.reindexLinearEquiv_apply]
    rw [← Matrix.blockDiagonal_mul]
    change Matrix.reindex e e
        (Matrix.blockDiagonal (fun x => CFC.sqrt (A x).toOp * CFC.sqrt (A x).toOp)) =
      Matrix.reindex e e (Matrix.blockDiagonal (fun x => (A x).toOp))
    apply congrArg (fun M => Matrix.reindex e e M)
    ext i j
    by_cases hij : i.2 = j.2
    · simpa [Matrix.blockDiagonal_apply, hij, sqrtPosSemidefOp] using
        congr_fun₂ (sqrtPosSemidefOp_sq (A j.2)) i.1 j.1
    · simp [Matrix.blockDiagonal_apply, hij]
  · rw [Matrix.nonneg_iff_posSemidef]
    rw [Matrix.reindex_apply]
    exact (Matrix.posSemidef_submatrix_equiv e.symm).mpr
      (Matrix.posSemidef_blockDiagonal fun x => by
        simpa [sqrtPosSemidefOp] using sqrtPosSemidefOp_posSemidef (A x))

/-- The trace-norm fidelity expression of two block-diagonal PSD operators
decomposes as the sum of the blockwise trace-norm fidelity expressions.

This is the block-diagonal square-root/fidelity counterpart of
`traceNorm_blockDiagonal`. -/
theorem traceNorm_sqrtProduct_cqBlock_eq_sum
    {X : Type*} [Fintype X] [DecidableEq X]
    {d : ℕ} [NeZero d] [NeZero (d * Fintype.card X)]
    (A B : X → PosSemidefOp d) :
    traceNorm
        (sqrtPosSemidefOp (cqBlockPosSemidefOp A) *
          sqrtPosSemidefOp (cqBlockPosSemidefOp B)) =
      ∑ x : X, traceNorm (sqrtPosSemidefOp (A x) * sqrtPosSemidefOp (B x)) := by
  haveI : NeZero (Fintype.card X) := ⟨by
    intro h
    exact NeZero.ne (d * Fintype.card X) (by rw [h, Nat.mul_zero])⟩
  let e : Fin d × X ≃ Fin (d * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin X)).trans finProdFinEquiv
  rw [sqrtPosSemidefOp_cqBlock A, sqrtPosSemidefOp_cqBlock B]
  have hmul :
      Matrix.reindex e e (Matrix.blockDiagonal (fun x => sqrtPosSemidefOp (A x))) *
        Matrix.reindex e e (Matrix.blockDiagonal (fun x => sqrtPosSemidefOp (B x))) =
      Matrix.reindex e e
        (Matrix.blockDiagonal
          (fun x => sqrtPosSemidefOp (A x) * sqrtPosSemidefOp (B x))) := by
    simp only [← Matrix.reindexLinearEquiv_apply ℂ ℂ]
    rw [Matrix.reindexLinearEquiv_mul]
    simp only [Matrix.reindexLinearEquiv_apply]
    rw [← Matrix.blockDiagonal_mul]
  rw [hmul]
  exact traceNorm_blockDiagonal
    (fun x : X => sqrtPosSemidefOp (A x) * sqrtPosSemidefOp (B x))

/-- Tensoring an operator with an identity register repeats its singular values
once for each basis state of the register. -/
lemma traceNorm_tensor_one {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (M : Op dE) :
    traceNorm (M ⊗ (1 : Op dR)) = dR * traceNorm M := by
  have hsum :
      M ⊗ (1 : Op dR) =
        ∑ i : Fin dR, M ⊗ (Matrix.single i i 1 : Op dR) := by
    ext p q
    simp only [Quantum.TensorProducts.Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply,
      finProdFinEquiv_symm_apply, mul_ite, mul_one, mul_zero]
    by_cases h : p.modNat = q.modNat
    · simp [h]
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x = p.modNat ∧ x = q.modNat
      · exact False.elim (h (hx.1.symm.trans hx.2))
      · simp [hx]
  rw [hsum, traceNorm_blockDiagonal_sum]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The positive square root of tensoring a PSD operator by the normalized
identity is the tensor of the positive square root with the identity, scaled by
`1 / sqrt dR`. -/
lemma sqrtPosSemidefOp_tensorMaxMixed {dE dR : ℕ} [NeZero dR]
    (A : PosSemidefOp dE) :
    sqrtPosSemidefOp (A.tensorMaxMixed dR) =
      ((1 / Real.sqrt (dR : ℝ)) : ℝ) •
        (sqrtPosSemidefOp A ⊗ (1 : Op dR)) := by
  let r : ℝ := 1 / Real.sqrt (dR : ℝ)
  have hr_nonneg : 0 ≤ r := by
    unfold r
    positivity
  have hr_sq : r * r = 1 / (dR : ℝ) := by
    have hsqrt_ne : Real.sqrt (dR : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne dR))))
    have hsqrt_sq : Real.sqrt (dR : ℝ) * Real.sqrt (dR : ℝ) = (dR : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt (Nat.cast_nonneg dR)
    unfold r
    calc
      (1 / Real.sqrt (dR : ℝ)) * (1 / Real.sqrt (dR : ℝ))
          = 1 / (Real.sqrt (dR : ℝ) * Real.sqrt (dR : ℝ)) := by
            field_simp [hsqrt_ne]
      _ = 1 / (dR : ℝ) := by rw [hsqrt_sq]
  have hr_sq_complex : ((r * r : ℝ) : ℂ) = 1 / (dR : ℂ) := by
    rw [hr_sq]
    simp
  unfold sqrtPosSemidefOp
  letI : PartialOrder (Op (dE * dR)) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op (dE * dR)) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op (dE * dR)) := Matrix.instNonnegSpectrumClass
  refine CFC.sqrt_unique
    (a := (A.tensorMaxMixed dR).toOp)
    (b := r • (CFC.sqrt A.toOp ⊗ (1 : Op dR))) ?_ ?_
  · change (r • (CFC.sqrt A.toOp ⊗ (1 : Op dR))) *
        (r • (CFC.sqrt A.toOp ⊗ (1 : Op dR))) =
      (A.tensorMaxMixed dR).toOp
    rw [PosSemidefOp.tensorMaxMixed_toOp]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Quantum.TensorProducts.Op.tensor_mul, Matrix.mul_one]
    have hsqrt_sq : CFC.sqrt A.toOp * CFC.sqrt A.toOp = A.toOp := by
      simpa [sqrtPosSemidefOp] using sqrtPosSemidefOp_sq A
    rw [hsqrt_sq]
    change (((r * r : ℝ) : ℂ) • (A.toOp ⊗ (1 : Op dR))) =
      A.toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))
    rw [← Quantum.TensorProducts.Op.tensor_smul_right]
    rw [hr_sq_complex]
  · have hTensor : (CFC.sqrt A.toOp ⊗ (1 : Op dR)).PosSemidef := by
      exact Quantum.TensorProducts.Op.tensor_posSemidef_mathlib
        (by simpa [sqrtPosSemidefOp] using sqrtPosSemidefOp_posSemidef A)
        Matrix.PosSemidef.one
    have hTensor_nonneg : 0 ≤ (CFC.sqrt A.toOp ⊗ (1 : Op dR)) := by
      rw [Matrix.nonneg_iff_posSemidef]
      exact hTensor
    exact smul_nonneg hr_nonneg hTensor_nonneg

/-- Tensoring two PSD operators with the same normalized maximally mixed
register preserves the trace-norm fidelity expression. -/
theorem traceNorm_sqrtProduct_tensorMaxMixed_eq
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (A B : PosSemidefOp dE) :
    traceNorm
        (sqrtPosSemidefOp (A.tensorMaxMixed dR) *
          sqrtPosSemidefOp (B.tensorMaxMixed dR)) =
      traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B) := by
  rw [sqrtPosSemidefOp_tensorMaxMixed A, sqrtPosSemidefOp_tensorMaxMixed B]
  let r : ℝ := 1 / Real.sqrt (dR : ℝ)
  have hr_nonneg : 0 ≤ r := by
    unfold r
    positivity
  have hr_sq : r * r = 1 / (dR : ℝ) := by
    have hsqrt_ne : Real.sqrt (dR : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne dR))))
    have hsqrt_sq : Real.sqrt (dR : ℝ) * Real.sqrt (dR : ℝ) = (dR : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt (Nat.cast_nonneg dR)
    unfold r
    calc
      (1 / Real.sqrt (dR : ℝ)) * (1 / Real.sqrt (dR : ℝ))
          = 1 / (Real.sqrt (dR : ℝ) * Real.sqrt (dR : ℝ)) := by
            field_simp [hsqrt_ne]
      _ = 1 / (dR : ℝ) := by rw [hsqrt_sq]
  change traceNorm
      ((r • (sqrtPosSemidefOp A ⊗ (1 : Op dR))) *
        (r • (sqrtPosSemidefOp B ⊗ (1 : Op dR)))) =
    traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B)
  have hprod :
      (r • (sqrtPosSemidefOp A ⊗ (1 : Op dR))) *
          (r • (sqrtPosSemidefOp B ⊗ (1 : Op dR))) =
        (r * r) •
          ((sqrtPosSemidefOp A * sqrtPosSemidefOp B) ⊗ (1 : Op dR)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Quantum.TensorProducts.Op.tensor_mul, Matrix.one_mul]
  rw [hprod]
  change traceNorm
      ((((r * r : ℝ) : ℂ) •
        ((sqrtPosSemidefOp A * sqrtPosSemidefOp B) ⊗ (1 : Op dR)))) =
    traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B)
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  rw [traceNorm_tensor_one]
  have hcoeff_norm : ‖((r * r : ℝ) : ℂ)‖ = 1 / (dR : ℝ) := by
    rw [Complex.norm_of_nonneg (mul_nonneg hr_nonneg hr_nonneg), hr_sq]
  rw [hcoeff_norm]
  have hdR_ne : (dR : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne dR
  field_simp [hdR_ne]

/-- Appending the same normalized maximally mixed register to every block of two
block-diagonal PSD operators preserves the trace-norm fidelity expression.

This is the lower-level metric/tensor fact needed by the CQ purified-distance
contraction. It should follow by combining a block-diagonal fidelity
decomposition with fidelity preservation under tensoring both PSD arguments by
`I / dR`. -/
theorem traceNorm_sqrtProduct_cqBlock_tensorMaxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (A B : X → PosSemidefOp dE) :
    traceNorm
        (sqrtPosSemidefOp
            (cqBlockPosSemidefOp (fun x => (A x).tensorMaxMixed dR)) *
          sqrtPosSemidefOp
            (cqBlockPosSemidefOp (fun x => (B x).tensorMaxMixed dR))) =
    traceNorm
        (sqrtPosSemidefOp (cqBlockPosSemidefOp A) *
          sqrtPosSemidefOp (cqBlockPosSemidefOp B)) := by
  haveI : NeZero (dE * dR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  calc
    traceNorm
        (sqrtPosSemidefOp
            (cqBlockPosSemidefOp (fun x => (A x).tensorMaxMixed dR)) *
          sqrtPosSemidefOp
            (cqBlockPosSemidefOp (fun x => (B x).tensorMaxMixed dR)))
        = ∑ x : X,
            traceNorm
              (sqrtPosSemidefOp ((A x).tensorMaxMixed dR) *
                sqrtPosSemidefOp ((B x).tensorMaxMixed dR)) := by
          exact traceNorm_sqrtProduct_cqBlock_eq_sum
            (fun x => (A x).tensorMaxMixed dR)
            (fun x => (B x).tensorMaxMixed dR)
    _ = ∑ x : X,
            traceNorm (sqrtPosSemidefOp (A x) * sqrtPosSemidefOp (B x)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact traceNorm_sqrtProduct_tensorMaxMixed_eq (A x) (B x)
    _ = traceNorm
        (sqrtPosSemidefOp (cqBlockPosSemidefOp A) *
          sqrtPosSemidefOp (cqBlockPosSemidefOp B)) := by
          exact (traceNorm_sqrtProduct_cqBlock_eq_sum A B).symm

end Quantum.Metrics

end
