import QCryptLean.Quantum.TensorProducts.Basic

/-!
# Unitary Action on Purification Kets

Small helper lemmas about applying a tensor-unitary on the system factor to a
normalized ket.

## Main statements

- `dag_op_mul_ket`: conjugate of a matrix-action on a ket,
  `(A * ψ).dag = ψ.dag * A†`.
- `tensorUnitary_ket_normalized`: for any `U : UnitaryOp d` and any normalized
  `ψ : Ket (d * d)` the rotated ket `(tensorUnitary U).toOp.mulVec ψ.vec` is
  again normalized.
- `op_op_mul_ket_assoc`: associativity of the operator-operator-ket action.
- `tensor_unitary_overlap_expand`: overlap expansion for two system-side
  tensor-unitary rotations of kets.
-/

open Quantum.Operators Quantum.TensorProducts Matrix

noncomputable section

namespace Quantum.Metrics.KitaevWatrousPurification

/-- Conjugate of a matrix-action ket: `(A * ψ).dag = ψ.dag * A†`. -/
lemma dag_op_mul_ket {n : ℕ} (A : Op n) (ψ : Ket n) :
    (A * ψ).dag = ψ.dag * A† := by
  ext j
  simp only [Ket.dag_vec, bra_mul_op_vec, Matrix.conjTranspose_apply, op_mul_ket_vec,
    Matrix.mulVec, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- Rotating a normalized ket by a tensor-unitary on the system factor
preserves normalization. -/
lemma tensorUnitary_ket_normalized
    {d : ℕ} (U : UnitaryOp d) (ψ : Ket (d * d))
    (hψ : ψ.dag * ψ = 1) :
    (⟨(tensorUnitary U).toOp.mulVec ψ.vec⟩ : Ket (d * d)).dag *
        (⟨(tensorUnitary U).toOp.mulVec ψ.vec⟩ : Ket (d * d)) = 1 := by
  set Ut : UnitaryOp (d * d) := tensorUnitary U with hUt
  change dotProduct (star (Ut.toOp.mulVec ψ.vec)) (Ut.toOp.mulVec ψ.vec) = 1
  rw [Ut.preserves_inner]
  exact hψ

/-- Associativity of `Op * Op * Ket`: acting sequentially by `B` then `A` on a
ket is the same as acting by the product `A * B`. -/
lemma op_op_mul_ket_assoc
    {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A * (B * ψ : Ket n) : Ket n) = ((A * B : Op n) * ψ : Ket n) := by
  ext i
  simp only [op_mul_ket_vec]
  rw [Matrix.mulVec_mulVec]

/-- Overlap expansion for two system-side tensor-unitary rotations of arbitrary
kets: `((U ⊗ 1) ψρ).dag * ((V ⊗ 1) ψτ) = ψρ.dag * ((U† * V) ⊗ 1) * ψτ`. -/
lemma tensor_unitary_overlap_expand
    {d : ℕ} (U V : UnitaryOp d) (ψρ ψτ : Ket (d * d)) :
    (((Op.tensor U.toOp (1 : Op d)) * ψρ : Ket (d * d)).dag *
        ((Op.tensor V.toOp (1 : Op d)) * ψτ : Ket (d * d)) : ℂ) =
      (ψρ.dag *
        (Op.tensor (U.toOp.conjTranspose * V.toOp) (1 : Op d)) * ψτ : ℂ) := by
  set A : Op (d * d) := Op.tensor U.toOp (1 : Op d) with hA
  set B : Op (d * d) := Op.tensor V.toOp (1 : Op d) with hB
  have hdag : ((A * ψρ : Ket (d * d)).dag : Bra (d * d)) = ψρ.dag * A† :=
    dag_op_mul_ket A ψρ
  have hassoc : A† * (B * ψτ : Ket (d * d)) = ((A† * B : Op (d * d)) * ψτ : Ket (d * d)) :=
    op_op_mul_ket_assoc A† B ψτ
  have hAB : A† * B =
      Op.tensor (U.toOp.conjTranspose * V.toOp) (1 : Op d) := by
    simp [A, B, Op.tensor_conjTranspose, Op.tensor_mul]
  calc (((A * ψρ : Ket (d * d)).dag * ((B * ψτ : Ket (d * d))) : ℂ))
      = ((ψρ.dag * A†) * (B * ψτ : Ket (d * d)) : ℂ) := by rw [hdag]
    _ = (ψρ.dag * (A† * (B * ψτ : Ket (d * d))) : ℂ) := by rw [braop_mul_ket]
    _ = (ψρ.dag * ((A† * B : Op (d * d)) * ψτ : Ket (d * d)) : ℂ) := by rw [hassoc]
    _ = (ψρ.dag * (A† * B) * ψτ : ℂ) := by rw [← braop_mul_ket]
    _ = (ψρ.dag *
          (Op.tensor (U.toOp.conjTranspose * V.toOp) (1 : Op d)) * ψτ : ℂ) := by
        rw [hAB]

end Quantum.Metrics.KitaevWatrousPurification

end -- noncomputable section
