import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic

/-!
# Environment Block Isometries — rectangular identity lifts

This file contains generic block-matrix lemmas for lifting rectangular
environment maps by an identity register.

## Main definitions
- `idTensorRectBlock`: block-diagonal lift of a rectangular environment matrix.

## Main statements
- `idTensorRectBlock_mul`: lifted blocks multiply by multiplying their environment blocks.
- `idTensorRectBlock_conjTranspose`: the adjoint of a lifted block is the lifted adjoint.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Block-diagonal lift of a rectangular environment matrix by the identity on a
finite register. -/
def idTensorRectBlock (B E E' : ℕ) (V : Matrix (Fin E) (Fin E') ℂ) :
    Matrix (Fin (B * E)) (Fin (B * E')) ℂ :=
  Matrix.of fun p q =>
    let ⟨a, e⟩ := finProdFinEquiv.symm p
    let ⟨b, f⟩ := finProdFinEquiv.symm q
    if a = b then V e f else 0

/-- Block-diagonal identity lifts multiply by multiplying their environment
blocks. -/
theorem idTensorRectBlock_mul
    {B E F G : ℕ} [NeZero B] [NeZero E] [NeZero F] [NeZero G]
    (V : Matrix (Fin E) (Fin F) ℂ) (W : Matrix (Fin F) (Fin G) ℂ) :
    idTensorRectBlock B E G (V * W) =
      idTensorRectBlock B E F V * idTensorRectBlock B F G W := by
  ext p q
  simp only [idTensorRectBlock, Matrix.of_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  by_cases hab : p.divNat = q.divNat
  · rw [Finset.sum_eq_single p.divNat]
    · simp [hab]
    · intro c _ hcp
      apply Finset.sum_eq_zero
      intro g _
      by_cases hcq : c = q.divNat
      · exact (hcp (hcq.trans hab.symm)).elim
      · simp [hcq]
    · simp
  · apply Eq.symm
    rw [Finset.sum_eq_zero]
    · simp [hab]
    · intro c _
      apply Finset.sum_eq_zero
      intro g _
      by_cases hcp : p.divNat = c
      · have hqc : ¬ c = q.divNat := fun hcq => hab (hcp.trans hcq)
        simp [hcp, hqc]
      · simp [hcp]

/-- The adjoint of a block-diagonal identity lift is the lift of the adjoint
environment block. -/
theorem idTensorRectBlock_conjTranspose
    {B E E' : ℕ} [NeZero B] [NeZero E] [NeZero E']
    (V : Matrix (Fin E) (Fin E') ℂ) :
    (idTensorRectBlock B E E' V)ᴴ = idTensorRectBlock B E' E Vᴴ := by
  ext p q
  simp only [idTensorRectBlock, Matrix.of_apply, Matrix.conjTranspose_apply,
    finProdFinEquiv_symm_apply]
  by_cases hab : q.divNat = p.divNat
  · have hba : p.divNat = q.divNat := hab.symm
    rw [ite_eq_left hab, ite_eq_left hba]
  · have hba : ¬ p.divNat = q.divNat := by
      simpa [eq_comm] using hab
    rw [ite_eq_right hab, ite_eq_right hba]
    simp

end Quantum.Channels

end -- noncomputable section
