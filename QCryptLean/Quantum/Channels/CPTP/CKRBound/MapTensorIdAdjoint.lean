import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# `mapTensorId` preserves adjoints and Hermiticity

This file records that `mapTensorId` commutes with conjugate transpose, and hence
preserves Hermiticity, whenever the underlying linear map does.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- A map commuting with `conjTranspose` sends matrix units to the corresponding
conjugate-transposed matrix units entrywise. -/
lemma preserves_conjTranspose_on_matrix_units {n m : ℕ}
    [NeZero n] [NeZero m]
    (Δ : Op n →ₗ[ℂ] Op m)
    (hΔ_conj : ∀ M : Op n, Δ M.conjTranspose = (Δ M).conjTranspose)
    (i j : Fin n) (s t : Fin m) :
    star (Δ (single i j 1) t s) = Δ (single j i 1) s t := by
  have h_conj : (single i j (1 : ℂ)).conjTranspose = single j i 1 := by
    rw [Matrix.conjTranspose_single]
    simp
  have h_entry := congr_fun₂ (hΔ_conj (single i j 1)) s t
  rw [h_conj, Matrix.conjTranspose_apply] at h_entry
  exact h_entry.symm

/-- `mapTensorId` preserves conjugate transpose when the underlying map does. -/
lemma mapTensorId_preserves_conjTranspose_of_preserves_conj {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Δ : Op n →ₗ[ℂ] Op m)
    (hΔ_conj : ∀ M : Op n, Δ M.conjTranspose = (Δ M).conjTranspose)
    (A : Op (n * k)) :
    mapTensorId Δ A.conjTranspose = (mapTensorId Δ A).conjTranspose := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp only [star_sum, star_mul']
  simp_rw [preserves_conjTranspose_on_matrix_units (Δ := Δ) (hΔ_conj := hΔ_conj)]
  simp only [← Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- `mapTensorId` preserves Hermiticity when the underlying map commutes with `conjTranspose`. -/
lemma mapTensorId_preserves_hermitian {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Δ : Op n →ₗ[ℂ] Op m)
    (hΔ_conj : ∀ M : Op n, Δ M.conjTranspose = (Δ M).conjTranspose)
    (A : Op (n * k)) (hA : A.IsHermitian) :
    (mapTensorId Δ A).IsHermitian := by
  rw [Matrix.IsHermitian]
  rw [← mapTensorId_preserves_conjTranspose_of_preserves_conj Δ hΔ_conj A, hA.eq]

end Quantum.Channels
