import QCryptLean.Quantum.TensorProducts.TensorFamilyPi

/-!
# A matrix acting on one factor of a finite tensor family

A local matrix and identity spectators form a tensor family. Its Gram matrix has only one
nontrivial factor, and summing that factor commutes with the tensor product.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- A local rectangular matrix at one tensor factor and value-preserving identities elsewhere. -/
def localFam {k : ℕ} (n n' : Fin k → ℕ) (i : Fin k)
    (K : Matrix (Fin (n' i)) (Fin (n i)) ℂ) (j : Fin k) :
    Matrix (Fin (n' j)) (Fin (n j)) ℂ :=
  if _h : j = i then castRect (n' i) (n' j) * K * castRect (n j) (n i)
  else castRect (n j) (n' j)

/-- A square matrix at one factor of an otherwise identity family. -/
def slot {k : ℕ} (n : Fin k → ℕ) (i : Fin k) (M : Op (n i))
    (j : Fin k) : Op (n j) :=
  if _h : j = i then castRect (n i) (n j) * M * castRect (n j) (n i) else 1

@[simp] theorem slot_self {k : ℕ} (n : Fin k → ℕ) (i : Fin k)
    (M : Op (n i)) : slot n i M i = M := by
  rw [slot, dif_pos rfl, castRect_self, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem slot_of_ne {k : ℕ} (n : Fin k → ℕ) (i : Fin k)
    (M : Op (n i)) {j : Fin k} (h : j ≠ i) : slot n i M j = 1 :=
  dif_neg h

@[simp] theorem slot_one {k : ℕ} (n : Fin k → ℕ) (i : Fin k) :
    slot n i (1 : Op (n i)) = fun _ => 1 := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · rw [slot_self]
  · rw [slot_of_ne _ _ _ h]

/-- With spectator dimensions fixed, the local family's Gram matrix has one nontrivial factor. -/
theorem localFam_conjTranspose_mul_self {k : ℕ} (n n' : Fin k → ℕ) (i : Fin k)
    (hag : ∀ j, j ≠ i → n' j = n j)
    (K : Matrix (Fin (n' i)) (Fin (n i)) ℂ) (j : Fin k) :
    (localFam n n' i K j)ᴴ * localFam n n' i K j = slot n i (Kᴴ * K) j := by
  rcases eq_or_ne j i with rfl | h
  · rw [localFam, dif_pos rfl, slot_self]
    simp only [castRect_self, Matrix.one_mul, Matrix.mul_one]
  · rw [localFam, dif_neg h, slot_of_ne _ _ _ h]
    exact castRect_isometry (hag j h).symm

/-- Summing the only varying factor commutes with the tensor product. -/
theorem tensorFamilyPi_slot_sum {k : ℕ} (n : Fin k → ℕ) (i : Fin k) {κ : Type*} [Fintype κ]
    (M : κ → Op (n i)) :
    ∑ x, tensorFamilyPi (slot n i (M x)) = tensorFamilyPi (slot n i (∑ x, M x)) := by
  ext I J
  rw [Matrix.sum_apply]
  have hsplit : ∀ N : Op (n i),
      tensorFamilyPi (slot n i N) I J
        = N (finPiFinEquiv.symm I i) (finPiFinEquiv.symm J i) *
            ∏ j ∈ Finset.univ.erase i,
              (if finPiFinEquiv.symm I j = finPiFinEquiv.symm J j then (1 : ℂ) else 0) := by
    intro N
    rw [tensorFamilyPi_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), slot_self]
    refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
    rw [slot_of_ne _ _ _ (Finset.ne_of_mem_erase hj), Matrix.one_apply]
  simp only [hsplit]
  rw [← Finset.sum_mul, ← Matrix.sum_apply]

/-- The two-factor family is the rectangular tensor with factor one in the high digit. -/
theorem tensorFamilyPi_two {a b : Fin 2 → ℕ} (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    tensorFamilyPi A
      = castRect (a 1 * a 0) (∏ j, a j) * tensorRect (A 1) (A 0)
          * castRect (∏ j, b j) (b 1 * b 0) := by
  have ha : a 1 * a 0 = ∏ j, a j := by rw [Fin.prod_univ_two]; ring
  have hb : (∏ j, b j) = b 1 * b 0 := by rw [Fin.prod_univ_two]; ring
  rw [castRect_mul ha, mul_castRect hb]
  ext I J
  obtain ⟨f, rfl⟩ := finPiFinEquiv.surjective I
  obtain ⟨g, rfl⟩ := finPiFinEquiv.surjective J
  simp only [Matrix.submatrix_apply, id_eq]
  rw [tensorFamilyPi_apply_finPiFinEquiv]
  have hI : Fin.cast ha.symm (finPiFinEquiv f) = finProdFinEquiv (f 1, f 0) := by
    apply Fin.ext
    rw [Fin.val_cast, finPiFinEquiv_apply, finProdFinEquiv_val, Fin.sum_univ_two]
    simp [Nat.mul_comm]
  have hJ : Fin.cast hb (finPiFinEquiv g) = finProdFinEquiv (g 1, g 0) := by
    apply Fin.ext
    rw [Fin.val_cast, finPiFinEquiv_apply, finProdFinEquiv_val, Fin.sum_univ_two]
    simp [Nat.mul_comm]
  rw [hI, hJ, tensorRect_apply]
  simp only [Equiv.symm_apply_apply]
  rw [Fin.prod_univ_two]
  ring

/-- A rectangular tensor is the two-factor family read through value-preserving dimension casts. -/
theorem tensorRect_two {a b : Fin 2 → ℕ} (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    tensorRect (A 1) (A 0)
      = castRect (∏ j, a j) (a 1 * a 0) * tensorFamilyPi A * castRect (b 1 * b 0) (∏ j, b j) := by
  have ha : a 1 * a 0 = ∏ j, a j := by rw [Fin.prod_univ_two]; ring
  have hb : (∏ j, b j) = b 1 * b 0 := by rw [Fin.prod_univ_two]; ring
  rw [tensorFamilyPi_two A, Matrix.mul_assoc, Matrix.mul_assoc,
    castRect_comp hb.symm hb, castRect_self, Matrix.mul_one,
    ← Matrix.mul_assoc, castRect_comp ha ha.symm, castRect_self, Matrix.one_mul]

end Quantum.TensorProducts
