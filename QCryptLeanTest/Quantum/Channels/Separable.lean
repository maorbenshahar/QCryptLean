import QCryptLean.Quantum.Channels.Separable

/-!
# Joint-XOR and SWAP channel examples
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace Quantum.Channels

/-- The first factor outputs the XOR of the two input bits. -/
def jointKeyA (p : Fin 2 × Fin 2) : Op (Fin 2) := Matrix.single (p.1 + p.2) p.1 1

/-- The second factor outputs the same XOR of the two input bits. -/
def jointKeyB (p : Fin 2 × Fin 2) : Op (Fin 2) := Matrix.single (p.1 + p.2) p.2 1

/-- The classical channel that replaces both input bits by their XOR. -/
def jointKeyChannel : Op (Fin 2 × Fin 2) →ₗ[ℂ] Op (Fin 2 × Fin 2) :=
  krausMap (fun p : Fin 2 × Fin 2 => (Matrix.kroneckerMap (· * ·)) (jointKeyA p) (jointKeyB p))

/-- The two output registers both contain the XOR of the two input basis bits. -/
theorem jointKeyChannel_apply (a b : Fin 2) :
    jointKeyChannel ((Matrix.kroneckerMap (· * ·)) (Matrix.single a a 1) (Matrix.single b b 1))
      = (Matrix.kroneckerMap (· * ·)) (Matrix.single (a + b) (a + b) (1 : ℂ))
          (Matrix.single (a + b) (a + b) (1 : ℂ)) := by
  have hbranch : ∀ p : Fin 2 × Fin 2,
      (Matrix.kroneckerMap (· * ·)) (jointKeyA p) (jointKeyB p) *
          (Matrix.kroneckerMap (· * ·)) (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)) *
          ((Matrix.kroneckerMap (· * ·)) (jointKeyA p) (jointKeyB p))ᴴ
        = (Matrix.kroneckerMap (· * ·)) (jointKeyA p * Matrix.single a a (1 : ℂ) * (jointKeyA p)ᴴ)
            (jointKeyB p * Matrix.single b b (1 : ℂ) * (jointKeyB p)ᴴ) := by
    intro p
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  change (∑ p : Fin 2 × Fin 2,
    (Matrix.kroneckerMap (· * ·)) (jointKeyA p) (jointKeyB p) *
      (Matrix.kroneckerMap (· * ·)) (Matrix.single a a 1) (Matrix.single b b 1) *
      ((Matrix.kroneckerMap (· * ·)) (jointKeyA p) (jointKeyB p))ᴴ) = _
  rw [Finset.sum_eq_single ((a, b) : Fin 2 × Fin 2)]
  · rw [hbranch]
    simp only [jointKeyA, jointKeyB, Matrix.conjTranspose_single, star_one,
      Matrix.single_mul_single_same, one_mul]
  · rintro ⟨c, d⟩ - hne
    rw [hbranch]
    rcases eq_or_ne d b with hdb | hdb
    · have hca : c ≠ a := fun h => hne (by rw [h, hdb])
      have hz : jointKeyA (c, d) * Matrix.single a a (1 : ℂ) = 0 := by
        rw [jointKeyA]
        exact Matrix.single_mul_single_of_ne _ _ _ _ hca _
      rw [hz, Matrix.zero_mul, Matrix.zero_kronecker]
    · have hz : jointKeyB (c, d) * Matrix.single b b (1 : ℂ) = 0 := by
        rw [jointKeyB]
        exact Matrix.single_mul_single_of_ne _ _ _ _ hdb _
      rw [hz, Matrix.zero_mul, Matrix.kronecker_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Computing the joint XOR into both registers is a separable channel. -/
theorem isSeparableOperation_jointKeyChannel : IsSeparableChannel jointKeyChannel := by
  refine ⟨Fin 2 × Fin 2, inferInstance, jointKeyA, jointKeyB, rfl, ?_⟩
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [jointKeyA, jointKeyB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Product Kraus matrices give positive partial transpose in laboratory order. -/
theorem isPPT_choiMatrix_jointKeyChannel :
    (Matrix.partialTransposeRight
      (Matrix.reindex (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
        (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
        (choiMatrix jointKeyChannel))).PosSemidef :=
  isSeparableOperation_jointKeyChannel.posSemidef_partialTransposeRight_choiMatrix

/-- The SWAP channel's Choi matrix in laboratory order. -/
def swapChoiReshuffled : Op ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Matrix.reindex (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
    (choiMatrix ((Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodComm (Fin 2) (Fin 2))
      (Equiv.prodComm (Fin 2) (Fin 2))).toLinearMap))

private def η₁ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) := ((0, 0), (1, 0))
private def η₂ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) := ((0, 1), (0, 0))

/-- The laboratory-grouped SWAP Choi matrix has a negative partial-transpose quadratic form. -/
theorem swap_choi_not_ppt : ¬ (Matrix.partialTransposeRight swapChoiReshuffled).PosSemidef := by
  intro h
  have hsub := (h.submatrix ![η₁, η₂]).dotProduct_mulVec_nonneg ![1, -1]
  norm_num [Matrix.partialTransposeRight, swapChoiReshuffled, choiMatrix, Matrix.reindexLinearEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single, Matrix.of_apply,
    η₁, η₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hsub

end Quantum.Channels
