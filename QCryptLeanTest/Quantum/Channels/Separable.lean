import QCryptLean.Quantum.Channels.Separable

/-!
# Joint-XOR and SWAP channel examples
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The first factor outputs the XOR of the two input bits. -/
def jointKeyA (p : Fin 2 × Fin 2) : Op 2 := Matrix.single (p.1 + p.2) p.1 1

/-- The second factor outputs the same XOR of the two input bits. -/
def jointKeyB (p : Fin 2 × Fin 2) : Op 2 := Matrix.single (p.1 + p.2) p.2 1

/-- The classical channel that replaces both input bits by their XOR. -/
def jointKeyChannel : Op (2 * 2) →ₗ[ℂ] Op (2 * 2) :=
  krausMapFintype (fun p : Fin 2 × Fin 2 => tensorRect (jointKeyA p) (jointKeyB p))

/-- The two output registers both contain the XOR of the two input basis bits. -/
theorem jointKeyChannel_apply (a b : Fin 2) :
    jointKeyChannel (Op.tensor (Matrix.single a a 1) (Matrix.single b b 1))
      = Op.tensor (Matrix.single (a + b) (a + b) (1 : ℂ))
          (Matrix.single (a + b) (a + b) (1 : ℂ)) := by
  have hbranch : ∀ p : Fin 2 × Fin 2,
      tensorRect (jointKeyA p) (jointKeyB p) *
          Op.tensor (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)) *
          (tensorRect (jointKeyA p) (jointKeyB p))ᴴ
        = tensorRect (jointKeyA p * Matrix.single a a (1 : ℂ) * (jointKeyA p)ᴴ)
            (jointKeyB p * Matrix.single b b (1 : ℂ) * (jointKeyB p)ᴴ) := by
    intro p
    rw [← tensorRect_square (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)),
      tensorRect_conjTranspose, tensorRect_mul, tensorRect_mul]
  change (∑ p : Fin 2 × Fin 2,
    tensorRect (jointKeyA p) (jointKeyB p) *
      Op.tensor (Matrix.single a a 1) (Matrix.single b b 1) *
      (tensorRect (jointKeyA p) (jointKeyB p))ᴴ) = _
  rw [Finset.sum_eq_single ((a, b) : Fin 2 × Fin 2)]
  · rw [hbranch]
    simp only [jointKeyA, jointKeyB, Matrix.conjTranspose_single, star_one,
      Matrix.single_mul_single_same, one_mul, tensorRect_square]
  · rintro ⟨c, d⟩ - hne
    rw [hbranch]
    rcases eq_or_ne d b with hdb | hdb
    · have hca : c ≠ a := fun h => hne (by rw [h, hdb])
      have hz : jointKeyA (c, d) * Matrix.single a a (1 : ℂ) = 0 := by
        rw [jointKeyA]
        exact Matrix.single_mul_single_of_ne _ _ _ _ hca _
      rw [hz, Matrix.zero_mul, tensorRect_zero_left]
    · have hz : jointKeyB (c, d) * Matrix.single b b (1 : ℂ) = 0 := by
        rw [jointKeyB]
        exact Matrix.single_mul_single_of_ne _ _ _ _ hdb _
      rw [hz, Matrix.zero_mul, tensorRect_zero_right]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Computing the joint XOR into both registers is a separable channel. -/
theorem jointKeyChannel_isSeparableOperation :
    IsSeparableOperation (rA := 2) (rB := 2) (sA := 2) (sB := 2) jointKeyChannel := by
  refine isSeparableOperation_of_fintype (ι := Fin 2 × Fin 2) _ jointKeyA jointKeyB
    (fun _ => rfl) ?_
  have hstep : ∀ p : Fin 2 × Fin 2,
      (tensorRect (jointKeyA p) (jointKeyB p))ᴴ * tensorRect (jointKeyA p) (jointKeyB p)
        = tensorRect (Matrix.single p.1 p.1 (1 : ℂ)) (Matrix.single p.2 p.2 (1 : ℂ)) := by
    intro p
    rw [tensorRect_conjTranspose, tensorRect_mul, jointKeyA, jointKeyB]
    simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]
  rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
  have hrow : ∀ a : Fin 2, ∑ b : Fin 2,
      tensorRect (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ))
        = tensorRect (Matrix.single a a (1 : ℂ))
            (∑ b : Fin 2, Matrix.single b b (1 : ℂ)) := fun a => tensorRect_sum_right _ _
  rw [Finset.sum_congr rfl fun a _ => hrow a, tensorRect_sum_left]
  have hone : ∑ b : Fin 2, Matrix.single b b (1 : ℂ) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, ite_and]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hone, tensorRect_one]

/-- The joint-XOR channel has positive partial transpose across the laboratory Choi cut. -/
theorem jointKeyChannel_choi_isPPT :
    IsPPT (2 * 2) (2 * 2)
      (Matrix.reindex (choiReshuffle 2 2 2 2) (choiReshuffle 2 2 2 2)
        (ChoiMatrix (2 * 2) (2 * 2) ⇑jointKeyChannel)) :=
  isSeparable_choi_isPPT _ jointKeyChannel_isSeparableOperation

/-- The basis permutation that exchanges two qubit registers. -/
def swapBasisEquiv : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

/-- The SWAP channel's Choi matrix in laboratory order. -/
def swapChoiReshuffled : Op (4 * 4) :=
  Matrix.reindex (choiReshuffle 2 2 2 2) (choiReshuffle 2 2 2 2)
    (ChoiMatrix 4 4 (fun ρ => Matrix.submatrix ρ swapBasisEquiv.symm swapBasisEquiv.symm))

private def η₁ : Fin (4 * 4) := finProdFinEquiv ((0 : Fin 4), (2 : Fin 4))

private def η₂ : Fin (4 * 4) := finProdFinEquiv ((1 : Fin 4), (0 : Fin 4))

private theorem swapPt_entry_11 : partialTransposeB 4 4 swapChoiReshuffled η₁ η₁ = 0 := by
  have e : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((0 : Fin 4), (2 : Fin 4)))
      = finProdFinEquiv ((1 : Fin 4), (0 : Fin 4)) := rfl
  rw [η₁, partialTransposeB_apply, swapChoiReshuffled, Matrix.reindex_apply,
    Matrix.submatrix_apply, e, choi_of_reindexMap]
  rw [ite_eq_right (by simp only [swapBasisEquiv]; decide)]

private theorem swapPt_entry_12 : partialTransposeB 4 4 swapChoiReshuffled η₁ η₂ = 1 := by
  have e1 : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)))
      = finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)) := rfl
  have e2 : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((1 : Fin 4), (2 : Fin 4)))
      = finProdFinEquiv ((1 : Fin 4), (2 : Fin 4)) := rfl
  rw [η₁, η₂, partialTransposeB_apply, swapChoiReshuffled, Matrix.reindex_apply,
    Matrix.submatrix_apply, e1, e2, choi_of_reindexMap]
  rw [ite_eq_left (by simp only [swapBasisEquiv]; decide)]

private theorem swapPt_entry_21 : partialTransposeB 4 4 swapChoiReshuffled η₂ η₁ = 1 := by
  have e1 : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((1 : Fin 4), (2 : Fin 4)))
      = finProdFinEquiv ((1 : Fin 4), (2 : Fin 4)) := rfl
  have e2 : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)))
      = finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)) := rfl
  rw [η₁, η₂, partialTransposeB_apply, swapChoiReshuffled, Matrix.reindex_apply,
    Matrix.submatrix_apply, e1, e2, choi_of_reindexMap]
  rw [ite_eq_left (by simp only [swapBasisEquiv]; decide)]

private theorem swapPt_entry_22 : partialTransposeB 4 4 swapChoiReshuffled η₂ η₂ = 0 := by
  have e : (choiReshuffle 2 2 2 2).symm (finProdFinEquiv ((1 : Fin 4), (0 : Fin 4)))
      = finProdFinEquiv ((0 : Fin 4), (2 : Fin 4)) := rfl
  rw [η₂, partialTransposeB_apply, swapChoiReshuffled, Matrix.reindex_apply,
    Matrix.submatrix_apply, e, choi_of_reindexMap]
  rw [ite_eq_right (by simp only [swapBasisEquiv]; decide)]

/-- The laboratory-grouped SWAP Choi matrix has a negative partial-transpose quadratic form. -/
theorem swap_choi_not_ppt : ¬ IsPPT 4 4 swapChoiReshuffled := by
  intro h
  have hsub := (h.submatrix ![η₁, η₂]).dotProduct_mulVec_nonneg ![1, -1]
  have hval :
      (star ![(1 : ℂ), -1] ⬝ᵥ
        (((partialTransposeB 4 4 swapChoiReshuffled).submatrix
            ![η₁, η₂] ![η₁, η₂]) *ᵥ ![(1 : ℂ), -1])) = (-2 : ℂ) := by
    simp [dotProduct, Matrix.mulVec, Matrix.submatrix_apply,
      swapPt_entry_11, swapPt_entry_12, swapPt_entry_21, swapPt_entry_22]
    norm_num
  rw [hval] at hsub
  norm_num at hsub

end Quantum.Channels
