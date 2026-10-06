import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# `mapIdTensor` right-register conjugation

Generic linear-algebra lemma lifting a pointwise conjugacy of right-register maps
through `id ⊗ Φ`: if a right-register map is pointwise a conjugated, pre-conjugated
map, then `mapIdTensor Φ` satisfies the corresponding conjugacy on the right tensor
factor, for arbitrary `Φ Ψ : Op n →ₗ[ℂ] Op m`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

private lemma mapIdTensor_tensor_right
    {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (C : Op k) (D : Op n) :
    mapIdTensor Φ (Op.tensor C D) = Op.tensor C (Φ D) := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, kroneckerMap_apply]
  simp only [Equiv.symm_apply_apply]
  have hD_decomp : D = ∑ i, ∑ j, D i j • single i j 1 := by
    ext r c
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, mul_ite, mul_one, mul_zero]
    symm
    exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ =>
        if_neg (fun ⟨h1, _⟩ => hi h1)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  conv_rhs =>
    rw [hD_decomp, map_sum]
    simp only [map_sum, LinearMap.map_smul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  simp
  ring

private lemma single_prod_eq_tensor
    {k n : ℕ} (s t : Fin k) (i j : Fin n) :
    single (finProdFinEquiv (s, i)) (finProdFinEquiv (t, j))
      (1 : ℂ) =
      Op.tensor (single s t 1) (single i j 1) := by
  ext r c
  simp only [single_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have heq_r : finProdFinEquiv (s, i) = r ↔
      (finProdFinEquiv.symm r).1 = s ∧
        (finProdFinEquiv.symm r).2 = i := by
    constructor
    · intro h
      subst h
      simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm r = (s, i) := Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv r, this]
  have heq_c : finProdFinEquiv (t, j) = c ↔
      (finProdFinEquiv.symm c).1 = t ∧
        (finProdFinEquiv.symm c).2 = j := by
    constructor
    · intro h
      subst h
      simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm c = (t, j) := Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv c, this]
  simp only [heq_r, heq_c, and_assoc]
  split_ifs <;> simp_all

private lemma op_tensor_smul_right {k m : ℕ} (A : Op k) (B : Op m) (c : ℂ) :
    Op.tensor A (c • B) = c • Op.tensor A B := by
  ext i j
  simp [Op.tensor, Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  ring

/-- If a right-register map is pointwise a conjugated, pre-conjugated map, then
`id ⊗ Φ` satisfies the corresponding conjugacy on the right tensor factor. -/
theorem mapIdTensor_conj_right_of_apply
    {k n m : ℕ} [NeZero k] [NeZero n] [NeZero m]
    (Φ Ψ : Op n →ₗ[ℂ] Op m)
    (U : Op n) (W : Op m) (c : ℂ)
    (hΦ : ∀ A : Op n, Φ A = c • (W * Ψ (U * A * Uᴴ) * Wᴴ))
    (X : Op (k * n)) :
    mapIdTensor Φ X =
      c •
        (Op.tensor (1 : Op k) W *
          mapIdTensor Ψ (Op.tensor (1 : Op k) U * X * Op.tensor (1 : Op k) Uᴴ) *
          (Op.tensor (1 : Op k) W)ᴴ) := by
  let FL : Op (k * n) →ₗ[ℂ] Op (k * m) :=
    { toFun := fun X => mapIdTensor Φ X
      map_add' := mapIdTensor_add_basic Φ
      map_smul' := mapIdTensor_smul_basic Φ }
  let FR : Op (k * n) →ₗ[ℂ] Op (k * m) :=
    { toFun := fun X =>
        c •
          (Op.tensor (1 : Op k) W *
            mapIdTensor Ψ
              (Op.tensor (1 : Op k) U * X * Op.tensor (1 : Op k) Uᴴ) *
            (Op.tensor (1 : Op k) W)ᴴ)
      map_add' := by
        intro A B
        rw [mul_add, add_mul, mapIdTensor_add_basic, mul_add, add_mul, smul_add]
      map_smul' := by
        intro a A
        -- Pull `a` out through both products and through `mapIdTensor Ψ`.
        rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, mapIdTensor_smul_basic,
          Matrix.mul_smul, Matrix.smul_mul, smul_comm] }
  change FL X = FR X
  have h_eq : FL = FR := by
    apply (Matrix.stdBasis ℂ (Fin (k * n)) (Fin (k * n))).ext
    intro ⟨r, s⟩
    simp only [Matrix.stdBasis_eq_single, FL, FR, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show r = finProdFinEquiv
          ((finProdFinEquiv.symm r).1, (finProdFinEquiv.symm r).2) from
          (finProdFinEquiv.apply_symm_apply r).symm,
        show s = finProdFinEquiv
          ((finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2) from
          (finProdFinEquiv.apply_symm_apply s).symm,
        single_prod_eq_tensor]
    rw [mapIdTensor_tensor_right, hΦ, Op.tensor_conjTranspose, Op.tensor_mul,
      Op.tensor_mul, mapIdTensor_tensor_right, Op.tensor_mul, Op.tensor_mul]
    rw [op_tensor_smul_right]
    simp only [Matrix.conjTranspose_one, one_mul, mul_one]
  exact DFunLike.congr_fun h_eq X

end Quantum.Channels

end -- noncomputable section
