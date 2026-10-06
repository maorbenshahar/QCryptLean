import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# Map-Tensor-Id Ancilla Commutation

Four lemmas (`single_eq_tensor`, `single_eq_tensor_symm`, the two
`kw_mapTensorId_*_ancilla_mul`), namespaced the same as `KitaevWatrousContraction.lean`,
kept in this file rather than there so that `SupportPreservation.lean` can import them
without an import cycle through `Contractivity.lean`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrousContraction

/-- Single basis matrix as a pure tensor:
    `single (e(i,s)) (e(j,t)) 1 = (single i j 1) ⊗ (single s t 1)`. -/
private lemma single_eq_tensor {n k : ℕ}
    (i j : Fin n) (s t : Fin k) :
    single (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))
      (1 : ℂ) =
      Op.tensor (single i j 1) (single s t 1) := by
  ext r c
  simp only [single_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have heq_r : finProdFinEquiv (i, s) = r ↔
      (finProdFinEquiv.symm r).1 = i ∧
      (finProdFinEquiv.symm r).2 = s := by
    constructor
    · intro h
      subst h
      simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm r = (i, s) := Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv r, this]
  have heq_c : finProdFinEquiv (j, t) = c ↔
      (finProdFinEquiv.symm c).1 = j ∧
      (finProdFinEquiv.symm c).2 = t := by
    constructor
    · intro h
      subst h
      simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm c = (j, t) := Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv c, this]
  simp only [heq_r, heq_c, and_assoc]
  split_ifs <;> simp_all

/-- Every matrix unit on `Op (n * k)` is a pure tensor of matrix units
    from the product decomposition of its row and column indices. -/
private lemma single_eq_tensor_symm {n k : ℕ} (r c : Fin (n * k)) :
    single r c (1 : ℂ) =
      Op.tensor
        (single (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1 1)
        (single (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2 1) := by
  convert single_eq_tensor
    (i := (finProdFinEquiv.symm r).1) (j := (finProdFinEquiv.symm c).1)
    (s := (finProdFinEquiv.symm r).2) (t := (finProdFinEquiv.symm c).2)
    using 2 <;> exact (finProdFinEquiv.apply_symm_apply _).symm

/-- Left ancilla multiplication commutes with `mapTensorId`. -/
lemma kw_mapTensorId_left_ancilla_mul {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (A : Op k) (Y : Op (n * k)) :
    mapTensorId Φ (Op.tensor (1 : Op n) A * Y) =
      Op.tensor (1 : Op m) A * mapTensorId Φ Y := by
  let FL : Op (n * k) →ₗ[ℂ] Op (m * k) :=
    { toFun := fun Z => mapTensorId Φ (Op.tensor (1 : Op n) A * Z)
      map_add' := fun x y => by rw [mul_add, mapTensorId_add_basic]
      map_smul' := fun c x => by
        rw [mul_smul_comm, mapTensorId_smul_basic, RingHom.id_apply] }
  let FR : Op (n * k) →ₗ[ℂ] Op (m * k) :=
    { toFun := fun Z => Op.tensor (1 : Op m) A * mapTensorId Φ Z
      map_add' := fun x y => by rw [mapTensorId_add_basic, mul_add]
      map_smul' := fun c x => by
        rw [mapTensorId_smul_basic, mul_smul_comm, RingHom.id_apply] }
  change FL Y = FR Y
  have h_eq : FL = FR := by
    apply (Matrix.stdBasis ℂ (Fin (n * k)) (Fin (n * k))).ext
    intro ⟨r, c⟩
    simp only [Matrix.stdBasis_eq_single, FL, FR,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [single_eq_tensor_symm]
    rw [Op.tensor_mul, one_mul, mapTensorId_tensor,
      mapTensorId_tensor, Op.tensor_mul, one_mul]
  exact DFunLike.congr_fun h_eq Y

/-- Right ancilla multiplication commutes with `mapTensorId`. -/
lemma kw_mapTensorId_right_ancilla_mul {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (A : Op k) (Y : Op (n * k)) :
    mapTensorId Φ (Y * Op.tensor (1 : Op n) A) =
      mapTensorId Φ Y * Op.tensor (1 : Op m) A := by
  let FL : Op (n * k) →ₗ[ℂ] Op (m * k) :=
    { toFun := fun Z => mapTensorId Φ (Z * Op.tensor (1 : Op n) A)
      map_add' := fun x y => by rw [add_mul, mapTensorId_add_basic]
      map_smul' := fun c x => by
        rw [smul_mul_assoc, mapTensorId_smul_basic, RingHom.id_apply] }
  let FR : Op (n * k) →ₗ[ℂ] Op (m * k) :=
    { toFun := fun Z => mapTensorId Φ Z * Op.tensor (1 : Op m) A
      map_add' := fun x y => by rw [mapTensorId_add_basic, add_mul]
      map_smul' := fun c x => by
        rw [mapTensorId_smul_basic, smul_mul_assoc, RingHom.id_apply] }
  change FL Y = FR Y
  have h_eq : FL = FR := by
    apply (Matrix.stdBasis ℂ (Fin (n * k)) (Fin (n * k))).ext
    intro ⟨r, c⟩
    simp only [Matrix.stdBasis_eq_single, FL, FR,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [single_eq_tensor_symm]
    rw [Op.tensor_mul, mul_one, mapTensorId_tensor,
      mapTensorId_tensor, Op.tensor_mul, mul_one]
  exact DFunLike.congr_fun h_eq Y

end Quantum.Metrics.KitaevWatrousContraction

end -- noncomputable section
