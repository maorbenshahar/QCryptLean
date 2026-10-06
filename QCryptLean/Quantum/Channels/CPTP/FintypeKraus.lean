import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Finite-Type Indexed Kraus Maps

This module packages the standard finite Kraus-map construction for an arbitrary
finite index type. In particular, `Fin r` is covered directly.

## Main statements

- `krausMapFintype_equiv`: reindexing the Kraus family by an equivalence preserves its map.
- `krausMapFintype_posSemidef`, `krausMapFintype_isHermitian`: `NeZero`-free
  positivity and Hermiticity preservation (no Choi matrix is involved).
- `krausMapFintype_sandwich_eq_self`: left and right range identities absorb
  into a finite Kraus map.
- `krausMapFintype_trace_eq`: trace cycling identity
  `Tr(∑ₖ Kₖ A Kₖ†) = Tr((∑ₖ Kₖ† Kₖ) A)`.
- `krausMapFintype_isCompletelyPositive`: finite-index Kraus maps are completely positive.
- `krausMapFintype_isCPTP`: a finite-index Kraus map is CPTP when the Kraus completeness
  relation holds.

The Hilbert–Schmidt adjoint `Λ*(M) = ∑ₖ Kₖᴴ M Kₖ` of a finite Kraus map, and the Petz
transpose map built from it, are in `KrausAdjoint.lean` and `PetzMap.lean`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- A Kraus map indexed by an arbitrary finite type.

The core `KrausRepresentation` API stores the index type as `Fin numOps`; this
wrapper keeps proofs over natural product index types readable, and reindexes
through `Fintype.equivFin` only at the boundary. -/
noncomputable def krausMapFintype {n m : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin m) (Fin n) ℂ) :
    Op n →ₗ[ℂ] Op m where
  toFun A := ∑ k, K k * A * (K k)ᴴ
  map_add' A B := by
    simp_rw [Matrix.mul_add, Matrix.add_mul]
    rw [← Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [RingHom.id_apply]
    have h : ∀ k, K k * (c • A) * (K k)ᴴ = c • (K k * A * (K k)ᴴ) := by
      intro k
      ext p q
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.conjTranspose_apply]
      simp [Finset.sum_mul, mul_comm c, mul_assoc]
    simp_rw [h]
    exact Finset.smul_sum.symm

/-- Reindexing a finite Kraus family by an equivalence preserves its map. -/
theorem krausMapFintype_equiv {p q : ℕ} {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (e : κ ≃ κ') (G : κ' → Matrix (Fin p) (Fin q) ℂ) (M : Op q) :
    krausMapFintype (fun x => G (e x)) M = krausMapFintype G M := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  exact Fintype.sum_equiv e _ _ (fun x => rfl)

/-- A left range identity for every Kraus operator fixes every output of the
finite Kraus map under left multiplication. -/
lemma mul_krausMapFintype_eq_self {n m : ℕ} {κ : Type*} [Fintype κ]
    (L : Op m) (K : κ → Matrix (Fin m) (Fin n) ℂ)
    (hleft : ∀ c, L * K c = K c) (M : Op n) :
    L * krausMapFintype K M = krausMapFintype K M := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Matrix.mul_assoc L (K c * M) (K c)ᴴ,
    ← Matrix.mul_assoc L (K c) M, hleft]

/-- A right range identity for every adjoint Kraus operator fixes every output
of the finite Kraus map under right multiplication. -/
lemma krausMapFintype_mul_eq_self {n m : ℕ} {κ : Type*} [Fintype κ]
    (R : Op m) (K : κ → Matrix (Fin m) (Fin n) ℂ)
    (hright : ∀ c, (K c)ᴴ * R = (K c)ᴴ) (M : Op n) :
    krausMapFintype K M * R = krausMapFintype K M := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_assoc, hright]

/-- If `L` fixes the range of every Kraus operator and `R` fixes the range of
every adjoint Kraus operator, then every output is fixed by the sandwich
`X ↦ L * X * R`.

This algebraic statement is rectangular and needs no nonzero-dimension,
positivity, Hermiticity, or completeness hypothesis. -/
lemma krausMapFintype_sandwich_eq_self {n m : ℕ} {κ : Type*} [Fintype κ]
    (L R : Op m) (K : κ → Matrix (Fin m) (Fin n) ℂ)
    (hleft : ∀ c, L * K c = K c)
    (hright : ∀ c, (K c)ᴴ * R = (K c)ᴴ)
    (M : Op n) :
    L * krausMapFintype K M * R = krausMapFintype K M := by
  rw [mul_krausMapFintype_eq_self L K hleft M,
    krausMapFintype_mul_eq_self R K hright M]

/-- A finite Kraus map preserves positive semidefiniteness.

Unlike `krausMapFintype_isCompletelyPositive` this is `NeZero`-free, because it does
not go through the Choi matrix. -/
lemma krausMapFintype_posSemidef {n m : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin m) (Fin n) ℂ)
    {A : Op n} (hA : A.PosSemidef) : (krausMapFintype K A).PosSemidef := by
  change (∑ k, K k * A * (K k)ᴴ).PosSemidef
  exact Matrix.posSemidef_sum _ fun k _ => hA.mul_mul_conjTranspose_same (K k)

/-- A finite Kraus map preserves Hermiticity. -/
lemma krausMapFintype_isHermitian {n m : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin m) (Fin n) ℂ)
    {A : Op n} (hA : A.IsHermitian) : (krausMapFintype K A).IsHermitian := by
  change (∑ k, K k * A * (K k)ᴴ)ᴴ = ∑ k, K k * A * (K k)ᴴ
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- Trace of a finite-index Kraus map factors through the sum of conjugate products:
    `Tr(∑ₖ Kₖ A Kₖ†) = Tr((∑ₖ Kₖ† Kₖ) A)`.
-/
lemma krausMapFintype_trace_eq {n m : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin m) (Fin n) ℂ) (A : Op n) :
    (krausMapFintype K A).trace = ((∑ k, (K k)ᴴ * K k) * A).trace := by
  change (∑ k, K k * A * (K k)ᴴ).trace = _
  rw [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact Matrix.trace_mul_cycle (K k) A (K k)ᴴ

/-- If two finite Kraus families are intertwined by rectangular maps on input and output,
then the corresponding Kraus maps are intertwined by conjugation. -/
theorem krausMapFintype_conj_of_intertwining {κ : Type*} [Fintype κ]
    {aM aN bM bN : ℕ}
    (Km : κ → Matrix (Fin bM) (Fin aM) ℂ)
    (Kn : κ → Matrix (Fin bN) (Fin aN) ℂ)
    (Wa : Matrix (Fin aM) (Fin aN) ℂ)
    (Wb : Matrix (Fin bM) (Fin bN) ℂ)
    (hInter : ∀ i, Km i * Wa = Wb * Kn i)
    (A : Op aN) :
    krausMapFintype Km (Wa * A * Wa.conjTranspose) =
      Wb * krausMapFintype Kn A * Wb.conjTranspose := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ i : κ, Km i * (Wa * A * Wa.conjTranspose) * (Km i).conjTranspose)
        = ∑ i : κ, Wb * (Kn i * A * (Kn i).conjTranspose) * Wb.conjTranspose := by
          apply Finset.sum_congr rfl
          intro i _
          have hKi := hInter i
          calc
            Km i * (Wa * A * Wa.conjTranspose) * (Km i).conjTranspose
                = (Km i * Wa) * A * (Km i * Wa).conjTranspose := by
                  simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
            _ = (Wb * Kn i) * A * (Wb * Kn i).conjTranspose := by
                  rw [hKi]
            _ = Wb * (Kn i * A * (Kn i).conjTranspose) * Wb.conjTranspose := by
                  simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
    _ = Wb * (∑ i : κ, Kn i * A * (Kn i).conjTranspose) * Wb.conjTranspose := by
          rw [Matrix.mul_sum]
          rw [Matrix.sum_mul]

/-- A finite-index Kraus map is completely positive. -/
theorem krausMapFintype_isCompletelyPositive {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] (K : κ → Matrix (Fin m) (Fin n) ℂ) :
    IsCompletelyPositive (⇑(krausMapFintype K)) := by
  unfold IsCompletelyPositive
  set w : κ → (Fin (n * m) → ℂ) := fun k p =>
    K k (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm p).1
  suffices h_eq : ChoiMatrix n m (⇑(krausMapFintype K)) =
      ∑ k, vecMulVec (w k) (star (w k)) by
    rw [h_eq]
    exact Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_vecMulVec_self_star _
  ext p q
  simp only [ChoiMatrix, Matrix.of_apply, Matrix.sum_apply, vecMulVec, Pi.star_apply, w]
  change (∑ k : κ, K k * (Matrix.of fun r' c =>
    if r' = (finProdFinEquiv.symm p).1 ∧ c = (finProdFinEquiv.symm q).1
    then (1 : ℂ) else 0) * (K k)ᴴ)
    (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 = _
  have hE : ∀ (k : κ),
      (K k * (Matrix.of fun r' c =>
        if r' = (finProdFinEquiv.symm p).1 ∧ c = (finProdFinEquiv.symm q).1
        then (1 : ℂ) else 0) * (K k)ᴴ)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 =
      K k (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm p).1 *
      star (K k (finProdFinEquiv.symm q).2 (finProdFinEquiv.symm q).1) := by
    intro k
    have hof : (Matrix.of fun r' c =>
        if r' = (finProdFinEquiv.symm p).1 ∧ c = (finProdFinEquiv.symm q).1
        then (1 : ℂ) else 0) =
        single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 1 := by
      ext r' c; simp [single_apply, eq_comm]
    rw [hof]
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero,
      Matrix.conjTranspose_apply]
    have h_KE : ∀ x, (K k * single (finProdFinEquiv.symm p).1
        (finProdFinEquiv.symm q).1 (1 : ℂ))
        (finProdFinEquiv.symm p).2 x =
        if x = (finProdFinEquiv.symm q).1
        then K k (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm p).1 else 0 := by
      intro x; simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hx : x = (finProdFinEquiv.symm q).1
      · subst hx
        simp only [and_true, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      · rw [if_neg hx]
        exact Finset.sum_eq_zero fun y _ => if_neg (fun ⟨_, h⟩ => hx h.symm)
    simp_rw [ite_and]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  simp_rw [Matrix.sum_apply, hE]

/-- Tensor operators acting on the left factor commute with a rectangular
`id ⊗ V` on the right factor. -/
theorem tensorRightId_mul_idTensorRect {a b m n : ℕ}
    [NeZero a] [NeZero b] [NeZero m] [NeZero n]
    (K : Matrix (Fin b) (Fin a) ℂ)
    (V : Matrix (Fin m) (Fin n) ℂ) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) K (1 : Op m))) *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (1 : Op a) V)) =
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (1 : Op b) V)) *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) K (1 : Op n))) := by
  dsimp [Matrix.reindex]
  rw [Matrix.submatrix_mul_equiv]
  rw [Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul]
  rw [← Matrix.mul_kronecker_mul]
  simp [Matrix.one_mul, Matrix.mul_one]

/-- A finite-index Kraus map is CPTP when the Kraus completeness relation holds. -/
theorem krausMapFintype_isCPTP {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] (K : κ → Matrix (Fin m) (Fin n) ℂ)
    (hK : ∑ k, (K k)ᴴ * K k = 1) :
    IsCPTP (⇑(krausMapFintype K)) := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let KR : KrausRepresentation n m :=
    { numOps := Fintype.card κ
      operators := fun i => K (e.symm i)
      completeness := by
        calc
          ∑ i : Fin (Fintype.card κ), (K (e.symm i))ᴴ * K (e.symm i)
              = ∑ k : κ, (K k)ᴴ * K k := by
                exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
          _ = 1 := hK }
  have hKR : IsCPTP KR.applyOp := KR.is_cptp
  have hEq : KR.applyOp = ⇑(krausMapFintype K) := by
    funext A
    change (∑ i : Fin (Fintype.card κ), K (e.symm i) * A * (K (e.symm i))ᴴ) =
      ∑ k : κ, K k * A * (K k)ᴴ
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  simpa [hEq] using hKR

end Quantum.Channels

end
