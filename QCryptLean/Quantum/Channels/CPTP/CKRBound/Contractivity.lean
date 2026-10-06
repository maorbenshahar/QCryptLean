import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic

/-!
# Trace Norm Contractivity for Tensored Maps — CPTP preservation, composition, contractivity

Infrastructure for `mapTensorId` and `mapIdTensor` acting on tensor product operators:
distributivity over arithmetic, CPTP preservation, trace-norm contractivity, and
commutativity of maps on disjoint tensor factors. These properties are essential for
the CKR per-operator bound.

## Main definitions
- `mapTensorId_add_basic` / `mapIdTensor_add_basic`: distributivity over addition
- `mapTensorId_smul_basic` / `mapIdTensor_smul_basic`: distributivity over scalar multiplication
- `mapTensorIdLinear`: linear-map wrapper for tensoring a linear map with the identity

## Main statements
- `mapTensorId_smul_basic`, `mapTensorId_sub`: arithmetic identities for `mapTensorId`
- `traceNorm_mapTensorId_cptp_contractive`: `‖(Φ ⊗ id)(X)‖₁ ≤ ‖X‖₁` for CPTP Φ
- `traceNorm_mapIdTensor_cptp_contractive`: `‖(id ⊗ Φ)(X)‖₁ ≤ ‖X‖₁` for CPTP Φ
- `mapTensorId_compose_different_factors`: maps on disjoint tensor factors commute
- `mapTensorId_isCPTP` / `mapIdTensor_isCPTP`: CPTP maps tensor to CPTP maps

## References
- Christandl, Konig, Renner (2009) arXiv:0809.3019
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The first component packed by `finProdFinEquiv` is recovered by `divNat`. -/
lemma finProdFinEquiv_apply_divNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.fst h).symm

/-- The second component packed by `finProdFinEquiv` is recovered by `modNat`. -/
lemma finProdFinEquiv_apply_modNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.snd h).symm

/-!
## mapTensorId distributes over arithmetic and preserves CPTP
-/

/-- `mapTensorId` distributes over addition. -/
lemma mapTensorId_add_basic {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (A B : Op (n * k)) :
    mapTensorId Φ (A + B) = mapTensorId Φ A + mapTensorId Φ B := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- `mapTensorId` distributes over scalar multiplication.  Reproved here so that
    `CKRBound/Basic.lean` can use it without depending on higher-level modules. -/
lemma mapTensorId_smul_basic {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (c : ℂ) (X : Op (n * k)) :
    mapTensorId Φ (c • X) = c • mapTensorId Φ X := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  ring

/-- `mapTensorId` distributes over subtraction. -/
lemma mapTensorId_sub {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (X Y : Op (n * k)) :
    mapTensorId Φ (X - Y) = mapTensorId Φ X - mapTensorId Φ Y := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, Matrix.sub_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- `mapTensorId` distributes over finite-set sums in the channel argument. -/
lemma mapTensorId_linearMap_finset_sum {n m k : ℕ} [NeZero n] [NeZero m]
    [NeZero k] {ι : Type*} (s : Finset ι) (Φ : ι → Op n →ₗ[ℂ] Op m)
    (X : Op (n * k)) :
    mapTensorId (∑ i ∈ s, Φ i) X = ∑ i ∈ s, mapTensorId (Φ i) X := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [mapTensorId_zero_map]
  · intro a s ha ih
    simp [ha, ih, mapTensorId_linearMap_add]

/-- `mapTensorId` distributes over finite sums in the channel argument. -/
lemma mapTensorId_linearMap_sum {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    {ι : Type*} [Fintype ι] (Φ : ι → Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    mapTensorId (∑ i, Φ i) X = ∑ i, mapTensorId (Φ i) X := by
  simpa using mapTensorId_linearMap_finset_sum (s := Finset.univ) Φ X

/-- The function `fun X => mapTensorId Φ X` is linear for any linear map Φ. -/
lemma mapTensorId_isLinearMap {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) :
    IsLinearMap ℂ (fun (X : Op (n * k)) => mapTensorId Φ X) :=
  { map_add := mapTensorId_add_basic Φ
    map_smul := mapTensorId_smul_basic Φ }

/-- Linear-map wrapper for tensoring a linear map with the identity on the right. -/
noncomputable def mapTensorIdLinear {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) :
    Op (n * k) →ₗ[ℂ] Op (m * k) :=
  { toFun := fun X => mapTensorId Φ X
    map_add' := (mapTensorId_isLinearMap Φ).map_add
    map_smul' := (mapTensorId_isLinearMap Φ).map_smul }

/-- Tracing out the untouched tensor factor after `mapTensorId Φ` is the same
    as applying `Φ` after tracing out that factor. -/
lemma partialTraceB_mapTensorId {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    partialTraceB (mapTensorId Φ X) = Φ (partialTraceB X) := by
  ext a b
  rw [Quantum.Channels.linearMap_apply_eq_sum_single Φ (partialTraceB X) a b]
  simp only [partialTraceB, mapTensorId, Matrix.of_apply,
    finProdFinEquiv_symm_apply]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext j
  rw [Finset.sum_mul]
  congr 1
  funext r
  ring_nf

/-- Trace through `mapTensorId`: tracing the tensored output equals tracing the base map applied to
    the base partial trace. -/
lemma trace_mapTensorId {N M K : ℕ}
    [NeZero N] [NeZero M] [NeZero K] (Φ : Op N →ₗ[ℂ] Op M) (A : Op (N * K)) :
    (mapTensorId Φ A).trace = (Φ (partialTraceB A)).trace := by
  rw [← trace_partialTraceB (mapTensorId Φ A), partialTraceB_mapTensorId]

/-- **Trailing-factor `partialTraceB_mapTensorId`.**  When the untouched tensor
    factor splits as `d1 * d2`, tracing out only the trailing `d2` factor (after the
    reassociation cast) commutes with `mapTensorId Φ`, leaving the inner `d1` factor
    as the spectator of the resulting `mapTensorId Φ`. -/
lemma partialTraceB_mapTensorId_trailing {n m d1 d2 : ℕ}
    [NeZero n] [NeZero m] [NeZero d1] [NeZero d2]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * (d1 * d2))) :
    partialTraceB ((Nat.mul_assoc m d1 d2).symm ▸ mapTensorId Φ X) =
      mapTensorId Φ (partialTraceB ((Nat.mul_assoc n d1 d2).symm ▸ X)) := by
  ext α β
  simp only [partialTraceB, mapTensorId, Matrix.of_apply, matrix_eqRec_apply,
    finProdFinEquiv_symm_cast_assoc, finProdFinEquiv_cast_assoc,
    Equiv.symm_apply_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Finset.sum_comm

/-- Tracing out the `Φ`-image tensor factor after `mapTensorId Φ` is the same
    as tracing out that factor first, when `Φ` is trace-preserving.

    `Tr_A((Φ ⊗ id)(X)) = Tr_A(X)`: summing the `Φ`-image diagonal collapses
    `Σ_a Φ(E_{i'j'})_{a,a} = Tr(Φ(E_{i'j'})) = δ_{i'j'}`, leaving the partial
    trace of `X` over its own first factor. -/
lemma partialTraceA_mapTensorId {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ_tp : IsTracePreserving ⇑Φ) (X : Op (n * k)) :
    partialTraceA (mapTensorId Φ X) = partialTraceA X := by
  ext i j
  simp only [partialTraceA, mapTensorId, Matrix.of_apply,
    finProdFinEquiv_symm_apply]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  -- `Σ_a` is outermost; swap it past `Σ_{i'}` and `Σ_{j'}`, then factor it as
  -- `Tr(Φ(E_{i'j'}))`.
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i'; rw [Finset.sum_comm]
    arg 2; ext j'; rw [← Finset.sum_mul]
  -- `Σ_a Φ(E_{i'j'})_{a,a} = Tr(Φ(E_{i'j'})) = Tr(E_{i'j'}) = δ_{i'j'}`.
  have hδ : ∀ i' j' : Fin n,
      (∑ a : Fin m, Φ (single i' j' 1) a a) = if i' = j' then (1 : ℂ) else 0 := by
    intro i' j'
    have htr : (∑ a : Fin m, Φ (single i' j' 1) a a) = (Φ (single i' j' 1)).trace := rfl
    rw [htr, hΦ_tp (single i' j' 1)]
    by_cases h : i' = j'
    · subst h; simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h, h]
  simp_rw [hδ]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The Choi matrix of `fun X => mapTensorId Φ X` (acting on `Op (n * k)`)
    is PSD when the Choi matrix of Φ is PSD (i.e., when Φ is completely
    positive).

    Mathematically: `Choi(Φ ⊗ id_k) = Choi(Φ) ⊗ I_{k²}` and the tensor
    product of PSD matrices is PSD. -/
lemma mapTensorId_isCompletelyPositive {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (hΦ_cp : IsCompletelyPositive Φ) :
    IsCompletelyPositive (fun (X : Op (n * k)) => mapTensorId Φ X) := by
  -- Kraus decomposition: Φ(A) = Σ_ℓ K_ℓ A K_ℓ† since Φ is CP and linear
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum Φ hΦ_cp
  -- Tensored Kraus operators: L_ℓ = K_ℓ ⊗ I_k
  set L : Fin r → Matrix (Fin (m * k)) (Fin (n * k)) ℂ := fun ℓ =>
    Matrix.of fun p q =>
      K ℓ (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 *
        if (finProdFinEquiv.symm p).2 = (finProdFinEquiv.symm q).2
        then 1 else 0
  -- mapTensorId Φ equals the Kraus map with operators L
  suffices h_eq : ∀ X : Op (n * k),
      mapTensorId Φ X = krausMapFintype L X by
    unfold IsCompletelyPositive
    rw [show (fun (X : Op (n * k)) => mapTensorId Φ X) =
        ⇑(krausMapFintype L) from funext h_eq]
    exact krausMapFintype_isCompletelyPositive L
  intro X; ext p q
  -- Unfold both sides and match entry-by-entry
  simp only [mapTensorId, Matrix.of_apply, krausMapFintype, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  -- Rewrite Φ(E_{ij}) using Kraus decomposition
  simp_rw [hK, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  -- Simplify matrix units and expand L
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [L, Matrix.of_apply, finProdFinEquiv_symm_apply]
  simp only [star_mul', apply_ite, star_one, star_zero]
  -- Transform RHS: decompose Fin(n*k) sums, simplify, collapse indicators
  symm
  conv_lhs => arg 2; ext ℓ; rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  simp only [mul_one, mul_zero, ite_mul, zero_mul]
  simp_rw [Fintype.sum_ite_eq]
  conv_lhs =>
    arg 2; ext ℓ; arg 2; ext j; arg 1
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Fintype.sum_prod_type]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  simp_rw [Fintype.sum_ite_eq]
  -- Distribute, reorder sums (∑_ℓ ∑_j ∑_i → ∑_i ∑_j ∑_ℓ), factor
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j; arg 2; ext ℓ
    rw [mul_right_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A trace-preserving map sends each matrix unit to an operator with trace `δᵢⱼ`. -/
lemma IsTracePreserving.sum_apply_single {n m : ℕ} [NeZero n] [NeZero m]
    {Φ : Op n → Op m} (hΦ : IsTracePreserving Φ) (i j : Fin n) :
    ∑ a : Fin m, Φ (single i j 1) a a = if i = j then 1 else 0 := by
  have h_trace : ∑ a : Fin m, Φ (single i j 1) a a =
      (Φ (single i j 1)).trace := rfl
  rw [h_trace, hΦ]
  by_cases h : i = j
  · subst h
    simp only [Matrix.trace_single_eq_same, ↓reduceIte]
  · simp only [Matrix.trace_single_eq_of_ne _ _ _ h, h, ↓reduceIte]

/-- `mapTensorId Φ` preserves trace when Φ is trace-preserving.

    `Tr((Φ ⊗ id)(X)) = Tr(X)` follows from:
    `Tr((Φ ⊗ id)(X)) = Σ_{c,s} Σ_{i,j} Φ(E_{ij})_{c,c} · X_{(i,s),(j,s)}`
    `= Σ_s Σ_{i,j} Tr(Φ(E_{ij})) · X_{(i,s),(j,s)}`
    `= Σ_s Σ_i X_{(i,s),(i,s)}` (using Tr(Φ(E_{ij})) = δ_{ij})
    `= Tr(X)`. -/
lemma mapTensorId_isTracePreserving {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (hΦ_tp : IsTracePreserving Φ) :
    IsTracePreserving (fun (X : Op (n * k)) => mapTensorId Φ X) := by
  intro A
  change (mapTensorId Φ A).trace = A.trace
  simp only [mapTensorId, Matrix.trace, Matrix.diag, Matrix.of_apply,
    finProdFinEquiv_symm_apply]
  -- Reindex outer sum to Fin m × Fin k and split
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  -- Swap sums to bring ∑_a innermost (forms trace of Φ(E_{ij}))
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext s; rw [Finset.sum_comm]
    arg 2; ext i; rw [Finset.sum_comm]
    arg 2; ext j; rw [← Finset.sum_mul]
  simp_rw [IsTracePreserving.sum_apply_single (Φ := Φ) hΦ_tp]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Reindex RHS to match
  conv_rhs =>
    rw [← Equiv.sum_comp finProdFinEquiv (g := fun x => A x x)]
    rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The tensored map `fun X => mapTensorId Φ X` is CPTP when Φ is CPTP.

    Combines linearity, complete positivity, and trace preservation. -/
lemma mapTensorId_isCPTP {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ : IsCPTP Φ) :
    IsCPTP (fun (X : Op (n * k)) => mapTensorId Φ X) :=
  ⟨mapTensorId_isLinearMap Φ,
   mapTensorId_isCompletelyPositive Φ hΦ.2.1,
   mapTensorId_isTracePreserving Φ hΦ.2.2⟩

/-- Trace-norm contractivity of `mapTensorId Φ` for CPTP Φ:
    `‖(Φ ⊗ id)(X)‖₁ ≤ ‖X‖₁` for any operator X.

    This follows from `traceNorm_cptp_contractive_general` applied to the
    CPTP map `fun X => mapTensorId Φ X` established by `mapTensorId_isCPTP`. -/
theorem traceNorm_mapTensorId_cptp_contractive {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ : IsCPTP Φ) (X : Op (n * k)) :
    traceNorm (mapTensorId Φ X) ≤ traceNorm X :=
  traceNorm_cptp_contractive_general _ (mapTensorId_isCPTP Φ hΦ) X

/-!
## mapIdTensor distributes over arithmetic and preserves CPTP
-/

/-- `mapIdTensor` distributes over addition. -/
lemma mapIdTensor_add_basic {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (A B : Op (k * n)) :
    mapIdTensor Φ (A + B) = mapIdTensor Φ A + mapIdTensor Φ B := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- `mapIdTensor` distributes over scalar multiplication. -/
lemma mapIdTensor_smul_basic {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (c : ℂ) (X : Op (k * n)) :
    mapIdTensor Φ (c • X) = c • mapIdTensor Φ X := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  ring

/-- The function `fun X => mapIdTensor Φ X` is linear for any linear map Φ. -/
lemma mapIdTensor_isLinearMap {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) :
    IsLinearMap ℂ (fun (X : Op (k * n)) => mapIdTensor Φ X) :=
  { map_add := mapIdTensor_add_basic Φ
    map_smul := mapIdTensor_smul_basic Φ }

/-- The Choi matrix of `fun X => mapIdTensor Φ X` (acting on `Op (k * n)`)
    is PSD when the Choi matrix of Φ is PSD (i.e., when Φ is completely
    positive).

    Mathematically: `Choi(id_k ⊗ Φ) = I_{k²} ⊗ Choi(Φ)` and the tensor
    product of PSD matrices is PSD. -/
lemma mapIdTensor_isCompletelyPositive {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (hΦ_cp : IsCompletelyPositive Φ) :
    IsCompletelyPositive (fun (X : Op (k * n)) => mapIdTensor Φ X) := by
  -- Kraus decomposition: Φ(A) = Σ_ℓ K_ℓ A K_ℓ† since Φ is CP and linear
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum Φ hΦ_cp
  -- Tensored Kraus operators: L_ℓ = I_k ⊗ K_ℓ
  -- L_ℓ_{(s,a),(t,i)} = δ_{s,t} · K_ℓ(a,i)
  set L : Fin r → Matrix (Fin (k * m)) (Fin (k * n)) ℂ := fun ℓ =>
    Matrix.of fun p q =>
      if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm q).1
      then K ℓ (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2
      else 0
  -- mapIdTensor Φ equals the Kraus map with operators L
  suffices h_eq : ∀ X : Op (k * n),
      mapIdTensor Φ X = krausMapFintype L X by
    unfold IsCompletelyPositive
    rw [show (fun (X : Op (k * n)) => mapIdTensor Φ X) =
        ⇑(krausMapFintype L) from funext h_eq]
    exact krausMapFintype_isCompletelyPositive L
  intro X
  -- Show the equality entry-by-entry
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, krausMapFintype, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  -- Rewrite Φ(E_{ij}) using Kraus decomposition
  simp_rw [hK, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  -- Simplify matrix units on LHS
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Expand L on RHS
  simp only [L, Matrix.of_apply, finProdFinEquiv_symm_apply]
  -- Handle star/conjugate of if-then-else
  simp only [apply_ite star, star_zero]
  -- Collapse inner Fin(k*n) sum: the delta on divNat selects one k-component
  -- For fixed ℓ, the inner sum ∑_{r:Fin(k*n)} L(p,r)*X(r,c) collapses to ∑_i K*X
  -- using the identity-factor delta
  conv_rhs =>
    arg 2; ext ℓ; arg 2; ext c
    rw [show (∑ x_2 : Fin (k * n),
        (if p.divNat = x_2.divNat then K ℓ p.modNat x_2.modNat else 0)
          * X x_2 c) =
      ∑ i : Fin n, K ℓ p.modNat i * X (finProdFinEquiv (p.divNat, i)) c from by
        rw [← Equiv.sum_comp finProdFinEquiv]
        simp only [Fintype.sum_prod_type]
        simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
        simp]
  -- Now collapse outer Fin(k*n) sum: delta on divNat for the q-side
  conv_rhs =>
    arg 2; ext ℓ
    rw [show (∑ c : Fin (k * n),
        (∑ i : Fin n, K ℓ p.modNat i * X (finProdFinEquiv (p.divNat, i)) c) *
          (if q.divNat = c.divNat then star (K ℓ q.modNat c.modNat) else 0)) =
      ∑ j : Fin n, (∑ i : Fin n, K ℓ p.modNat i *
        X (finProdFinEquiv (p.divNat, i)) (finProdFinEquiv (q.divNat, j))) *
        star (K ℓ q.modNat j) from by
        rw [← Equiv.sum_comp finProdFinEquiv]
        simp only [Fintype.sum_prod_type]
        simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
        simp only [mul_ite, mul_zero]
        simp]
  -- Now both sides sum over Fin n × Fin n × Fin r but in different order
  -- LHS: ∑_i ∑_j (∑_ℓ K(a,i)*conj(K(b,j))) * X(e(s,i),e(t,j))
  -- RHS: ∑_ℓ ∑_j (∑_i K(a,i)*X(e(s,i),e(t,j))) * conj(K(b,j))
  -- Distribute and reorder sums to match
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j; arg 2; ext ℓ
    rw [mul_right_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `mapIdTensor Φ` preserves trace when Φ is trace-preserving.

    `Tr((id ⊗ Φ)(X)) = Tr(X)` follows from:
    `Tr((id ⊗ Φ)(X)) = Σ_{s,a} Σ_{i,j} Φ(E_{ij})_{a,a} · X_{(s,i),(s,j)}`
    `= Σ_s Σ_{i,j} Tr(Φ(E_{ij})) · X_{(s,i),(s,j)}`
    `= Σ_s Σ_i X_{(s,i),(s,i)}` (using Tr(Φ(E_{ij})) = δ_{ij})
    `= Tr(X)`. -/
lemma mapIdTensor_isTracePreserving {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (hΦ_tp : IsTracePreserving Φ) :
    IsTracePreserving (fun (X : Op (k * n)) => mapIdTensor Φ X) := by
  intro A
  change (mapIdTensor Φ A).trace = A.trace
  simp only [mapIdTensor, Matrix.trace, Matrix.diag, Matrix.of_apply,
    finProdFinEquiv_symm_apply]
  -- Reindex outer sum to Fin k × Fin m and split
  rw [← Equiv.sum_comp (finProdFinEquiv (m := k) (n := m))]
  simp only [Fintype.sum_prod_type]
  simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  -- Now LHS = ∑_s ∑_a ∑_i ∑_j Φ(E_{ij})_{a,a} * A(e(s,i),e(s,j))
  -- Swap sums to bring ∑_a innermost (forms trace of Φ(E_{ij}))
  conv_lhs =>
    arg 2; ext s; rw [Finset.sum_comm]
    arg 2; ext i; rw [Finset.sum_comm]
    arg 2; ext j; rw [← Finset.sum_mul]
  simp_rw [IsTracePreserving.sum_apply_single (Φ := Φ) hΦ_tp]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Reindex RHS to match
  conv_rhs =>
    rw [← Equiv.sum_comp (finProdFinEquiv (m := k) (n := n))
        (g := fun x => A x x)]
    rw [Fintype.sum_prod_type]

/-- The tensored map `fun X => mapIdTensor Φ X` is CPTP when Φ is CPTP.

    Combines linearity, complete positivity, and trace preservation. -/
lemma mapIdTensor_isCPTP {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ : IsCPTP Φ) :
    IsCPTP (fun (X : Op (k * n)) => mapIdTensor Φ X) :=
  ⟨mapIdTensor_isLinearMap Φ,
   mapIdTensor_isCompletelyPositive Φ hΦ.2.1,
   mapIdTensor_isTracePreserving Φ hΦ.2.2⟩

/-- Trace-norm contractivity of `mapIdTensor Φ` for CPTP Φ:
    `‖(id ⊗ Φ)(X)‖₁ ≤ ‖X‖₁` for any operator X. -/
theorem traceNorm_mapIdTensor_cptp_contractive {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ : IsCPTP Φ) (X : Op (k * n)) :
    traceNorm (mapIdTensor Φ X) ≤ traceNorm X :=
  traceNorm_cptp_contractive_general _ (mapIdTensor_isCPTP Φ hΦ) X

/-- Maps on disjoint tensor factors commute:
    (Δ ⊗ id_K) ∘ (id_H ⊗ T) = (id_out ⊗ T) ∘ (Δ ⊗ id_R)

    when Δ : End(H) → End(out) and T : End(R) → End(K).

    The existing `mapTensorId_tensor` handles only product inputs A ⊗ B.
    This is the general version needed for the CKR bound. -/
theorem mapTensorId_compose_different_factors
    {nH nOut nK nR : ℕ} [NeZero nH] [NeZero nOut] [NeZero nK] [NeZero nR]
    (Δ : Op nH →ₗ[ℂ] Op nOut)
    (T : Op nR →ₗ[ℂ] Op nK)
    (X : Op (nH * nR)) :
    mapTensorId Δ (mapIdTensor T X) = mapIdTensor T (mapTensorId Δ X) := by
  ext p q
  simp only [mapTensorId, mapIdTensor, Matrix.of_apply]
  simp only [Equiv.symm_apply_apply, finProdFinEquiv_symm_apply]
  simp_rw [Finset.mul_sum, mul_left_comm (Δ _ _ _) (T _ _ _)]
  conv_lhs =>
    arg 2; ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin nH)))]
  conv_lhs =>
    arg 2; ext x_2; arg 2; ext x
    rw [Finset.sum_comm]
  congr 1; ext x_2
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin nH)))]

/-- `mapIdTensor` for the single-Kraus rectangular conjugation map is
    conjugation by the rectangular tensor `id ⊗ V`. -/
private lemma mapIdTensor_krausMapFintype_single_idTensorRect_conj {c m n : ℕ}
    [NeZero c] [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ) (X : Op (c * n)) :
    let W : Matrix (Fin (c * m)) (Fin (c * n)) ℂ :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (1 : Op c) V)
    mapIdTensor (krausMapFintype (fun _ : Fin 1 => V)) X = W * X * W.conjTranspose := by
  dsimp
  ext p q
  simp only [mapIdTensor, krausMapFintype, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_const, Finset.card_singleton, one_smul,
    finProdFinEquiv_symm_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_apply, single_apply,
    mul_ite, mul_one, mul_zero, conjTranspose_apply, RCLike.star_def, of_apply,
    conjTranspose_submatrix, submatrix_apply, kroneckerMap_apply, one_apply, ite_mul,
    one_mul, zero_mul]
  have hinner : ∀ x x_1 : Fin n,
      (∑ x_2 : Fin n, (∑ x_3 : Fin n,
          if x = x_3 ∧ x_1 = x_2 then V p.modNat x_3 else 0) *
        (starRingEnd ℂ) (V q.modNat x_2)) =
        V p.modNat x * (starRingEnd ℂ) (V q.modNat x_1) := by
    intro x x_1
    rw [Finset.sum_eq_single x_1]
    · simp
    · intro y _ hy
      have hxy : x_1 ≠ y := fun h => hy h.symm
      simp [hxy]
    · intro h
      exact (h (Finset.mem_univ x_1)).elim
  simp_rw [hinner]
  rw [show (∑ x : Fin (c * n),
        (∑ x_1 : Fin (c * n),
            if p.divNat = x_1.divNat then
              V p.modNat x_1.modNat * X x_1 x
            else 0) *
          (starRingEnd ℂ)
            (if q.divNat = x.divNat then V q.modNat x.modNat else 0)) =
      ∑ y : Fin n,
        (∑ x : Fin n,
            V p.modNat x *
              X (finProdFinEquiv (p.divNat, x)) (finProdFinEquiv (q.divNat, y))) *
          (starRingEnd ℂ) (V q.modNat y) from by
        rw [← Equiv.sum_comp finProdFinEquiv]
        simp only [Fintype.sum_prod_type]
        conv_lhs =>
          arg 2; ext r
          arg 2; ext y
          arg 1
          rw [← Equiv.sum_comp finProdFinEquiv]
          rw [Fintype.sum_prod_type]
        simp_rw [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
        simp [apply_ite, Finset.sum_ite_eq, Finset.mem_univ]]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  congr 1
  ext y
  congr 1
  ext x
  ring

/-- A `mapTensorIdLinear`-shaped channel commutes with rectangular
    `id ⊗ V` conjugation on the right tensor factor. This is purely algebraic;
    no isometry assumption on `V` is needed. -/
theorem mapTensorIdLinear_idTensorRect_conj
    {a b m n : ℕ} [NeZero a] [NeZero b] [NeZero m] [NeZero n]
    (Φ : Op a →ₗ[ℂ] Op b)
    (V : Matrix (Fin m) (Fin n) ℂ)
    (X : Op (a * n)) :
    let Wa : Matrix (Fin (a * m)) (Fin (a * n)) ℂ :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (1 : Op a) V)
    let Wb : Matrix (Fin (b * m)) (Fin (b * n)) ℂ :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (1 : Op b) V)
    mapTensorIdLinear Φ (Wa * X * Wa.conjTranspose) =
      Wb * mapTensorIdLinear Φ X * Wb.conjTranspose := by
  dsimp [mapTensorIdLinear]
  let T : Op n →ₗ[ℂ] Op m := krausMapFintype (fun _ : Fin 1 => V)
  calc
    mapTensorId Φ
        ((Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
              (1 : Op a) V)) *
          X *
          (Matrix.reindex finProdFinEquiv finProdFinEquiv
            (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
              (1 : Op a) V)).conjTranspose) =
      mapTensorId Φ (mapIdTensor T X) := by
        rw [mapIdTensor_krausMapFintype_single_idTensorRect_conj]
    _ = mapIdTensor T (mapTensorId Φ X) :=
        mapTensorId_compose_different_factors Φ T X
    _ =
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
            (1 : Op b) V)) *
        mapTensorId Φ X *
        (Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
            (1 : Op b) V)).conjTranspose := by
        rw [mapIdTensor_krausMapFintype_single_idTensorRect_conj]

end Quantum.Channels
