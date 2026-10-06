import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Frobenius
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import Mathlib.Data.Real.Pointwise
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Diamond Norm — completely bounded trace norm, mapTensorId, boundedness

The diamond norm (completely bounded trace norm) quantifies the worst-case
distinguishability of a superoperator when the adversary has access to
entanglement with an ancilla system.

## Main definitions
- `mapTensorId`: Tensor product of a linear map with identity on an ancilla
- `diamondNorm`: Diamond norm ‖Φ‖_◇ = sup { ‖(Φ ⊗ id)(X)‖₁ : ‖X‖₁ ≤ 1 }

## Main statements
- `mapTensorId_output_sandwich`: output sandwiches pass through `mapTensorId`.
- `mapTensorId_castDimLinear`: tensor-id extension commutes with dimension casts.
- `mapTensorId_integral_commute`: `mapTensorId` commutes with Bochner integration
- `diamondNorm_nonneg`: Diamond norm is non-negative
- `diamondNorm_ge_traceNorm_apply`: Single-input trace norm bounded by diamond norm
- `diamondNorm_bddAbove`: The diamond norm set is bounded above
- `diamondNorm_add_le`: Triangle inequality for the diamond norm
- `diamondNorm_smul`: Scalar homogeneity of the diamond norm
- `diamondNorm_neg`: Negation preserves the diamond norm
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace Quantum.Channels

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-!
## Diamond Norm

The diamond norm (completely bounded trace norm) is the worst-case
distinguishability of a superoperator, allowing the adversary to use
entanglement with an ancilla system.
-/

/-- Tensor product of a linear map Φ with the identity on an ancilla system.

    (Φ ⊗ id_k)(X)_{(a,s),(b,t)} = ∑_{i,j} Φ(|i⟩⟨j|)_{a,b} · X_{(i,s),(j,t)}

    Uses `finProdFinEquiv` to identify `Fin (n*k) ≃ Fin n × Fin k`.
    The map acts as Φ on the first tensor factor and identity on the second.

    Takes a `→ₗ[ℂ]` (linear map) to enforce at the type level that the
    decomposition into matrix units Φ(E_{ij}) is consistent with Φ(X) for
    arbitrary X. For a non-linear function, this decomposition would not
    reconstruct Φ(X) correctly. -/
noncomputable def mapTensorId {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (X : Op (n * k)) :
    Op (m * k) :=
  let e_in : Fin n × Fin k ≃ Fin (n * k) := finProdFinEquiv
  let e_out : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv
  Matrix.of fun p q =>
    let (a, s) := e_out.symm p
    let (b, t) := e_out.symm q
    ∑ i : Fin n, ∑ j : Fin n,
      Φ (single i j 1) a b * X (e_in (i, s)) (e_in (j, t))

/-! ## Structural laws for `mapTensorId` -/

/-- Entry of `P ⊗ 1` on product indices. -/
lemma Op_tensor_one_apply {n k : ℕ} (P : Op n) (i a : Fin n) (s u : Fin k) :
    Op.tensor P (1 : Op k) (finProdFinEquiv (i, s)) (finProdFinEquiv (a, u)) =
    P i a * if s = u then 1 else 0 := by
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- Entry of `P ⊗ 1` with an arbitrary left index. -/
lemma Op_tensor_one_apply_right {n k : ℕ} (P : Op n)
    (r : Fin (n * k)) (j : Fin n) (t : Fin k) :
    Op.tensor P (1 : Op k) r (finProdFinEquiv (j, t)) =
    P (finProdFinEquiv.symm r).1 j *
      if (finProdFinEquiv.symm r).2 = t then 1 else 0 := by
  conv_lhs => rw [show r = finProdFinEquiv (finProdFinEquiv.symm r)
    from (finProdFinEquiv.apply_symm_apply r).symm]
  exact Op_tensor_one_apply P _ j _ t

/-- Entry of `P ⊗ 1` with an arbitrary right index. -/
lemma Op_tensor_one_apply_left {n k : ℕ} (P : Op n)
    (i : Fin n) (s : Fin k) (q : Fin (n * k)) :
    Op.tensor P (1 : Op k) (finProdFinEquiv (i, s)) q =
    P i (finProdFinEquiv.symm q).1 *
      if s = (finProdFinEquiv.symm q).2 then 1 else 0 := by
  conv_lhs => rw [show q = finProdFinEquiv (finProdFinEquiv.symm q)
    from (finProdFinEquiv.apply_symm_apply q).symm]
  exact Op_tensor_one_apply P i _ s _

/-- A linear map on matrices decomposes entrywise through matrix units. -/
lemma linearMap_apply_eq_sum_single {n m : ℕ} (Δ : Op n →ₗ[ℂ] Op m)
    (M : Op n) (c d : Fin m) :
    Δ M c d = ∑ i : Fin n, ∑ j : Fin n, M i j * Δ (single i j 1) c d := by
  have hM : M = ∑ i, ∑ j, M i j • single i j 1 := by
    ext r l
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, mul_ite, mul_one, mul_zero]
    symm
    exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ =>
        if_neg (fun ⟨h1, _⟩ => hi h1)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single l
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2))
          (fun h => absurd (Finset.mem_univ l) h) |>.trans (by simp))
  conv_lhs => rw [hM, map_sum, Matrix.sum_apply]
  congr 1
  ext i
  rw [map_sum, Matrix.sum_apply]
  congr 1
  ext j
  rw [Δ.map_smul, Matrix.smul_apply, smul_eq_mul]

/-- The defining sum for a `mapTensorId` entry is the underlying map applied
to the corresponding ancilla block. -/
lemma mapTensorId_entry_eq_apply_block {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (W : Op (n * k)) (c d : Fin m) (s t : Fin k) :
    (∑ i : Fin n, ∑ j : Fin n,
      Φ (single i j 1) c d * W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
    Φ (Matrix.of fun i j => W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) c d := by
  rw [linearMap_apply_eq_sum_single Φ _ c d]
  congr 1
  ext i
  congr 1
  ext j
  simp only [Matrix.of_apply]
  ring

/-- Entry form of `mapTensorId` as the underlying map applied to the
corresponding ancilla block. -/
lemma mapTensorId_apply_eq_apply_block {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (W : Op (n * k)) (p q : Fin (m * k)) :
    mapTensorId Φ W p q =
      Φ (Matrix.of fun i j =>
        W (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
          (finProdFinEquiv (j, (finProdFinEquiv.symm q).2)))
        (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 := by
  simp only [mapTensorId, Matrix.of_apply]
  rw [mapTensorId_entry_eq_apply_block]
  rfl

/-- `mapTensorId` respects composition in the first tensor factor. -/
lemma mapTensorId_comp {n m m' k : ℕ} [NeZero n] [NeZero m] [NeZero m'] [NeZero k]
    (Δ : Op n →ₗ[ℂ] Op m) (K : Op m →ₗ[ℂ] Op m')
    (X : Op (n * k)) :
    mapTensorId K (mapTensorId Δ X) = mapTensorId (K.comp Δ) X := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, LinearMap.comp_apply]
  simp_rw [mapTensorId_entry_eq_apply_block Δ X]
  simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
  simp_rw [mul_comm (K _ _ _) (Δ _ _ _)]
  rw [← linearMap_apply_eq_sum_single K
    (Δ (Matrix.of fun i j =>
      X (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))))]
  change (K.comp Δ)
    (Matrix.of fun i j =>
      X (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2)))
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 = _
  rw [linearMap_apply_eq_sum_single (K.comp Δ)
    (Matrix.of fun i j =>
      X (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2)))
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1]
  simp only [LinearMap.comp_apply, Matrix.of_apply]
  congr 1
  ext x
  congr 1
  ext x_1
  ring

/-- The ancilla block of a sandwich by `P ⊗ 1` and `Q ⊗ 1` is the
corresponding block sandwiched by `P` and `Q`. -/
lemma tensor_sandwich_block {n k : ℕ} [NeZero n] [NeZero k]
    (P Q : Op n) (ρ : Op (n * k)) (s t : Fin k) :
    (Matrix.of fun i j =>
      (Op.tensor P (1 : Op k) * ρ * Op.tensor Q (1 : Op k))
        (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
    P * (Matrix.of fun i j =>
      ρ (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) * Q := by
  set R := Matrix.of fun i j =>
    ρ (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, R]
  simp_rw [Op_tensor_one_apply_left P i s,
    Op_tensor_one_apply_right Q _ j t]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  have h_inner : ∀ (x : Fin (n * k)),
      (∑ r : Fin (n * k),
        (if s = (finProdFinEquiv.symm r).2
          then P i (finProdFinEquiv.symm r).1 * ρ r x else 0)) =
      ∑ a : Fin n,
        P i a * ρ (finProdFinEquiv (a, s)) x := by
    intro x
    rw [show (∑ r, _) = ∑ au : Fin n × Fin k,
          (if s = au.2 then P i au.1 * ρ (finProdFinEquiv au) x else 0)
      from Fintype.sum_equiv finProdFinEquiv.symm _ _
        (fun r => by simp only [finProdFinEquiv.apply_symm_apply])]
    rw [Fintype.sum_prod_type]
    simp [Finset.mem_univ]
  rw [show (∑ x : Fin (n * k), _) = ∑ bv : Fin n × Fin k,
        (∑ r, (if s = (finProdFinEquiv.symm r).2
          then P i (finProdFinEquiv.symm r).1 * ρ r (finProdFinEquiv bv) else 0)) *
        (if bv.2 = t then Q bv.1 j else 0)
    from Fintype.sum_equiv finProdFinEquiv.symm _ _
      (fun r => by
        simp only [finProdFinEquiv.apply_symm_apply]
        split_ifs <;> simp)]
  rw [Fintype.sum_prod_type]
  simp_rw [h_inner]
  congr 1
  ext b
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Sandwiching the output of `Φ ⊗ id` by `L ⊗ 1` and `R ⊗ 1` is
the tensor-id extension of the output-sandwiched map `M ↦ L * Φ M * R`. -/
lemma mapTensorId_output_sandwich {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (L R : Op m) (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    Op.tensor L (1 : Op k) * mapTensorId Φ X * Op.tensor R (1 : Op k) =
      mapTensorId ((LinearMap.mulLeft ℂ L).comp ((LinearMap.mulRight ℂ R).comp Φ)) X := by
  ext p q
  rw [← finProdFinEquiv.apply_symm_apply p, ← finProdFinEquiv.apply_symm_apply q,
    mapTensorId_apply_eq_apply_block]
  have hblock := congr_fun₂ (tensor_sandwich_block L R (mapTensorId Φ X)
    (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2)
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
  have hΦblock : (Matrix.of fun i j => mapTensorId Φ X
        (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))) =
      Φ (Matrix.of fun i j => X (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))) := by
    ext i j
    rw [Matrix.of_apply, mapTensorId_apply_eq_apply_block]
    simp only [Equiv.symm_apply_apply]
  simp only [Matrix.of_apply] at hblock
  rw [hblock, hΦblock]
  simp only [Equiv.symm_apply_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Matrix.mul_assoc]

/-- If every output of `Φ` is fixed by `M ↦ L * M * R`, then every output of
`Φ ⊗ id` is fixed by the corresponding tensor sandwich. -/
lemma mapTensorId_output_sandwich_eq_self {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (L R : Op m) (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * k))
    (hLR : ∀ M : Op n, L * Φ M * R = Φ M) :
    Op.tensor L (1 : Op k) * mapTensorId Φ X * Op.tensor R (1 : Op k) = mapTensorId Φ X := by
  rw [mapTensorId_output_sandwich]
  congr 1
  ext1 M
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    ← Matrix.mul_assoc, hLR]

/-- Extending a dimension cast by the identity is the product-dimension cast. -/
lemma mapTensorId_castDimLinear {a b k : ℕ} [NeZero a] [NeZero b] [NeZero k] (h : a = b)
    (M : Op (a * k)) :
    mapTensorId (k := k) (Op.castDimLinear h) M = Op.castDim (congrArg (· * k) h) M := by
  subst h
  ext p q
  rw [mapTensorId_apply_eq_apply_block]
  simp only [Op.castDimLinear, Op.castDim, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  rw [show (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2) :
        Fin (a * k)) = p from Equiv.apply_symm_apply finProdFinEquiv p,
    show (finProdFinEquiv ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2) :
        Fin (a * k)) = q from Equiv.apply_symm_apply finProdFinEquiv q]

/-- `mapTensorId` distributes over subtraction in the channel argument. -/
lemma mapTensorId_linearMap_sub {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ Ψ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    mapTensorId (Φ - Ψ) X = mapTensorId Φ X - mapTensorId Ψ X := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, LinearMap.sub_apply, Matrix.sub_apply]
  simp_rw [sub_mul]
  simp only [Finset.sum_sub_distrib]

/-- `mapTensorId` distributes over addition in the channel argument. -/
lemma mapTensorId_linearMap_add {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ Ψ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    mapTensorId (Φ + Ψ) X = mapTensorId Φ X + mapTensorId Ψ X := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, LinearMap.add_apply, Matrix.add_apply]
  simp_rw [add_mul]
  simp only [Finset.sum_add_distrib]

/-- `mapTensorId` distributes over scalar multiplication in the channel argument. -/
lemma mapTensorId_linearMap_smul {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (c : ℂ) (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    mapTensorId (c • Φ) X = c • mapTensorId Φ X := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, LinearMap.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext i
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- **Diamond norm** (completely bounded trace norm) of a linear map.

    ‖Φ‖_◇ = sup { ‖(Φ ⊗ id_n)(X)‖₁ : X ∈ Op(H⊗H), ‖X‖₁ ≤ 1 }

    The supremum is over ALL operators X with trace norm ≤ 1, not just
    Hermitian ones. Uses `traceNorm` (singular value sum) which
    works for arbitrary matrices.

    Takes a `→ₗ[ℂ]` (linear map) to enforce linearity at the type level.
    This is essential because `mapTensorId` decomposes X into matrix units
    and applies Φ entry-by-entry — this equals (Φ ⊗ id)(X) only when Φ
    is linear.

    Reference: Kitaev (1997), Paulsen "Completely Bounded Maps". -/
noncomputable def diamondNorm {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) : ℝ :=
  haveI : NeZero (n * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos n) (NeZero.pos n))⟩
  haveI : NeZero (m * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos m) (NeZero.pos n))⟩
  sSup (setOf fun t : ℝ => ∃ X : Op (n * n),
    traceNorm X ≤ 1 ∧
    t = traceNorm (mapTensorId Φ X))

/-- The trace norm of the zero operator is zero. -/
lemma traceNorm_zero {n : ℕ} [NeZero n] :
    Quantum.Metrics.traceNorm (0 : Op n) = 0 := by
  unfold Quantum.Metrics.traceNorm
  apply Finset.sum_eq_zero
  intro i _
  suffices h : ∀ (hAA : (0 : Op n).IsHermitian),
      hAA.eigenvalues i = 0 by simp [h]
  intro hAA
  have := hAA.eigenvalues_eq i
  simp only [Matrix.zero_mulVec, dotProduct_zero, map_zero] at this
  exact_mod_cast this

/-- The tensor-id extension of any linear map sends zero to zero. -/
lemma mapTensorId_zero {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) :
    mapTensorId (k := k) Φ 0 = 0 := by
  ext p q; simp [mapTensorId, Matrix.of_apply]

/-- The tensor-id extension of the zero linear map is zero on every input. -/
lemma mapTensorId_zero_map {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (X : Op (n * k)) :
    mapTensorId (k := k) (0 : Op n →ₗ[ℂ] Op m) X = 0 := by
  ext p q; simp [mapTensorId, Matrix.of_apply]

/-- The tensor-id extension of a linear map as a continuous linear map. -/
private def mapTensorIdCLM {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) :
    Op (n * k) →L[ℂ] Op (m * k) :=
  ({ toFun := mapTensorId Φ
     map_add' := by
       intro A B
       ext p q
       simp [mapTensorId, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intro c X
       ext p q
       simp only [mapTensorId, Matrix.of_apply, RingHom.id_apply, Matrix.smul_apply, smul_eq_mul]
       rw [Finset.mul_sum]
       congr 1
       ext i
       rw [Finset.mul_sum]
       congr 1
       ext j
       ring } :
      Op (n * k) →ₗ[ℂ] Op (m * k)).toContinuousLinearMap

/-- `mapTensorId` commutes with Bochner integration. -/
theorem mapTensorId_integral_commute
    {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    (Φ : Op n →ₗ[ℂ] Op m) (f : α → Op (n * k)) (hf : Integrable f μ) :
    mapTensorId Φ (∫ x, f x ∂μ) = ∫ x, mapTensorId Φ (f x) ∂μ := by
  let T : Op (n * k) →L[ℂ] Op (m * k) := mapTensorIdCLM (n := n) (m := m) (k := k) Φ
  simpa [mapTensorIdCLM, LinearMap.coe_toContinuousLinearMap'] using
    (T.integral_comp_comm hf).symm

/-- The diamond norm is non-negative. -/
lemma diamondNorm_nonneg {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) : 0 ≤ diamondNorm Φ := by
  haveI : NeZero (n * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos n) (NeZero.pos n))⟩
  haveI : NeZero (m * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos m) (NeZero.pos n))⟩
  unfold diamondNorm
  by_cases hbdd : BddAbove
    (setOf fun t : ℝ => ∃ X : Op (n * n),
      Quantum.Metrics.traceNorm X ≤ 1 ∧
      t = Quantum.Metrics.traceNorm (mapTensorId Φ X))
  · apply le_csSup_of_le hbdd
    · exact ⟨0, by
        rw [traceNorm_zero (n := n * n)]
        exact zero_le_one, by
        rw [mapTensorId_zero, traceNorm_zero (n := m * n)]⟩
    · exact le_refl 0
  · rw [csSup_of_not_bddAbove hbdd, Real.sSup_empty]

/-- For PSD matrices, trace norm equals the real part of the trace. -/
lemma traceNorm_posSemidef_eq_trace {d : ℕ} [NeZero d]
    (P : Op d) (hP : P.PosSemidef) :
    traceNorm P = P.trace.re := by
  rw [traceNorm_hermitian_eq P hP.1]
  exact Quantum.Metrics.traceNormHermitian_of_posSemidef P hP

/-- Density operators have trace norm equal to 1. -/
lemma traceNorm_densityOp_eq_one {d : ℕ} [NeZero d] (ρ : DensityOp d) :
    traceNorm ρ.toOp = 1 := by
  rw [traceNorm_posSemidef_eq_trace ρ.toOp (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)]
  simp [ρ.trace_one]

/-- The standard basis projector |0⟩⟨0| is positive semidefinite. -/
lemma stdBasisProj_posSemidef {d : ℕ} [NeZero d] :
    (Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ)).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · exact star_zero _
  · intro x
    apply Finsupp.sum_nonneg
    intro i _
    apply Finsupp.sum_nonneg
    intro j _
    simp only [Matrix.single_apply]
    split_ifs with h
    · obtain ⟨hi, hj⟩ := h; subst hi; subst hj
      simp only [mul_one]
      exact star_mul_self_nonneg (x 0)
    · simp [mul_zero, zero_mul]

/-- The standard basis projector |0⟩⟨0| has trace 1. -/
lemma stdBasisProj_trace {d : ℕ} [NeZero d] :
    (Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ)).trace = 1 := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.single_apply]
  have : ∀ x : Fin d, (if (0 : Fin d) = x ∧ (0 : Fin d) = x then (1 : ℂ) else 0) =
      if x = (0 : Fin d) then 1 else 0 := by
    intro x; split_ifs with h1 h2 h2 <;> simp_all
  simp_rw [this]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- The standard basis projector is self-adjoint. -/
lemma stdBasisProj_conjTranspose {d : ℕ} [NeZero d] :
    (Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ))† =
    Matrix.single (0 : Fin d) (0 : Fin d) (1 : ℂ) := by
  exact stdBasisProj_posSemidef.1

/-- The standard basis projector is idempotent. -/
lemma stdBasisProj_mul_self {d : ℕ} [NeZero d] :
    (Matrix.single (0 : Fin d) 0 1 : Op d) * (Matrix.single (0 : Fin d) 0 1 : Op d) =
    Matrix.single (0 : Fin d) 0 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply]
  -- Sum over k: (if 0=i ∧ 0=k then 1 else 0) * (if 0=k ∧ 0=j then 1 else 0)
  by_cases hi : (0 : Fin d) = i <;> by_cases hj : (0 : Fin d) = j
  · subst hi; subst hj; simp [Finset.mem_univ]
  · subst hi; simp only [true_and, ite_mul, one_mul, zero_mul]
    simp [hj]
  · subst hj; simp only [and_true, mul_ite, mul_one, mul_zero]
    simp [hi]
  · simp only [hi, false_and, ite_false, zero_mul, Finset.sum_const_zero, hj]

/-- (A ⊗ E₀₀)† * (A ⊗ E₀₀) = (A† * A) ⊗ E₀₀ -/
lemma conjTranspose_mul_tensor_stdBasisProj {d₁ d₂ : ℕ} [NeZero d₂]
    (A : Op d₁) :
    (A ⊗ (Matrix.single (0 : Fin d₂) 0 1 : Op d₂))† *
    (A ⊗ (Matrix.single (0 : Fin d₂) 0 1 : Op d₂)) =
    (A† * A) ⊗ (Matrix.single (0 : Fin d₂) 0 1 : Op d₂) := by
  rw [Op.tensor_conjTranspose, stdBasisProj_conjTranspose, Op.tensor_mul,
      stdBasisProj_mul_self]

/-- Sum of f(eigenvalues) is invariant under reindexing by finProdFinEquiv.

For a Hermitian matrix M on Fin n × Fin m, the sum of f(eigenvalues) of
the reindexed matrix (on Fin (n*m)) equals the sum of f(eigenvalues) of M.
This follows from the fact that reindexing preserves the characteristic polynomial. -/
lemma sum_f_eigenvalues_reindex {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (M : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ)
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    let hR : (Matrix.reindex finProdFinEquiv finProdFinEquiv M).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_reindex, hM.eq]
    ∑ i : Fin (d₁ * d₂), f (hR.eigenvalues i) =
    ∑ k : Fin d₁ × Fin d₂, f (hM.eigenvalues k) := by
  intro hR
  -- Step 1: charpolys are equal
  have hcp : (Matrix.reindex finProdFinEquiv finProdFinEquiv M).charpoly = M.charpoly :=
    Matrix.charpoly_reindex finProdFinEquiv M
  -- Step 2: roots (as multisets of ℂ) are equal
  have hroots_R := hR.roots_charpoly_eq_eigenvalues
  have hroots_M := hM.roots_charpoly_eq_eigenvalues
  -- Step 3: eigenvalue multisets (over ℝ) are equal
  have hms : Multiset.map hR.eigenvalues Finset.univ.val =
      Multiset.map hM.eigenvalues Finset.univ.val := by
    apply Multiset.map_injective Complex.ofReal_injective
    simp only [Multiset.map_map]
    change Multiset.map (RCLike.ofReal ∘ hR.eigenvalues) _ =
           Multiset.map (RCLike.ofReal ∘ hM.eigenvalues) _
    rw [← hroots_R, ← hroots_M, hcp]
  -- Step 4: sums of f(eigenvalues) are equal
  have h := congr_arg (Multiset.map f) hms
  have hsums := congr_arg Multiset.sum h
  rw [Multiset.map_map, Multiset.map_map] at hsums
  rwa [Finset.sum_map_val, Finset.sum_map_val] at hsums

/-- For a PSD idempotent (projector) matrix, eigenvalues satisfy λ² = λ.

This follows from the spectral theorem: P = U D U†, P² = U D² U† = P implies D² = D. -/
lemma projector_eigenvalues_sq_eq {d : ℕ} [NeZero d]
    (P : Op d) (hP_herm : P.IsHermitian) (hP_idem : P * P = P) :
    ∀ j, hP_herm.eigenvalues j ^ 2 = hP_herm.eigenvalues j := by
  -- Direct proof via eigenvectors: P vⱼ = λⱼ vⱼ and P² vⱼ = λⱼ² vⱼ = P vⱼ = λⱼ vⱼ
  intro j
  set v := (hP_herm.eigenvectorBasis j).ofLp with hv_def
  have h_ev := hP_herm.mulVec_eigenvectorBasis j
  -- (P * P) · v = P · (P · v) = λⱼ · (P · v) = λⱼ · λⱼ · v = λⱼ² · v
  have h_sq : (P * P).mulVec v =
      (hP_herm.eigenvalues j * hP_herm.eigenvalues j) • v := by
    rw [← Matrix.mulVec_mulVec, h_ev, Matrix.mulVec_smul, h_ev, smul_smul]
  -- P² = P, so (P*P)·v = P·v = λⱼ v
  rw [hP_idem, h_ev] at h_sq
  -- h_sq : λⱼ • v = (λⱼ * λⱼ) • v, so (λⱼ * λⱼ - λⱼ) • v = 0
  have h_sub : (hP_herm.eigenvalues j * hP_herm.eigenvalues j -
      hP_herm.eigenvalues j) • v = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr h_sq.symm
  -- v ≠ 0 (orthonormal basis element)
  have hv_ne : v ≠ 0 := by
    intro h_abs
    exact hP_herm.eigenvectorBasis.orthonormal.ne_zero j
      (show (hP_herm.eigenvectorBasis j) = 0 by ext i; exact congr_fun h_abs i)
  -- Extract scalar equality from smul equality
  have h_eq : hP_herm.eigenvalues j * hP_herm.eigenvalues j = hP_herm.eigenvalues j := by
    rcases smul_eq_zero.mp h_sub with h | h
    · linarith
    · exact absurd h hv_ne
  linarith [h_eq]

/-- For a PSD idempotent (projector) matrix with trace t, ∑ √(eigenvalues) = t.

Since eigenvalues of a projector are in {0, 1}, √λ = λ, so ∑ √λ = ∑ λ = trace. -/
lemma sum_sqrt_eigenvalues_projector {d : ℕ} [NeZero d]
    (P : Op d) (hP : P.PosSemidef) (hP_idem : P * P = P) :
    ∑ j : Fin d, Real.sqrt (hP.1.eigenvalues j) = P.trace.re := by
  have h_nn : ∀ j, 0 ≤ hP.1.eigenvalues j := hP.eigenvalues_nonneg
  have h_sq_ev := projector_eigenvalues_sq_eq P hP.1 hP_idem
  -- √λ = λ for each non-negative eigenvalue satisfying λ² = λ
  have h_sqrt_eq : ∀ j, Real.sqrt (hP.1.eigenvalues j) = hP.1.eigenvalues j := by
    intro j
    have h01 : hP.1.eigenvalues j = 0 ∨ hP.1.eigenvalues j = 1 := by
      have : hP.1.eigenvalues j * (hP.1.eigenvalues j - 1) = 0 := by nlinarith [h_sq_ev j]
      rcases mul_eq_zero.mp this with h | h
      · left; exact h
      · right; linarith
    rcases h01 with h | h <;> simp [h]
  simp_rw [h_sqrt_eq]
  rw [hP.1.trace_eq_sum_eigenvalues]
  simp [Complex.ofReal_re]

/-- Sum of √eigenvalues of a tensor product equals double sum of √(product eigenvalues).

Bridges Op.tensor (Fin(d₁*d₂)-indexed) with sum_eigenvalues_kronecker (Fin d₁ × Fin d₂-indexed). -/
lemma sum_sqrt_eigenvalues_tensor {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (P : Op d₁) (Q : Op d₂)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPQ : (P ⊗ Q).IsHermitian)
    (f : ℝ → ℝ) :
    ∑ i : Fin (d₁ * d₂), f (hPQ.eigenvalues i) =
    ∑ i : Fin d₁, ∑ j : Fin d₂, f (hP.eigenvalues i * hQ.eigenvalues j) := by
  -- Step 1: P ⊗ Q = reindex e e (P ⊗ₖ Q) by definition of Op.tensor
  have h_tensor_def : P ⊗ Q = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) P Q) := rfl
  -- Step 2: Kronecker product is Hermitian
  have h_kron := Math.SpectralTheory.kronecker_isHermitian P Q hP hQ
  -- Step 3: Use sum_f_eigenvalues_reindex
  have h_reindex := sum_f_eigenvalues_reindex (Matrix.kroneckerMap (· * ·) P Q) h_kron f
  -- Need to match hPQ with the reindex Hermitian proof
  have h_reindex_herm : (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) P Q)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_reindex, h_kron.eq]
  have h_ev_match : hPQ.eigenvalues = h_reindex_herm.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact congr_arg Matrix.charpoly h_tensor_def
  simp_rw [h_ev_match]
  rw [h_reindex]
  -- Step 4: Apply sum_eigenvalues_kronecker
  exact Math.SpectralTheory.sum_eigenvalues_kronecker P Q hP hQ f

/-- Trace norm of a tensor product A ⊗ |0⟩⟨0| equals trace norm of A. -/
lemma traceNorm_tensor_stdBasisProj {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    [NeZero (d₁ * d₂)]
    (A : Op d₁) :
    traceNorm (A ⊗ (Matrix.single (0 : Fin d₂) 0 1 : Op d₂)) = traceNorm A := by
  set E₀₀ : Op d₂ := Matrix.single 0 0 1 with hE_def
  -- (A ⊗ E₀₀)† * (A ⊗ E₀₀) = (A† * A) ⊗ E₀₀
  have h_product := conjTranspose_mul_tensor_stdBasisProj (d₂ := d₂) A
  -- Hermiticity proofs
  have h_AcA_herm : (A† * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have h_E_herm : E₀₀.IsHermitian := (stdBasisProj_posSemidef (d := d₂)).1
  have h_E_psd : E₀₀.PosSemidef := stdBasisProj_posSemidef (d := d₂)
  have h_AcA_psd : (A† * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  -- Hermiticity of tensor product
  have h_tensor_herm : ((A ⊗ E₀₀)† * (A ⊗ E₀₀)).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have h_AE_herm : ((A† * A) ⊗ E₀₀).IsHermitian := by
    rw [← h_product]; exact h_tensor_herm
  -- Unfold traceNorm
  simp only [traceNorm]
  -- Match eigenvalues via same matrix
  set h1 : ((A ⊗ E₀₀)† * (A ⊗ E₀₀)).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  set h2 : (A† * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  -- eigenvalues of (A⊗E₀₀)†*(A⊗E₀₀) = eigenvalues of (A†A) ⊗ E₀₀
  have h_ev1 : h1.eigenvalues = h_AE_herm.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, h_product]
  -- Use sum_sqrt_eigenvalues_tensor to convert to double sum
  conv_lhs => rw [show ∑ i, √(h1.eigenvalues i) =
      ∑ i, √(h_AE_herm.eigenvalues i) from by simp_rw [h_ev1]]
  rw [sum_sqrt_eigenvalues_tensor (A† * A) E₀₀ h_AcA_herm h_E_herm h_AE_herm Real.sqrt]
  -- Now: ∑ i, ∑ j, √(eigenval_i(A†A) * eigenval_j(E₀₀)) = ∑ i, √(eigenval_i(A†A))
  -- Factor using √(a*b) = √a * √b for a,b ≥ 0
  have h_nn_A : ∀ i, 0 ≤ h_AcA_herm.eigenvalues i := h_AcA_psd.eigenvalues_nonneg
  have h_nn_E : ∀ j, 0 ≤ h_E_herm.eigenvalues j := h_E_psd.eigenvalues_nonneg
  simp_rw [Real.sqrt_mul (h_nn_A _)]
  -- Factor: ∑ x₁, √(λᵢ) * √(μⱼ) = √(λᵢ) * ∑ x₁, √(μⱼ)
  simp_rw [← Finset.mul_sum]
  -- ∑ j, √(eigenval_j(E₀₀)) = trace(E₀₀).re = 1
  have h_E_sum : ∑ j : Fin d₂, Real.sqrt (h_E_herm.eigenvalues j) = 1 := by
    rw [sum_sqrt_eigenvalues_projector E₀₀ h_E_psd (stdBasisProj_mul_self (d := d₂)),
        stdBasisProj_trace (d := d₂)]
    simp
  simp_rw [h_E_sum, mul_one]

/-- mapTensorId on a tensor product gives the tensor product of Φ(A) with B. -/
lemma mapTensorId_tensor {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (A : Op n) (B : Op k) :
    mapTensorId Φ (A ⊗ B) = (Φ A) ⊗ B := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, kroneckerMap_apply]
  -- Both sides should now be entry-level expressions
  -- LHS: ∑ i j, Φ(E_{ij})(a,b) * A(i,j) * B(s,t)
  -- RHS: Φ(A)(a,b) * B(s,t) where (a,s)=e.symm p, (b,t)=e.symm q
  -- Decompose A = ∑ i j, A(i,j) • E_{ij} for linearity step
  have hA_decomp : A = ∑ i, ∑ j, A i j • single i j 1 := by
    ext r c; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact if_neg (fun ⟨h1, _⟩ => hi h1)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  -- Simplify finProdFinEquiv.symm (finProdFinEquiv ...) = id
  simp only [Equiv.symm_apply_apply]
  -- Now need: ∑ x x_1, Φ(E_{x,x_1})(a,b) * (A x x_1 * B s t) = Φ(A)(a,b) * B(s,t)
  -- Use linearity
  have linearity : ∀ (a b : Fin m), ∑ i : Fin n, ∑ j : Fin n,
      A i j * Φ (single i j 1) a b = Φ A a b := by
    intro a b
    conv_rhs => rw [hA_decomp, map_sum, Matrix.sum_apply]
    congr 1; ext i
    rw [map_sum, Matrix.sum_apply]
    congr 1; ext j
    rw [Φ.map_smul]
    simp [Matrix.smul_apply, smul_eq_mul]
  -- Factor out B(s,t) and apply linearity
  simp_rw [show ∀ (x y z : ℂ), x * (y * z) = z * (y * x) from fun x y z => by ring]
  simp_rw [← Finset.mul_sum]
  rw [linearity]
  simp only [Equiv.toFun_as_coe, mul_comm]

/-- For nonneg reals, if ∑ √λ ≤ 1 then ∑ λ ≤ 1.
Each √λ ∈ [0,1], so λ = (√λ)² ≤ √λ, and summing gives ∑λ ≤ ∑√λ ≤ 1. -/
lemma sum_le_of_sum_sqrt_le_one {d : ℕ}
    (f : Fin d → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, Real.sqrt (f i) ≤ 1) :
    ∑ i, f i ≤ 1 := by
  calc ∑ i, f i ≤ ∑ i, Real.sqrt (f i) := by
        apply Finset.sum_le_sum; intro i _
        have hi_nonneg : 0 ≤ Real.sqrt (f i) := Real.sqrt_nonneg _
        have hi_le_one : Real.sqrt (f i) ≤ 1 := by
          calc Real.sqrt (f i) ≤ ∑ j, Real.sqrt (f j) :=
                Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
              _ ≤ 1 := hsum
        calc f i = Real.sqrt (f i) ^ 2 := (Real.sq_sqrt (hf i)).symm
          _ = Real.sqrt (f i) * Real.sqrt (f i) := sq (Real.sqrt (f i))
          _ ≤ Real.sqrt (f i) * 1 := by
              exact mul_le_mul_of_nonneg_left hi_le_one hi_nonneg
          _ = Real.sqrt (f i) := mul_one _
    _ ≤ 1 := hsum

/-- The trace of A†A equals the sum of squared norms of entries. -/
lemma trace_conjTranspose_mul_self_re {d : ℕ}
    (A : Op d) :
    (A† * A).trace.re = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [Complex.re_sum]
  congr 1; ext j
  rw [show star (A j i) = (starRingEnd ℂ) (A j i) from rfl,
      Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]

/-- traceNorm X ≤ 1 implies trace(X†X).re ≤ 1 (Frobenius norm² ≤ 1). -/
lemma frobenius_sq_le_one_of_traceNorm_le_one {d : ℕ} [NeZero d]
    (X : Op d) (hX : traceNorm X ≤ 1) :
    (X† * X).trace.re ≤ 1 := by
  -- trace(X†X).re = ∑ eigenvalues of X†X
  -- traceNorm X = ∑ √(eigenvalues of X†X) ≤ 1
  -- By sum_le_of_sum_sqrt_le_one, ∑ eigenvalues ≤ 1
  have hAA : (X† * X).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hAA.trace_eq_sum_eigenvalues]
  have hAA_psd : (X† * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have h_re : (∑ i, (↑(hAA.eigenvalues i) : ℂ)).re = ∑ i, hAA.eigenvalues i := by
    simp [Complex.ofReal_re]
  calc (∑ i, (↑(hAA.eigenvalues i) : ℂ)).re = ∑ i, hAA.eigenvalues i := h_re
    _ ≤ 1 := sum_le_of_sum_sqrt_le_one _ (fun i => hAA_psd.eigenvalues_nonneg i) hX

/-- Cauchy-Schwarz for complex finite sums: ‖∑ c·x‖² ≤ ∑ normSq(c) when ∑ ‖x‖² ≤ 1. -/
lemma norm_sq_sum_mul_le {ι : Type*} [Fintype ι]
    (c x : ι → ℂ) (hx : ∑ k, ‖x k‖ ^ 2 ≤ 1) :
    ‖∑ k, c k * x k‖ ^ 2 ≤ ∑ k, Complex.normSq (c k) := by
  have h1 : ‖∑ k, c k * x k‖ ≤ ∑ k, ‖c k‖ * ‖x k‖ := by
    calc _ ≤ ∑ k, ‖c k * x k‖ := norm_sum_le _ _
      _ = _ := by simp_rw [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖c k‖) (fun k => ‖x k‖)
  calc ‖∑ k, c k * x k‖ ^ 2
      ≤ (∑ k, ‖c k‖ * ‖x k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ k, ‖c k‖ ^ 2) * (∑ k, ‖x k‖ ^ 2) := h2
    _ ≤ (∑ k, ‖c k‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hx
          (Finset.sum_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
    _ = ∑ k, Complex.normSq (c k) := by
        rw [mul_one]; congr 1; ext k
        exact (Complex.normSq_eq_norm_sq _).symm

-- Cauchy-Schwarz + partial sum bound for mapTensorId entries
/-- Per-entry Cauchy-Schwarz bound for mapTensorId:
    ‖(mapTensorId Φ X)(q,p)‖² ≤ ∑_{i,j} normSq(Φ(E_{ij})(a,b))
    when ∑|X entries|² ≤ 1. -/
lemma mapTensorId_entry_bound {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * n))
    (hX : ∑ i : Fin (n * n), ∑ j : Fin (n * n), ‖X j i‖ ^ 2 ≤ 1)
    (p q : Fin (m * n)) :
    ‖mapTensorId Φ X q p‖ ^ 2 ≤
    ∑ i : Fin n, ∑ j : Fin n,
      Complex.normSq (Φ (Matrix.single i j 1)
        (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm p).1) := by
  -- Pin typeclass instances to avoid repeated synthesis
  letI : Fintype (Fin n × Fin n) := inferInstance
  letI : Fintype (Fin (n * n)) := inferInstance
  letI : Fintype (Fin (m * n)) := inferInstance
  simp only [mapTensorId, Matrix.of_apply]
  -- Partial sum bound for x entries
  set s' := (finProdFinEquiv.symm q).2
  set t' := (finProdFinEquiv.symm p).2
  have h_col_inj : Function.Injective
      (fun j : Fin n => finProdFinEquiv (j, t')) :=
    fun a₁ a₂ h => (Prod.mk.inj (finProdFinEquiv.injective h)).1
  have h_row_inj : Function.Injective
      (fun i : Fin n => finProdFinEquiv (i, s')) :=
    fun a₁ a₂ h => (Prod.mk.inj (finProdFinEquiv.injective h)).1
  have hX' : ∑ r : Fin (n * n), ∑ c : Fin (n * n),
      ‖X r c‖ ^ 2 ≤ 1 := by rw [Finset.sum_comm]; exact hX
  have hx_bound : ∑ k : Fin n × Fin n,
      ‖X (finProdFinEquiv (k.1, s'))
        (finProdFinEquiv (k.2, t'))‖ ^ 2 ≤ 1 := by
    simp_rw [Fintype.sum_prod_type]
    have h_inner : ∀ i : Fin n,
        ∑ j : Fin n, ‖X (finProdFinEquiv (i, s'))
          (finProdFinEquiv (j, t'))‖ ^ 2 ≤
        ∑ c : Fin (n * n),
          ‖X (finProdFinEquiv (i, s')) c‖ ^ 2 := by
      intro i
      have key : ∑ c ∈ Finset.univ.map ⟨_, h_col_inj⟩,
          ‖X (finProdFinEquiv (i, s')) c‖ ^ 2 ≤
          ∑ c, ‖X (finProdFinEquiv (i, s')) c‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun c => pow_nonneg (norm_nonneg _) _)
      rwa [Finset.sum_map] at key
    have h_outer : ∑ i : Fin n,
        ∑ c, ‖X (finProdFinEquiv (i, s')) c‖ ^ 2 ≤
        ∑ r : Fin (n * n), ∑ c, ‖X r c‖ ^ 2 := by
      have key : ∑ r ∈ Finset.univ.map ⟨_, h_row_inj⟩,
          (∑ c, ‖X r c‖ ^ 2) ≤ ∑ r, ∑ c, ‖X r c‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun r =>
          Finset.sum_nonneg fun c _ =>
            pow_nonneg (norm_nonneg _) _)
      rwa [Finset.sum_map] at key
    calc _ ≤ ∑ i : Fin n,
          ∑ c, ‖X (finProdFinEquiv (i, s')) c‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => h_inner i
      _ ≤ ∑ r, ∑ c, ‖X r c‖ ^ 2 := h_outer
      _ ≤ 1 := hX'
  -- Apply CS lemma (flattened over Fin n × Fin n)
  have := norm_sq_sum_mul_le
    (fun k : Fin n × Fin n => Φ (Matrix.single k.1 k.2 1)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm p).1)
    (fun k => X (finProdFinEquiv (k.1, s'))
      (finProdFinEquiv (k.2, t')))
    hx_bound
  simp_rw [Fintype.sum_prod_type] at this
  exact this

/-- Reindex helper: summing a function of `(finProdFinEquiv.symm q).1` and
    `(finProdFinEquiv.symm p).1` over `Fin (m * n)` gives `n * n` times the
    sum over `Fin m`. -/
private lemma sum_reindex_bound {n m : ℕ}
    (f : Fin m → Fin m → ℝ) :
    ∑ p : Fin (m * n), ∑ q : Fin (m * n),
      f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm p).1 =
    ↑(n * n) * ∑ a : Fin m, ∑ b : Fin m, f b a := by
  -- Reindex both sums from Fin(m*n) to Fin m × Fin n
  conv_lhs =>
    arg 2; ext p
    rw [show ∑ q : Fin (m * n), f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm p).1 =
        ∑ r : Fin m × Fin n, f r.1 (finProdFinEquiv.symm p).1 from
        (Fintype.sum_equiv finProdFinEquiv _ _ (fun r => by simp)).symm]
  rw [show ∑ p : Fin (m * n),
      (∑ r : Fin m × Fin n, f r.1 (finProdFinEquiv.symm p).1) =
      ∑ s : Fin m × Fin n,
      (∑ r : Fin m × Fin n, f r.1 s.1) from
      (Fintype.sum_equiv finProdFinEquiv _ _ (fun s => by simp)).symm]
  -- Decompose product sums
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  -- Sum over unused Fin n indices gives factor of n each time
  conv_lhs =>
    arg 2; ext a; arg 2; ext _s; arg 2; ext b
    rw [show ∀ (c : ℝ), ∑ _ : Fin n, c = n * c from fun c => by
      simp [Finset.sum_const, nsmul_eq_mul]]
  conv_lhs =>
    arg 2; ext a
    rw [show ∀ (c : ℝ), ∑ _ : Fin n, c = n * c from fun c => by
      simp [Finset.sum_const, nsmul_eq_mul]]
  simp_rw [← Finset.mul_sum]
  push_cast [Nat.cast_mul]
  ring

/-- Frobenius norm² of mapTensorId Φ X is bounded by n² * C_Φ
    when Frobenius norm² of X is ≤ 1. -/
lemma mapTensorId_frobenius_bound {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * n))
    (hX : ∑ i : Fin (n * n), ∑ j : Fin (n * n), ‖X j i‖ ^ 2 ≤ 1) :
    ∑ i : Fin (m * n), ∑ j : Fin (m * n), ‖mapTensorId Φ X j i‖ ^ 2 ≤
    ↑(n * n) * ∑ a : Fin m, ∑ b : Fin m, ∑ i : Fin n, ∑ j : Fin n,
      Complex.normSq (Φ (Matrix.single i j 1) a b) := by
  -- Set up the per-entry bound function
  set bound : Fin (m * n) → Fin (m * n) → ℝ := fun q p =>
    ∑ i : Fin n, ∑ j : Fin n,
      Complex.normSq (Φ (Matrix.single i j 1) (finProdFinEquiv.symm q).1
                                                (finProdFinEquiv.symm p).1)
  -- Step 1: Bound each entry using the standalone helper
  have h_entry_bound : ∀ p q : Fin (m * n),
      ‖mapTensorId Φ X q p‖ ^ 2 ≤ bound q p := by
    intro p q; exact mapTensorId_entry_bound Φ X hX p q
  -- Step 2: Sum the bounds
  calc ∑ p, ∑ q, ‖mapTensorId Φ X q p‖ ^ 2
      ≤ ∑ p, ∑ q, bound q p := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        exact h_entry_bound p q
    _ ≤ ↑(n * n) * ∑ a, ∑ b, ∑ i, ∑ j, Complex.normSq (Φ (single i j 1) a b) := by
        -- Unfold bound and apply the reindex lemma
        show ∑ p, ∑ q, bound q p ≤ _
        simp only [bound]
        -- Use the reindex helper to turn ∑_{p,q : Fin(m*n)} into n² * ∑_{a,b : Fin m}
        rw [sum_reindex_bound (n := n) (m := m)
          (fun a b => ∑ i : Fin n, ∑ j : Fin n,
            Complex.normSq (Φ (single i j 1) a b))]
        -- Now: n*n * ∑_a ∑_b ∑_i ∑_j normSq(Φ(E_{ij})(b, a)) ≤
        --      n*n * ∑_a ∑_b ∑_i ∑_j normSq(Φ(E_{ij})(a, b))
        -- Swap sum order: ∑_a ∑_b f(b,a) = ∑_a ∑_b f(a,b)
        apply le_of_eq
        congr 1
        rw [Finset.sum_comm]

/-- The diamond norm set is bounded above. -/
lemma diamondNorm_bddAbove {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Φ : Op n →ₗ[ℂ] Op m) :
    BddAbove (setOf fun t : ℝ => ∃ X : Op (n * n), traceNorm X ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X)) := by
  -- Upper bound: √(m*n) * √(n² * C_Φ) where C_Φ = Frobenius norm² of Φ's basis images
  set C_Φ := ∑ a : Fin m, ∑ b : Fin m, ∑ i : Fin n, ∑ j : Fin n,
    Complex.normSq (Φ (Matrix.single i j 1) a b) with hC_Φ_def
  use Real.sqrt (m * n : ℕ) * Real.sqrt ((n * n : ℕ) * C_Φ)
  intro t ⟨X, hX, ht⟩
  rw [ht]
  -- Step 1: traceNorm ≤ √dim * √(Frobenius²)
  calc traceNorm (mapTensorId Φ X)
      ≤ Real.sqrt (m * n : ℕ) *
          Real.sqrt ((mapTensorId Φ X)† * mapTensorId Φ X).trace.re :=
        traceNorm_le_sqrt_dim_mul_sqrt_frobenius _
    _ ≤ Real.sqrt (m * n : ℕ) * Real.sqrt (↑(n * n) * C_Φ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Real.sqrt_le_sqrt
        -- Step 2: Frobenius² = ∑ |entries|² ≤ n² * C_Φ
        -- Use trace_conjTranspose_mul_self_re to expand
        rw [trace_conjTranspose_mul_self_re]
        -- Need: ∑ i j, ‖(mapTensorId Φ X) j i‖² ≤ n² * C_Φ
        -- Each entry is a bilinear form ∑_ij c_{ij} * x_{..}
        -- Use Cauchy-Schwarz: |∑ c_k x_k|² ≤ (∑|c_k|²)(∑|x_k|²)
        -- and ∑|x_k|² ≤ Frobenius²(X) ≤ 1
        -- First get the Frobenius bound on X
        have hX_frob : (X† * X).trace.re ≤ 1 :=
          frobenius_sq_le_one_of_traceNorm_le_one X hX
        -- Expand using trace_conjTranspose_mul_self_re
        have hX_entry_sum : ∑ i : Fin (n * n), ∑ j : Fin (n * n),
            ‖X j i‖ ^ 2 ≤ 1 := by
          rw [← trace_conjTranspose_mul_self_re]; exact hX_frob
        -- Bound Frobenius² of mapTensorId output
        -- Use the standalone helper lemma
        exact mapTensorId_frobenius_bound Φ X hX_entry_sum

/-! ## The two directions of the defining supremum -/

/-- **Upper bound on a diamond norm from a uniform bound on the defining supremum.** The set the
supremum is taken over is nonempty (it contains `0`), so `csSup_le` applies. -/
lemma diamondNorm_le_of_forall {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (h : ∀ X : Op (n * n), traceNorm X ≤ 1 → traceNorm (mapTensorId Φ X) ≤ B) :
    diamondNorm Φ ≤ B := by
  unfold diamondNorm
  refine csSup_le ⟨0, 0, ?_, ?_⟩ ?_
  · rw [traceNorm_zero]; exact zero_le_one
  · rw [mapTensorId_zero, traceNorm_zero]
  · rintro t ⟨X, hX, rfl⟩
    exact h X hX

/-- **Every admissible input of the defining supremum is bounded by the diamond norm**, at the
ancilla the definition pins. The free-ancilla versions are
`traceNorm_mapTensorId_le_diamondNorm` and
`traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving`. -/
lemma traceNorm_mapTensorId_le_diamondNorm_pinned {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * n)) (hX : traceNorm X ≤ 1) :
    traceNorm (mapTensorId Φ X) ≤ diamondNorm Φ := by
  unfold diamondNorm
  exact le_csSup (diamondNorm_bddAbove Φ) ⟨X, hX, rfl⟩

/-- The zero map has zero diamond norm. -/
@[simp] theorem diamondNorm_zero {n m : ℕ} [NeZero n] [NeZero m] :
    diamondNorm (0 : Op n →ₗ[ℂ] Op m) = 0 := by
  refine le_antisymm (diamondNorm_le_of_forall _ _ fun X _ => ?_) (diamondNorm_nonneg _)
  rw [mapTensorId_zero_map, traceNorm_zero]

/-- The diamond norm satisfies the triangle inequality. -/
theorem diamondNorm_add_le {n m : ℕ} [NeZero n] [NeZero m]
    (Φ Ψ : Op n →ₗ[ℂ] Op m) :
    diamondNorm (Φ + Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := by
  refine diamondNorm_le_of_forall _ _ fun X hX => ?_
  rw [mapTensorId_linearMap_add]
  exact (traceNorm_add_le _ _).trans
    (add_le_add (traceNorm_mapTensorId_le_diamondNorm_pinned Φ X hX)
      (traceNorm_mapTensorId_le_diamondNorm_pinned Ψ X hX))

/-- Scalar multiplication scales the diamond norm by the complex norm of the scalar. -/
@[simp] theorem diamondNorm_smul {n m : ℕ} [NeZero n] [NeZero m]
    (c : ℂ) (Φ : Op n →ₗ[ℂ] Op m) :
    diamondNorm (c • Φ) = ‖c‖ * diamondNorm Φ := by
  unfold diamondNorm
  simp_rw [mapTensorId_linearMap_smul, TraceNormHoelder.traceNorm_smul_eq]
  change _ = ‖c‖ • (sSup _ : ℝ)
  rw [← Real.sSup_smul_of_nonneg (norm_nonneg c)]
  congr 1
  ext t
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨traceNorm (mapTensorId Φ X), ⟨X, hX, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨X, hX, rfl⟩, rfl⟩
    exact ⟨X, hX, rfl⟩

/-- Negation preserves the diamond norm. -/
@[simp] theorem diamondNorm_neg {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) : diamondNorm (-Φ) = diamondNorm Φ := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using diamondNorm_smul (-1) Φ

/-- The diamond norm of a difference is at most the sum of the diamond norms. -/
theorem diamondNorm_sub_le {n m : ℕ} [NeZero n] [NeZero m]
    (Φ Ψ : Op n →ₗ[ℂ] Op m) :
    diamondNorm (Φ - Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := by
  simpa only [sub_eq_add_neg, diamondNorm_neg] using diamondNorm_add_le Φ (-Ψ)

/-- The trace norm of Φ(ρ) on any fixed input is bounded by the diamond norm.

    For any linear map Φ and density operator ρ:
      ‖Φ(ρ)‖₁ ≤ ‖Φ‖_◇

    In plain language: evaluating a linear map on a single input can never
    exceed the worst-case (diamond norm) over all inputs with ancilla.

    **Proof strategy**: Embed ρ ↦ ρ ⊗ |0⟩⟨0| into Op(n*n), observe that
    (Φ ⊗ id)(ρ ⊗ |0⟩⟨0|) has the same singular values as Φ(ρ) (tensored
    with zeros), so ‖Φ(ρ)‖₁ = ‖(Φ ⊗ id)(ρ ⊗ |0⟩⟨0|)‖₁ ≤ ‖Φ‖_◇ since
    ‖ρ ⊗ |0⟩⟨0|‖₁ = ‖ρ‖₁ ≤ 1. -/
lemma diamondNorm_ge_traceNorm_apply {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (ρ : DensityOp n) :
    traceNorm (Φ ρ.toOp) ≤ diamondNorm Φ := by
  haveI hnn : NeZero (n * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos n) (NeZero.pos n))⟩
  haveI hmn : NeZero (m * n) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (NeZero.pos m) (NeZero.pos n))⟩
  -- Define X₀ = ρ ⊗ |0⟩⟨0|
  set E₀₀ : Op n := Matrix.single 0 0 1
  set X₀ : Op (n * n) := ρ.toOp ⊗ E₀₀
  -- X₀ is PSD (tensor of two PSD matrices)
  have hX₀_psd : X₀.PosSemidef := by
    have hρ_psd := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    have hE_psd := stdBasisProj_posSemidef (d := n)
    constructor
    · exact (hρ_psd.kronecker hE_psd).submatrix _|>.1
    · exact (hρ_psd.kronecker hE_psd).submatrix _|>.2
  -- traceNorm X₀ = trace(X₀).re = trace(ρ) * trace(E₀₀) = 1
  have hX₀_norm : traceNorm X₀ ≤ 1 := by
    rw [traceNorm_posSemidef_eq_trace X₀ hX₀_psd]
    rw [Op.trace_tensor, stdBasisProj_trace, mul_one, ρ.trace_one]
    simp
  -- mapTensorId Φ X₀ = (Φ ρ.toOp) ⊗ E₀₀
  have hOut : traceNorm (mapTensorId Φ X₀) = traceNorm (Φ ρ.toOp) := by
    rw [show X₀ = ρ.toOp ⊗ E₀₀ from rfl, mapTensorId_tensor]
    exact traceNorm_tensor_stdBasisProj (Φ ρ.toOp)
  -- Apply le_csSup
  unfold diamondNorm
  apply le_csSup
  · exact diamondNorm_bddAbove Φ
  · exact ⟨X₀, hX₀_norm, hOut.symm⟩

end Quantum.Channels
