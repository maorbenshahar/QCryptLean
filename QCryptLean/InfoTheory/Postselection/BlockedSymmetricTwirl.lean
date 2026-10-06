import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.InfoTheory.Postselection.Mixture
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.InfoTheory.Postselection.FixedMarginalMomentMeasures
import QCryptLean.Quantum.Symmetry.FiniteGroupTensorCommutant
import QCryptLean.Quantum.Symmetry.ProjectedSymmetricSubspace
import QCryptLean.Quantum.TensorProducts.FixedMarginalDomination
import QCryptLean.InfoTheory.Postselection.GroupInvariantStates
import QCryptLean.InfoTheory.Postselection.GroupPurification
import QCryptLean.InfoTheory.Postselection.BlockedGroupTwirl

/-!
# The blocked symmetric group twirl

The intersection of the blocked group-invariant subspace and the symmetric
subspace: the product of the blocked group twirl with the paired symmetric
projector. Its trace is the symmetric-power dimension of the one-round group
twirl, its Alice marginal is positive definite, and it commutes with the
normalized marginal — the properties that let the fixed-marginal de Finetti
reduction normalize it into a reference state.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ### The blocked symmetric twirl -/

/-- The symmetric tensor power of the group-twirl range has dimension
`deFinettiPrefactor x n`, where `x` is the trace of the one-round twirl.
Regrouping preserves trace, and the dimension is the symmetric-power dimension
of an orthogonal projection of rank `x`. -/
lemma groupPairedTwirlProjector_mul_symmetricProjectorPaired_trace {G : Type*} [Group G]
    [Fintype G] {d n x : ℕ} [NeZero d] [NeZero n] (π : G → Op d) (hπ : IsUnitaryRep π)
    (hx : (groupTwirlProjector π).trace = (x : ℂ)) :
    (groupPairedTwirlProjector n π * symmetricProjectorPaired d n).trace =
      (deFinettiPrefactor x n : ℂ) := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  haveI : NeZero x := ⟨Nat.cast_ne_zero.mp (by
    rw [← hx]
    exact groupTwirlProjector_trace_ne_zero π hπ)⟩
  have hflat : Matrix.reindex (interleavingEquivGen d d n) (interleavingEquivGen d d n)
      (symmetricProjectorPaired d n) = symmetricProjector (d * d) n := by
    rw [symmetricProjectorPaired_eq_gen]
    exact interleavingEquivGen_conjugates_projector
  have hsym : symmetricProjectorPaired d n =
      Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
        (symmetricProjector (d * d) n) := by
    rw [← hflat, Matrix.reindex_symm_reindex]
  rw [groupPairedTwirlProjector, hsym, ← Matrix.reindex_mul, Matrix.trace_reindex_self]
  obtain ⟨hherm, hidem⟩ := groupTwirlProjector_isOrthogonalProjection π hπ
  exact trace_tensorPow_projection_mul_symmetricProjector _ hherm hidem hx

/-- An operator sandwiched by an idempotent `P` is fixed by left and right multiplication
    by `P`. -/
lemma idempotent_sandwich_left_right {N : ℕ} {P X : Op N}
    (hP : P * P = P) (hX : P * X * P = X) : P * X = X ∧ X * P = X := by
  refine ⟨?_, ?_⟩
  · calc P * X = P * (P * X * P) := by rw [hX]
      _ = (P * P) * X * P := by rw [← mul_assoc P (P * X) P, mul_assoc P P X]
      _ = P * X * P := by rw [hP]
      _ = X := hX
  · calc X * P = P * X * P * P := by rw [hX]
      _ = P * X * (P * P) := by rw [mul_assoc]
      _ = P * X * P := by rw [hP]
      _ = X := hX

/-- The intersection of the blocked group-invariant and symmetric subspaces
is represented by the product of their commuting orthogonal projections. -/
lemma groupBlockedSymmetricTwirl_isOrthogonalProjection
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    let Q := groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n
    Q.IsHermitian ∧ Q * Q = Q := by
  haveI : NeZero (dA * dB ^ 2) := ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  obtain ⟨hG, hGG⟩ := groupBlockedTwirlProjector_isOrthogonalProjection
    (n := n) πA hπA πB hπB
  have hP := symmetricProjectorPairedGen_isHermitian dA (dA * dB ^ 2) n
  have hPP := (symmetricProjectorPairedGen_is_projector dA (dA * dB ^ 2) n).1
  have hcomm := groupBlockedTwirlProjector_commute_symmetricProjectorPairedGen (n := n) πA πB
  exact ⟨(hG.commute_iff hP).mp hcomm, IsIdempotentElem.mul_of_commute hcomm hGG hPP⟩

/-- Joint group and permutation support transports to the blocked intersection
projection. -/
lemma groupBlockedSymmetricTwirl_mul_reindex_of_supported
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (X : Op ((dA * dB) ^ n * (dA * dB) ^ n))
    (hG : groupPairedTwirlProjector n (prodRep πA πB) * X *
      groupPairedTwirlProjector n (prodRep πA πB) = X)
    (hP : symmetricProjectorPaired (dA * dB) n * X *
      symmetricProjectorPaired (dA * dB) n = X) :
    let e := pairedToBlockedEquiv dA dB n
    (groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n) *
      Matrix.reindex e e X = Matrix.reindex e e X := by
  haveI : NeZero (dA * dB ^ 2) := ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  intro e
  have hG' := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hG
  simp only [map_mul, Matrix.coe_reindexAlgEquiv] at hG'
  have hGl := (idempotent_sandwich_left_right
    (groupBlockedTwirlProjector_isOrthogonalProjection (n := n) πA hπA πB hπB).2 hG').1
  have hPl := (idempotent_sandwich_left_right
    (symmetricProjectorPairedGen_is_projector dA (dA * dB ^ 2) n).1
    (pairedToBlockedEquiv_transports_support dA dB n X hP)).1
  rw [mul_assoc, hPl]
  exact hGl

/-- The canonical entangled seed is fixed by the paired group twirl. -/
lemma groupPairedTwirlProjector_mul_maxEntangledOp
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} [NeZero d] [NeZero n]
    (π : G → Op d) (hπ : IsUnitaryRep π) :
    groupPairedTwirlProjector n π * maxEntangledOp (d ^ n) = maxEntangledOp (d ^ n) := by
  have hfix (v : Fin n → G) :
      Op.tensor (tensorFamily fun k => π (v k)) (tensorFamily fun k => entryConj (π (v k))) *
        maxEntangledOp (d ^ n) = maxEntangledOp (d ^ n) := by
    have htr : (tensorFamily fun k => entryConj (π (v k)))ᵀ =
        (tensorFamily fun k => π (v k))ᴴ := by
      ext i j
      simp [entryConj, Matrix.transpose_apply, tensorFamily_apply, Matrix.conjTranspose_apply]
    rw [maxEntangledOp_tensor_ricochet, htr,
      tensorFamily_mul_conjTranspose_self (fun k => mul_eq_one_comm.mpr (hπ.2 (v k))),
      Op.tensor_one, one_mul]
  rw [groupPairedTwirlProjector_eq_sum, smul_mul_assoc, Finset.sum_mul]
  simp [hfix, ← Nat.cast_smul_eq_nsmul ℂ]

/-- The blocked entangled seed lies in the group-symmetric projection range. -/
lemma groupBlockedSymmetricTwirl_mul_blockedEntangledSeed
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    (groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n) *
      blockedEntangledSeed dA dB n = blockedEntangledSeed dA dB n := by
  rw [mul_assoc, symmetricProjectorPairedGen_mul_blockedEntangledSeed,
    blockedEntangledSeed, groupBlockedTwirlProjector, mul_smul_comm, ← Matrix.reindex_mul,
    groupPairedTwirlProjector_mul_maxEntangledOp _ (prodRep_isUnitaryRep πA hπA πB hπB)]

/-- The dimension of the blocked intersection projection is the symmetric-power
dimension of the one-round group-twirl range. -/
lemma groupBlockedSymmetricTwirl_trace
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n x : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (hx : (groupTwirlProjector (prodRep πA πB)).trace = (x : ℂ)) :
    (groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n).trace =
      (deFinettiPrefactor x n : ℂ) := by
  haveI : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  rw [groupBlockedTwirlProjector, ← pairedToBlockedEquiv_conjugates_projector,
    ← Matrix.reindex_mul, Matrix.trace_reindex_self]
  exact groupPairedTwirlProjector_mul_symmetricProjectorPaired_trace _
    (prodRep_isUnitaryRep πA hπA πB hπB) hx

/-- The symmetric group-twirl projection has positive definite Alice marginal:
its range contains a purification of the maximally mixed state. -/
lemma groupBlockedSymmetricTwirl_partialTraceB_posDef
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    (partialTraceB (groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n)).PosDef := by
  haveI : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) := ⟨pow_ne_zero n (NeZero.ne (dA * dB))⟩
  haveI : NeZero (dA * dB ^ 2) := ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  let ρ := DensityOp.maxMixed ((dA * dB) ^ n)
  have hperm : IsPermutationInvariant ρ := by
    apply (isPermutationInvariant_iff_commutes ρ).mpr
    intro σ
    simp only [ρ, DensityOp.maxMixed, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  have hiid : IsIIDGroupInvariant (prodRep πA πB) ρ := by
    intro v
    have hunit := prodRep_isUnitaryRep πA hπA πB hπB
    have hU : tensorFamily (fun k => prodRep πA πB (v k)) *
        (tensorFamily (fun k => prodRep πA πB (v k)))ᴴ = 1 :=
      tensorFamily_mul_conjTranspose_self fun k => by
        rw [← hunit.inv, ← hunit.1, mul_inv_cancel, hunit.one]
    simpa only [ρ, DensityOp.maxMixed, Matrix.mul_smul, Matrix.smul_mul, mul_one] using
      congrArg (fun M => (1 / (((dA * dB) ^ n : ℕ) : ℂ)) • M) hU
  obtain ⟨Ψ, _, hΨmarg, hΨG, hΨP⟩ :=
    groupPurification (prodRep πA πB) (prodRep_isUnitaryRep πA hπA πB hπB) ρ hperm hiid
  let e := pairedToBlockedEquiv dA dB n
  let Ψb := densityOp_reindex e Ψ
  let PG := groupBlockedTwirlProjector (n := n) πA πB
  let P := symmetricProjectorPairedGen dA (dA * dB ^ 2) n
  obtain ⟨hGherm, hGG⟩ := groupBlockedTwirlProjector_isOrthogonalProjection (n := n) πA hπA πB hπB
  have hPherm := symmetricProjectorPairedGen_isHermitian dA (dA * dB ^ 2) n
  have hPP := (symmetricProjectorPairedGen_is_projector dA (dA * dB ^ 2) n).1
  have hcomm := groupBlockedTwirlProjector_commute_symmetricProjectorPairedGen (n := n) πA πB
  have hPG : PG * Ψb.toOp = Ψb.toOp := by
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hΨG
    simp only [map_mul, Matrix.coe_reindexAlgEquiv] at h
    exact (idempotent_sandwich_left_right hGG h).1
  have hP : P * Ψb.toOp = Ψb.toOp :=
    (idempotent_sandwich_left_right hPP
      (pairedToBlockedEquiv_transports_support dA dB n Ψ.toOp hΨP)).1
  apply partialTraceB_projection_posDef_of_supported (PG * P) Ψb
    ((hGherm.commute_iff hPherm).mp hcomm)
    (IsIdempotentElem.mul_of_commute hcomm hGG hPP)
    (by rw [mul_assoc, hP, hPG])
  change (partialTraceB (Matrix.reindex e e Ψ.toOp)).PosDef
  rw [pairedToBlockedEquiv_partialTraceB_eq_roundGroup, hΨmarg]
  apply partialTraceB_posDef
  change (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
    ((1 / (((dA * dB) ^ n : ℕ) : ℂ)) • (1 : Op ((dA * dB) ^ n)))).PosDef
  rw [Matrix.reindex_smul, show Matrix.reindex (roundGroupEquiv dA dB n)
    (roundGroupEquiv dA dB n) (1 : Op ((dA * dB) ^ n)) = 1 from
      (Matrix.reindexAlgEquiv ℂ ℂ (roundGroupEquiv dA dB n)).map_one]
  apply Matrix.PosDef.one.smul
  have hpos : (0 : ℝ) < 1 / (((dA * dB) ^ n : ℕ) : ℝ) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero ((dA * dB) ^ n)))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using
    Complex.zero_lt_real.mpr hpos

/-- The Alice marginal of the symmetric group-twirl projection, lifted back to
the full register, commutes with the projection. -/
lemma groupBlockedSymmetricTwirl_partialTraceB_commute
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    let Q := groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n
    Commute (Op.tensor (partialTraceB Q) (1 : Op ((dA * dB ^ 2) ^ n))) Q := by
  haveI : NeZero (dA * dB ^ 2) := ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  intro Q
  obtain ⟨hGherm, hGG⟩ := groupBlockedTwirlProjector_isOrthogonalProjection (n := n) πA hπA πB hπB
  have hPherm := symmetricProjectorPairedGen_isHermitian dA (dA * dB ^ 2) n
  have hPP := (symmetricProjectorPairedGen_is_projector dA (dA * dB ^ 2) n).1
  have hcomm := groupBlockedTwirlProjector_commute_symmetricProjectorPairedGen (n := n) πA πB
  have hQherm : Q.IsHermitian := (hGherm.commute_iff hPherm).mp hcomm
  have hGQ : groupBlockedTwirlProjector πA πB * Q = Q := by
    dsimp only [Q]
    rw [← mul_assoc, hGG]
  have hPQ : symmetricProjectorPairedGen dA (dA * dB ^ 2) n * Q = Q := by
    dsimp only [Q]
    rw [← mul_assoc, ← hcomm.eq, mul_assoc, hPP]
  apply Commute.mul_right
  · exact partialTraceB_groupBlockedTwirl_supported_commute πA hπA πB hπB Q hQherm hGQ
  · exact tensor_one_commute_symmetricProjectorPairedGen (partialTraceB Q)
      (partialTraceB_symmetric_supported_commute Q hQherm hPQ)

/-- Restricted reference Haar measure realizes the normalized group-symmetric projection. -/
lemma groupBlockedSymmetricTwirl_eq_referenceHaar
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (κ : Op (dA ^ n)) (hκ : κ.PosDef)
    (hκinv : κ⁻¹ = partialTraceB (groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n)) :
    referenceTwirl (unitaryCentralizerHaar (groupReferenceRep πA hπA πB hπB))
      (unitaryCentralizerTensorPower (groupReferenceRep πA hπA πB hπB) n)
      (blockedEntangledSeed dA dB n) =
      Op.tensor (CFC.sqrt κ) (1 : Op ((dA * dB ^ 2) ^ n)) *
        (groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n) *
        Op.tensor (CFC.sqrt κ) (1 : Op ((dA * dB ^ 2) ^ n)) := by
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  letI := hκ.isUnit.invertible
  let Q := groupBlockedTwirlProjector (n := n) πA πB *
    symmetricProjectorPairedGen dA (dA * dB ^ 2) n
  have hQ : Q.IsHermitian :=
    (groupBlockedSymmetricTwirl_isOrthogonalProjection πA hπA πB hπB).1
  have hseed := groupBlockedSymmetricTwirl_mul_blockedEntangledSeed πA hπA πB hπB (n := n)
  change Q * blockedEntangledSeed dA dB n = blockedEntangledSeed dA dB n at hseed
  have hright : blockedEntangledSeed dA dB n * Q = blockedEntangledSeed dA dB n := by
    simpa only [Matrix.conjTranspose_mul, hQ.eq,
      (blockedEntangledSeed_posSemidef dA dB n).isHermitian.eq] using
      congrArg Matrix.conjTranspose hseed
  have hΩcomm := groupBlockedSymmetricTwirl_partialTraceB_commute πA hπA πB hπB (n := n)
  dsimp only at hΩcomm
  rw [← hκinv] at hΩcomm
  have hκcomm := tensor_inv_one_commute hκ.inv.isUnit hΩcomm
  rw [Matrix.inv_inv_of_invertible] at hκcomm
  apply referenceTwirl_eq_sqrt_sandwich _ _ _ Q
    (referenceTwirl_integrable _ _ (continuous_unitaryCentralizerTensorPower _ n) _)
    hQ hright _ (groupBlockedSymmetric_hasLocalCommutant πA hπA πB hπB)
    κ hκ hκinv hκcomm (blockedEntangledSeed_partialTraceB dA dB n)
  intro U
  exact (unitaryCentralizer_commute_groupBlockedTwirlProjector πA hπA πB hπB U).mul_right
    (tensor_one_tensorPow_commute_symmetricProjectorPairedGen (U.val : Op (dA * dB ^ 2)))

/-! ### Normalizing the blocked twirl into a group-invariant reference -/

/-- The partial trace of the symmetric group-twirl projection has a positive
invertible inverse `κ`. Its lift to the full register commutes with the projection.
Conjugation by `√κ ⊗ 1` normalizes the Alice marginal of the projection. -/
theorem exists_flatten_groupSymmetricTwirl
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    ∃ κ : Op (dA ^ n),
      κ.PosSemidef ∧
      IsUnit κ ∧
      Commute (Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)))
        (groupBlockedTwirlProjector πA πB *
          symmetricProjectorPairedGen dA (dA * dB ^ 2) n) ∧
      κ⁻¹ = partialTraceB (groupBlockedTwirlProjector πA πB *
        symmetricProjectorPairedGen dA (dA * dB ^ 2) n) := by
  let Ω := partialTraceB (groupBlockedTwirlProjector (n := n) πA πB *
    symmetricProjectorPairedGen dA (dA * dB ^ 2) n)
  have hΩ : Ω.PosDef := groupBlockedSymmetricTwirl_partialTraceB_posDef πA hπA πB hπB
  refine ⟨Ω⁻¹, hΩ.inv.posSemidef, hΩ.inv.isUnit, ?_, ?_⟩
  · exact tensor_inv_one_commute hΩ.isUnit
      (groupBlockedSymmetricTwirl_partialTraceB_commute πA hπA πB hπB)
  · letI := hΩ.isUnit.invertible
    exact Matrix.inv_inv_of_invertible Ω

/-- The locally normalized group-symmetric reference remains supported on the
blocked group-twirl range. -/
lemma groupBlockedReference_group_supported
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n)
    (κ : Op (dA ^ n)) (hκ : κ.PosDef)
    (hκinv : κ⁻¹ = partialTraceB (groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n)) :
    let S := Op.tensor (CFC.sqrt (σA.tensorPowGen n).toOp) (1 : Op ((dA * dB ^ 2) ^ n))
    let W := Op.tensor (CFC.sqrt κ) (1 : Op ((dA * dB ^ 2) ^ n))
    let T := S * (W * (groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n) * W) * S
    groupBlockedTwirlProjector πA πB * T = T := by
  haveI : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  letI := hκ.isUnit.invertible
  let G := groupBlockedTwirlProjector (n := n) πA πB
  let Q := G * symmetricProjectorPairedGen dA (dA * dB ^ 2) n
  let A := (σA.tensorPowGen n).toOp
  intro S W T
  have hA : A.PosSemidef := posSemidefOp_implies_mathlib (σA.tensorPowGen n).toPosSemidefOp
  have hQ : Q.IsHermitian :=
    (groupBlockedSymmetricTwirl_isOrthogonalProjection (n := n) πA hπA πB hπB).1
  have hGQ : G * Q = Q := by
    dsimp only [Q]
    rw [← mul_assoc, (groupBlockedTwirlProjector_isOrthogonalProjection
      (n := n) πA hπA πB hπB).2]
  have hΩcomm := partialTraceB_groupBlockedTwirl_supported_commute πA hπA πB hπB Q hQ hGQ
  rw [← hκinv] at hΩcomm
  have hκcomm := tensor_inv_one_commute hκ.inv.isUnit hΩcomm
  rw [Matrix.inv_inv_of_invertible] at hκcomm
  have hS : Commute S G := tensor_sqrt_one_commute hA
    (sigmaA_tensorPowGen_commute_groupBlockedTwirlProjector πA hπA πB hπB σA ρ hiid hmarg)
  have hW : Commute W G := tensor_sqrt_one_commute hκ.posSemidef hκcomm
  calc G * T = (G * (S * W)) * Q * (W * S) := by simp only [T, Q, G, mul_assoc]
    _ = (S * W) * (G * Q) * (W * S) := by
      rw [← (hS.mul_left hW).eq, mul_assoc (S * W) G Q]
    _ = T := by rw [hGQ]; simp only [T, Q, G, mul_assoc]

/-- Tracing a filtered centralizer orbit yields a group-invariant one-round state. -/
lemma groupReferenceOrbit_partialTrace_isInvariant
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Finite G_A] [Finite G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n)
    (U : unitaryCentralizer (groupReferenceRep πA hπA πB hπB))
    (τ : DensityOp (dA * (dA * dB ^ 2)))
    (hτ : τ.toOp = Op.tensor (CFC.sqrt σA.toOp) (U.val : Op (dA * dB ^ 2)) *
      blockedEntangledSeedRound dA dB *
      (Op.tensor (CFC.sqrt σA.toOp) (U.val : Op (dA * dB ^ 2)))ᴴ) :
    IsGroupInvariantState (prodRep πA πB)
      (densityOp_reindex
        (finCongr (show dA * (dA * dB ^ 2) = (dA * dB) * (dA * dB) by ring)) τ).partialTraceB := by
  letI := Fintype.ofFinite G_A
  letI := Fintype.ofFinite G_B
  haveI : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  let G := groupBlockedTwirlProjector (n := n) πA πB
  let S := Op.tensor (CFC.sqrt (σA.tensorPowGen n).toOp) (1 : Op ((dA * dB ^ 2) ^ n))
  let K := Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U.val : Op (dA * dB ^ 2)) n)
  let Z := Matrix.reindex (interleavingEquivGen dA (dA * dB ^ 2) n).symm
    (interleavingEquivGen dA (dA * dB ^ 2) n).symm (τ.tensorPowGen n).toOp
  have hZ : Z = S * (K * blockedEntangledSeed dA dB n * Kᴴ) * Sᴴ := by
    dsimp only [Z, S, K]
    rw [DensityOp.tensorPowGen_toOp, hτ, tensorPow_conjugation_interleaving,
      DensityOp.tensorPowGen_toOp, sqrt_tensorPow σA.toOp
        (posSemidefOp_implies_mathlib σA.toPosSemidefOp), blockedEntangledSeed_eq_tensorPow]
  have hS : Commute S G := tensor_sqrt_one_commute
    (posSemidefOp_implies_mathlib (σA.tensorPowGen n).toPosSemidefOp)
    (sigmaA_tensorPowGen_commute_groupBlockedTwirlProjector πA hπA πB hπB σA ρ hiid hmarg)
  have hK : Commute K G := unitaryCentralizer_commute_groupBlockedTwirlProjector πA hπA πB hπB U
  have hGT : G * blockedEntangledSeed dA dB n = blockedEntangledSeed dA dB n := by
    dsimp only [G]
    rw [blockedEntangledSeed, groupBlockedTwirlProjector, mul_smul_comm, ← Matrix.reindex_mul,
      groupPairedTwirlProjector_mul_maxEntangledOp _ (prodRep_isUnitaryRep πA hπA πB hπB)]
  have hGZ : G * Z = Z := by
    rw [hZ]
    simp only [mul_assoc]
    rw [hS.symm.left_comm, hK.symm.left_comm, ← mul_assoc G, hGT]
  let e := pairedToBlockedEquiv dA dB n
  let Y := Matrix.reindex e.symm e.symm Z
  have hY : Y.IsHermitian := by
    have hτn := posSemidefOp_implies_mathlib (τ.tensorPowGen n).toPosSemidefOp
    exact ((hτn.reindex _).reindex _).isHermitian
  have hGY : groupPairedTwirlProjector n (prodRep πA πB) * Y = Y := by
    have h := congrArg (Matrix.reindex e.symm e.symm) hGZ
    simpa only [G, e, Y, groupBlockedTwirlProjector, Matrix.reindex_mul,
      Matrix.reindex_symm_reindex] using h
  apply (isIIDGroupInvariant_tensorPowGen_iff (n := n) _
    (prodRep_isUnitaryRep πA hπA πB hπB) _).mp
  intro v
  rw [← partialTraceB_pairedToBlocked_tensorPow τ]
  exact partialTraceB_groupPairedTwirl_supported_invariant _
    (prodRep_isUnitaryRep πA hπA πB hπB) Y hY hGY v

section MomentMeasures

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The locally normalized group-symmetric reference is a mixture of tensor powers
of group-invariant extensions of the prescribed Alice marginal. -/
lemma exists_groupMeasure_of_blockedReference
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero (dA * dB)] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n)
    (κ : Op (dA ^ n)) (hκ : κ.PosDef)
    (hκinv : κ⁻¹ = partialTraceB (groupBlockedTwirlProjector πA πB *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n)) :
    let S := Op.tensor (CFC.sqrt (σA.tensorPowGen n).toOp) (1 : Op ((dA * dB ^ 2) ^ n))
    let W := Op.tensor (CFC.sqrt κ) (1 : Op ((dA * dB ^ 2) ^ n))
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      IsGroupInvariantMeasure (prodRep πA πB) μ ∧
      partialTraceB (Matrix.reindex (pairedToBlockedEquiv dA dB n).symm
        (pairedToBlockedEquiv dA dB n).symm
        (S * (W * (groupBlockedTwirlProjector πA πB *
          symmetricProjectorPairedGen dA (dA * dB ^ 2) n) * W) * S))
        = (deFinettiMixtureFixedMarginal dA dB n μ).toOp := by
  classical
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  let r := groupReferenceRep πA hπA πB hπB
  let ν := unitaryCentralizerHaar r
  let U : unitaryCentralizer r → Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ := Subtype.val
  have hU : Continuous U := continuous_subtype_val
  obtain ⟨f, hf, hop, hfA⟩ := exists_fixedMarginal_referenceOrbit σA
    (blockedEntangledSeedRound dA dB) (blockedEntangledSeedRound_posSemidef dA dB)
    (blockedEntangledSeedRound_partialTraceB dA dB) U hU
  let e := finCongr (show dA * (dA * dB ^ 2) = (dA * dB) * (dA * dB) by ring)
  let g x := (densityOp_reindex e (f x)).partialTraceB
  have hg : Continuous g := partialTraceB_continuous_general.comp
    ((continuous_densityOp_reindex e).comp hf)
  let μ := densityMeasureOfFamily ν g hg.measurable
  intro S W
  refine ⟨μ, densityMeasureOfFamily_isFixedMarginal ν g hg.measurable σA ?_, ?_, ?_⟩
  · exact ae_of_all _ fun x => (partialTraceB_pairedReference_marginal (f x)).trans (hfA x)
  · apply (densityMeasureOfFamily_ae_iff ν g hg.measurable _
      (isClosed_isGroupInvariantState (prodRep πA πB)).measurableSet).mpr
    exact ae_of_all _ fun x => groupReferenceOrbit_partialTrace_isInvariant
      πA hπA πB hπB σA ρ hiid hmarg x (f x) (hop x)
  · have hS : S = Op.tensor (Op.tensorPow (CFC.sqrt σA.toOp) n)
        (1 : Op ((dA * dB ^ 2) ^ n)) := by
      dsimp only [S]
      rw [DensityOp.tensorPowGen_toOp, sqrt_tensorPow _ hσA.posSemidef]
    have hSherm : Sᴴ = S := by
      dsimp only [S]
      rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one,
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (σA.tensorPowGen n).toOp)).isHermitian.eq]
    have hmoment := referenceOrbit_tensorPower_moment (n := n) ν
      (CFC.sqrt σA.toOp) (blockedEntangledSeedRound dA dB) U hU f hf.measurable hop
    dsimp only at hmoment
    rw [← hS, ← blockedEntangledSeed_eq_tensorPow] at hmoment
    change Matrix.reindex (interleavingEquivGen dA (dA * dB ^ 2) n).symm
      (interleavingEquivGen dA (dA * dB ^ 2) n).symm
      (∫ x, ((f x).tensorPowGen n).toOp ∂ν) =
      S * referenceTwirl ν (unitaryCentralizerTensorPower r n)
        (blockedEntangledSeed dA dB n) * Sᴴ at hmoment
    rw [groupBlockedSymmetricTwirl_eq_referenceHaar πA hπA πB hπB κ hκ hκinv,
      hSherm] at hmoment
    rw [← hmoment, partialTraceB_pairedToBlocked_family_moment ν f hf.measurable]
    exact (integralTensorPower_densityMeasureOfFamily (n := n) ν g hg.measurable).symm

end MomentMeasures

end InfoTheory.Postselection

end
