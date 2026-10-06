import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.InfoTheory.DeFinetti.IntegralPurification
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Instrument
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyAcceptSplit
import QCryptLean.Quantum.Metrics.PurificationUhlmannUniqueness
import QCryptLean.Math.LinearAlgebra.IsometricEncoding

/-!
# Purification factorization of a measure-then-hash protocol

`MeasureThenHash.exists_hashDifference_eq_conj` realizes the protocol's reference difference
as the seed-visible hashing difference of a CQ extension. The conjugating map preserves the
support of the difference, including when that difference is zero.

The proof integrates the IID purifications, purifies the resulting state in a symmetric-space
ancilla, and transports the instrument along a reference isometry. This is the register
identification in Nahar et al., arXiv:2403.11851, Appendix B, `eq:splittingoffV` and main.tex:1418.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Quantum.Metrics MeasureTheory
open InfoTheory.DeFinetti InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection.MeasureThenHash

variable {dA dB n l' : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
  {M : RawKeyMeasurement dA dB n} (C : MeasureThenHash M l')

/-- The register equivalence from public transcript, Eve, and the new ancillary
register to the raw-key conditioning register extended by that ancilla. -/
def extendedCondEquiv (r : ℕ) :
    Fin (C.publicDim * ((dA * dB) ^ n * r)) ≃ Fin (M.condDim * r) :=
  (finCongr (Nat.mul_assoc C.publicDim ((dA * dB) ^ n) r).symm).trans
    (Equiv.finProdCongrExt C.condEquiv r)

/-- The actual accept instrument on an extension with Eve and an ancillary
register, expressed in the measurement's conditioning-register convention. -/
def extendedRawKeyCQ (r : ℕ) [NeZero r]
    (ρ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r))) :
    CQState (Fin M.toProtocol.rawKeyDim) (M.condDim * r) :=
  CQState.reindexQHetero (C.extendedCondEquiv r)
    (CQState.ofInstrumentExtension C.instrument C.instrument_isCompletelyPositive
      C.instrument_weight_le_one ρ)

/-- The explicit blocks of the extended raw-key state. -/
lemma extendedRawKeyCQ_stateMap_toOp (r : ℕ) [NeZero r]
    (ρ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r)))
    (x : Fin M.toProtocol.rawKeyDim) :
    ((C.extendedRawKeyCQ r ρ).stateMap x).toOp =
      Matrix.reindex (C.extendedCondEquiv r) (C.extendedCondEquiv r)
        (mapTensorId (C.instrument x) ρ.toOp) := rfl

/-- Tracing out the new ancilla of an extended raw-key block leaves the
instrument applied to the system--Eve marginal. -/
lemma extendedRawKeyCQ_partialTraceB (r : ℕ) [NeZero r]
    (ρ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r)))
    (x : Fin M.toProtocol.rawKeyDim) :
    partialTraceB ((C.extendedRawKeyCQ r ρ).stateMap x).toOp =
      Matrix.reindex C.condEquiv C.condEquiv
        (mapTensorId (C.instrument x)
          (partialTraceB (Op.castDim
            (Nat.mul_assoc ((dA * dB) ^ n) ((dA * dB) ^ n) r).symm ρ.toOp))) := by
  rw [C.extendedRawKeyCQ_stateMap_toOp]
  change partialTraceB (Matrix.reindex
    ((finCongr (Nat.mul_assoc C.publicDim ((dA * dB) ^ n) r).symm).trans _)
    ((finCongr (Nat.mul_assoc C.publicDim ((dA * dB) ^ n) r).symm).trans _)
    _) = _
  rw [← Matrix.reindex_trans]
  simp only [Equiv.trans_apply]
  rw [← Op.castDim_eq_reindex_finCongr, partialTraceB_reindex_finProdCongrExt]
  congr 1
  exact partialTraceB_mapTensorId_trailing (C.instrument x) ρ.toOp

/-- The instrument commutes with the purification mixture, giving exactly the
raw-key mixture specified by `MeasureThenHash.rawKeyCQ_stateMap_toOp`. -/
lemma integral_rawKeyCQ_stateMap_toOp (μ : DensityMeasure (dA * dB))
    (x : Fin M.toProtocol.rawKeyDim) :
    Matrix.reindex C.condEquiv C.condEquiv
        (mapTensorId (C.instrument x) (∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure)) =
      ((M.mixCQ_En μ (C.integrable μ)).stateMap x).toOp := by
  rw [mapTensorId_integral_commute _ _ _ (integrable_purificationDensityOp_tensorPowGen μ)]
  let L := (Matrix.reindexLinearEquiv ℂ ℂ C.condEquiv C.condEquiv).toLinearMap
  have hmap := (mapTensorIdLinear (k := (dA * dB) ^ n) (C.instrument x)).toContinuousLinearMap
    |>.integrable_comp (integrable_purificationDensityOp_tensorPowGen μ)
  change L (∫ σ : DensityOp (dA * dB),
    mapTensorId (C.instrument x) (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) = _
  calc
    _ = ∫ σ : DensityOp (dA * dB), L
        (mapTensorId (C.instrument x) (purificationDensityOp (σ.tensorPowGen n)).toOp)
          ∂μ.measure := (L.toContinuousLinearMap.integral_comp_comm hmap).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun σ => (C.rawKeyCQ_stateMap_toOp σ x).symm)

/-- Applying the protocol instrument to a rank-bounded pure extension gives
the required raw-key block marginals, while retaining a purification of the
de Finetti system mixture. -/
lemma exists_isPure_extendedRawKeyCQ_partialTraceB_eq (μ : DensityMeasure (dA * dB)) :
    ∃ τ : DensityOp ((dA * dB) ^ n *
        ((dA * dB) ^ n * deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)),
      τ.IsPure ∧
      τ.partialTraceB = deFinettiMixtureFixedMarginal dA dB n μ ∧
      ∀ x : Fin M.toProtocol.rawKeyDim,
        partialTraceB ((C.extendedRawKeyCQ (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n) τ).stateMap
          x).toOp = ((M.mixCQ_En μ (C.integrable μ)).stateMap x).toOp := by
  have hext := exists_isPure_partialTraceB_eq_integral_purificationDensityOp_tensorPowGen (n := n) μ
  rw [mul_pow dA dB 2] at hext
  obtain ⟨ψ, hpure, hmarg⟩ := hext
  let g := deFinettiPrefactor (dA ^ 2 * dB ^ 2) n
  let τ := DensityOp.castDim (Nat.mul_assoc ((dA * dB) ^ n) ((dA * dB) ^ n) g) ψ
  have hop : τ.toOp = Op.castDim (Nat.mul_assoc ((dA * dB) ^ n) ((dA * dB) ^ n) g) ψ.toOp :=
    densityOp_castDim_toOp _ ψ
  refine ⟨τ, DensityOp.castDim_IsPure _ _ hpure, ?_, ?_⟩
  · apply DensityOp.ext
    change partialTraceB τ.toOp = _
    rw [hop]
    calc
      _ = partialTraceB (partialTraceB ψ.toOp) :=
        (partialTraceB_partialTraceB_eq_assoc ψ.toOp).symm
      _ = _ := by
        rw [hmarg]
        exact partialTraceB_integral_purificationDensityOp_tensorPowGen μ
  · intro x
    rw [C.extendedRawKeyCQ_partialTraceB, hop]
    rw [Op.castDim_cancel, hmarg]
    exact C.integral_rawKeyCQ_stateMap_toOp μ x

/-- The linear real-minus-ideal hash operation applied to the accept instrument. -/
def hashDifferenceMap :
    Op ((dA * dB) ^ n) →ₗ[ℂ] Op (C.publicDim * Fintype.card (C.Seed × C.Key)) :=
  jointInstrumentMap (hashDifferenceBlock C.hash C.instrument)

/-- On an input density operator, the linear hashed instrument is the specified
real-minus-uniform CQ output. -/
lemma hashDifferenceMap_apply_toOp (ρ : DensityOp ((dA * dB) ^ n)) :
    C.hashDifferenceMap ρ.toOp =
      (seedKeyExtractorOutputState C.hash (C.acceptCQ ρ)).toJointDensity.toOp -
        (seedUniformOutputState (S := C.Seed) (Z := C.Key)
          (C.acceptCQ ρ).quantumMarginal).toJointDensity.toOp := by
  rw [hashDifferenceBlock_joint]
  change cqJointLinearMap _ _ _ = cqJointLinearMap _ _ _
  congr 1
  funext sz
  simp only [LinearMap.pi_apply, hashDifferenceBlock, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply,
    C.acceptCQ_stateMap_toOp]
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

/-- Abort agreement and the channel semantics identify the full protocol
difference with the encoded linear hashed instrument on every operator. -/
lemma roundDifferenceMap_eq_encoded (A : Op ((dA * dB) ^ n)) :
    M.toProtocol.roundDifferenceMap l' A =
      C.encode * C.hashDifferenceMap A * C.encodeᴴ := by
  let T : Op (C.publicDim * Fintype.card (C.Seed × C.Key)) →ₗ[ℂ]
      Op (M.toProtocol.keyDim * M.toProtocol.annDim) :=
    { toFun B := C.encode * B * C.encodeᴴ
      map_add' B D := by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' z B := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        rfl }
  suffices h : M.toProtocol.roundDifferenceMap l' = T.comp C.hashDifferenceMap from
    congrArg (fun F => F A) h
  apply linearMap_eq_of_densityOp
  intro ρ
  conv_lhs => rw [← M.toProtocol.acceptProj_comp_roundDifferenceMap l']
  change M.toProtocol.acceptProj
    ((M.toProtocol.variantReal l' _ - M.toProtocol.variantIdeal l' _)) = _
  simp only [map_sub, LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv]
  rw [C.acceptProj_variantReal ρ, C.acceptProj_variantIdeal ρ]
  change _ = C.encode * C.hashDifferenceMap ρ.toOp * C.encodeᴴ
  rw [C.hashDifferenceMap_apply_toOp, Matrix.mul_sub, Matrix.sub_mul]
  rfl

/-- Register order for hashing an extension: move the reference before the
seed/key pair, then use the measurement's conditioning-register labels. -/
def hashOutputEquiv (r : ℕ) :
    Fin ((C.publicDim * Fintype.card (C.Seed × C.Key)) * ((dA * dB) ^ n * r)) ≃
      Fin ((M.condDim * r) * Fintype.card (C.Seed × C.Key)) :=
  (jointReferenceEquiv (C.Seed × C.Key) C.publicDim ((dA * dB) ^ n * r)).trans
    (Equiv.finProdCongrExt (C.extendedCondEquiv r) (Fintype.card (C.Seed × C.Key)))

/-- The hash of the extended raw-key instrument is the reference extension of
the linear hashed instrument, with the output registers put in CQ order. -/
lemma extendedRawKeyCQ_hashDifference (r : ℕ) [NeZero r]
    (τ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r))) :
    (seedKeyExtractorOutputState C.hash (C.extendedRawKeyCQ r τ)).toJointDensity.toOp -
        (seedUniformOutputState (S := C.Seed) (Z := C.Key)
          (C.extendedRawKeyCQ r τ).quantumMarginal).toJointDensity.toOp =
      Matrix.reindex (C.hashOutputEquiv r) (C.hashOutputEquiv r)
        (mapTensorId C.hashDifferenceMap τ.toOp) := by
  let T : (Op ((dA * dB) ^ n) →ₗ[ℂ] Op C.publicDim) →ₗ[ℂ]
      Op (C.publicDim * ((dA * dB) ^ n * r)) :=
    { toFun F := mapTensorId F τ.toOp
      map_add' F G := mapTensorId_linearMap_add F G τ.toOp
      map_smul' z F := mapTensorId_linearMap_smul z F τ.toOp }
  let R := (Matrix.reindexLinearEquiv ℂ ℂ
    (C.extendedCondEquiv r) (C.extendedCondEquiv r)).toLinearMap
  rw [hashDifferenceBlock_joint]
  have hb : hashDifferenceBlock C.hash (fun x => ((C.extendedRawKeyCQ r τ).stateMap x).toOp) =
      fun sz => Matrix.reindex (C.extendedCondEquiv r) (C.extendedCondEquiv r)
        (mapTensorId (hashDifferenceBlock C.hash C.instrument sz) τ.toOp) := by
    funext sz
    exact (map_hashDifferenceBlock C.hash (R.comp T) C.instrument sz).symm
  rw [hb, cqJointLinearMap_reindex, cqJointLinearMap_mapTensorId]
  rfl

/-- Hashing after changing the purifying register factors through decoding the
protocol output. The factor preserves the support of the protocol difference. -/
lemma exists_hashDifference_eq_conj_of_partialTraceB_eq (r : ℕ) [NeZero r]
    [NeZero (M.toProtocol.keyDim * M.toProtocol.annDim)]
    (τ₀ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n))
    (τ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r)))
    (h₀ : τ₀.IsPure) (hτ : τ.IsPure) (hmarg : τ.partialTraceB = τ₀.partialTraceB) :
    ∃ V : Matrix (Fin ((M.condDim * r) * Fintype.card (C.Seed × C.Key)))
        (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ,
      Vᴴ * V * mapTensorId (M.toProtocol.roundDifferenceMap l') τ₀.toOp =
        mapTensorId (M.toProtocol.roundDifferenceMap l') τ₀.toOp ∧
      (seedKeyExtractorOutputState C.hash (C.extendedRawKeyCQ r τ)).toJointDensity.toOp -
          (seedUniformOutputState (S := C.Seed) (Z := C.Key)
            (C.extendedRawKeyCQ r τ).quantumMarginal).toJointDensity.toOp =
        V * mapTensorId (M.toProtocol.roundDifferenceMap l') τ₀.toOp * Vᴴ := by
  have := M.toProtocol.keyDim_neZero
  have := M.toProtocol.annDim_neZero
  obtain ⟨W, hW, hτW⟩ := exists_isometry_eq_idTensorRect_conj_of_partialTraceB_eq
    τ₀ τ h₀ hτ hmarg (Nat.le_mul_of_pos_right _ (NeZero.pos r))
  let E := tensorRect C.encode (1 : Op ((dA * dB) ^ n))
  let J₀ := idTensorRectMatrix (C.publicDim * Fintype.card (C.Seed × C.Key))
    ((dA * dB) ^ n * r) ((dA * dB) ^ n) W
  let J := Matrix.reindex (C.hashOutputEquiv r) (Equiv.refl _) J₀
  have hE : Eᴴ * E = 1 := by
    dsimp only [E]
    rw [tensorRect_conjTranspose, tensorRect_mul, C.encode_isometry,
      Matrix.conjTranspose_one, Matrix.one_mul, tensorRect_one]
  have hJ₀ : J₀ᴴ * J₀ = 1 := by
    change (tensorRect (1 : Op _) W)ᴴ * tensorRect (1 : Op _) W = 1
    rw [tensorRect_conjTranspose, tensorRect_mul, hW,
      Matrix.conjTranspose_one, Matrix.one_mul, tensorRect_one]
  have hJ : Jᴴ * J = 1 := by
    dsimp only [J]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, hJ₀]
    rfl
  let A := mapTensorId C.hashDifferenceMap τ₀.toOp
  have hD : mapTensorId (M.toProtocol.roundDifferenceMap l') τ₀.toOp = E * A * Eᴴ :=
    mapTensorId_conj_of_conj _ _ C.encode C.roundDifferenceMap_eq_encoded τ₀.toOp
  have hY : (seedKeyExtractorOutputState C.hash (C.extendedRawKeyCQ r τ)).toJointDensity.toOp -
      (seedUniformOutputState (S := C.Seed) (Z := C.Key)
        (C.extendedRawKeyCQ r τ).quantumMarginal).toJointDensity.toOp = J * A * Jᴴ := by
    rw [C.extendedRawKeyCQ_hashDifference, hτW]
    have hmap := mapTensorIdLinear_idTensorRect_conj C.hashDifferenceMap W τ₀.toOp
    change mapTensorId C.hashDifferenceMap _ = J₀ * A * J₀ᴴ at hmap
    exact (congrArg (Matrix.reindex (C.hashOutputEquiv r) (C.hashOutputEquiv r)) hmap).trans
      (by
        dsimp only [J]
        simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
        change (J₀ * A * J₀ᴴ).submatrix _ _ =
          J₀.submatrix _ (Equiv.refl _) *
            A.submatrix (Equiv.refl _) (Equiv.refl _) *
            J₀ᴴ.submatrix (Equiv.refl _) _
        rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv])
  obtain ⟨V, hsupport, hfactor⟩ := Matrix.exists_conj_eq_conj_of_isometry E J hE hJ A
  refine ⟨V, ?_, ?_⟩
  · rw [hD]
    exact hsupport
  · rw [hY, hD]
    exact hfactor

/-- The protocol difference is isometrically decoded into its own hash family's CQ difference.
The resulting CQ state has the prescribed mixed raw-key blocks as its marginal. -/
theorem exists_hashDifference_eq_conj (μ : DensityMeasure (dA * dB)) :
    ∃ (V : Matrix (Fin (M.mixCondDim * Fintype.card (C.Seed × C.Key)))
          (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ)
      (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) M.mixCondDim),
      Vᴴ * V * M.toProtocol.referenceDifference l' μ = M.toProtocol.referenceDifference l' μ ∧
      (seedKeyExtractorOutputState C.hash ρ_EnV).toJointDensity.toOp -
          (seedUniformOutputState ρ_EnV.quantumMarginal).toJointDensity.toOp =
        V * M.toProtocol.referenceDifference l' μ * Vᴴ ∧
      ∀ x, partialTraceB (ρ_EnV.stateMap x).toOp =
        ((M.mixCQ_En μ (C.integrable μ)).stateMap x).toOp := by
  have := M.toProtocol.keyDim_neZero
  have := M.toProtocol.annDim_neZero
  obtain ⟨τ, hτ, hmarg, hblocks⟩ := C.exists_isPure_extendedRawKeyCQ_partialTraceB_eq μ
  obtain ⟨V, hsupport, hfactor⟩ := C.exists_hashDifference_eq_conj_of_partialTraceB_eq
    (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)
    (deFinettiMixturePurification dA dB n μ) τ
    (purificationDensityOp_isPure (deFinettiMixtureFixedMarginal dA dB n μ)) hτ
    (hmarg.trans (deFinettiMixturePurification_partialTraceB dA dB n μ).symm)
  exact ⟨V, C.extendedRawKeyCQ (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n) τ,
    hsupport, hfactor, hblocks⟩

end InfoTheory.Postselection.MeasureThenHash
