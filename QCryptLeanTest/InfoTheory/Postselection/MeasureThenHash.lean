import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.Quantum.Channels.CPTP.PositiveTransport
import QCryptLean.Quantum.Channels.CPTP.DiamondNormReindex

/-!
# A nontrivial measure-then-hash protocol

A one-dimensional input is always accepted, with a deterministic raw key.
Hashing that key to one bit gives a deterministic real key and a uniform ideal
key. This witnesses that the protocol class used in Corollary 3.1 admits
unequal real and ideal variants. It is a semantics example, not a secure QKD
protocol or an instance of the corollary's entropy assumptions.
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open InfoTheory.Postselection
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QCryptLeanTest.MeasureThenHash

section Consistency

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
variable {M : RawKeyMeasurement dA dB n} {l' : ℕ}

/-- Equal real and ideal maps force exact uniformity of the *same* instrument's
hashed output, because its output encoding is an isometry. -/
lemma extractor_eq_uniform_of_variants_eq (C : MeasureThenHash M l')
    (h : M.toProtocol.variantReal l' = M.toProtocol.variantIdeal l')
    (ρ : DensityOp ((dA * dB) ^ n)) :
    (seedKeyExtractorOutputState C.hash (C.acceptCQ ρ)).toJointDensity.toOp =
      (seedUniformOutputState (S := C.Seed) (Z := C.Key)
        (C.acceptCQ ρ).quantumMarginal).toJointDensity.toOp := by
  have heq := congrArg (fun f => M.toProtocol.acceptProj
    (f (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n) ρ.toOp))) h
  rw [C.acceptProj_variantReal ρ, C.acceptProj_variantIdeal ρ] at heq
  have hinj : Function.Injective (fun A : Op (C.publicDim * Fintype.card (C.Seed × C.Key)) =>
      C.encode * A * C.encodeᴴ) := by
    apply Function.LeftInverse.injective (g := fun A => C.encodeᴴ * A * C.encode)
    intro A
    simp only [← Matrix.mul_assoc, C.encode_isometry, Matrix.one_mul]
    rw [Matrix.mul_assoc, C.encode_isometry, Matrix.mul_one]
  exact hinj heq

/-- Positive acceptance implies that at least one raw-key block is nonzero. -/
lemma exists_rawKeyCQ_stateMap_toOp_ne_zero_of_pos (C : MeasureThenHash M l')
    (σ : DensityOp (dA * dB))
    (hpos : 0 < (M.toProtocol.acceptProj (M.toProtocol.variantReal l'
      (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (σ.tensorPowGen n).toOp))).trace.re) :
    ∃ x, ((M.rawKeyCQ σ).stateMap x).toOp ≠ 0 := by
  classical
  by_contra hzero
  push Not at hzero
  rw [C.acceptProj_variantReal_trace_re_eq_pAcc] at hpos
  have hmass : M.pAcc σ = 0 := by
    simp only [RawKeyMeasurement.pAcc, SubDensityOp.trace, hzero, Matrix.trace_zero,
      Complex.zero_re, Finset.sum_const_zero]
  rw [hmass] at hpos
  exact (lt_irrefl 0) hpos

/-- Equal real and ideal variants have zero acceptance when the key alphabet
is larger than the raw-key alphabet. -/
lemma pAcc_eq_zero_of_variants_eq_of_card_lt (C : MeasureThenHash M l')
    (heq : M.toProtocol.variantReal l' = M.toProtocol.variantIdeal l')
    (hcard : M.toProtocol.rawKeyDim < 2 ^ l') (σ : DensityOp (dA * dB)) :
    M.pAcc σ = 0 := by
  have hz := quantumMarginal_eq_zero_of_card_lt_of_seedKeyExtractorOutputState_eq C.hash
    (C.acceptCQ (σ.tensorPowGen n))
    (by simpa only [Fintype.card_fin, C.card_key] using hcard)
    (extractor_eq_uniform_of_variants_eq C heq (σ.tensorPowGen n))
  calc M.pAcc σ = ∑ x, ((C.acceptCQ (σ.tensorPowGen n)).stateMap x).trace :=
        Finset.sum_congr rfl fun x _ => C.rawKeyCQ_stateMap_trace σ x
    _ = (C.acceptCQ (σ.tensorPowGen n)).quantumMarginal.toOp.trace.re := by
        simp only [CQState.quantumMarginal, CQState.quantumMarginalOp,
          Matrix.trace_sum, Complex.re_sum, SubDensityOp.trace]
    _ = 0 := by rw [hz, Matrix.trace_zero, Complex.zero_re]

end Consistency

private lemma oneDim_toOp (ρ : DensityOp 1) : ρ.toOp = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [Matrix.trace] using ρ.trace_one

/-- One possible raw key, with a one-dimensional transcript. -/
def raw : CQState (Fin 1) 1 where
  stateMap := fun _ => (DensityOp.toSubDensityOp (DensityOp.maxMixed 1))
  weight_le_one := by simp [toSubDensityOp_trace]

private lemma raw_marginal :
    raw.quantumMarginal = DensityOp.toSubDensityOp (DensityOp.maxMixed 1) := by
  apply SubDensityOp.ext
  simp [CQState.quantumMarginal, CQState.quantumMarginalOp, raw]

/-- A one-seed hash sends the only raw key to zero. Universality is vacuous
because there are no distinct raw-key inputs. -/
def hash : QuantumHashFamily (Fin 1) (Fin 1) (Fin 2) where
  hash := fun _ _ => 0

lemma hash_universal : hash.isUniversal := by
  intro x y hne
  exact (hne (Subsingleton.elim x y)).elim

/-- The real output, including its public seed. -/
def realState : DensityOp (1 * Fintype.card (Fin 1 × Fin 2)) where
  toPosSemidefOp := (seedKeyExtractorOutputState hash raw).toJointDensity.toPosSemidefOp
  trace_one := by
    rw [SubDensityOp.trace_complex_eq]
    have h := seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace hash raw
    rw [raw_marginal, toSubDensityOp_trace] at h
    change ((seedKeyExtractorOutputState hash raw).toJointDensity.trace : ℂ) = 1
    rw [show (seedKeyExtractorOutputState hash raw).toJointDensity.trace = 1 from h]
    norm_num

/-- The ideal output is uniform on the key and retains the seed. -/
def idealState : DensityOp (1 * Fintype.card (Fin 1 × Fin 2)) where
  toPosSemidefOp := (seedUniformOutputState (S := Fin 1) (Z := Fin 2)
    raw.quantumMarginal).toJointDensity.toPosSemidefOp
  trace_one := by
    rw [SubDensityOp.trace_complex_eq]
    rw [seedUniformOutputState, uniformCQState_toJointDensity_trace, raw_marginal,
      toSubDensityOp_trace]
    norm_num

/-- Always accept and prepare the real or ideal one-bit output. -/
def protocol : PMQKDProtocol 1 1 1 where
  keyDim := 1 * Fintype.card (Fin 1 × Fin 2)
  keyDim_neZero := inferInstance
  cDim := 1
  ceDim := 1
  cpDim := 1
  annDim := 1
  annDim_factored := rfl
  annDim_neZero := inferInstance
  rawKeyDim := 1
  rawKeyDim_neZero := inferInstance
  l := 1
  variantReal := fun _ => traceSmulMap 1 realState.toOp
  variantIdeal := fun _ => traceSmulMap 1 idealState.toOp
  variantReal_isCPTP := fun _ => traceSmulMap_one_isCPTP realState
  variantIdeal_isCPTP := fun _ => traceSmulMap_one_isCPTP idealState
  acceptProj := LinearMap.id
  acceptProj_idem := LinearMap.id_comp _
  abortAgreement := fun _ => by simp

/-- The protocol's own deterministic raw-key measurement. -/
def measurement : RawKeyMeasurement 1 1 1 where
  toProtocol := protocol
  condDim := 1
  condDim_neZero := inferInstance
  rawKeyCQ := fun _ => raw
  sigmaE := (DensityOp.toSubDensityOp (DensityOp.maxMixed 1))
  sigmaE_posDef := by
    change (DensityOp.maxMixed 1).toOp.PosDef
    rw [oneDim_toOp]
    exact Matrix.PosDef.one

private lemma ofInstrument_id_eq_raw (ρ : DensityOp 1)
    (hL : ∀ _ : Fin 1, IsCompletelyPositive ⇑(LinearMap.id : Op 1 →ₗ[ℂ] Op 1))
    (hw : ∀ σ : DensityOp 1, ∑ _ : Fin 1, σ.toOp.trace.re ≤ 1) :
    CQState.ofInstrument (fun _ : Fin 1 => (LinearMap.id : Op 1 →ₗ[ℂ] Op 1)) hL hw ρ =
      raw := by
  apply CQState.ext_stateMap
  funext x
  apply SubDensityOp.ext
  change ρ.toOp = (DensityOp.maxMixed 1).toOp
  rw [oneDim_toOp, oneDim_toOp]

/-- The deterministic-key example satisfies the channel-level instrument and hashing semantics. -/
def measureThenHash : MeasureThenHash measurement 1 where
  publicDim := 1
  publicDim_neZero := inferInstance
  condEquiv := Equiv.refl _
  instrument := fun _ => LinearMap.id
  instrument_isCompletelyPositive := fun _ => (id_is_cptp 1).2.1
  instrument_weight_le_one := by
    intro ρ
    change ∑ _ : Fin 1, ρ.toOp.trace.re ≤ 1
    simp [ρ.trace_one]
  rawKeyCQ_stateMap_toOp := by
    intro σ x
    change (DensityOp.maxMixed 1).toOp =
      Matrix.reindex (Equiv.refl _) (Equiv.refl _)
        (mapTensorId LinearMap.id (purificationDensityOp (σ.tensorPowGen 1)).toOp)
    rw [mapTensorId_id]
    change (DensityOp.maxMixed 1).toOp = (purificationDensityOp (σ.tensorPowGen 1)).toOp
    rw [oneDim_toOp, oneDim_toOp]
  Seed := Fin 1
  Key := Fin 2
  seedFintype := inferInstance
  seedDecidableEq := inferInstance
  seedNonempty := inferInstance
  keyFintype := inferInstance
  keyDecidableEq := inferInstance
  keyNonempty := inferInstance
  hash := hash
  hash_isUniversal := hash_universal
  card_key := rfl
  encode := (1 : Op (1 * Fintype.card (Fin 1 × Fin 2)))
  encode_isometry := by
    change (1 : Op 2)ᴴ * (1 : Op 2) = (1 : Op 2)
    simp
  acceptProj_isCompletelyPositive := (id_is_cptp (1 * Fintype.card (Fin 1 × Fin 2))).2.1
  acceptProj_variantReal := by
    intro ρ
    dsimp only [measurement, protocol]
    change DensityOp 1 at ρ
    have hraw := ofInstrument_id_eq_raw ρ (fun _ => (id_is_cptp 1).2.1)
      (fun σ => by simp [σ.trace_one])
    refine Eq.trans ?_ (congrArg (fun σ : CQState (Fin 1) 1 =>
      (1 : Op (1 * Fintype.card (Fin 1 × Fin 2))) *
        (seedKeyExtractorOutputState hash σ).toJointDensity.toOp *
        (1 : Op (1 * Fintype.card (Fin 1 × Fin 2)))ᴴ) hraw).symm
    change ((Matrix.reindex (roundGroupEquiv 1 1 1) (roundGroupEquiv 1 1 1)
      ρ.toOp).trace * 1) • realState.toOp =
        (1 : Op (1 * Fintype.card (Fin 1 × Fin 2))) * realState.toOp *
          (1 : Op (1 * Fintype.card (Fin 1 × Fin 2)))ᴴ
    rw [Matrix.trace_reindex_self, ρ.trace_one]
    simp
  acceptProj_variantIdeal := by
    intro ρ
    dsimp only [measurement, protocol]
    change DensityOp 1 at ρ
    have hraw := ofInstrument_id_eq_raw ρ (fun _ => (id_is_cptp 1).2.1)
      (fun σ => by simp [σ.trace_one])
    refine Eq.trans ?_ (congrArg (fun σ : CQState (Fin 1) 1 =>
      (1 : Op (1 * Fintype.card (Fin 1 × Fin 2))) *
        (seedUniformOutputState (S := Fin 1) (Z := Fin 2) σ.quantumMarginal).toJointDensity.toOp *
        (1 : Op (1 * Fintype.card (Fin 1 × Fin 2)))ᴴ) hraw).symm
    change ((Matrix.reindex (roundGroupEquiv 1 1 1) (roundGroupEquiv 1 1 1)
      ρ.toOp).trace * 1) • idealState.toOp =
        (1 : Op (1 * Fintype.card (Fin 1 × Fin 2))) * idealState.toOp *
          (1 : Op (1 * Fintype.card (Fin 1 × Fin 2)))ᴴ
    rw [Matrix.trace_reindex_self, ρ.trace_one]
    simp

/-- The real key never equals one, whereas the ideal key has weight `1/2` there. -/
lemma realState_ne_idealState : realState.toOp ≠ idealState.toOp := by
  intro h
  have hblocks := CQState.toJointDensity_injective
    (SubDensityOp.ext h : (seedKeyExtractorOutputState hash raw).toJointDensity =
      (seedUniformOutputState (S := Fin 1) (Z := Fin 2) raw.quantumMarginal).toJointDensity)
  have hentry := congrArg (fun f => (f (0, 1)).toOp 0 0) hblocks
  norm_num [seedKeyExtractorOutputState, seedPerSeedConditionedOp, seedPerSeedWeightedOp,
    hash, seedUniformOutputState, uniformCQState, SubDensityOp.smul,
    raw_marginal, DensityOp.toSubDensityOp, DensityOp.maxMixed] at hentry
  change (0 : ℂ) = ((1 / 2 : ℝ) : ℂ) at hentry
  norm_num at hentry

/-- This compatible protocol has distinct real and ideal variants. -/
lemma protocol_variantReal_ne_variantIdeal : protocol.variantReal 1 ≠ protocol.variantIdeal 1 := by
  intro h
  apply realState_ne_idealState
  have hout := congrArg (fun f : Op 1 →ₗ[ℂ] Op (1 * Fintype.card (Fin 1 × Fin 2)) =>
    f (1 : Op 1)) h
  change ((1 : Op 1).trace * 1) • realState.toOp =
    ((1 : Op 1).trace * 1) • idealState.toOp at hout
  simpa using hout

/-- The instrument and hashing semantics are satisfiable even when the real and ideal
protocol maps differ. -/
theorem exists_measureThenHash_variants_ne :
    ∃ M : RawKeyMeasurement 1 1 1,
      Nonempty (MeasureThenHash.{0} M 1) ∧
        M.toProtocol.variantReal 1 ≠ M.toProtocol.variantIdeal 1 :=
  ⟨measurement, ⟨measureThenHash⟩, protocol_variantReal_ne_variantIdeal⟩

end QCryptLeanTest.MeasureThenHash
