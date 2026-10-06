import QCryptLean.Quantum.Matrix.RectangularGramIsometry
import QCryptLean.InfoTheory.Postselection.RawKeyMeasurement
import QCryptLean.InfoTheory.Postselection.PairedBlockedTransport
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Instrument

/-!
# The accept measurement and privacy amplification of a QKD protocol

This module specifies the protocol class used in Appendix B of Nahar et al.,
arXiv:2403.11851. A single completely positive instrument on the round-grouped
`n`-round input produces the raw key and public transcript. Its output on a
purified IID input is precisely `RawKeyMeasurement.rawKeyCQ`. The real accept
map hashes this instrument's output, and the ideal accept map replaces the key
by uniform randomness. Both retain the public hash seed.

`MeasureThenHash.acceptCQ` constructs the accepted CQ state from the instrument blocks.
`MeasureThenHash.continuous_rawKeyCQ_stateMap_toOp` and `MeasureThenHash.integrable` derive the
regularity needed for mixtures from the instrument formula. Acceptance is modeled by a CP
idempotent map; no representation as a projector sandwich is assumed.

References: Nahar et al., arXiv:2403.11851, Appendix B's proof of Theorem 3,
`eq:tausplit` (main.tex:1356–1362), `eq:splittingoffV` (1391–1395), and the reference
identification at main.tex:1418.
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- Channel semantics for a length-`l'` measure-then-hash variant (Appendix B,
B13--B19). `publicDim` is the register before the PA seed is appended; the IID
conditioning register additionally contains the untouched purifying register
`Eⁿ`, of dimension `(dA * dB)^n`.

`instrument` is the accept instrument, with one CP map for each raw key.
`instrument_weight_le_one` expresses trace nonincrease on states.
`rawKeyCQ_stateMap_toOp` identifies the supplied IID data with this same instrument.
`acceptProj_variantReal` and `acceptProj_variantIdeal` specify hashing and uniform replacement on
arbitrary input states. The isometry `encode` permits an unused abort slot in
the protocol output. Complete positivity of the accept projection is required
because it is also applied in the presence of an entangled reference.

The definition concerns one supported hash length: a finite shared protocol
output cannot accommodate every natural-number key length simultaneously.
No nonzero-difference or nonzero-acceptance assumption is needed. -/
structure MeasureThenHash (M : RawKeyMeasurement dA dB n) (l' : ℕ) where
  /-- Dimension of the public transcript before appending the hash seed. -/
  publicDim : ℕ
  /-- The public transcript register has positive dimension. -/
  [publicDim_neZero : NeZero publicDim]
  /-- Identify transcript and IID reference with the supplied conditioning register. -/
  condEquiv : Fin (publicDim * (dA * dB) ^ n) ≃ Fin M.condDim
  /-- The accepted instrument block for each raw key. -/
  instrument : Fin M.toProtocol.rawKeyDim →
    (Op ((dA * dB) ^ n) →ₗ[ℂ] Op publicDim)
  /-- Each block remains positive under extension by a reference register. -/
  instrument_isCompletelyPositive : ∀ x, IsCompletelyPositive ⇑(instrument x)
  /-- The total accepted weight is at most one on normalized inputs. -/
  instrument_weight_le_one : ∀ ρ : DensityOp ((dA * dB) ^ n),
    ∑ x, (instrument x ρ.toOp).trace.re ≤ 1
  /-- IID raw-key blocks are obtained from this instrument on canonical purifications. -/
  rawKeyCQ_stateMap_toOp : ∀ σ x,
    ((M.rawKeyCQ σ).stateMap x).toOp =
      Matrix.reindex condEquiv condEquiv
        (mapTensorId (instrument x) (purificationDensityOp (σ.tensorPowGen n)).toOp)
  /-- The public hash-seed alphabet. -/
  Seed : Type u
  /-- The hashed-key alphabet. -/
  Key : Type u
  /-- The seed alphabet is finite. -/
  [seedFintype : Fintype Seed]
  /-- Seed equality is decidable. -/
  [seedDecidableEq : DecidableEq Seed]
  /-- A seed can be sampled. -/
  [seedNonempty : Nonempty Seed]
  /-- The key alphabet is finite. -/
  [keyFintype : Fintype Key]
  /-- Key equality is decidable. -/
  [keyDecidableEq : DecidableEq Key]
  /-- The uniform key state is defined on a nonempty alphabet. -/
  [keyNonempty : Nonempty Key]
  /-- The hash family used by the real protocol. -/
  hash : QuantumHashFamily Seed (Fin M.toProtocol.rawKeyDim) Key
  /-- Distinct raw keys collide with probability at most the inverse key cardinality. -/
  hash_isUniversal : hash.isUniversal
  /-- The key alphabet has the prescribed bit length. -/
  card_key : Fintype.card Key = 2 ^ l'
  /-- Embed transcript, seed and key into the protocol output, allowing an abort slot. -/
  encode : Matrix (Fin (M.toProtocol.keyDim * M.toProtocol.annDim))
    (Fin (publicDim * Fintype.card (Seed × Key))) ℂ
  /-- The output encoding preserves inner products. -/
  encode_isometry : encodeᴴ * encode = 1
  /-- The protocol's idempotent accept map is completely positive. -/
  acceptProj_isCompletelyPositive :
    letI := M.toProtocol.keyDim_neZero
    letI := M.toProtocol.annDim_neZero
    IsCompletelyPositive ⇑M.toProtocol.acceptProj
  /-- The accepted real output hashes the instrument state and retains the seed. -/
  acceptProj_variantReal : ∀ ρ : DensityOp ((dA * dB) ^ n),
    M.toProtocol.acceptProj (M.toProtocol.variantReal l'
      (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n) ρ.toOp)) =
      encode * (seedKeyExtractorOutputState hash
        (CQState.ofInstrument instrument instrument_isCompletelyPositive
          instrument_weight_le_one ρ)).toJointDensity.toOp * encodeᴴ
  /-- The accepted ideal output replaces the key by uniform randomness. -/
  acceptProj_variantIdeal : ∀ ρ : DensityOp ((dA * dB) ^ n),
    M.toProtocol.acceptProj (M.toProtocol.variantIdeal l'
      (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n) ρ.toOp)) =
      encode * (seedUniformOutputState (S := Seed) (Z := Key)
        (CQState.ofInstrument instrument instrument_isCompletelyPositive
          instrument_weight_le_one ρ).quantumMarginal).toJointDensity.toOp * encodeᴴ

attribute [instance] MeasureThenHash.publicDim_neZero MeasureThenHash.seedFintype
  MeasureThenHash.seedDecidableEq MeasureThenHash.seedNonempty MeasureThenHash.keyFintype
  MeasureThenHash.keyDecidableEq MeasureThenHash.keyNonempty

namespace MeasureThenHash

variable {M : RawKeyMeasurement dA dB n} {l' : ℕ} (C : MeasureThenHash M l')

/-- The accepted CQ state determined by the instrument blocks. -/
def acceptCQ (ρ : DensityOp ((dA * dB) ^ n)) :
    CQState (Fin M.toProtocol.rawKeyDim) C.publicDim :=
  CQState.ofInstrument C.instrument C.instrument_isCompletelyPositive
    C.instrument_weight_le_one ρ

/-- The accepted CQ blocks are exactly the outputs of the instrument. -/
@[simp] lemma acceptCQ_stateMap_toOp (ρ : DensityOp ((dA * dB) ^ n))
    (x : Fin M.toProtocol.rawKeyDim) :
    ((C.acceptCQ ρ).stateMap x).toOp = C.instrument x ρ.toOp := rfl

include C in
/-- Instrument blocks vary continuously with the IID input state. -/
lemma continuous_rawKeyCQ_stateMap_toOp (x : Fin M.toProtocol.rawKeyDim) :
    Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp) := by
  have hblocks := C.rawKeyCQ_stateMap_toOp
  simp_rw [hblocks]
  exact ((LinearMap.continuous_of_finiteDimensional
    (mapTensorIdLinear (C.instrument x))).comp
      continuous_purificationDensityOp_tensorPowGen_toOp).matrix_reindex
        C.condEquiv C.condEquiv

include C in
/-- Continuous instrument blocks are integrable for every probability measure on IID states. -/
lemma integrable (μ : DensityMeasure (dA * dB)) : M.Integrable μ := by
  have := μ.isProbability
  exact fun x => (C.continuous_rawKeyCQ_stateMap_toOp x).integrable_of_compactSpace

/-- Discarding the IID purifying register does not change the accept mass. -/
lemma rawKeyCQ_stateMap_trace (σ : DensityOp (dA * dB)) (x : Fin M.toProtocol.rawKeyDim) :
    ((M.rawKeyCQ σ).stateMap x).trace =
      ((C.acceptCQ (σ.tensorPowGen n)).stateMap x).trace := by
  change (((M.rawKeyCQ σ).stateMap x).toOp.trace).re = _
  rw [C.rawKeyCQ_stateMap_toOp, Matrix.trace_reindex_self,
    trace_mapTensorId]
  have hmarg := purificationDensityOp_partialTraceB (σ.tensorPowGen n)
  have hop := congrArg (fun ρ : DensityOp ((dA * dB) ^ n) => ρ.toOp) hmarg
  change partialTraceB (purificationDensityOp (σ.tensorPowGen n)).toOp = _ at hop
  rw [hop, ← C.acceptCQ_stateMap_toOp]
  rfl

/-- The instrument's accept mass is the accept probability of the protocol.
Its trace agrees with the IID acceptance functional `RawKeyMeasurement.pAcc`. -/
lemma acceptProj_variantReal_trace_re_eq_pAcc (C : MeasureThenHash M l') (σ : DensityOp (dA * dB)) :
    (M.toProtocol.acceptProj (M.toProtocol.variantReal l'
      (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (σ.tensorPowGen n).toOp))).trace.re = M.pAcc σ := by
  rw [C.acceptProj_variantReal, Matrix.trace_isometry_conj _ _ C.encode_isometry,
    seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace]
  change (∑ x, ((C.acceptCQ (σ.tensorPowGen n)).stateMap x).toOp).trace.re = _
  rw [Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun x _ => (C.rawKeyCQ_stateMap_trace σ x).symm

end MeasureThenHash

end InfoTheory.Postselection
