import QCryptLean.InfoTheory.QuantumLHL.SeedKeyAcceptSplit
import QCryptLean.InfoTheory.Postselection.RawKeyMeasurement
import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.DistanceBounds.AcceptSplit
import QCryptLean.Quantum.Metrics.TraceNorm.PartialIsometryConj
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapTensorIdAdjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discharging measure-then-hash security bounds

The raw-key measurement interfaces supply mixture entropy and leftover-hashing bounds for the
postselection reference experiment. Entropy is extended-valued and `hashingError` vanishes at `⊤`.
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts MeasureTheory
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

open InfoTheory.QuantumLHL

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-! ## The isometric-embedding transport primitive (raw-key-measurement bridge, §2.2–2.3) -/

namespace RawKeyMeasurement

variable (M : RawKeyMeasurement dA dB n)

/-! ## `hMixFloor` discharge (Nahar et al. App. B, `\label{eq:boundingsmoothedmin}`
(main.tex:1379–:1387)/(B17)) -/

/-! ## The App-B pre-PA channel factorization (Nahar et al. main.tex:1341–:1413 (Appendix B's proof
of Theorem 3: the accept-block split `\label{eq:tausplit}` (main.tex:1356–:1362), the
Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed min-entropy bound
`\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting step
`\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413)) -/

/-- The protocol reference secrecy equals the generalized trace distance of the seed-visible
extractor outputs when their difference is a conjugate of the protocol difference.

The map `V` need only preserve the support of that difference. Trace preservation of the
real and ideal channels makes the difference traceless, so the generalized trace-distance
correction vanishes. For a `MeasureThenHash` protocol, the required operator identity is supplied
by `MeasureThenHash.exists_hashDifference_eq_conj`. The accept-supported constructor
`PMQKDProtocol.ofAcceptSupported` alone does not supply an instrument or hash factorization.

This is the reference identification in Nahar et al., arXiv:2403.11851, Appendix B's proof of
Theorem 3, following `eq:splittingoffV` (main.tex:1391–1395), at main.tex:1418.

Generalized to a free conditioning-register dimension `r` (`r := M.mixCondDim` recovers the
raw-key-measurement instance, `RawKeyMeasurement.mixCondDim`). -/
theorem referenceSecrecy_eq_seedKeyExtractor_traceDistanceGen
    (μ : DensityMeasure (dA * dB))
    (r : ℕ) (hr : NeZero r)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) r)
    (l' : ℕ) {S Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (H : InfoTheory.QuantumLHL.QuantumHashFamily S (Fin M.toProtocol.rawKeyDim) Z)
    (V : Matrix (Fin (r * Fintype.card (S × Z)))
                (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ)
    -- Only the support of the protocol difference must be preserved.
    (hV' :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos M.toProtocol.keyDim_neZero.pos M.toProtocol.annDim_neZero.pos)⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      Vᴴ * V *
          (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
            (deFinettiMixturePurification dA dB n μ).toOp)
        = mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
            (deFinettiMixturePurification dA dB n μ).toOp)
    -- hPA_realization reshaped from `HEq` to the partial-isometric-embedding form (raw-key-
    -- measurement bridge): a rectangular partial isometry `V`
    -- transporting the protocol-side operator `X` onto the extractor-side difference `ρ − σ` built
    -- from the caller-supplied register extension `ρ_EnV`. `V`/`ρ_EnV` are DISCLOSED, undischarged
    -- parameters here — their concrete construction (the purified mixture and its rank-`g`
    -- purifier)
    -- is not this bridge's job; see the module docstring.
    (hPA_realization :
      haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
      haveI : NeZero (r * Fintype.card (S × Z)) :=
        ⟨Nat.mul_ne_zero hr.out Fintype.card_ne_zero⟩
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos M.toProtocol.keyDim_neZero.pos M.toProtocol.annDim_neZero.pos)⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      (InfoTheory.QuantumLHL.seedKeyExtractorOutputState H
              ρ_EnV).toJointDensity.toOp
          - (InfoTheory.QuantumLHL.seedUniformOutputState
              ρ_EnV.quantumMarginal).toJointDensity.toOp
        = V *
            (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
              (deFinettiMixturePurification dA dB n μ).toOp)
          * Vᴴ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (r * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero hr.out Fintype.card_ne_zero⟩
    referenceSecrecy M.toProtocol l' μ =
      Quantum.Metrics.traceDistanceGen
        (InfoTheory.QuantumLHL.seedKeyExtractorOutputState H ρ_EnV).toJointDensity.toOp
        (InfoTheory.QuantumLHL.seedUniformOutputState
          ρ_EnV.quantumMarginal).toJointDensity.toOp := by
  haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (r * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero hr.out Fintype.card_ne_zero⟩
  haveI := M.toProtocol.keyDim_neZero
  haveI := M.toProtocol.annDim_neZero
  haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos M.toProtocol.keyDim_neZero.pos M.toProtocol.annDim_neZero.pos)⟩
  haveI hknz : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne)
      (pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)))⟩
  set X := mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
    (deFinettiMixturePurification dA dB n μ).toOp with hX_def
  set ρ := (InfoTheory.QuantumLHL.seedKeyExtractorOutputState H
    ρ_EnV).toJointDensity.toOp with hρ_def
  set σ := (InfoTheory.QuantumLHL.seedUniformOutputState (S := S) (Z := Z)
    ρ_EnV.quantumMarginal).toJointDensity.toOp with hσ_def
  -- `X` is Hermitian: the round-difference map preserves the adjoint (both variants are CPTP),
  -- and `mapTensorId` preserves Hermiticity of the (Hermitian) de Finetti mixture purification.
  have hXherm : X.IsHermitian := by
    rw [hX_def]
    haveI := M.toProtocol.keyDim_neZero
    haveI := M.toProtocol.annDim_neZero
    exact Quantum.Channels.mapTensorId_preserves_hermitian
      (M.toProtocol.roundDifferenceMap l')
      (fun Mat => M.toProtocol.roundDifferenceMap_conjTranspose l' Mat)
      (deFinettiMixturePurification dA dB n μ).toOp
      (deFinettiMixturePurification dA dB n μ).isHermitian
  -- `tr X = 0`: the round-difference map is trace-annihilating (Nahar et al. main.tex:1397–:1405
  -- (unlabeled; the leftover-hashing hash-length reduction)/(B19)).
  have hXtr : X.trace = 0 :=
    PMQKDProtocol.mapTensorId_roundDifferenceMap_trace_zero M.toProtocol l' _
  -- The trace gap `tr ρ − tr σ = tr(ρ − σ) = tr(V·X·Vᴴ) = tr X = 0`.
  have htrconj : (V * X * Vᴴ).trace = X.trace :=
    Quantum.Metrics.TraceNormHoelder.trace_partialIsometry_conj V X hV'
  have hgaptr : (ρ - σ).trace = 0 := by rw [hPA_realization, htrconj, hXtr]
  have htrace_re : ρ.trace.re = σ.trace.re := by
    have h0 : ρ.trace - σ.trace = 0 := by rw [← Matrix.trace_sub]; exact hgaptr
    have h1 : ρ.trace.re - σ.trace.re = 0 := by
      have := congrArg Complex.re h0
      simpa [Complex.sub_re] using this
    linarith
  change (1 / 2 : ℝ) * traceNorm X = traceDistanceGen ρ σ
  rw [traceDistanceGen_eq_traceDistance ρ σ htrace_re]
  unfold traceDistance
  rw [hPA_realization,
    Quantum.Metrics.TraceNormHoelder.traceNorm_partialIsometry_conj V X hV' hXherm]

/-! ## `hLeftover` discharge (Nahar et al. App. B, main.tex:1397–:1405 (unlabeled; the
leftover-hashing hash-length reduction)) -/

/-- An isometric realization and extended leftover hashing bound reference secrecy at every
nonnegative smoothing radius. Infinite entropy contributes no hashing error. -/
theorem hLeftover_discharge
    (μ : DensityMeasure (dA * dB))
    (r : ℕ) (hr : NeZero r)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) r)
    (mixRef : SubDensityOp r) (hmixRef_pd : mixRef.toOp.PosDef)
    (εAT εbar : ℝ) (hεbar_nonneg : 0 ≤ εbar)
    (l' : ℕ) {S Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (H : InfoTheory.QuantumLHL.QuantumHashFamily S (Fin M.toProtocol.rawKeyDim) Z)
    (hH : H.isUniversal) (hcardZ : Fintype.card Z = 2 ^ l')
    (V : Matrix (Fin (r * Fintype.card (S × Z)))
                (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ)
    (hV' :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      Vᴴ * V *
          (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
            (deFinettiMixturePurification dA dB n μ).toOp) =
        mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
          (deFinettiMixturePurification dA dB n μ).toOp)
    (hPA_realization :
      haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
      haveI : NeZero (r * Fintype.card (S × Z)) :=
        ⟨Nat.mul_ne_zero hr.out Fintype.card_ne_zero⟩
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      (seedKeyExtractorOutputState H ρ_EnV).toJointDensity.toOp -
          (seedUniformOutputState ρ_EnV.quantumMarginal).toJointDensity.toOp =
        V *
            (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
              (deFinettiMixturePurification dA dB n μ).toOp) * Vᴴ) :
    referenceSecrecy M.toProtocol l' μ ≤
      hashingError l' (smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) ρ_EnV mixRef) +
        2 * (εbar + Real.sqrt (2 * εAT)) := by
  rw [M.referenceSecrecy_eq_seedKeyExtractor_traceDistanceGen μ r hr ρ_EnV l' H V hV'
    hPA_realization]
  exact quantum_seedKey_LHL_smooth_hashingError H hH ρ_EnV mixRef hmixRef_pd
    (εbar + Real.sqrt (2 * εAT)) (add_nonneg hεbar_nonneg (Real.sqrt_nonneg _)) l' hcardZ

end RawKeyMeasurement

/-! ## The protocol-level wrapper -/

/-- Extended IID security data imply the reference bound for a realized raw-key measurement
with a closed accepting set. This set may be empty and the accepted mixture may have zero weight. -/
theorem postselection_protocol_referenceBound_of_iidSecurityProof
    (M : RawKeyMeasurement dA dB n)
    (μ : DensityMeasure (dA * dB))
    (εAT εPA εbar : ℝ) (l' g : ℕ) (hg : NeZero g)
    (h_int : M.Integrable μ)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) (M.condDim * g))
    (hblocks : ∀ x : Fin M.toProtocol.rawKeyDim,
      Quantum.TensorProducts.partialTraceB (ρ_EnV.stateMap x).toOp =
        ((M.mixCQ_En μ h_int).stateMap x).toOp)
    (hproof : HasIIDSecurityProof M.toProtocol εAT εPA εbar)
    (hl' : (l' : ℝ) ≤ (M.toProtocol.l : ℝ) - 2 * Real.logb 2 (g : ℝ))
    (hι : hproof.ι = DensityOp (dA * dB))
    (hcond : hproof.condDim = M.condDim)
    (hraw : HEq hproof.rawKeyCQ M.rawKeyCQ)
    (href : HEq hproof.ref M.refCommon)
    (goodSet Pset : Set (DensityOp (dA * dB)))
    (hS : HEq hproof.S (goodSet ∩ Pset))
    (hClosed : IsClosed goodSet)
    (hP_closed : IsClosed Pset) (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ Pset)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ εAT)
    {S Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (H : InfoTheory.QuantumLHL.QuantumHashFamily S (Fin M.toProtocol.rawKeyDim) Z)
    (hH : H.isUniversal) (hcardZ : Fintype.card Z = 2 ^ l')
    (V : Matrix (Fin ((M.condDim * g) * Fintype.card (S × Z)))
                (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ)
    (hV' :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      Vᴴ * V *
          (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
            (deFinettiMixturePurification dA dB n μ).toOp) =
        mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
          (deFinettiMixturePurification dA dB n μ).toOp)
    (hPA_realization :
      haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
      haveI : NeZero ((M.condDim * g) * Fintype.card (S × Z)) :=
        ⟨Nat.mul_ne_zero (Nat.mul_ne_zero M.condDim_neZero.out hg.out)
          Fintype.card_ne_zero⟩
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      (seedKeyExtractorOutputState H ρ_EnV).toJointDensity.toOp -
          (seedUniformOutputState ρ_EnV.quantumMarginal).toJointDensity.toOp =
        V *
            (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
              (deFinettiMixturePurification dA dB n μ).toOp) * Vᴴ) :
    SatisfiesReferenceBound M.toProtocol l' μ (coherentIIDSecrecy εAT εPA εbar) := by
  have hεbar_nonneg := hproof.eq11.2.1
  have hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ Pset →
      (⨅ σ' : (goodSet ∩ Pset : Set (DensityOp (dA * dB))),
          smoothMinEntropy εbar (M.rawKeyCQ σ'.1) M.sigmaE) ≤
        smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE := by
    intro σ hσg hσp
    exact iInf_le (fun σ' : (goodSet ∩ Pset : Set (DensityOp (dA * dB))) =>
      smoothMinEntropy εbar (M.rawKeyCQ σ'.1) M.sigmaE) ⟨σ, hσg, hσp⟩
  obtain ⟨ι, Sσhat, S', pAcc, condTraceDist, condDim, condDim_neZero, rawKeyCQ, ref, eq10,
    eq11⟩ := hproof
  subst hι
  subst hcond
  rw [heq_iff_eq] at hraw href hS
  subst hraw
  subst href
  subst hS
  have hmixDim : NeZero (M.condDim * g) :=
    ⟨Nat.mul_ne_zero M.condDim_neZero.out hg.out⟩
  have hmixRef : (M.sigmaE.tensorMaxMixed g).toOp.PosDef :=
    SubDensityOp.tensor_posDef M.sigmaE
      (DensityOp.toSubDensityOp (DensityOp.maxMixed g))
      M.sigmaE_posDef maxMixed_toSubDensityOp_posDef
  exact postselection_referenceBound_of_iidSecurityProof M.toProtocol μ εAT εPA εbar l' g
    ⟨DensityOp (dA * dB), Sσhat, goodSet ∩ Pset, pAcc, condTraceDist, M.condDim,
      M.condDim_neZero, M.rawKeyCQ, M.refCommon, eq10, eq11⟩
    hl' hmixDim ρ_EnV (M.sigmaE.tensorMaxMixed g)
    (M.registerExtendedMixtureFloor_le_add μ h_int g hg hcont goodSet hClosed Pset
      hP_closed hP_ae
      (⨅ σ : (goodSet ∩ Pset : Set (DensityOp (dA * dB))),
        smoothMinEntropy εbar (M.rawKeyCQ σ.1) M.sigmaE)
      εbar εAT hεbar_nonneg h_badBranch_traceNorm hf_smoothFloor ρ_EnV hblocks)
    (M.hLeftover_discharge μ (M.condDim * g) hmixDim ρ_EnV (M.sigmaE.tensorMaxMixed g)
      hmixRef εAT εbar hεbar_nonneg l' H hH hcardZ V hV' hPA_realization)

end InfoTheory.Postselection

end
