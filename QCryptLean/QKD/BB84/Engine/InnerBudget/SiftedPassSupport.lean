import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.Quantum.Channels.CPTP.CKRBound.OffLabelBlocks
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.CastHelpers
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.Quantum.Symmetry.AttackSymmetrization
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQTrace
import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SupportPreservation

/-!
# The genuine-LOCC accept-weight stack: τ-side objects, transcript-free weight, dichotomy

The τ-side accept-weight stack for the genuine-LOCC BB84 channels. Every declaration here reads
the fail-closed LOCC two-basis accept event: the test `bb84SiftedLocalPETestPassed` (two disjoint
subsamples, each of size `≈ n/4` at the canonical selectors) evaluated after the local `H ⊗ H`
sift `bb84SiftedRotation`.

The real/ideal difference channel (`SiftedPEAnnounce.lean`) is supported on this accept event, so
the functionals here are keyed on the **PE-only** test `bb84SiftedLocalPETestPassed`. The channels'
own accept gate is `PE ∧ EV` (error verification); accepting there implies PE-passing here
(`bb84SiftedLocalPEAndEVPassed_imp_PETestPassed`), so the gated event sits inside the PE-only event
and bounds stated against these functionals cover the channels' accept event.

## Main definitions

* `bb84SiftedTauPreOutputDensity`, `bb84SiftedTauEveRefConditioned`,
  `bb84SiftedTauPostMeasurementNormalizedCQState` — the τ-side post-measurement objects.
* `bb84SiftedEveVisible_tauLocalPEAcceptedWeight` — the τ-side local-PE-pass-filtered weight.
* `bb84CKRPostselectionSiftedLocalPEAcceptedWeight` — the transcript-free accept weight of the
  CKR de Finetti mixture.

## Main results

* `bb84SiftedTauPreOutputDensity_partialTraceB_eq`,
  `bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned`(`_ckr`),
  `bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq` — the τ partial-trace
  bridges: the sift conjugation acts on the Alice–Bob register only, disjoint from the traced-out
  CKR reference.
* `bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_localPEAcceptedWeight` — the τ-side
  local-PE-pass weight equals the transcript-free accept weight at a CKR purification.


## References

Renner (2005) `arXiv:quant-ph/0512258v2` §5, §6.5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024)
`arXiv:2403.11851` §B, Thm 3; Christandl–König–Mitchison–Renner (2007) Thm II.7 (postselection).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
## τ-side trailing-factor embedding bridge
-/

/-- The `τ`-Eve-reference embedding commutes with the trailing-factor reassociation cast:
embedding into `dimR = d1 * d2` after reassociating and tracing the trailing `d2` factor
agrees with embedding into the surviving inner reference `d1`. -/
private lemma bb84TauOutcomeEveRefEmbedding_cast_index
    {n eveDim d1 d2 : ℕ} (ωIdx : Fin (4 ^ n)) (A : Fin (eveDim * d1)) (k : Fin d2) :
    bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1 * d2) ωIdx
        (Fin.cast (Nat.mul_assoc eveDim d1 d2) (finProdFinEquiv (A, k))) =
      Fin.cast (Nat.mul_assoc (4 ^ n * eveDim) d1 d2)
        (finProdFinEquiv
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1) ωIdx A, k)) := by
  obtain ⟨⟨a, x⟩, rfl⟩ : ∃ p, finProdFinEquiv p = A := ⟨_, finProdFinEquiv.apply_symm_apply A⟩
  rw [finProdFinEquiv_cast_assoc, bb84TauOutcomeEveRefEmbedding_finProd,
    bb84TauOutcomeEveRefEmbedding_finProd, finProdFinEquiv_cast_assoc]

/-- **Trailing-factor `partialTraceB` / τ-embedding bridge.**  Tracing out only the trailing
`d2` factor of the reference `dimR = d1 * d2` (after the reassociation cast) commutes with
extracting the τ-Eve-reference block, the inner `d1` factor becoming the new reference slot.
The trailing-factor mirror of `bb84Sifted_partialTraceB_submatrix_tauEmbedding`. -/
lemma bb84Sifted_partialTraceB_trailing_submatrix_tauEmbedding
    {n eveDim d1 d2 : ℕ} (M : Op ((4 ^ n * eveDim) * (d1 * d2))) (ωIdx : Fin (4 ^ n)) :
    partialTraceB ((Nat.mul_assoc eveDim d1 d2).symm ▸ M.submatrix
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1 * d2) ωIdx)
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1 * d2) ωIdx)) =
      (partialTraceB ((Nat.mul_assoc (4 ^ n * eveDim) d1 d2).symm ▸ M)).submatrix
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1) ωIdx)
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := d1) ωIdx) := by
  ext A B
  simp only [partialTraceB, Matrix.submatrix_apply, Matrix.of_apply, matrix_eqRec_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bb84TauOutcomeEveRefEmbedding_cast_index, bb84TauOutcomeEveRefEmbedding_cast_index]

/-! ## The τ-side post-measurement CQ state and accept weight -/

/-- **The sifted τ-side output density of a CPTP pre-channel.**

`((bb84SiftedRotation peSel xSel ⊗ 1_E) ⊗ 1_R) · bb84TauOutputDensity · (…)†`, a genuine
density operator because the conjugating operator is unitary
(`bb84SiftedRotation_tensor_one_unitary`).  Reading its computational-basis outcome/Eve/reference
blocks reads the X-test rounds in the `H ⊗ H`-rotated frame and every other round in the
computational `Z` basis.

Indexed by a bare retained-Eve dimension `eveDim` and an opaque CPTP pre-channel `pre` rather than
by an attack object: the attack instance is `eveDim := atk.eveDim`, `pre := attackChannelLinear
atk`, `hpre := attackChannelLinear_isCPTP atk`. -/
noncomputable def bb84SiftedTauPreOutputDensity {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    DensityOp ((4 ^ n * eveDim) * dimR) :=
  densityOpUnitaryConj
    (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
      (1 : Op dimR))
    (by rw [Op.tensor_conjTranspose, Op.tensor_mul, bb84SiftedRotation_tensor_one_unitary,
            Matrix.conjTranspose_one, Matrix.one_mul, Op.tensor_one])
    (bb84TauOutputDensity eveDim pre hpre τ)

/-- **Eve plus CKR-reference sifted-outcome-conditioned sub-density.**

The `(ωIdx, ωIdx)`-diagonal `(eveDim · dimR) × (eveDim · dimR)` block of the sifted τ-side
output conditioned on the outcome string `ω`. -/
noncomputable def bb84SiftedTauEveRefConditioned {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (ω : Fin n → Fin signalDim) :
    SubDensityOp (eveDim * dimR) :=
  let σ := bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ
  let embed : Fin (eveDim * dimR) → Fin ((4 ^ n * eveDim) * dimR) :=
    bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) (bb84OutcomeIndex ω)
  { toOp := σ.toOp.submatrix embed embed
    isHermitian := densityOp_submatrix_isHermitian σ embed
    pos_semidef := densityOp_submatrix_pos_semidef σ embed
    trace_le_one := densityOp_submatrix_trace_le_one σ embed
      (bb84TauOutcomeEveRefEmbedding_injective (eveDim := eveDim) (dimR := dimR)
        (bb84OutcomeIndex ω)) }

/-- The τ-induced post-measurement CQ blocks have total weight one. -/
theorem bb84SiftedTauPostMeasurementCQState_weight_eq_one {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    ∑ ω : Fin n → Fin signalDim,
      (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).trace = 1 := by
  simpa only [bb84SiftedTauEveRefConditioned, SubDensityOp.trace,
    trace_re_submatrix_eq_sum_diag_re]
    using bb84TauOutcomeEveRefEmbedding_diag_sum_eq_one (n := n)
      (eveDim := eveDim) (dimR := dimR)
      (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ)

/-- **The τ-side post-measurement CQ state.** -/
noncomputable def bb84SiftedTauPostMeasurementNormalizedCQState {n : ℕ}
    [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    NormalizedCQState (Fin n → Fin signalDim) (eveDim * dimR) where
  stateMap := bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ
  weight_le_one :=
    (bb84SiftedTauPostMeasurementCQState_weight_eq_one eveDim pre hpre peSel xSel τ).le
  weight_eq_one := bb84SiftedTauPostMeasurementCQState_weight_eq_one eveDim pre hpre peSel xSel τ

/-- **The τ-side local-PE-pass-filtered weight.**  The total weight retained by the fail-closed
LOCC two-basis pass filter `bb84PostMeasurementCQSiftedLocalPEPassFilter` applied to the τ-side
post-measurement CQ state: the functional the channels' `ckrTensorTraceNorm` is bounded by. It is
keyed on the PE-only test, so a later `PE ∧ EV` accept gate only shrinks the filtered event. -/
noncomputable def bb84SiftedEveVisible_tauLocalPEAcceptedWeight
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) : ℝ :=
  haveI : NeZero (eveDim * dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  ∑ ω : Fin n → Fin signalDim,
    ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
      (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ :
        CQState (Fin n → Fin signalDim) (eveDim * dimR))).stateMap
        ω).trace

/-!
## τ partial-trace bridges

The `bb84SiftedRotation` conjugation acts only on the Alice–Bob register, disjoint from the CKR
reference `R` that `partialTraceB` traces out, so the partial-trace identities are the literal
unitary conjugates of their computational siblings (`partialTraceB_sandwich_tensor_one`,
`partialTraceB_mapTensorId`).
-/

/-- `partialTraceB` commutes with extracting a τ-Eve-reference block: the statement is about
indices only and mentions no rotation. -/
private lemma bb84Sifted_partialTraceB_submatrix_tauEmbedding
    {n eveDim dimR : ℕ} (M : Op ((4 ^ n * eveDim) * dimR)) (ωIdx : Fin (4 ^ n)) :
    partialTraceB (M.submatrix
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) ωIdx)
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) ωIdx)) =
      (partialTraceB M).submatrix
        (bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx)
        (bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx) := by
  ext a b
  simp only [partialTraceB, Matrix.of_apply, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bb84TauOutcomeEveRefEmbedding_finProd, bb84TauOutcomeEveRefEmbedding_finProd]

/-- **Full-level τ partial-trace identity.**  Tracing out the CKR reference register from the
sifted τ-side output recovers the sifted output of the pre-channelled marginal
`τ.partialTraceB`. -/
theorem bb84SiftedTauPreOutputDensity_partialTraceB_eq {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    partialTraceB (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ).toOp =
      (bb84SiftedRotatedPreOutput eveDim pre hpre peSel xSel τ.partialTraceB).toOp := by
  have hM : partialTraceB (bb84TauOutputDensity eveDim pre hpre τ).toOp =
      pre τ.partialTraceB.toOp := by
    rw [show (bb84TauOutputDensity eveDim pre hpre τ).toOp =
          mapTensorId pre τ.toOp from rfl, partialTraceB_mapTensorId]
    rfl
  simp only [bb84SiftedTauPreOutputDensity, densityOpUnitaryConj_toOp]
  rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one, partialTraceB_sandwich_tensor_one, hM]
  simp only [bb84SiftedRotatedPreOutput, densityOpUnitaryConj_toOp, cptpDensityOp_toOp]

/-- **Block-level τ partial-trace bridge.**  Tracing out the CKR reference from a sifted
τ-conditioned Eve–reference block recovers the ordinary sifted Eve block for the pre-channelled
marginal input `τ.partialTraceB`. -/
theorem bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (ω : Fin n → Fin signalDim) :
    partialTraceB (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).toOp =
      (bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).toOp := by
  rw [show (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).toOp =
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ).toOp.submatrix
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR)
            (bb84OutcomeIndex ω))
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR)
            (bb84OutcomeIndex ω)) from rfl,
    bb84Sifted_partialTraceB_submatrix_tauEmbedding,
    bb84SiftedTauPreOutputDensity_partialTraceB_eq]
  rfl

/-- CKR-specialized block bridge: the marginal identified by `hτ.marginal` is the CKR de Finetti
state. -/
theorem bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned_ckr
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (ω : Fin n → Fin signalDim) :
    partialTraceB (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).toOp =
      (bb84SiftedEveConditioned eveDim pre hpre peSel xSel
        (ckrDeFinettiState signalDim n) ω).toOp := by
  rw [← hτ.marginal]
  exact bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned
    eveDim pre hpre peSel xSel τ ω

/-- The fail-closed local-PE pass filter preserves a blockwise partial-trace identity. -/
theorem bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq
    {n dE dR : ℕ} [NeZero dE] [NeZero dR]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρER : CQState (Fin n → Fin signalDim) (dE * dR))
    (ρE : CQState (Fin n → Fin signalDim) dE)
    (hblocks : ∀ ω : Fin n → Fin signalDim,
      partialTraceB (ρER.stateMap ω).toOp = (ρE.stateMap ω).toOp)
    (ω : Fin n → Fin signalDim) :
    partialTraceB
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ ρER).stateMap ω).toOp =
      ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ ρE).stateMap ω).toOp := by
  simp only [bb84PostMeasurementCQSiftedLocalPEPassFilter]
  split_ifs with h
  · exact hblocks ω
  · show partialTraceB (0 : SubDensityOp (dE * dR)).toOp = (0 : SubDensityOp dE).toOp
    rw [show (0 : SubDensityOp (dE * dR)).toOp = 0 from rfl,
        show (0 : SubDensityOp dE).toOp = 0 from rfl]
    ext i j
    simp [partialTraceB]

/-- **PE-filtered τ blocks trace down to the corresponding accept blocks.** -/
theorem bb84_SiftedLocalPEAccepted_tau_postMeasurementCQState_stateMap_partialTraceB_eq
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    (μ : InfoTheory.DeFinetti.DensityMeasure signalDim)
    (hμ : InfoTheory.DeFinetti.integralTensorPower n μ =
      Quantum.Channels.ckrDeFinettiState signalDim n)
    (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (ω : Fin n → Fin signalDim) :
    partialTraceB
        (((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ :
            CQState (Fin n → Fin signalDim) (eveDim * dimR))).stateMap
            ω).toOp) =
      (((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel μ Q δ).stateMap
          ω).toOp) := by
  have hblocks : ∀ ω : Fin n → Fin signalDim,
      partialTraceB
          (((bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ :
            CQState (Fin n → Fin signalDim) (eveDim * dimR)).stateMap ω).toOp) =
        ((bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel
          (InfoTheory.DeFinetti.integralTensorPower n μ)).stateMap ω).toOp := by
    intro ω
    rw [hμ]
    exact bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned_ckr
      eveDim pre hpre peSel xSel τ hτ ω
  exact bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq
    peSel xSel Q δ _ _ hblocks ω

/-- **The τ-side local-PE-pass weight equals the accepted de Finetti weight.**

The proof is sift-agnostic: it commutes `partialTraceB` past the pass filter blockwise, using only
that the conjugating operator is a unitary on the Alice–Bob register, disjoint from the traced-out
CKR reference. -/
theorem bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_localPEAcceptedWeight
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    (μ : InfoTheory.DeFinetti.DensityMeasure signalDim)
    (hμ : InfoTheory.DeFinetti.integralTensorPower n μ =
      Quantum.Channels.ckrDeFinettiState signalDim n)
    (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ) :
    bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ =
      ∑ ω : Fin n → Fin signalDim,
        ((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel μ Q δ).stateMap
          ω).trace := by
  unfold bb84SiftedEveVisible_tauLocalPEAcceptedWeight
  apply Finset.sum_congr rfl
  intro ω _hω
  unfold SubDensityOp.trace
  rw [← trace_partialTraceB
    (((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
      (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ :
        CQState (Fin n → Fin signalDim) (eveDim * dimR))).stateMap
        ω).toOp)]
  rw [bb84_SiftedLocalPEAccepted_tau_postMeasurementCQState_stateMap_partialTraceB_eq
    eveDim pre hpre peSel xSel μ hμ Q δ τ hτ ω]

/-! ## The transcript-free accept weight -/

/-- The accept weight of the CKR de Finetti mixture for a retained-Eve attack: the total weight
of the physical accept CQ state `bb84SiftedLocalPEAcceptedPostMeasurementCQState` over the CKR
mixture.  Transcript-free (indexed by the outcome string only). -/
noncomputable def bb84CKRPostselectionSiftedLocalPEAcceptedWeight
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) : ℝ :=
  ∑ ω : Fin n → Fin signalDim,
    ((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel
        (Quantum.Channels.ckrMixtureMeasure signalDim) Q δ).stateMap ω).trace


end QKD.BB84.Engine

end -- noncomputable section
