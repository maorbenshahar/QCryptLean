import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.B19Bridge
import QCryptLean.QKD.BB84.Engine.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SymAverageBound
import QCryptLean.QKD.BB84.Engine.Budgets
import QCryptLean.QKD.BB84.Completeness
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.BadBranchConcentration
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.InfoTheory.Postselection.ErrorVerificationCorrectness
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier

/-!
# CPTP preservation and the error-verification correctness leg for the announced-PE BB84 channels

Complete-positivity/trace-preservation facts for the announced-parameter-estimation BB84 channels
(`bb84SiftedPEAnnounceLinear`, `…EveVisible`, `bb84SymRealChannel`, `bb84SymIdealChannel`, built
from the LOCC sift `bb84SiftedRotation`, an Alice-hash/Bob-decode key pair, an announced
`2^leakEC` syndrome and an announced `ℓEV`-bit error-verification tag), the trace/accept-weight
bookkeeping lemmas that connect a channel's pass-output trace to the sifted local-PE accepted
weight, and the error-verification correctness bound: for every attack, input and
error-correction scheme, the joint Born mass that Alice's and Bob's reconciled key strings differ
*and* the protocol accepts is at most `2^(−ℓEV)`.

## Main definitions and results

* `bb84SiftedPEAnnounceLinear_isCPTP`, `bb84SiftedPEAnnounceLinearEveVisible_isCPTP` — appending the
  public permutation announcement (with or without retaining Eve) is CPTP.
* `bb84SymRealChannel_isCPTP`, `bb84SymIdealChannel_isCPTP` — the symmetrized real/ideal channels
  are CPTP, proved without naming an attack object.
* `bb84SymChannels_preserves_conjTranspose` — their difference preserves the conjugate transpose
  (both arms completely positive), the `hΔ_conj` hypothesis `ckr_security_reduction_exact` needs.
* `bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum`,
  `bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_sum_marginalBlocks`,
  `bb84SiftedPEAndEVGated_le_PEGated` — trace bookkeeping connecting a pass channel's accept-gated
  output trace to the τ-side accepted weight.
* `bb84SiftedEveVisible_differAndAcceptWeight` — the joint Born mass that the reconciled key strings
  differ and the protocol accepts.
* `bb84_differAndAccept_weight_le_two_pow_neg_lEV` — that mass is at most `2^(−ℓEV)`, from the
  universality of the announced key-hash family
(`errorVerification_outcome_joint_correctness_of_universal`
  fed `aliceKeyHashFamily_isUniversal`).  Stated jointly: the conditional statement is false
  (`InfoTheory.Postselection.ErrorVerification.conditional_correctness_fails`), so the charge must
  enter a budget additively.  The operator lift of this bound to the trace norm of the
  differ-and-accept block of the real/ideal channel difference is
  `bb84SiftedPEAnnounceEveVisible_differBlock_ckrTensorTraceNorm_le_two_pow_neg_lEV`
  (`InnerBudgetCorrectness.lean`).

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Thm 3, App. B, the correctness
event `Pr[S_A ≠ S_B ∧ accept]` of §V.C; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5;
Christandl-König-Renner 2009 (`arXiv:0809.3019`) `main.tex:268`–`:401` (Main Result: Theorem
`\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-!
### CPTP facts for the bare (attack-free) channels, at a general test-set size `m`

The bare channels `bb84SymRealChannel` / `bb84SymIdealChannel` (`SiftedPEAnnounce.lean`) name no
attack object in their statements, and the proofs below name none either: the permutation average
is assembled from `bb84UnitRegisterEmbed_isCPTP`, and the retained-Eve slot is the literal `1`.

The announced PE register is a spectator throughout — the announcement map appends the `n!` register
to whatever the base output is, and the average is taken over an abstract CPTP base map — so no
constraint relating `m` to `n` arises here.
-/

/-- Appending the public permutation announcement to the general-`m` enlarged base output is
    CPTP. -/
theorem bb84SiftedPEAnnounceLinear_isCPTP (n m ℓ ℓEV : ℕ) [NeZero n] (peSel : Fin n → Bool)
    (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    IsCPTP (⇑(bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm)) := by
  let baseDim := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC
  let idx : Fin n.factorial :=
    (Fintype.equivFin (Equiv.Perm (Fin n)) perm).cast (by simp [Fintype.card_perm])
  have : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  have : NeZero (baseDim * n.factorial) :=
    ⟨Nat.mul_ne_zero (NeZero.ne baseDim) (Nat.factorial_ne_zero n)⟩
  let hdim : baseDim * n.factorial =
      2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC :=
    bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC
  have happend :
      IsCPTP (⇑(appendKetLinear (d := baseDim) (stdKet n.factorial idx))) :=
    appendKetLinear_isCPTP (d := baseDim) (stdKet n.factorial idx)
      (stdKet_braket_self idx)
  have hcast : IsCPTP (⇑(Op.castDimLinear hdim)) :=
    castDimLinear_isCPTP hdim
  exact cptp_comp (⇑(Op.castDimLinear hdim))
    (⇑(appendKetLinear (d := baseDim) (stdKet n.factorial idx))) hcast happend

/-- Appending the public permutation announcement while retaining Eve is CPTP at a general test-set
    size `m`. -/
theorem bb84SiftedPEAnnounceLinearEveVisible_isCPTP (n m ℓ ℓEV eveDim : ℕ) [NeZero n]
    [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    IsCPTP (⇑(bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC perm)) := by
  have : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
    bb84PEAnnounceBaseOutputDim_neZero n m ℓ ℓEV peSel leakEC
  have : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  simpa [bb84SiftedPEAnnounceLinearEveVisible, mapTensorIdLinear] using
    (mapTensorId_isCPTP
      (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm)
      (bb84SiftedPEAnnounceLinear_isCPTP n m ℓ ℓEV peSel leakEC perm))

/-- A uniform permutation average of general-`m` announce-composed **bare** direct-channel summands
    is CPTP, at an abstract CPTP base protocol map `base`. -/
private theorem announce_PEAnnounce_bare_average_isCPTP (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (base : Op (4 ^ n * 1) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC 1))
    (hbase : IsCPTP (⇑base)) :
    IsCPTP (⇑((1 / (n.factorial : ℂ)) •
      ∑ π : Equiv.Perm (Fin n),
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
          (base.comp (((bb84SiftedConjChannel n 1 peSel xSel).comp
            (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π))))) := by
  have : NeZero (4 ^ n * 1) := ⟨by simp⟩
  let Φ : Equiv.Perm (Fin n) → Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC 1) :=
    fun π =>
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
        (base.comp (((bb84SiftedConjChannel n 1 peSel xSel).comp
          (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π)))
  have hΦ : ∀ π, IsCPTP (⇑(Φ π)) := by
    intro π
    have hembed : IsCPTP (⇑((bb84SiftedConjChannel n 1 peSel xSel).comp
        (bb84UnitRegisterEmbed n))) := by
      exact cptp_comp (⇑(bb84SiftedConjChannel n 1 peSel xSel)) (⇑(bb84UnitRegisterEmbed n))
          (bb84SiftedConjChannel_isCPTP n 1 peSel xSel)
          (bb84UnitRegisterEmbed_isCPTP n)
    have hinner : IsCPTP (⇑(((bb84SiftedConjChannel n 1 peSel xSel).comp
        (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π))) := by
      exact cptp_comp (⇑((bb84SiftedConjChannel n 1 peSel xSel).comp (bb84UnitRegisterEmbed n)))
          (⇑(permuteSignalLinear n π)) hembed (permuteSignalLinear_isCPTP n π)
    have hbaseinner : IsCPTP (⇑(base.comp (((bb84SiftedConjChannel n 1 peSel xSel).comp
        (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π)))) := by
      exact cptp_comp (⇑base) (⇑(((bb84SiftedConjChannel n 1 peSel xSel).comp
          (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π))) hbase hinner
    exact cptp_comp (⇑(bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π))
        (⇑(base.comp (((bb84SiftedConjChannel n 1 peSel xSel).comp
          (bb84UnitRegisterEmbed n)).comp (permuteSignalLinear n π))))
        (bb84SiftedPEAnnounceLinearEveVisible_isCPTP n m ℓ ℓEV 1 peSel leakEC π) hbaseinner
  have hmix := cptp_uniformAverage (κ := Equiv.Perm (Fin n)) Φ hΦ
  change IsCPTP (⇑((1 / (n.factorial : ℂ)) • ∑ π : Equiv.Perm (Fin n), Φ π))
  rw [one_div]
  simp only [Fintype.card_perm, Fintype.card_fin, Complex.ofReal_natCast] at hmix
  exact hmix

/-- **The bare general-`m` symmetrized real channel is CPTP** — proved without naming an attack
    object. -/
theorem bb84SymRealChannel_isCPTP (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    IsCPTP (⇑(bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec)) := by
  have : NeZero (4 ^ n * 1) := ⟨by simp⟩
  unfold bb84SymRealChannel
  refine announce_PEAnnounce_bare_average_isCPTP n m ℓ ℓEV peSel xSel leakEC
    ((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
      δ).realProtocolMap (eveDim := 1)) ?_
  have h := cptp_comp
    (⇑(bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV 1 peSel xSel
      leakEC ec δ Q))
    (⇑(measurementChannel n 1))
    (bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap_isCPTP n m ℓ ℓEV 1 peSel
      xSel leakEC ec δ Q)
    (measurementChannel_isCPTP n 1)
  simpa [bb84SiftedPEAnnounceEveVisibleProtocol] using h

/-- **The bare general-`m` symmetrized ideal channel is CPTP** — proved without naming an attack
    object. -/
theorem bb84SymIdealChannel_isCPTP (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    IsCPTP (⇑(bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec)) := by
  have : NeZero (4 ^ n * 1) := ⟨by simp⟩
  unfold bb84SymIdealChannel
  refine announce_PEAnnounce_bare_average_isCPTP n m ℓ ℓEV peSel xSel leakEC
    ((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
      δ).idealProtocolMap (eveDim := 1)) ?_
  have h := cptp_comp
    (⇑(bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV 1 peSel xSel leakEC ec
      δ Q))
    (⇑(measurementChannel n 1))
    (bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel_isCPTP n m ℓ ℓEV 1 peSel xSel leakEC
      ec δ Q)
    (measurementChannel_isCPTP n 1)
  simpa [bb84SiftedPEAnnounceEveVisibleProtocol] using h

/-- **The bare general-`m` real/ideal difference preserves the conjugate transpose** (both arms CP)
    — the attack-free `hΔ_conj` supplier at a general test-set size `m`, and the second of the two
    bare-channel inputs `ckr_security_reduction_exact` requires.  Proved without naming an attack
    object. -/
theorem bb84SymChannels_preserves_conjTranspose (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    ∀ M : Op (4 ^ n),
      (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) M.conjTranspose =
        ((bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) M).conjTranspose :=
  cp_linear_sub_preserves_conjTranspose
    (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymRealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec).2.1
    (bb84SymIdealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec).2.1

/-!
### The pass channels and the accept-gated trace formula

The accept gate is `PE ∧ EV` (`bb84SiftedLocalPEAndEVPassed`), strictly stronger than the PE-only
test `bb84SiftedLocalPETestPassed` that the accepted-weight functional
`bb84SiftedEveVisible_tauLocalPEAcceptedWeight` reads.  Accepting implies PE-passing
(`bb84SiftedLocalPEAndEVPassed_imp_PETestPassed`) and every block is positive, so a pass channel's
accept-gated output trace is bounded by the PE-gated accepted weight.

The pass-output trace is computed from the scaled `∑ KᴴK` collapse: for a single-entry Kraus
operator the whole output index cancels in `KᴴK`, leaving the input-outcome projector, so the trace
reads exactly the accept-gated diagonal blocks of the sifted attack output.
-/

/-- `Tr(|i⟩⟨i| · A) = A i i`. -/
lemma trace_single_diag_mul {N : ℕ} (i : Fin N) (A : Op N) :
    ((Matrix.single i i (1 : ℂ)) * A).trace = A i i := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- The outcome-`ω` diagonal projector traced against a measured operator reads the corresponding
    diagonal block of the *pre*-measurement operator (the measurement channel is the identity on
    diagonal outcome/Eve entries, `measurementChannel_diag_apply`). -/
lemma trace_outcomeProjector_mul_measurementChannel (n eveDim : ℕ) [NeZero eveDim]
    (M : Op (4 ^ n * eveDim)) (ω : Fin n → Fin signalDim) :
    ((∑ r : Fin eveDim,
        Matrix.single (finProdFinEquiv (finFunctionFinEquiv ω, r))
          (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)) *
      measurementChannel n eveDim M).trace =
      ∑ r : Fin eveDim,
        M (finProdFinEquiv (bb84OutcomeIndex ω, r)) (finProdFinEquiv (bb84OutcomeIndex ω, r)) := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [trace_single_diag_mul]
  exact measurementChannel_diag_apply n eveDim M (bb84OutcomeIndex ω) r

/-- The sift-after-pre channel applied to a density operator is the sifted rotated pre-channel
    output. -/
lemma bb84SiftedConjAfterPre_apply_densityOp {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n)) :
    bb84SiftedConjAfterPre eveDim pre peSel xSel ρ.toOp =
      (bb84SiftedRotatedPreOutput eveDim pre hpre peSel xSel ρ).toOp := by
  rw [bb84SiftedConjAfterPre, LinearMap.comp_apply]
  simp [bb84SiftedConjChannel, krausMapFintype, bb84SiftedRotatedPreOutput,
    densityOpUnitaryConj_toOp, Op.tensor_conjTranspose]

/-- The measured LOCC sift-after-pre channel is completely positive (both factors are CPTP). -/
theorem bb84SiftedMeasAfterPre_isCompletelyPositive {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) :
    IsCompletelyPositive (⇑((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))) := by
  have h := Quantum.Channels.isCompletelyPositive_comp
    (⇑(measurementChannel n eveDim))
    (⇑(bb84SiftedConjAfterPre eveDim pre peSel xSel))
    (measurementChannel_isCPTP n eveDim).2.1
    (bb84SiftedConjAfterPre_isCPTP eveDim pre hpre peSel xSel).2.1
    (measurementChannel_isCPTP n eveDim).1
  simpa [LinearMap.comp_apply, Function.comp_apply] using h

/-- **The accept-gated pass-output trace formula.**  For any Kraus family whose adjoint products
    collapse onto the gate-indicated input-outcome projectors — which is what a single-entry Kraus
    operator does, the whole output index cancelling
    (`bb84.retainedSiftedPEAnnounce{Pass,IdealPass}…Kraus_adjoint_mul`) — the trace of the
    `mapTensorId`-extended scaled pass channel at the reference state `τ` is the `c`-scaled
    gate-indicated sum of the diagonal blocks of the sifted attack output on the attacked CKR
    marginal `τ.partialTraceB`.

    Both the real and the ideal pass channel instantiate it; the differences are the index type
    `κ`, the scale `c`, and how the gate reads `κ`. -/
lemma bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {outDim : ℕ} [NeZero outDim]
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin outDim) (Fin (4 ^ n * eveDim)) ℂ)
    (c : ℂ) (gate : κ → Bool) (ωof : κ → (Fin n → Fin signalDim))
    (hKK : ∀ k : κ, (K k)ᴴ * K k =
      if gate k then
        ∑ r : Fin eveDim,
          Matrix.single (finProdFinEquiv (finFunctionFinEquiv (ωof k), r))
            (finProdFinEquiv (finFunctionFinEquiv (ωof k), r)) (1 : ℂ)
      else 0)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (mapTensorId ((c • krausMapFintype K).comp
      ((measurementChannel n eveDim).comp
        (bb84SiftedConjAfterPre eveDim pre peSel xSel))) τ.toOp).trace =
      c * ∑ k : κ, (if gate k then
        (((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB (ωof k)).trace : ℝ) :
            ℂ)
        else 0) := by
  rw [trace_mapTensorId, LinearMap.comp_apply, LinearMap.comp_apply,
    show partialTraceB τ.toOp = τ.partialTraceB.toOp from rfl,
    bb84SiftedConjAfterPre_apply_densityOp eveDim pre hpre peSel xSel τ.partialTraceB,
    LinearMap.smul_apply, Matrix.trace_smul, smul_eq_mul, krausMapFintype_trace_eq]
  congr 1
  rw [Finset.sum_congr rfl (fun k _ => hKK k), Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : gate k = true
  · rw [ite_eq_left h, ite_eq_left h, trace_outcomeProjector_mul_measurementChannel]
    have hblk :
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB (ωof k)).toOp).trace =
          ∑ r : Fin eveDim,
            (bb84SiftedRotatedPreOutput eveDim pre hpre peSel xSel τ.partialTraceB).toOp
              (finProdFinEquiv (bb84OutcomeIndex (ωof k), r))
              (finProdFinEquiv (bb84OutcomeIndex (ωof k), r)) := by
      simp [bb84SiftedEveConditioned, Matrix.trace, bb84OutcomeEveEmbedding]
    rw [← hblk, SubDensityOp.trace_complex_eq]
  · rw [ite_eq_right h, ite_eq_right h]
    simp

/-- **The τ-side accept weight is the PE-filtered sum of the attacked-marginal blocks.**  Tracing
    out the CKR reference commutes with the fail-closed pass filter, by the τ partial-trace bridges
    of `SiftedPassSupport.lean`. -/
theorem bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_sum_marginalBlocks
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ =
      ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
          (bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace else 0) :=
              by
  have : NeZero (eveDim * dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  simp only [bb84SiftedEveVisible_tauLocalPEAcceptedWeight,
    bb84PostMeasurementCQSiftedLocalPEPassFilter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true
  · rw [ite_eq_left h, ite_eq_left h]
    change (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).trace = _
    unfold SubDensityOp.trace
    rw [← trace_partialTraceB (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ ω).toOp,
      bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned]
  · rw [ite_eq_right h, ite_eq_right h]
    show SubDensityOp.trace (0 : SubDensityOp (eveDim * dimR)) = 0
    simp [SubDensityOp.trace]

/-- **Termwise accept-gate shrinkage.**  Each accept-gated block weight is at most the corresponding
    PE-gated one, because accepting implies PE-passing
    (`bb84SiftedLocalPEAndEVPassed_imp_PETestPassed`) and the blocks are positive. -/
lemma bb84SiftedPEAndEVGated_le_PEGated {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (ℓEV : ℕ) (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ) (ρ : DensityOp (4 ^ n))
    (t : KeyHashSeed n ℓEV peSel) (ω : Fin n → Fin signalDim) :
    (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
        (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace else 0) ≤
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
        (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace else 0) := by
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true
  · rw [ite_eq_left h,
      ite_eq_left (bb84SiftedLocalPEAndEVPassed_imp_PETestPassed ℓEV peSel xSel ec δ Q t ω h)]
  · rw [ite_eq_right h]
    split_ifs
    · exact (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace_nonneg
    · exact le_refl 0

/-!
### The correctness leg: the joint differ-and-accept mass
-/

/-- **The differ-and-accept weight**: the total Born mass, averaged uniformly over the announced
    error-verification seed, of the event

      "Alice's key string differs from Bob's reconciled key string AND the protocol accepts".

    This is the explicit protocol-level realization of the composable *correctness* event
    `Pr[S_A ≠ S_B ∧ accept]` of Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C.
    The per-outcome weight is the trace of the outcome-conditioned Eve block
    `bb84SiftedEveConditioned` — the Born weight of the round-outcome string `ω` after the LOCC
    sift and the attack — and the accept predicate is the channels' own gate
    `bb84SiftedLocalPEAndEVPassed`.

    Only the error-verification seed is averaged: the differ event and the accept gate are both
    independent of the privacy-amplification seed, so averaging over the full announced pair
    `KeyHashSeedPairEV` would give the same number.

    **Stated jointly, never conditionally.**  The conditional form `Pr[differ | accept]` is NOT
    bounded by `2^(−ℓEV)` —
    `InfoTheory.Postselection.ErrorVerification.conditional_correctness_fails` proves an instance
    where it equals `1` — so this charge must enter a security budget additively, not
    conditionally. -/
noncomputable def bb84SiftedEveVisible_differAndAcceptWeight {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre) (ℓEV : ℕ)
        (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) (ρ : DensityOp (4 ^ n)) : ℝ :=
  (1 / (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ)) *
    ∑ t : KeyHashSeed n ℓEV peSel, ∑ ω : Fin n → Fin signalDim,
      (if aliceKeyString peSel ω ≠
            ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) ∧
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true
        then (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace
        else 0)

open InfoTheory.Postselection.ErrorVerification in
/-- **The error-verification correctness bound**: for every attack, every input state and every
    error-correction scheme, the joint mass of "the key strings differ and the protocol accepts" is
    at most `2^(−ℓEV)`.  Nothing here constrains `ec`: the bound holds for an arbitrary decoder,
    because the accept gate compares Alice's announced `ℓEV`-bit tag with the tag of whatever
    string Bob's decoder produced.

    The proof route:
    1.  On the differ event, `evVerified ℓEV peSel ec t ω = true` is exactly the tag-collision
        event of the pair `(aliceKeyString ω, ec.decode (bobKeyString ω) (ec.syndrome …))`, and the
        PE conjunct is seed-free; so the accept gate factors as
        `bb84SiftedLocalPETestPassed … ω && decide (hash t a = hash t b)` definitionally.
    2.  The seed average of the collision indicator against any sub-normalised outcome weight is
`errorVerification_outcome_joint_correctness_of_universal`,
        the outcome-indexed form of `errorVerification_joint_correctness_indexed` (it groups the
        outcomes into key pairs and applies that lemma at the induced pair law, whose sub-normalised
        hypotheses `(hp_nonneg) (hp_total : ∑ p ≤ 1)` the accept-branch weight supplies — its
        deficit is the abort mass).
    3.  Its universality hypothesis is discharged verbatim by
        `aliceKeyHashFamily_isUniversal n ℓEV peSel` (`KeyHashEC.lean`), which is an EXACT
        per-row halving, so `δ = 1/|Fin (2^ℓEV)| = 2^(−ℓEV)` is attained rather than merely bounded.
    4.  Sub-normalisation of the ω-weights is
        `bb84SiftedPostMeasurementCQState_weight_eq_one` (they sum to `1`), and nonnegativity is
        `SubDensityOp.trace_nonneg`.

    **Scope: this is the scalar (mass) leg; the operator lift is**
    `bb84SiftedPEAnnounceEveVisible_differBlock_ckrTensorTraceNorm_le_two_pow_neg_lEV`
    (`InnerBudgetCorrectness.lean`), which charges the mass to the trace norm of the
    differ-and-accept block of the real/ideal channel difference.  Because this scalar statement
    quantifies over an arbitrary input density operator, the lift instantiates it at the attacked
    CKR marginal `τ.partialTraceB`; no τ-side (reference-carrying) twin of it is needed. -/
theorem bb84_differAndAccept_weight_le_two_pow_neg_lEV {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre) (ℓEV : ℕ)
        (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) (ρ : DensityOp (4 ^ n)) :
    bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ ρ ≤
      (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  have : NeZero (2 ^ ℓEV) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : Nonempty (Fin (2 ^ ℓEV)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ ℓEV))⟩⟩
  have hkey :=
    errorVerification_outcome_joint_correctness_of_universal
      (S := KeyBitString n peSel) (T := Fin (2 ^ ℓEV))
      (Sd := KeyHashSeed n ℓEV peSel) (Ω := Fin n → Fin signalDim)
      (aliceKeyHashFamily n ℓEV peSel).hash
      (aliceKeyHashFamily_isUniversal n ℓEV peSel)
      (fun ω => aliceKeyString peSel ω)
      (fun ω => ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω)))
      (fun ω => bb84SiftedLocalPETestPassed peSel xSel δ Q ω)
      (fun ω => (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace)
      (fun ω => SubDensityOp.trace_nonneg _)
      (bb84SiftedPostMeasurementCQState_weight_eq_one eveDim pre hpre peSel xSel ρ).le
  have hcard : (1 : ℝ) / (Fintype.card (Fin (2 ^ ℓEV)) : ℝ) = (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
    rw [Fintype.card_fin, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast
    ring
  rw [hcard] at hkey
  simp only [bb84SiftedEveVisible_differAndAcceptWeight, bb84SiftedLocalPEAndEVPassed,
    evVerified, verificationTag]
  exact hkey

/-!
### The operator form of the correctness leg

The scalar bound above is a statement about Born masses; the security budget must charge an
OPERATOR — the differ-and-accept block of the real/ideal channel difference on
(Eve ⊗ reference).  The lift (`InnerBudgetCorrectness.lean`) specialises the accept-gated trace
formula `bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum` above to the differ-restricted
gate: split the pass Kraus families (real and ideal) into their agree and differ sub-families,
apply that formula at the gate `differ ∧ (PE ∧ EV)`, and read off the differ-and-accept weight
exactly.  Both blocks are then PSD (both arms are CP), so the PSD⇒trace bridge
`Quantum.Channels.traceNorm_posSemidef_eq_trace` turns each trace norm into a trace, and
`Quantum.Metrics.traceNorm_sub_le` supplies the factor 2 — real mass plus ideal mass on the same
event.

Everything stays joint. The conditional form `Pr[differ | accept]` is proved false in
`QCryptLean/InfoTheory/Postselection/ErrorVerificationCorrectness.lean`
(`conditional_correctness_fails`, the arXiv:2502.10340 §5.4.6 p. 27 attack), so the charge enters a
security budget additively.

The Bell rotation is nowhere on this route: every object here is conjugated by the LOCC sift
`bb84SiftedRotation`, and the only property of the conjugator that is used is that
`bb84SiftedConjAfterPre` is CPTP (`bb84SiftedConjAfterPre_isCPTP`).  In particular
the accept-gated trace formula reads only the single-entry Kraus adjoint collapse
(`bb84.retainedSiftedPEAnnounce{Pass,IdealPass}Kraus_adjoint_mul`), which is a statement about the
transcript index, not about the sift.
-/

/-- Kraus-level split of a family into two sub-families that partition it termwise. -/
lemma krausMapFintype_split {N M : ℕ} {κ : Type*} [Fintype κ]
    (K Ka Kd : κ → Matrix (Fin M) (Fin N) ℂ)
    (h : ∀ (k : κ) (A : Op N), K k * A * (K k)ᴴ = Ka k * A * (Ka k)ᴴ + Kd k * A * (Kd k)ᴴ) :
    krausMapFintype K = krausMapFintype Ka + krausMapFintype Kd := by
  ext A i j
  simp only [LinearMap.add_apply, Matrix.add_apply]
  change (∑ k, K k * A * (K k)ᴴ) i j =
    (∑ k, Ka k * A * (Ka k)ᴴ) i j + (∑ k, Kd k * A * (Kd k)ᴴ) i j
  simp only [Matrix.sum_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [h k A]; rfl)

/-- A sum over `Ω × A × B` whose summand reads only the `(B, Ω)` factors factors through
    `Fintype.card A`. -/
lemma sumProd3_eq {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B] (F : B → Ω → ℝ) :
    ∑ k : Ω × A × B, F k.2.2 k.1 = (Fintype.card A : ℝ) * ∑ b : B, ∑ ω : Ω, F b ω := by
  classical
  simp only [Fintype.sum_prod_type_right]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]

/-- The `Bool` differ-and-accept gate agrees with the `Prop` conjunction the scalar weight
    functional uses. -/
lemma differAndAcceptGate_ite {n : ℕ} (ℓEV : ℕ) (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (t : KeyHashSeed n ℓEV peSel)
    (ω : Fin n → Fin signalDim) (x : ℝ) :
    (if bb84SiftedKeyStringsDiffer peSel ec ω &&
        bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then x else 0) =
      (if aliceKeyString peSel ω ≠
            ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) ∧
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true then x else 0) :=
  if_congr (by simp [bb84SiftedKeyStringsDiffer]) rfl rfl

/-- The error-verification-seed sum of the differ-and-accept gated block weights is the seed
    cardinality times the differ-and-accept weight (of which it is the uniform average). -/
lemma differGatedTSum_eq {n : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (ρ : DensityOp (4 ^ n)) :
    ∑ t : KeyHashSeed n ℓEV peSel, ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedKeyStringsDiffer peSel ec ω &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace : ℝ) else 0) =
      (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ) *
        bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ ρ := by
  have hT : (0 : ℝ) < (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [bb84SiftedEveVisible_differAndAcceptWeight]
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl
    (fun ω _ => differAndAcceptGate_ite ℓEV peSel xSel ec δ Q t ω _))]
  field_simp

/-- The seed-PAIR sum of the differ-and-accept gated block weights is the seed-pair cardinality
    times the differ-and-accept weight: the privacy-amplification seed is a spectator. -/
lemma differGatedSum_eq {n : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓ ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (ρ : DensityOp (4 ^ n)) :
    ∑ _s : KeyHashSeed n ℓ peSel, ∑ t : KeyHashSeed n ℓEV peSel,
        ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedKeyStringsDiffer peSel ec ω &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace : ℝ) else 0) =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ) *
        bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ ρ := by
  rw [Finset.sum_congr rfl (fun _ _ => differGatedTSum_eq ℓEV eveDim pre hpre peSel xSel ec Q δ ρ),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod]
  push_cast
  ring

end QKD.BB84.Engine

end -- noncomputable section
