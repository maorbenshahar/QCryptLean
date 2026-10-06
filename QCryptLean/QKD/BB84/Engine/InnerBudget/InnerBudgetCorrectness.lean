import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetPinned
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.InnerBudgetAgreeBlock

/-!
# The exact pass-block split and error-verification correctness

The real and ideal abort branches coincide. Their pass channels split exactly into agree and
differ outcomes according to the reconciled strings, including the ideal channel's fresh-key
outputs. The differ blocks have total trace norm at most `2 * 2^(-ℓEV)` on every input and
reference. This bound uses the universal verification hash and holds for every decoder.

The pass-channel positivity and trace estimates support the channel-level decomposition in
`PassBlocks.lean`; correctness is bounded before applying postselection to the agree block.

Reference: Nahar et al. 2024, arXiv:2403.11851, Section V.C and Appendix B.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
## The general-`m` differ pass Kraus families

Restrictions of the general-`m` pass Kraus families
`bb84.retainedSiftedPEAnnounce{PassBranch,IdealPass}Kraus` (`SiftedPEAnnounce.lean`) to the branch
where Alice's and Bob's key strings differ.  Their agree complements
`bb84RealPassAgreeKraus` / `bb84IdealPassAgreeKraus` live in `AgreeChannels.lean`.
-/

/-- **Differ-restricted general-`m` real pass Kraus family**: the general-`m` pass Kraus, zeroed
on the outcomes where Alice's and Bob's key strings agree. -/
def bb84RealPassDifferKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun k =>
    if bb84SiftedKeyStringsDiffer peSel ec k.2 then
      bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k
    else 0

/-- **Differ-restricted general-`m` ideal pass Kraus family.** -/
def bb84IdealPassDifferKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun k =>
    if bb84SiftedKeyStringsDiffer peSel ec k.1 then
      bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k
    else 0

/-- Adjoint product of a differ-restricted general-`m` real pass Kraus operator: the input-outcome
projector on the branch where the strings differ AND the full `PE ∧ EV` gate accepts.  The differ
conjunct passes straight through
`bb84.retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul`. -/
lemma bb84RealPassDifferKraus_adjoint_mul (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    (bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k)ᴴ *
        bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k =
      if bb84SiftedKeyStringsDiffer peSel ec k.2 &&
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
        ∑ r : Fin eveDim,
          Matrix.single (finProdFinEquiv (finFunctionFinEquiv k.2, r))
            (finProdFinEquiv (finFunctionFinEquiv k.2, r)) (1 : ℂ)
      else 0 := by
  by_cases h : bb84SiftedKeyStringsDiffer peSel ec k.2 = true
  · simp only [bb84RealPassDifferKraus, h, ite_true, Bool.true_and]
    exact bb84.retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q k.1 k.2
  · simp [bb84RealPassDifferKraus, h]

/-- Adjoint product of a differ-restricted general-`m` ideal pass Kraus operator. -/
lemma bb84IdealPassDifferKraus_adjoint_mul (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k)ᴴ *
        bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q k =
      if bb84SiftedKeyStringsDiffer peSel ec k.1 &&
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        ∑ r : Fin eveDim,
          Matrix.single (finProdFinEquiv (finFunctionFinEquiv k.1, r))
            (finProdFinEquiv (finFunctionFinEquiv k.1, r)) (1 : ℂ)
      else 0 := by
  by_cases h : bb84SiftedKeyStringsDiffer peSel ec k.1 = true
  · simp only [bb84IdealPassDifferKraus, h, ite_true, Bool.true_and]
    exact bb84.retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q k.1 k.2.1 k.2.2
  · simp [bb84IdealPassDifferKraus, h]

/-!
## The general-`m` base-scheme pass channels

The general-`m` mirrors of `bb84SiftedPEAnnounceEveVisible{Real,Ideal}PassChannel`
(`InnerBudgetPinned.lean`) restricted to the differ branch, with the binder shape of the
general-`m` agree channels (`InnerBudgetAgreeBlock.lean`).
-/

/-- **General-`m` base-scheme real DIFFER pass channel**: the accept branch of the general-`m`
real PA/abort map restricted to the outcomes where Alice's and Bob's key strings differ. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMapFintype (bb84RealPassDifferKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

/-- **General-`m` base-scheme ideal DIFFER pass channel.** -/
noncomputable def bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMapFintype (bb84IdealPassDifferKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

/-- **General-`m` base-scheme real pass channel**: the accept branch of the general-`m` real
PA/abort map (uniform seed-pair average) after the computational measurement and the LOCC attack
channel. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleRealPassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMapFintype (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

/-- **General-`m` base-scheme ideal pass channel**: the fresh-uniform-key accept branch of the
general-`m` ideal key/abort map. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleIdealPassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMapFintype (bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

/-- General-`m` base-scheme real pass output at the CKR reference state `τ`. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleRealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR) :=
  mapTensorId (bb84SiftedPEAnnounceEveVisibleRealPassChannel (m := m) ℓ ℓEV eveDim pre
    peSel xSel leakEC ec Q δ) τ.toOp

/-- General-`m` base-scheme ideal pass output at the CKR reference state `τ`. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleIdealPassOutput
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR) :=
  mapTensorId (bb84SiftedPEAnnounceEveVisibleIdealPassChannel (m := m) ℓ ℓEV eveDim pre
    peSel xSel leakEC ec Q δ) τ.toOp

/-- **The general-`m` base channels differ only by their pass branches** (the shared-fail-branch
cancellation, D5).  The general-`m` fail Kraus family is literally the same object in the real and
in the ideal map, at the same seed-pair scale, so it cancels in the difference. -/
theorem bb84SiftedPEAnnounceEveVisible_baseChannel_real_sub_ideal_eq_passBranch_sub
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
        (eveDim := eveDim) -
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).idealProtocolMap
        (eveDim := eveDim)).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel)) =
      bb84SiftedPEAnnounceEveVisibleRealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
          ec Q δ -
        bb84SiftedPEAnnounceEveVisibleIdealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
            leakEC ec Q δ := by
  simp only [bb84SiftedPEAnnounceEveVisibleProtocol,
    bb84SiftedPEAnnounceEveVisibleRealPassChannel,
    bb84SiftedPEAnnounceEveVisibleIdealPassChannel,
    bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap,
    bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel]
  ext M i j
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Matrix.sub_apply]
  change ((_ : ℂ) + _) - (_ + _) = _ - _
  abel

/-- The general-`m` real pass channel is completely positive. -/
theorem bb84SiftedPEAnnounceEveVisibleRealPassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleRealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
          leakEC ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleRealPassChannel
  set c : ℂ := 1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ) with hc_def
  set K := bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
    peSel xSel leakEC ec δ Q with hK_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hScaled_cp : IsCompletelyPositive (⇑(c • krausMapFintype K)) :=
    Quantum.Channels.isCompletelyPositive_smul c (krausMapFintype K) hc
      (Quantum.Channels.krausMapFintype_isCompletelyPositive K)
  have h := Quantum.Channels.isCompletelyPositive_comp
    (⇑(c • krausMapFintype K))
    (⇑((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
    hScaled_cp (bb84SiftedMeasAfterPre_isCompletelyPositive eveDim pre hpre peSel xSel)
    ((c • krausMapFintype K).isLinear)
  simpa only [LinearMap.coe_comp] using h

/-- The general-`m` ideal pass channel is completely positive. -/
theorem bb84SiftedPEAnnounceEveVisibleIdealPassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleIdealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
          leakEC ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleIdealPassChannel
  set c : ℂ := 1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel)) with hc_def
  set K := bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
    peSel xSel leakEC ec δ Q with hK_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hScaled_cp : IsCompletelyPositive (⇑(c • krausMapFintype K)) :=
    Quantum.Channels.isCompletelyPositive_smul c (krausMapFintype K) hc
      (Quantum.Channels.krausMapFintype_isCompletelyPositive K)
  have h := Quantum.Channels.isCompletelyPositive_comp
    (⇑(c • krausMapFintype K))
    (⇑((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
    hScaled_cp (bb84SiftedMeasAfterPre_isCompletelyPositive eveDim pre hpre peSel xSel)
    ((c • krausMapFintype K).isLinear)
  simpa only [LinearMap.coe_comp] using h

/-- The general-`m` real pass output is positive semidefinite. -/
theorem bb84SiftedPEAnnounceEveVisibleRealPassOutput_posSemidef
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (bb84SiftedPEAnnounceEveVisibleRealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ
      τ).PosSemidef :=
  mapTensorId_posSemidef (dR := dimR)
    (bb84SiftedPEAnnounceEveVisibleRealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ) τ.toOp (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleRealPassChannel_isCompletelyPositive (m := m) ℓ ℓEV eveDim pre
        hpre
      peSel xSel leakEC ec Q δ)

/-- The general-`m` ideal pass output is positive semidefinite. -/
theorem bb84SiftedPEAnnounceEveVisibleIdealPassOutput_posSemidef
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (bb84SiftedPEAnnounceEveVisibleIdealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ
      τ).PosSemidef :=
  mapTensorId_posSemidef (dR := dimR)
    (bb84SiftedPEAnnounceEveVisibleIdealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ) τ.toOp (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleIdealPassChannel_isCompletelyPositive (m := m) ℓ ℓEV eveDim pre
        hpre
      peSel xSel leakEC ec Q δ)

/-- **The general-`m` real pass-output trace is at most the τ-side accept weight.**  The pass
channel's accept gate is `PE ∧ EV`, the weight functional's is `PE` alone, so the seed-pair average
of the accept-gated block sum is dominated termwise by the PE-gated one; the uniform seed-pair scale
then cancels exactly.  The right-hand side is the UNCHANGED, `m`-free
`bb84SiftedEveVisible_tauLocalPEAcceptedWeight`. -/
theorem realPassOutput_trace_re_le_tauLocalPEAcceptedWeight
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (bb84SiftedPEAnnounceEveVisibleRealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ τ).trace.re ≤
      bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ := by
  set W : ℝ := bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ with
      hW
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by
    rw [hcard]; exact_mod_cast Fintype.card_pos
  have htrace :=
    bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum eveDim pre hpre peSel xSel
      (K := bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)
      (c := 1 / (card : ℂ))
      (gate := fun k => bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2)
      (ωof := fun k => k.2)
      (fun k => bb84.retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul n m ℓ ℓEV
        eveDim peSel xSel leakEC ec δ Q k.1 k.2)
      τ
  rw [bb84SiftedPEAnnounceEveVisibleRealPassOutput,
    bb84SiftedPEAnnounceEveVisibleRealPassChannel, ← hcard, htrace]
  rw [show (∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          (((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / (card : ℂ)) = (((1 : ℝ) / (card : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum_eq : ∑ ω : Fin n → Fin signalDim,
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace : ℝ) else 0)
            = W := by
    rw [hW, bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_sum_marginalBlocks]
  have hstep : ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
      (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ)
        else 0) ≤ (card : ℝ) * W := by
    calc ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
          (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
            ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ)
                else 0)
           ≤ ∑ _k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            (if bb84SiftedLocalPETestPassed peSel xSel δ Q _k.2 then
              ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB _k.2).trace : ℝ)
              else 0) :=
          Finset.sum_le_sum (fun k _ =>
            bb84SiftedPEAndEVGated_le_PEGated eveDim pre hpre ℓEV peSel xSel ec Q δ τ.partialTraceB
                k.1.2 k.2)
      _ = ∑ _st : KeyHashSeedPairEV n ℓ ℓEV peSel, ∑ ω : Fin n → Fin signalDim,
            (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
              ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace : ℝ)
                  else 0) :=
          Fintype.sum_prod_type _
      _ = (card : ℝ) * W := by
          rw [hsum_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcard]
  calc (1 : ℝ) / (card : ℝ) *
        ∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
          (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
            ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ)
                else 0)
         ≤ (1 : ℝ) / (card : ℝ) * ((card : ℝ) * W) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = W := by field_simp

/-- **The general-`m` ideal pass-output trace is at most the τ-side accept weight.**  Same
argument as the real arm: the ideal pass Kraus family carries the same `PE ∧ EV` gate and the same
input-outcome projectors, and its fresh-key/seed-pair scale `1/(2^ℓ·|ST|)` cancels the `2^ℓ·|ST|`
multiplicity of the gate-indicator sum exactly. -/
theorem idealPassOutput_trace_re_le_tauLocalPEAcceptedWeight
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (bb84SiftedPEAnnounceEveVisibleIdealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ τ).trace.re ≤
      bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ := by
  set W : ℝ := bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ with
      hW
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by
    rw [hcard]; exact_mod_cast Fintype.card_pos
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have htrace :=
    bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum eveDim pre hpre peSel xSel
      (K := bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)
      (c := 1 / ((2 ^ ℓ : ℂ) * (card : ℂ)))
      (gate := fun k => bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1)
      (ωof := fun k => k.1)
      (fun k => bb84.retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul n m ℓ ℓEV
        eveDim peSel xSel leakEC ec δ Q k.1 k.2.1 k.2.2)
      τ
  rw [bb84SiftedPEAnnounceEveVisibleIdealPassOutput,
    bb84SiftedPEAnnounceEveVisibleIdealPassChannel, ← hcard, htrace]
  rw [show (∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          (((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / ((2 ^ ℓ : ℂ) * (card : ℂ))) =
      (((1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum_eq : ∑ ω : Fin n → Fin signalDim,
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace : ℝ) else 0)
            = W := by
    rw [hW, bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_sum_marginalBlocks]
  have hstep : ∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
        KeyHashSeedPairEV n ℓ ℓEV peSel,
      (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ)
        else 0) ≤ ((2 : ℝ) ^ ℓ * (card : ℝ)) * W := by
    calc ∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
          (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
            ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ)
                else 0)
           ≤ ∑ _k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
            (if bb84SiftedLocalPETestPassed peSel xSel δ Q _k.1 then
              ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB _k.1).trace : ℝ)
              else 0) :=
          Finset.sum_le_sum (fun k _ =>
            bb84SiftedPEAndEVGated_le_PEGated eveDim pre hpre ℓEV peSel xSel ec Q δ τ.partialTraceB
                k.2.2.2 k.1)
      _ = ∑ ω : Fin n → Fin signalDim,
            ∑ _y : Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel,
            (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
              ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace : ℝ)
                  else 0) :=
          Fintype.sum_prod_type _
      _ = ((2 : ℝ) ^ ℓ * (card : ℝ)) * W := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum, ← hcard]
          rw [hsum_eq]
          push_cast
          ring
  calc (1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) *
        ∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
            KeyHashSeedPairEV n ℓ ℓEV peSel,
          (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
            ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ)
                else 0)
         ≤ (1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) * (((2 : ℝ) ^ ℓ * (card : ℝ)) * W) := by
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = W := by field_simp

/-- **The general-`m` base difference is the real-minus-ideal pass output.**  The general-`m` fail
Kraus family is the same object at the same scale in both maps (D5), so it cancels after tensoring
with the CKR reference. -/
theorem bb84SiftedPEAnnounceEveVisible_baseChannel_mapTensorId_diff_eq_passOutput_sub
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    haveI : NeZero (2 ^ ℓ * 2 ^ ℓ *
        (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).transcriptDim *
        eveDim) := by
      change NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)
      infer_instance
    mapTensorId
        (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).realProtocolMap
            (eveDim := eveDim) -
          (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
              Q δ).idealProtocolMap (eveDim := eveDim)).comp
          (bb84SiftedConjAfterPre eveDim pre peSel xSel)) τ.toOp =
      bb84SiftedPEAnnounceEveVisibleRealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
          ec Q δ τ -
        bb84SiftedPEAnnounceEveVisibleIdealPassOutput (m := m) ℓ ℓEV eveDim pre peSel xSel
            leakEC ec Q δ τ := by
  have : NeZero (2 ^ ℓ * 2 ^ ℓ *
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).transcriptDim *
      eveDim) := by
    change NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)
    infer_instance
  rw [bb84SiftedPEAnnounceEveVisible_baseChannel_real_sub_ideal_eq_passBranch_sub]
  exact mapTensorId_linearMap_sub _ _ _

/-! ## The general-`m` agree/differ split and the differ-block correctness charge -/

private lemma realPassKraus_split {n : ℕ} (m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMapFintype (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel
        leakEC ec δ Q) =
      krausMapFintype (bb84RealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) +
        krausMapFintype (bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) := by
  refine krausMapFintype_split _ _ _ (fun k A => ?_)
  by_cases h : bb84SiftedKeyStringsDiffer peSel ec k.2 = true <;>
    simp [bb84RealPassAgreeKraus, bb84RealPassDifferKraus, h]

private lemma idealPassKraus_split {n : ℕ} (m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMapFintype (bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel
        leakEC ec δ Q) =
      krausMapFintype (bb84IdealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) +
        krausMapFintype (bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) := by
  refine krausMapFintype_split _ _ _ (fun k A => ?_)
  by_cases h : bb84SiftedKeyStringsDiffer peSel ec k.1 = true <;>
    simp [bb84IdealPassAgreeKraus, bb84IdealPassDifferKraus, h]

/-- **The general-`m` real pass channel is the sum of its agree and differ blocks.** -/
theorem bb84SiftedPEAnnounceEveVisibleRealPassChannel_eq_agree_add_differ
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    bb84SiftedPEAnnounceEveVisibleRealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ =
      bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
          leakEC ec Q δ +
        bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
            xSel leakEC
          ec Q δ := by
  rw [bb84SiftedPEAnnounceEveVisibleRealPassChannel,
    bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel,
    bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel,
    realPassKraus_split, smul_add, LinearMap.add_comp]

/-- **The general-`m` ideal pass channel is the sum of its agree and differ blocks.** -/
theorem bb84SiftedPEAnnounceEveVisibleIdealPassChannel_eq_agree_add_differ
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    bb84SiftedPEAnnounceEveVisibleIdealPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC
        ec Q δ =
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
          leakEC ec Q δ +
        bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
            xSel leakEC
          ec Q δ := by
  rw [bb84SiftedPEAnnounceEveVisibleIdealPassChannel,
    bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel,
    bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel,
    idealPassKraus_split, smul_add, LinearMap.add_comp]

/-- **The general-`m` real differ-block pass-output TRACE IDENTITY**: the trace of the differ block
of the real pass output on the CKR reference `τ` is EXACTLY the differ-and-accept weight of the
attacked marginal `τ.partialTraceB`.

Equality, not an inequality: the accept-gated trace formula collapses the single-entry Kraus family
onto the gate-indicated outcome projectors, and the uniform seed-pair scale `1/|ST|` cancels the
`|ST|`-fold multiplicity exactly.  The right-hand side is the UNCHANGED, `m`-free
`bb84SiftedEveVisible_differAndAcceptWeight`. -/
theorem realDifferPassOutput_trace_re_eq_differAndAcceptWeight
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (mapTensorId
      (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
          leakEC ec Q δ)
      τ.toOp).trace.re =
      bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceB := by
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by rw [hcard]; exact_mod_cast Fintype.card_pos
  have htrace :=
    bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum eveDim pre hpre peSel xSel
      (K := bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (c := 1 / (card : ℂ))
      (gate := fun k => bb84SiftedKeyStringsDiffer peSel ec k.2 &&
        bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2)
      (ωof := fun k => k.2)
      (fun k => bb84RealPassDifferKraus_adjoint_mul n m ℓ ℓEV eveDim peSel xSel
        leakEC ec δ Q k)
      τ
  rw [bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel, ← hcard, htrace]
  rw [show (∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
        (if bb84SiftedKeyStringsDiffer peSel ec k.2 &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          (((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
        (if bb84SiftedKeyStringsDiffer peSel ec k.2 &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.1.2 k.2 then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.2).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / (card : ℂ)) = (((1 : ℝ) / (card : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    differGatedSum_eq ℓ ℓEV eveDim pre hpre peSel xSel ec Q δ τ.partialTraceB, ← hcard]
  field_simp

/-- **The general-`m` ideal differ-block pass-output TRACE IDENTITY.**  Same computation as the
real arm: the ideal pass Kraus family carries the same gate and the same input-outcome projectors,
and its fresh-key/seed-pair scale `1/(2^ℓ·|ST|)` cancels the `2^ℓ·|ST|`-fold multiplicity exactly.
-/
theorem idealDifferPassOutput_trace_re_eq_differAndAcceptWeight
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    (mapTensorId
      (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
          xSel leakEC ec Q δ)
      τ.toOp).trace.re =
      bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceB := by
  set card : ℕ := Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) with hcard
  have hcard_pos : 0 < (card : ℝ) := by rw [hcard]; exact_mod_cast Fintype.card_pos
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have htrace :=
    bb84SiftedPEAnnounce_passOutput_trace_eq_gated_blockSum eveDim pre hpre peSel xSel
      (K := bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (c := 1 / ((2 ^ ℓ : ℂ) * (card : ℂ)))
      (gate := fun k => bb84SiftedKeyStringsDiffer peSel ec k.1 &&
        bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1)
      (ωof := fun k => k.1)
      (fun k => bb84IdealPassDifferKraus_adjoint_mul n m ℓ ℓEV eveDim peSel xSel
        leakEC ec δ Q k)
      τ
  rw [bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel, ← hcard, htrace]
  rw [show (∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if bb84SiftedKeyStringsDiffer peSel ec k.1 &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          (((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ) :
              ℂ)
          else 0)) =
      ((∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
          KeyHashSeedPairEV n ℓ ℓEV peSel,
        (if bb84SiftedKeyStringsDiffer peSel ec k.1 &&
            bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
          ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ)
          else 0) : ℝ) : ℂ) by push_cast; exact (Finset.sum_congr rfl (fun k _ => by
            split_ifs <;> simp)).symm]
  rw [show ((1 : ℂ) / ((2 ^ ℓ : ℂ) * (card : ℂ))) =
      (((1 : ℝ) / ((2 : ℝ) ^ ℓ * (card : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum : ∑ k : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) ×
        KeyHashSeedPairEV n ℓ ℓEV peSel,
      (if bb84SiftedKeyStringsDiffer peSel ec k.1 &&
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q k.2.2.2 k.1 then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB k.1).trace : ℝ) else
            0) =
      ((2 : ℝ) ^ ℓ * (card : ℝ)) *
        bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceB := by
    rw [sumProd3_eq (Ω := Fin n → Fin signalDim) (A := Fin (2 ^ ℓ))
      (B := KeyHashSeedPairEV n ℓ ℓEV peSel)
      (fun st ω => if bb84SiftedKeyStringsDiffer peSel ec ω &&
          bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ((bb84SiftedEveConditioned eveDim pre hpre peSel xSel τ.partialTraceB ω).trace : ℝ) else 0)]
    rw [Fintype.sum_prod_type,
      differGatedSum_eq ℓ ℓEV eveDim pre hpre peSel xSel ec Q δ τ.partialTraceB, ← hcard,
      Fintype.card_fin]
    push_cast
    ring
  rw [hsum]
  field_simp

/-- The general-`m` real differ pass channel is completely positive (a nonnegatively-scaled Kraus
map after a CP map — zeroing part of a Kraus family leaves a Kraus family). -/
theorem bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
          xSel leakEC
        ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel
  set c : ℂ := 1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ) with hc_def
  set K := bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q with hK_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hScaled_cp : IsCompletelyPositive (⇑(c • krausMapFintype K)) :=
    Quantum.Channels.isCompletelyPositive_smul c (krausMapFintype K) hc
      (Quantum.Channels.krausMapFintype_isCompletelyPositive K)
  have h := Quantum.Channels.isCompletelyPositive_comp
    (⇑(c • krausMapFintype K))
    (⇑((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
    hScaled_cp (bb84SiftedMeasAfterPre_isCompletelyPositive eveDim pre hpre peSel xSel)
    ((c • krausMapFintype K).isLinear)
  simpa only [LinearMap.coe_comp] using h

/-- The general-`m` ideal differ pass channel is completely positive. -/
theorem bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
          xSel leakEC
        ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel
  set c : ℂ := 1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel)) with hc_def
  set K := bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q with hK_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hScaled_cp : IsCompletelyPositive (⇑(c • krausMapFintype K)) :=
    Quantum.Channels.isCompletelyPositive_smul c (krausMapFintype K) hc
      (Quantum.Channels.krausMapFintype_isCompletelyPositive K)
  have h := Quantum.Channels.isCompletelyPositive_comp
    (⇑(c • krausMapFintype K))
    (⇑((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
    hScaled_cp (bb84SiftedMeasAfterPre_isCompletelyPositive eveDim pre hpre peSel xSel)
    ((c • krausMapFintype K).isLinear)
  simpa only [LinearMap.coe_comp] using h

/-- **The operator form of the correctness leg at a general test-set size `m`.**  The
differ-and-accept block of `real − ideal` — the sub-block of the general-`m` base-scheme difference
supported on "the two key strings differ AND the protocol accepts" — has CKR tensor trace norm at
most `2·2^(−ℓEV)`, for EVERY attack-free `pre` slot, EVERY reference state `τ`, EVERY
error-correction scheme `ec` and EVERY test-set size `m`.

The scalar input `bb84_differAndAccept_weight_le_two_pow_neg_lEV` (`InnerBudgetPinned.lean`) is
`m`-free — it bounds a Born mass of outcome strings and names no output register — so it is reused
verbatim at the attacked CKR marginal `τ.partialTraceB`.  What `m` moves is only the register the
two differ blocks are written into, and the trace identities above absorb that.

**Stated JOINTLY.**  `InfoTheory.Postselection.ErrorVerification.conditional_correctness_fails`
PROVES that the conditional form `Pr[differ | accept]` is not bounded by `2^(−ℓEV)`, which is why
the charge is additive.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) §V.C, error verification "by comparing hash values
of length log(1/ε_EV)". -/
theorem bb84SiftedPEAnnounceEveVisible_differBlock_ckrTensorTraceNorm_le_two_pow_neg_lEV
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
            xSel leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel
              xSel leakEC
            ec Q δ) τ ≤
      2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  have hRealPSD := mapTensorId_posSemidef (dR := dimR)
    (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
        leakEC ec Q δ) τ.toOp (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel_isCompletelyPositive (m := m) ℓ ℓEV eveDim
        pre hpre peSel
      xSel leakEC ec Q δ)
  have hIdealPSD := mapTensorId_posSemidef (dR := dimR)
    (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre peSel xSel
        leakEC ec Q δ) τ.toOp (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel_isCompletelyPositive (m := m) ℓ ℓEV eveDim
        pre hpre peSel
      xSel leakEC ec Q δ)
  have hScalar := bb84_differAndAccept_weight_le_two_pow_neg_lEV eveDim pre hpre ℓEV peSel xSel ec Q
      δ
    τ.partialTraceB
  unfold ckrTensorTraceNorm
  rw [mapTensorId_linearMap_sub]
  calc Quantum.Metrics.traceNorm
        (mapTensorId
            (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                peSel xSel leakEC
              ec Q δ) τ.toOp -
          mapTensorId
            (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                peSel xSel leakEC
              ec Q δ) τ.toOp)
      ≤ Quantum.Metrics.traceNorm
            (mapTensorId
              (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                  peSel xSel leakEC
                ec Q δ) τ.toOp) +
          Quantum.Metrics.traceNorm
            (mapTensorId
              (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                  peSel xSel leakEC
                ec Q δ) τ.toOp) :=
        Quantum.Metrics.traceNorm_sub_le _ _
    _ = (mapTensorId
            (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                peSel xSel leakEC
              ec Q δ) τ.toOp).trace.re +
          (mapTensorId
            (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel (m := m) ℓ ℓEV eveDim pre
                peSel xSel leakEC
              ec Q δ) τ.toOp).trace.re := by
        rw [Quantum.Channels.traceNorm_posSemidef_eq_trace _ hRealPSD,
          Quantum.Channels.traceNorm_posSemidef_eq_trace _ hIdealPSD]
    _ = 2 * bb84SiftedEveVisible_differAndAcceptWeight eveDim pre hpre ℓEV peSel xSel ec Q δ
          τ.partialTraceB := by
        rw [realDifferPassOutput_trace_re_eq_differAndAcceptWeight
            (hpre := hpre),
          idealDifferPassOutput_trace_re_eq_differAndAcceptWeight
            (hpre := hpre)]
        ring
    _ ≤ 2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by linarith

end QKD.BB84.Engine

end -- noncomputable section
