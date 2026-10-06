import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetCorrectness
import QCryptLean.Quantum.Channels.CPTP.CKRBound.TightPostselectionBound
import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp

/-!
# The agree and differ parts of the BB84 real-ideal difference

Each block restricts the Kraus outcomes according to equality of the reconciled strings.
`bb84PassBlockDelta` is the base difference, and `bb84SymPassBlockDelta` averages it over
announced input permutations. The sum of the two averaged blocks equals the full real-ideal
difference exactly; their output supports need not be disjoint.

The agree block has CKR trace norm at most twice the local PE acceptance weight. The differ
block has diamond norm at most `2 * 2^(-ℓEV)` without postselection or reference symmetry.
Both announced blocks are permutation covariant and preserve conjugate transpose.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics QKD.BB84.Model Math.RepresentationTheory InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- The real-ideal pass difference on agreeing or differing reconciled strings. -/
noncomputable def bb84PassBlockDelta
    (differ : Bool)
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  if differ then
    bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel
        (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel
        (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ
  else
    bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel
        (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel
        (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ

/-- The general-`m` real agree pass channel is completely positive (a nonnegatively-scaled Kraus
map after a CP map — zeroing part of a Kraus family leaves a Kraus family). -/
theorem bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
          xSel leakEC
        ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel
  set c : ℂ := 1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ) with hc_def
  set K := bb84RealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q with hK_def
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

/-- The general-`m` ideal agree pass channel is completely positive. -/
theorem bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel_isCompletelyPositive
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    IsCompletelyPositive
      (⇑(bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
          xSel leakEC
        ec Q δ)) := by
  unfold bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel
  set c : ℂ := 1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel)) with hc_def
  set K := bb84IdealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q with hK_def
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

/-- The announced average of one pass-block difference over input round permutations. -/
noncomputable def bb84SymPassBlockDelta
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC 1) :=
  (1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
        ((bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ).comp (permuteSignalLinear n π))

/-- The symmetrized real-ideal difference is exactly the sum of its two pass blocks. -/
theorem bb84SymChannels_sub_eq_passBlocks
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec +
        bb84SymPassBlockDelta true n m ℓ ℓEV Q δ peSel xSel leakEC ec := by
  have hbase := bb84SiftedPEAnnounceEveVisible_baseChannel_real_sub_ideal_eq_passBranch_sub
    (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n) peSel xSel leakEC ec Q δ
  rw [bb84SiftedPEAnnounceEveVisibleRealPassChannel_eq_agree_add_differ,
    bb84SiftedPEAnnounceEveVisibleIdealPassChannel_eq_agree_add_differ] at hbase
  have hsplit :
      (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
          Q δ).realProtocolMap (eveDim := 1) -
        (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
          Q δ).idealProtocolMap (eveDim := 1)).comp
        (bb84SiftedConjAfterPre 1 (bb84UnitRegisterEmbed n) peSel xSel)) =
      bb84PassBlockDelta false (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ +
        bb84PassBlockDelta true (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ := by
    rw [hbase]
    simp only [bb84PassBlockDelta, Bool.false_eq_true, if_false, if_true]
    abel
  unfold bb84SymRealChannel bb84SymIdealChannel bb84SymPassBlockDelta
  rw [← smul_sub, ← Finset.sum_sub_distrib, ← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
  simp only [← LinearMap.comp_sub, ← LinearMap.sub_comp, ← LinearMap.comp_add,
    ← LinearMap.add_comp]
  rw [← hsplit]
  rfl

/-- Paired reference permutation invariance transfers a base pass-block bound to its average. -/
theorem bb84SymPassBlockDelta_ckrTensorTraceNorm_le
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (τ : DensityOp ((4 ^ n) * (4 ^ n)))
    (hτ : IsPairedPermInvariant τ) :
    ckrTensorTraceNorm
        (bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) τ ≤
      ckrTensorTraceNorm
        (bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ) τ := by
  exact ckrTensorTraceNorm_symAverage_le_of_baseScheme_bound_generic
    _ _ (fun π => bb84SiftedPEAnnounceLinearEveVisible_isCPTP
      n m ℓ ℓEV 1 peSel leakEC π) _ τ hτ rfl le_rfl

/-- Each announced pass-block difference is permutation covariant. -/
theorem bb84SymPassBlockDelta_permCov
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    PermutationCovariant
      (bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) :=
  bb84SymAnnouncedMap_permCov n m ℓ ℓEV peSel leakEC 1 _

/-- Each announced pass-block difference preserves conjugate transpose. -/
theorem bb84SymPassBlockDelta_preserves_conjTranspose
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    ∀ M : Op (4 ^ n),
      bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec M.conjTranspose =
        (bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec M).conjTranspose := by
  have hbase : ∀ M : Op (4 ^ n),
      bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ Mᴴ =
        (bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
          peSel xSel leakEC ec Q δ M)ᴴ := by
    cases differ
    · exact cp_linear_sub_preserves_conjTranspose _ _
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel_isCompletelyPositive
          ℓ ℓEV 1 _ (bb84UnitRegisterEmbed_isCPTP n) peSel xSel leakEC ec Q δ)
        (bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel_isCompletelyPositive
          ℓ ℓEV 1 _ (bb84UnitRegisterEmbed_isCPTP n) peSel xSel leakEC ec Q δ)
    · exact cp_linear_sub_preserves_conjTranspose _ _
        (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel_isCompletelyPositive
          ℓ ℓEV 1 _ (bb84UnitRegisterEmbed_isCPTP n) peSel xSel leakEC ec Q δ)
        (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel_isCompletelyPositive
          ℓ ℓEV 1 _ (bb84UnitRegisterEmbed_isCPTP n) peSel xSel leakEC ec Q δ)
  intro M
  simp only [bb84SymPassBlockDelta, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    star_div₀, star_one, star_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  rw [← cptp_preserves_conjTranspose _ (permuteSignalLinear_isCPTP n π), hbase,
    ← cptp_preserves_conjTranspose _
      (bb84SiftedPEAnnounceLinearEveVisible_isCPTP n m ℓ ℓEV 1 peSel leakEC π)]

/-- The agree-block trace norm is at most twice the local PE acceptance weight. -/
theorem bb84AgreeBlock_ckrTensorTraceNorm_le_two_tauWeight
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    ckrTensorTraceNorm
        (bb84PassBlockDelta false (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ) τ ≤
      2 * bb84SiftedEveVisible_tauLocalPEAcceptedWeight
        eveDim pre hpre peSel xSel Q δ τ := by
  let R := bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel
    (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ
  let I := bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel
    (m := m) ℓ ℓEV eveDim pre peSel xSel leakEC ec Q δ
  have hR := mapTensorId_posSemidef R τ.toOp
    (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel_isCompletelyPositive
      ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ)
  have hI := mapTensorId_posSemidef I τ.toOp
    (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
    (bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel_isCompletelyPositive
      ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ)
  have htrace (Φ Ψ : Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
      (hΨ : IsCompletelyPositive ⇑Ψ) :
      (mapTensorId Φ τ.toOp).trace.re ≤ (mapTensorId (Φ + Ψ) τ.toOp).trace.re := by
    rw [mapTensorId_linearMap_add, Matrix.trace_add, Complex.add_re]
    exact le_add_of_nonneg_right (Complex.le_def.mp
      (mapTensorId_posSemidef Ψ τ.toOp
        (posSemidefOp_implies_mathlib τ.toPosSemidefOp) hΨ).trace_nonneg).1
  have hRle : (mapTensorId R τ.toOp).trace.re ≤
      bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ := by
    apply le_trans _ (realPassOutput_trace_re_le_tauLocalPEAcceptedWeight
      (m := m) ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ τ)
    unfold bb84SiftedPEAnnounceEveVisibleRealPassOutput
    rw [bb84SiftedPEAnnounceEveVisibleRealPassChannel_eq_agree_add_differ]
    exact htrace R _
      (bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel_isCompletelyPositive
        ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ)
  have hIle : (mapTensorId I τ.toOp).trace.re ≤
      bb84SiftedEveVisible_tauLocalPEAcceptedWeight eveDim pre hpre peSel xSel Q δ τ := by
    apply le_trans _ (idealPassOutput_trace_re_le_tauLocalPEAcceptedWeight
      (m := m) ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ τ)
    unfold bb84SiftedPEAnnounceEveVisibleIdealPassOutput
    rw [bb84SiftedPEAnnounceEveVisibleIdealPassChannel_eq_agree_add_differ]
    exact htrace I _
      (bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel_isCompletelyPositive
        ℓ ℓEV eveDim pre hpre peSel xSel leakEC ec Q δ)
  change traceNorm (mapTensorId (R - I) τ.toOp) ≤ _
  rw [mapTensorId_linearMap_sub]
  calc
    traceNorm (mapTensorId R τ.toOp - mapTensorId I τ.toOp) ≤
        traceNorm (mapTensorId R τ.toOp) + traceNorm (mapTensorId I τ.toOp) :=
      traceNorm_sub_le _ _
    _ = (mapTensorId R τ.toOp).trace.re + (mapTensorId I τ.toOp).trace.re := by
      rw [traceNorm_posSemidef_eq_trace _ hR, traceNorm_posSemidef_eq_trace _ hI]
    _ ≤ _ := by linarith only [hRle, hIle]

/-- The differ block costs twice the verification collision probability without postselection. -/
theorem bb84SymDifferBlock_diamondNorm_le_two_pow_neg_lEV
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    diamondNorm (bb84SymPassBlockDelta true n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      2 * (2 : ℝ) ^ (-(ℓEV : ℝ)) := by
  apply diamondNorm_le_of_density_bound _
    (bb84SymPassBlockDelta_preserves_conjTranspose
      true n m ℓ ℓEV Q δ peSel xSel leakEC ec) _ (by positivity)
  intro τ
  let B := 2 * (2 : ℝ) ^ (-(ℓEV : ℝ))
  let base := bb84PassBlockDelta true (m := m) ℓ ℓEV
    1 (bb84UnitRegisterEmbed n) peSel xSel leakEC ec Q δ
  let announce := bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC
  have hsummand : ∀ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId ((announce π).comp (base.comp (permuteSignalLinear n π)))
        τ.toOp) ≤ B := by
    intro π
    have hpre : IsCPTP ⇑((bb84UnitRegisterEmbed n).comp (permuteSignalLinear n π)) := by
      simpa only [LinearMap.coe_comp] using cptp_comp
        (bb84UnitRegisterEmbed n) (permuteSignalLinear n π)
        (bb84UnitRegisterEmbed_isCPTP n) (permuteSignalLinear_isCPTP n π)
    have hbound :=
      bb84SiftedPEAnnounceEveVisible_differBlock_ckrTensorTraceNorm_le_two_pow_neg_lEV
        (m := m) ℓ ℓEV 1 ((bb84UnitRegisterEmbed n).comp (permuteSignalLinear n π))
        hpre peSel xSel leakEC ec Q δ τ
    have hbase : ckrTensorTraceNorm (base.comp (permuteSignalLinear n π)) τ ≤ B := by
      simpa only [base, bb84PassBlockDelta, if_true,
        bb84SiftedPEAnnounceEveVisibleRealDifferPassChannel,
        bb84SiftedPEAnnounceEveVisibleIdealDifferPassChannel, bb84SiftedConjAfterPre,
        LinearMap.sub_comp, LinearMap.comp_assoc] using hbound
    exact (ckrTensorTraceNorm_postcomp_cptp_le (announce π)
      (bb84SiftedPEAnnounceLinearEveVisible_isCPTP n m ℓ ℓEV 1 peSel leakEC π)
      (base.comp (permuteSignalLinear n π)) τ).trans hbase
  change traceNorm (mapTensorId ((1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n), (announce π).comp (base.comp (permuteSignalLinear n π)))
      τ.toOp) ≤ B
  rw [mapTensorId_linearMap_smul, mapTensorId_linearMap_sum,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  have hsum : (∑ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId ((announce π).comp (base.comp (permuteSignalLinear n π)))
        τ.toOp)) ≤ (n.factorial : ℝ) * B := by
    calc
      _ ≤ ∑ _π : Equiv.Perm (Fin n), B := Finset.sum_le_sum (fun π _ => hsummand π)
      _ = _ := by simp [Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ ‖(1 / (n.factorial : ℂ))‖ * ((n.factorial : ℝ) * B) :=
      mul_le_mul_of_nonneg_left ((traceNorm_sum_le Finset.univ _).trans hsum) (norm_nonneg _)
    _ = B := by
      rw [norm_div, norm_one, Complex.norm_natCast]
      field_simp

/-- A negative-width or negative-upper-edge acceptance interval rejects every outcome, so the
real and ideal channels coincide. -/
theorem bb84SymChannels_eq_of_empty_acceptance
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (hempty : δ < 0 ∨ Q + δ < 0) :
    bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec := by
  have hpass (t : KeyHashSeed n ℓEV peSel) (ω : Fin n → Fin signalDim) :
      bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = false := by
    have habs (a : ℝ) (ha : 0 ≤ a) : ¬ |a - Q| ≤ δ := by
      intro h
      rcases hempty with hδ | hQ
      · linarith [abs_nonneg (a - Q)]
      · linarith [(le_abs_self (a - Q)).trans h]
    have hZ : ¬ |(bb84SiftedZTestErrorCount peSel xSel ω : ℝ) /
        bb84SiftedZTestSampleSize peSel xSel - Q| ≤ δ := habs _ (by positivity)
    simp [bb84SiftedLocalPEAndEVPassed, bb84SiftedLocalPETestPassed, hZ]
  have hmaps :
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
        Q δ).realProtocolMap (eveDim := 1) =
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec
        Q δ).idealProtocolMap (eveDim := 1) := by
    dsimp only [bb84SiftedPEAnnounceEveVisibleProtocol]
    congr 1
    ext A i j
    simp [bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap,
      bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel, krausMapFintype,
      bb84.retainedSiftedPEAnnouncePassBranchKraus,
      bb84.retainedSiftedPEAnnounceIdealPassKraus, hpass]
  simp only [bb84SymRealChannel, bb84SymIdealChannel, hmaps]

/-- Correctness is charged directly, while CKR postselection lifts the agree-block trace distance.
The full real/ideal distance uses the distinguishing-advantage convention. -/
theorem bb84SymChannels_diamondDist_le_correctness_add_symDim_mul_agreeTraceDistance
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    (1 / 2) * diamondNorm
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      (2 : ℝ) ^ (-(ℓEV : ℝ)) +
        (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) *
          ((1 / 2) * ckrTensorTraceNorm
            (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
            (bb84SymCKRDeFinettiPurification n)) := by
  have hagree := diamondNorm_le_symDim_mul_ckrTraceNorm (d := signalDim) (n := n)
    (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymPassBlockDelta_permCov false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymPassBlockDelta_preserves_conjTranspose
      false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymCKRDeFinettiPurification n)
    (bb84SymCKRDeFinettiPurification_isPurification n)
  rw [← Nat.add_sub_assoc (by norm_num : 1 ≤ signalDim ^ 2)] at hagree
  rw [bb84SymChannels_sub_eq_passBlocks]
  have hsum := add_le_add hagree
    (bb84SymDifferBlock_diamondNorm_le_two_pow_neg_lEV n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  have h := (diamondNorm_add_le _ _).trans (hsum.trans_eq (add_comm _ _))
  have hhalf := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hhalf using 1
  ring

end QKD.BB84.Engine

end
