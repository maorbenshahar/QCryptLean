import QCryptLean.QKD.BB84.Engine.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.Engine.Postselection.RegisterTrickGeneral

/-!
# Bell covariance of the agree and differ pass blocks

The gate selecting equal or different reconciled strings is preserved by Bell relabelling.
Consequently each restricted Kraus family has the same output relabelling as the pass family.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- Bell relabelling preserves whether the reconciled key strings differ. -/
theorem bb84SiftedKeyStringsDiffer_bellStringRelabel
    {n leakEC : ℕ}
    (peSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (h : Fin n → Fin 4)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (ω : Fin n → Fin signalDim) :
    bb84SiftedKeyStringsDiffer peSel ec (bellStringRelabel n h ω) =
      bb84SiftedKeyStringsDiffer peSel ec ω := by
  simp only [bb84SiftedKeyStringsDiffer, bb84AliceKeyString_bellStringRelabel,
    bb84BobKeyString_bellStringRelabel, hdec, ne_eq, add_left_inj]

/-- The real agree Kraus family intertwines Bell twirling and output relabelling. -/
theorem bb84RealPassAgreeKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    bb84RealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.2 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          bb84RealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := bb84SiftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.2
  have hbase := retainedSiftedPEAnnouncePassBranchKraus_bellTwirl_intertwining
    n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec idx.2 = true
  · simp [bb84RealPassAgreeKraus, bb84PEAnnounceOutcomeReindex,
      bellStringRelabelEquiv, hgate, hd]
  · simpa [bb84RealPassAgreeKraus, bb84PEAnnounceOutcomeReindex,
      bellStringRelabelEquiv, hgate, hd] using hbase

/-- The real differ Kraus family intertwines Bell twirling and output relabelling. -/
theorem bb84RealPassDifferKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.2 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          bb84RealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := bb84SiftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.2
  have hbase := retainedSiftedPEAnnouncePassBranchKraus_bellTwirl_intertwining
    n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec idx.2 = true
  · simpa [bb84RealPassDifferKraus, bb84PEAnnounceOutcomeReindex,
      bellStringRelabelEquiv, hgate, hd] using hbase
  · simp [bb84RealPassDifferKraus, bb84PEAnnounceOutcomeReindex,
      bellStringRelabelEquiv, hgate, hd]

/-- The ideal agree Kraus family intertwines Bell twirling and output relabelling. -/
theorem bb84IdealPassAgreeKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    bb84IdealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.1 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          bb84IdealPassAgreeKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (bb84PEAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := bb84SiftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.1
  have hbase := retainedSiftedPEAnnounceIdealPassKraus_bellTwirl_intertwining
    n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec idx.1 = true
  · simp [bb84IdealPassAgreeKraus, bb84PEAnnounceIdealReindex, hgate, hd]
  · simpa [bb84IdealPassAgreeKraus, bb84PEAnnounceIdealReindex, hgate, hd] using hbase

/-- The ideal differ Kraus family intertwines Bell twirling and output relabelling. -/
theorem bb84IdealPassDifferKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.1 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          bb84IdealPassDifferKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (bb84PEAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
  have hgate := bb84SiftedKeyStringsDiffer_bellStringRelabel peSel ec h hdec idx.1
  have hbase := retainedSiftedPEAnnounceIdealPassKraus_bellTwirl_intertwining
    n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec idx.1 = true
  · simpa [bb84IdealPassDifferKraus, bb84PEAnnounceIdealReindex, hgate, hd] using hbase
  · simp [bb84IdealPassDifferKraus, bb84PEAnnounceIdealReindex, hgate, hd]

/-- Each pass-block difference carries Bell twirling to a unitary output relabelling. -/
theorem bb84PassBlockDelta_bellTwirl_covariant
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (g : Fin n → Fin 4) :
    ∃ W : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC 1),
      Wᴴ * W = 1 ∧
      ∀ M : Op (4 ^ n),
        bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
            peSel xSel leakEC ec Q δ
            (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) =
          W * bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
              peSel xSel leakEC ec Q δ M * Wᴴ := by
  obtain ⟨⟨πsyn, hsyn⟩, hdec⟩ := hec (bellTwirlKeyError peSel g)
  let h := bb84SiftedTwirlString peSel xSel g
  have hkey : bellTwirlKeyError peSel h = bellTwirlKeyError peSel g :=
    bellTwirlKeyError_siftedTwirlString peSel xSel g
  have hsyn' : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a) := by
    rw [hkey]
    exact hsyn
  have hdec' : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h := by
    rw [hkey]
    exact hdec
  let U := Op.tensor (bellTwirlUnitary n h) (1 : Op 1)
  let W := Op.tensor
    (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn) (1 : Op 1)
  let KR := if differ then bb84RealPassDifferKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
    else bb84RealPassAgreeKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
  let KI := if differ then bb84IdealPassDifferKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
    else bb84IdealPassAgreeKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
  have hR : ∀ A, krausMapFintype KR (U * A * Uᴴ) = W * krausMapFintype KR A * Wᴴ := by
    intro A
    have hinter : ∀ idx, KR idx * U = bellTwirlSign n h idx.2 •
        (W * KR (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) := by
      intro idx
      cases differ
      · exact bb84RealPassAgreeKraus_bellTwirl_intertwining
          n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
      · exact bb84RealPassDifferKraus_bellTwirl_intertwining
          n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
    rw [krausMapFintype_conj_of_phased_intertwining KR
      (fun idx => KR (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx)) U W
      (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      hinter A, krausMapFintype_equiv]
  have hI : ∀ A, krausMapFintype KI (U * A * Uᴴ) = W * krausMapFintype KI A * Wᴴ := by
    intro A
    have hinter : ∀ idx, KI idx * U = bellTwirlSign n h idx.1 •
        (W * KI (bb84PEAnnounceIdealReindex n ℓ ℓEV peSel h idx)) := by
      intro idx
      cases differ
      · exact bb84IdealPassAgreeKraus_bellTwirl_intertwining
          n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
      · exact bb84IdealPassDifferKraus_bellTwirl_intertwining
          n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q h πsyn hsyn' hdec' idx
    rw [krausMapFintype_conj_of_phased_intertwining KI
      (fun idx => KI (bb84PEAnnounceIdealReindex n ℓ ℓEV peSel h idx)) U W
      (fun idx => bellTwirlSign n h idx.1) (fun idx => bellTwirlSign_unit n h idx.1)
      hinter A, krausMapFintype_equiv]
  refine ⟨W, bb84PEAnnounceBellRelabelUnitary_tensor_one_unitary
    n m ℓ ℓEV peSel leakEC 1 h πsyn, ?_⟩
  intro M
  let meas := (measurementChannel n 1).comp
    (bb84SiftedConjAfterPre 1 (bb84UnitRegisterEmbed n) peSel xSel)
  have hmeas : meas (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) =
      U * meas M * Uᴴ := by
    dsimp [meas, bb84SiftedConjAfterPre]
    rw [bb84UnitRegisterEmbed_isBellTwirlCovariantPre n g M,
      bb84SiftedConjChannel_bellTwirl_conj, measurementChannel_bellTwirl_outcomeRelabel]
  have hexpand : ∀ A, bb84PassBlockDelta differ (m := m) ℓ ℓEV
      1 (bb84UnitRegisterEmbed n) peSel xSel leakEC ec Q δ A =
        (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
            krausMapFintype KR (meas A) -
          (1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
            krausMapFintype KI (meas A) := by
    intro A
    cases differ <;> rfl
  rw [hexpand, hexpand, hmeas, hR, hI, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Each announced pass block is Bell-twirl trace-norm invariant at every ancilla width. -/
theorem bb84SymPassBlockDelta_bellTwirl_traceNorm_invariant_stabilized
    (differ : Bool) (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (dimR : ℕ) [NeZero dimR]
    (g : Fin n → Fin 4) (M : Op (4 ^ n * dimR)) :
    traceNorm
      (mapTensorId (k := dimR)
        (bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
      traceNorm
        (mapTensorId (k := dimR)
          (bb84SymPassBlockDelta differ n m ℓ ℓEV Q δ peSel xSel leakEC ec) M) := by
  let base := bb84PassBlockDelta differ (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
    peSel xSel leakEC ec Q δ
  let inner := fun π => base.comp (permuteSignalLinear n π)
  let announce := bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC
  let U := bellTwirlUnitary n g
  let Mtw := Op.tensor U (1 : Op dimR) * M * (Op.tensor U (1 : Op dimR))ᴴ
  have hsummand : ∀ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId (k := dimR) ((announce π).comp (inner π)) Mtw) =
        traceNorm (mapTensorId (k := dimR) ((announce π).comp (inner π)) M) := by
    intro π
    obtain ⟨W, hW, hcov⟩ := bb84PassBlockDelta_bellTwirl_covariant
      differ n m ℓ ℓEV Q δ peSel xSel leakEC ec hec (g ∘ ⇑π⁻¹)
    have hinner : ∀ A : Op (4 ^ n),
        inner π (U * A * Uᴴ) = W * inner π A * Wᴴ := by
      intro A
      dsimp [inner, U]
      rw [permuteSignalLinear_bellTwirl_conj]
      exact hcov _
    rw [← mapTensorId_comp (inner π) (announce π) Mtw,
      ← mapTensorId_comp (inner π) (announce π) M]
    rw [bb84_announceLinearEveVisible_mapTensorId_traceNorm_eq,
      bb84_announceLinearEveVisible_mapTensorId_traceNorm_eq]
    have hconj := mapTensorIdLinear_left_conj_of_conj (k := dimR)
      (inner π) U W hinner M
    change traceNorm (mapTensorIdLinear (inner π) Mtw) = _
    rw [hconj]
    have hWtensor : (Op.tensor W (1 : Op dimR))ᴴ * Op.tensor W (1 : Op dimR) = 1 := by
      rw [Op.tensor_conjTranspose, Op.tensor_mul, Matrix.conjTranspose_one,
        Matrix.one_mul, hW, Op.tensor_one]
    exact Quantum.Metrics.TraceNormHoelder.traceNorm_isometry_mul_left _ _ hWtensor
  have horth (A : Op (4 ^ n * dimR)) :
      traceNorm (∑ π : Equiv.Perm (Fin n),
        mapTensorId (k := dimR) ((announce π).comp (inner π)) A) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm (mapTensorId (k := dimR) ((announce π).comp (inner π)) A) := by
    simp_rw [← mapTensorId_comp]
    exact bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum
      peSel leakEC (fun π => mapTensorId (k := dimR) (inner π) A)
  change traceNorm (mapTensorId ((1 / (n.factorial : ℂ)) •
      ∑ π : Equiv.Perm (Fin n), (announce π).comp (inner π)) Mtw) =
    traceNorm (mapTensorId ((1 / (n.factorial : ℂ)) •
      ∑ π : Equiv.Perm (Fin n), (announce π).comp (inner π)) M)
  rw [mapTensorId_linearMap_smul, mapTensorId_linearMap_smul,
    mapTensorId_linearMap_sum, mapTensorId_linearMap_sum,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, horth Mtw, horth M]
  exact congrArg (fun r : ℝ => ‖(1 / (n.factorial : ℂ))‖ * r)
    (Finset.sum_congr rfl (fun π _ => hsummand π))

end QKD.BB84.Engine

end
