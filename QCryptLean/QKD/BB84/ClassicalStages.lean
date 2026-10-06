import QCryptLean.LOCC.Typed.Program.TwoPartyClassicalStorage
import QCryptLean.QKD.BB84.Streaming
import QCryptLean.QKD.BB84.Program

/-!
# Stagewise classical-storage certificates for measure-first BB84

These theorems expose the action-by-action certificates for the authored postmeasurement
continuation.  Renner, quant-ph/0512258v2, lines 673--736, and Pfister et al., arXiv:1506.07502v3,
Sections IV--V motivate the classical postprocessing order.  The exact certificates are properties
of the source-defined programs and preserve their raw outcomes, announcements, multipartite systems,
and abort behavior.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84.Engine

/-- A deterministic local readout with an arbitrary public relabelling preserves honest-register
diagonality on every raw branch. -/
theorem announcedReadout_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (i : TwoParty.Party) {Public Readout : Type}
    [Fintype Public] [DecidableEq Public]
    [Fintype Readout] [DecidableEq Readout]
    (f : R.reg i → Readout) (announce : Readout → Public) :
    (AnnouncedAction.ofInstrument i
      (Instrument.nondemolitionReadout f) announce).PreservesHonestRegistersDiagonal :=
  AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal i _ announce
    (Instrument.nondemolitionReadout_preservesDiagonalBranches f)

private theorem isHonestClassical_castBoundary
    {R : MultipartiteSystem TwoParty.Party} {B B' : Boundary TwoParty.Party}
    (h : B = B') (p : Program R B) (hp : p.IsHonestClassical) :
    (cast (congrArg (Program R) h) p).IsHonestClassical := by
  subst B'
  exact hp

private theorem isHonestClassical_castInput
    {R R' : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party}
    (h : R = R') (p : Program R B) (hp : p.IsHonestClassical) :
    (cast (congrArg (fun S => Program S B) h) p).IsHonestClassical := by
  subst R'
  exact hp

private theorem isHonestClassical_cast
    {R R' : MultipartiteSystem TwoParty.Party} {B B' : Boundary TwoParty.Party}
    (hR : R = R') (hB : B = B') (p : Program R B)
    (hp : p.IsHonestClassical) :
    (cast (by cases hR; cases hB; rfl) p : Program R' B').IsHonestClassical := by
  subst R'
  subst B'
  exact hp

/-- Selecting a fixed embedded record subvector is an honest-classical continuation. -/
theorem selectedRecordContinuation_isHonestClassical
    {n M : ℕ} (f : Fin n ↪ Fin M) :
    (Measurement.selectedRecordContinuation f).IsHonestClassical := by
  unfold Measurement.selectedRecordContinuation
  refine isHonestClassical_castBoundary (by
    apply congrArg Boundary.leaf
    change ((TwoParty.system (Measurement.CompletedLocalRecord M)
      (Measurement.CompletedLocalRecord M)).set .alice (Measurement.SelectedLocalRecord M n)).set
      .bob (Measurement.SelectedLocalRecord M n) =
        TwoParty.system (Measurement.SelectedLocalRecord M n) (Measurement.SelectedLocalRecord M n)
    rw [TwoParty.set_alice, TwoParty.set_bob]) _ ?_
  unfold Measurement.selectedRecordAliceAction Measurement.selectedRecordBobAction
    PrivateAction.then PrivateAction.run
  exact .priv _ _
    (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
      (Instrument.functionAndForget_preservesDiagonalBranches
        (Measurement.selectedLocalRecord f)))
    (.priv _ _
      (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.functionAndForget_preservesDiagonalBranches
          (Measurement.selectedLocalRecord f))) .done)

/-- Discarding completed record registers is an honest-classical continuation. -/
theorem discardCompletedRecords_isHonestClassical (M : ℕ) :
    (Measurement.discardCompletedRecords M).IsHonestClassical := by
  unfold Measurement.discardCompletedRecords
  refine isHonestClassical_castBoundary (by
    apply congrArg Boundary.leaf
    change ((TwoParty.system (Measurement.CompletedLocalRecord M)
      (Measurement.CompletedLocalRecord M)).set .alice Unit).set .bob Unit =
        TwoParty.system Unit Unit
    rw [TwoParty.set_alice, TwoParty.set_bob]) _ ?_
  unfold Measurement.discardCompletedAliceAction Measurement.discardCompletedBobAction
    PrivateAction.then PrivateAction.run
  exact .priv _ _
    (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
      (Instrument.discardToUnit_preservesDiagonalBranches
        (A := Measurement.CompletedLocalRecord M)))
    (.priv _ _
      (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.discardToUnit_preservesDiagonalBranches
          (A := Measurement.CompletedLocalRecord M))) .done)

/-- The quota-dependent selected-record or abort continuation is honest-classical. -/
theorem quotaSelectionContinuation_isHonestClassical
    (N nK mZ mX : ℕ) (omega : Sampling.RawControl N) :
    (Measurement.quotaSelectionContinuation N nK mZ mX omega).IsHonestClassical := by
  by_cases h : Sampling.HasQuotas nK mZ mX omega
  · have hleaf : Measurement.lateSelectionLeaf N nK mZ mX omega =
        .leaf (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)) := by
      simp [Measurement.lateSelectionLeaf, h]
    unfold Measurement.quotaSelectionContinuation
    split
    · exact isHonestClassical_castBoundary hleaf.symm
        (Measurement.selectedRecordContinuation (Sampling.selectedEmbedding omega h))
        (selectedRecordContinuation_isHonestClassical (Sampling.selectedEmbedding omega h))
    · contradiction
  · have hleaf : Measurement.lateSelectionLeaf N nK mZ mX omega =
        .leaf Measurement.lateSelectionAbortSystem := by
      simp [Measurement.lateSelectionLeaf, h]
    unfold Measurement.quotaSelectionContinuation
    split
    · contradiction
    · exact isHonestClassical_castBoundary hleaf.symm
        (Measurement.discardCompletedRecords N) (discardCompletedRecords_isHonestClassical N)

/-- Late basis announcements, public shuffling, quota selection, and their dependent multipartite
systems form an honest-classical program. -/
theorem latePublicSelectionProgram_isHonestClassical (N nK mZ mX : ℕ) :
    (Measurement.latePublicSelectionProgram N nK mZ mX).IsHonestClassical := by
  have hAlice :
      (Measurement.completedBasisAliceAnnouncement N).PreservesHonestRegistersDiagonal := by
    unfold Measurement.completedBasisAliceAnnouncement
    exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.nondemolitionReadout_preservesDiagonalBranches
        (Measurement.completedBasisString N))
  have hBob (a : Fin N → Measurement.Basis) :
      (Measurement.completedBasisBobAnnouncement N a).PreservesHonestRegistersDiagonal := by
    unfold Measurement.completedBasisBobAnnouncement
    exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.nondemolitionReadout_preservesDiagonalBranches
        (Measurement.completedBasisString N))
  have hShuffle (a b : Fin N → Measurement.Basis) :
      (Measurement.shuffleAnnouncement N a b).PreservesHonestRegistersDiagonal := by
    unfold Measurement.shuffleAnnouncement Measurement.uniformShuffleInstrument
    exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.uniformChoice_preservesDiagonalBranches _ fun _ =>
        Instrument.nondemolitionReadout_preservesDiagonalBranches (fun _ => ()))
  unfold Measurement.latePublicSelectionProgram AnnouncedAction.then
  refine .announced _ _ hAlice (fun a => .announced _ _ (hBob a)
    (fun b => .announced _ _ (hShuffle a b) (fun order => ?_)))
  refine isHonestClassical_castInput (by
    change TwoParty.system (Measurement.CompletedLocalRecord N)
      (Measurement.CompletedLocalRecord N) =
      (((TwoParty.system (Measurement.CompletedLocalRecord N)
        (Measurement.CompletedLocalRecord N)).set
        .alice (Measurement.CompletedLocalRecord N)).set .bob
          (Measurement.CompletedLocalRecord N)).set
        .alice (Measurement.CompletedLocalRecord N)
    rw [TwoParty.set_alice, TwoParty.set_bob, TwoParty.set_alice]) _
    (quotaSelectionContinuation_isHonestClassical N nK mZ mX ⟨a, b, order⟩)

/-- The parameter-estimation announcement loop preserves the recursive classical-storage
certificate whenever every continuation does. -/
theorem peAnnouncementLoop_isHonestClassical
    (n r : ℕ) (idx : Fin r → Fin n)
    {T : TypedLOCC.TList}
    (cont : (Fin r → Fin 2) → (Fin r → Fin 2) →
      Program (FinalStage.rawSystem n) (Boundary.uniform (FinalStage.rawSystem n) T))
    (hcont : ∀ a b, (cont a b).IsHonestClassical) :
    (peAnnouncementLoop n r idx cont).IsHonestClassical := by
  induction r with
  | zero => exact hcont Fin.elim0 Fin.elim0
  | succ r ih =>
      rw [peAnnouncementLoop_succ]
      refine .announced _ _
        (announcedReadout_preservesHonestRegistersDiagonal _
          (localRegisterBit n (idx 0) .bob) (LOCC.outcomeDigit 2).symm) (fun b => ?_)
      refine isHonestClassical_castInput (by
        simp only [bobPEBitAnnouncement, peBitAnnouncement,
          AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]) _ ?_
      refine .announced _ _
        (announcedReadout_preservesHonestRegistersDiagonal _
          (localRegisterBit n (idx 0) .alice) (LOCC.outcomeDigit 2).symm) (fun a => ?_)
      refine isHonestClassical_castInput (by
        simp only [alicePEBitAnnouncement, peBitAnnouncement,
          AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]) _ ?_
      exact ih (fun j => idx j.succ) _ fun as bs =>
        hcont (Fin.cons (LOCC.outcomeDigit 2 a) as) (Fin.cons (LOCC.outcomeDigit 2 b) bs)

/-- The fused error-verification, seed, tag, and syndrome announcement stage is
honest-classical. -/
theorem fusedStage_isHonestClassical
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leak : ℕ)
    (scheme : ECScheme n peSel leak) :
    (fusedStage n ℓ ℓEV peSel leak scheme
      (fun _ => Program.done)).IsHonestClassical := by
  have haction :
      (fusedAnnouncement n ℓ ℓEV peSel leak scheme).PreservesHonestRegistersDiagonal := by
    unfold fusedAnnouncement fusedReadoutInstrument
    exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.uniformChoice_preservesDiagonalBranches _ fun r =>
        Instrument.nondemolitionReadout_preservesDiagonalBranches
          (QKD.BB84.Model.evTagSynOf n ℓ ℓEV peSel leak scheme r))
  unfold fusedStage AnnouncedAction.then
  refine .announced _ _ haction (fun _ => ?_)
  exact isHonestClassical_castInput (by
    exact ((FinalStage.rawSystem n).set_self .alice).symm) _ .done

/-- The full parameter-estimation and fused predecision prefix is honest-classical. -/
theorem directPreDecisionProgram_isHonestClassical
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leak : ℕ)
    (scheme : ECScheme n peSel leak) :
    (QKD.BB84.directPreDecisionProgram n m ℓ ℓEV peSel leak scheme).IsHonestClassical := by
  unfold QKD.BB84.directPreDecisionProgram
  exact peAnnouncementLoop_isHonestClassical n _ _ _
    (fun _ _ => fusedStage_isHonestClassical n ℓ ℓEV peSel leak scheme)

/-- Each accept/abort continuation after the public decision flag is honest-classical. -/
theorem finalStageContinuation_isHonestClassical
    (n ℓ : ℕ) (peSel : Fin n → Bool) (leak : ℕ)
    (scheme : ECScheme n peSel leak)
    (seed : KeyHashSeed n ℓ peSel) (syn : Fin (2 ^ leak))
    (flag : Fin 2) :
    (FinalStage.continuation n ℓ peSel leak scheme seed syn flag).IsHonestClassical := by
  unfold FinalStage.continuation
  split
  · next hflag =>
    have hAlice : PrivateAction.PreservesHonestRegistersDiagonal
        (FinalStage.aliceKeyAction n ℓ peSel seed flag) := by
      unfold FinalStage.aliceKeyAction
      exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.functionAndForget_preservesDiagonalBranches _)
    have hBob : PrivateAction.PreservesHonestRegistersDiagonal
        (FinalStage.bobKeyAction n ℓ peSel leak scheme seed syn flag) := by
      unfold FinalStage.bobKeyAction
      exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.functionAndForget_preservesDiagonalBranches _)
    have haccept : Program.IsHonestClassical
        (FinalStage.acceptContinuation n ℓ peSel leak scheme seed syn flag) := by
      unfold FinalStage.acceptContinuation
      refine isHonestClassical_castBoundary (by
        apply congrArg Boundary.leaf
        change ((TwoParty.system (Fin (2 ^ n)) (Fin (2 ^ n))).set .alice (Fin (2 ^ ℓ))).set
          .bob (Fin (2 ^ ℓ)) = TwoParty.system (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
        rw [TwoParty.set_alice, TwoParty.set_bob]) _ ?_
      exact .priv _ _ hAlice (.priv _ _ hBob .done)
    exact isHonestClassical_castBoundary (by simp [FinalStage.flagBoundary, hflag]) _ haccept
  · next hflag =>
    have hAlice : PrivateAction.PreservesHonestRegistersDiagonal
        (FinalStage.discardAliceRaw n) := by
      unfold FinalStage.discardAliceRaw
      exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.discardToUnit_preservesDiagonalBranches (A := Fin (2 ^ n)))
    have hBob : PrivateAction.PreservesHonestRegistersDiagonal
        (FinalStage.discardBobRaw n) := by
      unfold FinalStage.discardBobRaw
      exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.discardToUnit_preservesDiagonalBranches (A := Fin (2 ^ n)))
    have habort : (FinalStage.discardKeys n).IsHonestClassical := by
      unfold FinalStage.discardKeys
      refine isHonestClassical_castBoundary (by
        apply congrArg Boundary.leaf
        change ((TwoParty.system (Fin (2 ^ n)) (Fin (2 ^ n))).set .alice Unit).set .bob Unit =
          TwoParty.system Unit Unit
        rw [TwoParty.set_alice, TwoParty.set_bob]) _ ?_
      exact .priv _ _ hAlice (.priv _ _ hBob .done)
    exact isHonestClassical_castBoundary (by simp [FinalStage.flagBoundary, hflag]) _ habort

/-- The decision announcement and its exact dependent accept/abort continuations are
honest-classical. -/
theorem finalStageProgram_isHonestClassical
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leak : ℕ)
    (scheme : ECScheme n peSel leak) (d Q' : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (tag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leak)) :
    (FinalStage.program n m ℓ ℓEV peSel xSel leak scheme d Q'
      as bs st tag syn).IsHonestClassical := by
  have hdecision :
      (FinalStage.decisionAnnouncement n m ℓEV peSel xSel leak scheme d Q'
        as bs st.2 tag syn).PreservesHonestRegistersDiagonal := by
    unfold FinalStage.decisionAnnouncement
    exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.nondemolitionReadout_preservesDiagonalBranches
        (QKD.BB84.Model.acceptFlagOf n m ℓEV peSel xSel leak scheme d Q'
          as bs st.2 tag syn))
  unfold FinalStage.program AnnouncedAction.then
  refine .announced _ _ hdecision (fun flag => ?_)
  exact isHonestClassical_castInput (by
    simp only [FinalStage.decisionAnnouncement, AnnouncedAction.out_ofInstrument,
      FinalStage.rawSystem, TwoParty.set_bob]
    rfl) _
    (finalStageContinuation_isHonestClassical n ℓ peSel leak scheme st.1 syn flag)

/-- The complete raw-register classical tail is honest-classical. -/
theorem rawClassicalTailProgram_isHonestClassical
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leak : ℕ)
    (scheme : ECScheme n peSel leak) (d Q' : ℝ) :
    (QKD.BB84.rawClassicalTailProgram n m ℓ ℓEV peSel xSel leak scheme d Q').IsHonestClassical := by
  unfold QKD.BB84.rawClassicalTailProgram
  apply Program.IsHonestClassical.graft
    (directPreDecisionProgram_isHonestClassical n m ℓ ℓEV peSel leak scheme)
  intro e
  have hSystem : FinalStage.rawSystem n =
      (classicalPreDecisionBoundary n m ℓ ℓEV peSel leak).system e := by
    simp only [Boundary.uniform_system]
  exact isHonestClassical_cast hSystem rfl _
    (finalStageProgram_isHonestClassical n m ℓ ℓEV peSel xSel leak scheme d Q'
      (classicalTailExitEquiv n m ℓ ℓEV peSel leak e).alicePE
      (classicalTailExitEquiv n m ℓ ℓEV peSel leak e).bobPE
      (classicalTailExitEquiv n m ℓ ℓEV peSel leak e).seedPair
      (classicalTailExitEquiv n m ℓ ℓEV peSel leak e).evTag
      (classicalTailExitEquiv n m ℓ ℓEV peSel leak e).syndrome)

/-- Converting selected measured bits into the raw-register representation is honest-classical. -/
theorem selectedBitsToRawProgram_isHonestClassical (M n : ℕ) :
    (QKD.BB84.selectedBitsToRawProgram M n).IsHonestClassical := by
  unfold QKD.BB84.selectedBitsToRawProgram
  refine isHonestClassical_castBoundary (by
    apply congrArg Boundary.leaf
    change ((TwoParty.system (Measurement.SelectedLocalRecord M n)
      (Measurement.SelectedLocalRecord M n)).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n)) =
        TwoParty.system (Fin (2 ^ n)) (Fin (2 ^ n))
    rw [TwoParty.set_alice, TwoParty.set_bob]) _ ?_
  unfold QKD.BB84.selectedBitsToRawAliceAction QKD.BB84.selectedBitsToRawBobAction
    PrivateAction.then PrivateAction.run
  exact .priv _ _
    (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
      (Instrument.functionAndForget_preservesDiagonalBranches selectedBitsToRaw))
    (.priv _ _
      (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
        (Instrument.functionAndForget_preservesDiagonalBranches selectedBitsToRaw)) .done)

/-- The successful selected-record continuation through the full raw classical tail is
honest-classical. -/
theorem successfulCompleteContinuation_isHonestClassical
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.successfulCompleteContinuation
      N nK mZ mX ℓ ℓEV leakEC ec delta Q).IsHonestClassical := by
  unfold QKD.BB84.successfulCompleteContinuation
  exact Program.IsHonestClassical.graft
    (selectedBitsToRawProgram_isHonestClassical N (nK + mZ + mX))
    (fun _ => rawClassicalTailProgram_isHonestClassical
      (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX)
      leakEC ec delta Q)

/-- Every success or abort exit of the late-selection boundary has an honest-classical complete
continuation. -/
theorem completeContinuation_isHonestClassical
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (QKD.BB84.completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q e).IsHonestClassical := by
  unfold QKD.BB84.completeContinuation
  split
  · next h =>
    have hstart : Measurement.weightedSelectedRecordSystem N (nK + mZ + mX) =
        (Measurement.lateSelectionBoundary N nK mZ mX).system e := by
      symm
      rcases e with ⟨a, b, order, leaf⟩
      have h' : Sampling.HasQuotas nK mZ mX ⟨a, b, order⟩ := by
        simpa [QKD.BB84.lateSelectionExitEquiv] using h
      change (Measurement.lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).system leaf = _
      rw [QKD.BB84.lateSelectionLeaf_system, ite_eq_left h']
    have hout :
        QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
            (@Sampling.packedPESel nK mZ mX) leakEC =
          QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e := by
      symm
      simp [QKD.BB84.completeContinuationBoundary, h]
    exact isHonestClassical_castInput hstart _
      (isHonestClassical_castBoundary hout _
        (successfulCompleteContinuation_isHonestClassical
          N nK mZ mX ℓ ℓEV leakEC ec delta Q))
  · next h =>
    have hstart : Measurement.lateSelectionAbortSystem =
        (Measurement.lateSelectionBoundary N nK mZ mX).system e := by
      symm
      rcases e with ⟨a, b, order, leaf⟩
      have h' : ¬Sampling.HasQuotas nK mZ mX ⟨a, b, order⟩ := by
        simpa [QKD.BB84.lateSelectionExitEquiv] using h
      change (Measurement.lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).system leaf = _
      rw [QKD.BB84.lateSelectionLeaf_system, ite_eq_right h']
    have hout : (.leaf Measurement.lateSelectionAbortSystem : Boundary TwoParty.Party) =
        QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e := by
      symm
      simp [QKD.BB84.completeContinuationBoundary, h]
    exact isHonestClassical_castInput hstart _
      (isHonestClassical_castBoundary hout Program.done .done)

end QKD.BB84
