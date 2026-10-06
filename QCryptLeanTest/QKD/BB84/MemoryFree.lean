import QCryptLean.QKD.BB84.Program
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the complete measure-first BB84 classical tail

The fixtures inspect the explicit packed masks, local private-basis erasure, chronological decoder,
quota branches, final output multipartite systems, and protocol constructors.  They do not use any
of the six supporting arithmetic and register-bit theorems.
-/

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Engine

open QKD.BB84
open QKD.BB84.Reduction

namespace ClassicalTailAudit

/-- The asymmetric `1/2/1` packed roles have key, Z-test, Z-test, X-test masks in order. -/
theorem asymmetric_masks :
    ((@Sampling.packedPESel 1 2 1 0, @Sampling.packedXSel 1 2 1 0),
      (@Sampling.packedPESel 1 2 1 1, @Sampling.packedXSel 1 2 1 1),
      (@Sampling.packedPESel 1 2 1 2, @Sampling.packedXSel 1 2 1 2),
      (@Sampling.packedPESel 1 2 1 3, @Sampling.packedXSel 1 2 1 3)) =
      ((false, false), (true, false), (true, false), (true, true)) := by
  decide

/-- With all quotas empty, the two packed masks have their unique empty domain. -/
theorem empty_masks (i : Fin (0 + 0 + 0)) :
    (@Sampling.packedPESel 0 0 0 i, @Sampling.packedXSel 0 0 0 i) =
      (false, false) := by
  exact Fin.elim0 i

/-- With no Z-test quota, the non-key role is an X-test role. -/
theorem noZTest_masks :
    ((@Sampling.packedPESel 1 0 1 0, @Sampling.packedXSel 1 0 1 0),
      (@Sampling.packedPESel 1 0 1 1, @Sampling.packedXSel 1 0 1 1)) =
      ((false, false), (true, true)) := by
  decide

/-- With no X-test quota, the non-key role is a Z-test role. -/
theorem noXTest_masks :
    ((@Sampling.packedPESel 1 1 0 0, @Sampling.packedXSel 1 1 0 0),
      (@Sampling.packedPESel 1 1 0 1, @Sampling.packedXSel 1 1 0 1)) =
      ((false, false), (true, false)) := by
  decide

/-- Two selected local records with the same bit and different private bases. -/
def selectedZ : Measurement.SelectedLocalRecord 1 1 :=
  (fun _ => Measurement.Basis.z, fun _ => 1)

/-- The corresponding record with the opposite private basis. -/
def selectedX : Measurement.SelectedLocalRecord 1 1 :=
  (fun _ => Measurement.Basis.x, fun _ => 1)

/-- Local conversion erases the full private basis copy while retaining the selected bit. -/
theorem privateBasis_erased_equalBits :
    QKD.BB84.selectedBitsToRaw selectedZ = QKD.BB84.selectedBitsToRaw selectedX := by
  rfl

/-- The concrete encoded selected bit is read back as one without using the general
register-bit theorem. -/
theorem selectedZ_registerBit_readback :
    LOCC.registerBit 1 0 (QKD.BB84.selectedBitsToRaw selectedZ) = 1 := by
  rfl

/-- Alice's local erasure node is the actual function-and-forget instrument. -/
theorem selectedBitsToRawAliceAction_constructor (N n : ℕ) :
    QKD.BB84.selectedBitsToRawAliceAction N n =
      PrivateAction.ofInstrument .alice
        (Instrument.functionAndForget QKD.BB84.selectedBitsToRaw) := by
  rfl

/-- The basis-erasure program runs Alice's local conversion and then Bob's. -/
theorem selectedBitsToRawProgram_shape (N n : ℕ) :
    HEq (QKD.BB84.selectedBitsToRawProgram N n)
      (Program.priv (QKD.BB84.selectedBitsToRawAliceAction N n)
        (Program.priv (QKD.BB84.selectedBitsToRawBobAction N n) Program.done)) := by
  unfold QKD.BB84.selectedBitsToRawProgram
  exact cast_heq _ _

/-- A two-cell raw PE record with nonconstant Bob and Alice values. -/
def nonconstantRawTwo
    (fused : Fin (QKD.BB84.Model.bb84AnnounceCard 2 0 0 (fun _ => false) 0)) :
    QKD.BB84.PreDecisionRaw (2 - bb84KeyRoundCount 2 2)
      (QKD.BB84.Model.bb84AnnounceCard 2 0 0 (fun _ => false) 0) where
  bobPERaw i := if i.val = 0 then 0 else 1
  alicePERaw i := if i.val = 0 then 1 else 0
  fusedRaw := fused

/-- The first PE coordinate in the concrete two-cell decoder fixture. -/
def peIndexZero : Fin (2 - bb84KeyRoundCount 2 2) :=
  ⟨0, by simp [bb84KeyRoundCount]⟩

/-- The second PE coordinate in the concrete two-cell decoder fixture. -/
def peIndexOne : Fin (2 - bb84KeyRoundCount 2 2) :=
  ⟨1, by simp [bb84KeyRoundCount]⟩

/-- The semantic decoder reads Bob's and Alice's values from their distinct chronological
coordinates without swapping the two parties. -/
theorem nonconstantRawTwo_chronology
    (fused : Fin (QKD.BB84.Model.bb84AnnounceCard 2 0 0 (fun _ => false) 0)) :
    let d := QKD.BB84.classicalTailRawDataEquiv 2 2 0 0 (fun _ => false) 0
      (nonconstantRawTwo fused)
    d.bobPE peIndexZero = LOCC.outcomeDigit 2 0 ∧
      d.bobPE peIndexOne = LOCC.outcomeDigit 2 1 ∧
      d.alicePE peIndexZero = LOCC.outcomeDigit 2 1 ∧
      d.alicePE peIndexOne = LOCC.outcomeDigit 2 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A literal two-round transcript with Bob/Alice cells `0/1` then `1/0`, followed by the fused
raw cell.  It is constructed without using either decoder inverse. -/
def literalTranscriptTwo
    (fused : Fin (QKD.BB84.Model.bb84AnnounceCard 2 0 0 (fun _ => false) 0)) :
    Transcript (QKD.BB84.classicalTailWord 2 2 0 0 (fun _ => false) 0) :=
  (0, (1, (1, (0, (fused, ())))))

/-- The actual transcript-to-raw-to-semantic path preserves the literal Bob-then-Alice cell
chronology. -/
theorem literalTranscriptTwo_decoder_path
    (fused : Fin (QKD.BB84.Model.bb84AnnounceCard 2 0 0 (fun _ => false) 0)) :
    let d := QKD.BB84.classicalTailDataEquiv 2 2 0 0 (fun _ => false) 0
      (literalTranscriptTwo fused)
    d.bobPE peIndexZero = LOCC.outcomeDigit 2 0 ∧
      d.bobPE peIndexOne = LOCC.outcomeDigit 2 1 ∧
      d.alicePE peIndexZero = LOCC.outcomeDigit 2 1 ∧
      d.alicePE peIndexOne = LOCC.outcomeDigit 2 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A semantic record with no PE cells and explicitly supplied fused values. -/
def fusedSemanticZero (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC)) :
    QKD.BB84.ClassicalTailData 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC where
  alicePE i := Fin.elim0 i
  bobPE i := Fin.elim0 i
  seedPair := seedPair
  evTag := tag
  syndrome := syn

/-- A literal zero-PE transcript cell using the actual fused public encoder, independently of the
semantic decoder inverse. -/
noncomputable def literalFusedTranscript (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC)) :
    Transcript (QKD.BB84.classicalTailWord 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC) :=
  (QKD.BB84.fusedPublicEquiv 0 ℓ ℓEV
      (fun i => Fin.elim0 i) leakEC
      (Fintype.equivFin _ seedPair, finProdFinEquiv (tag, syn)), ())

/-- The literal fused transcript decoder recovers its independently encoded seed pair,
verification tag, and syndrome coordinates exactly. -/
theorem fusedTranscript_decoder_values (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC)) :
    let d := QKD.BB84.classicalTailDataEquiv 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC
      (literalFusedTranscript ℓ ℓEV leakEC seedPair tag syn)
    d.seedPair = seedPair ∧ d.evTag = tag ∧ d.syndrome = syn := by
  change
    let d := QKD.BB84.classicalTailRawDataEquiv 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC
      { bobPERaw := fun i => Fin.elim0 i
        alicePERaw := fun i => Fin.elim0 i
        fusedRaw := QKD.BB84.fusedPublicEquiv 0 ℓ ℓEV
          (fun i => Fin.elim0 i) leakEC
          (Fintype.equivFin _ seedPair, finProdFinEquiv (tag, syn)) }
    d.seedPair = seedPair ∧ d.evTag = tag ∧ d.syndrome = syn
  simp only [QKD.BB84.classicalTailRawDataEquiv, QKD.BB84.Model.announcedSeed,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply, true_and]

/-- The retained public tail is exactly the Bob-then-Alice PE loop followed by the fused cell. -/
theorem directPreDecisionProgram_shape
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    QKD.BB84.directPreDecisionProgram n m ℓ ℓEV peSel leakEC ec =
      QKD.BB84.peAnnouncementLoop
        (T := .cons (QKD.BB84.FusedPublic n ℓ ℓEV peSel leakEC) .nil) n
        (n - bb84KeyRoundCount n m)
        (bb84PERoundIdx (m := m) peSel) (fun _ _ =>
          QKD.BB84.fusedStage n ℓ ℓEV peSel leakEC ec
            (fun _ : QKD.BB84.FusedPublic n ℓ ℓEV peSel leakEC =>
              (Program.done : Program (FinalStage.rawSystem n)
                (.leaf (FinalStage.rawSystem n))))) := by
  rfl

/-- The canonical empty raw control. -/
def emptyControl : Sampling.RawControl 0 := Sampling.defaultRawControl 0

/-- At zero rounds and zero quotas the attached continuation is the successful raw tail. -/
theorem zeroRound_zeroQuota_success :
    QKD.BB84.completeContinuationBoundary 0 0 0 0 0 0 0
        (Measurement.lateSelectionExit 0 0 0 0 emptyControl) =
      QKD.BB84.rawClassicalTailBoundary 0 0 0 0 (@Sampling.packedPESel 0 0 0) 0 := by
  have h : Sampling.HasQuotas 0 0 0 emptyControl := by decide
  change (if Sampling.HasQuotas 0 0 0
      ((QKD.BB84.lateSelectionExitEquiv 0 0 0 0)
        ((QKD.BB84.lateSelectionExitEquiv 0 0 0 0).symm emptyControl)) then
      QKD.BB84.rawClassicalTailBoundary 0 0 0 0 (@Sampling.packedPESel 0 0 0) 0
    else .leaf Measurement.lateSelectionAbortSystem) = _
  rw [Equiv.apply_symm_apply, if_pos h]

/-- A positive quota at zero rounds selects the actual Unit/Unit shortage leaf. -/
theorem zeroRound_positiveQuota_abort :
    QKD.BB84.completeContinuationBoundary 0 1 0 0 0 0 0
        (Measurement.lateSelectionExit 0 1 0 0 emptyControl) =
      .leaf Measurement.lateSelectionAbortSystem := by
  have h : ¬ Sampling.HasQuotas 1 0 0 emptyControl := by decide
  change (if Sampling.HasQuotas 1 0 0
      ((QKD.BB84.lateSelectionExitEquiv 0 1 0 0)
        ((QKD.BB84.lateSelectionExitEquiv 0 1 0 0).symm emptyControl)) then
      QKD.BB84.rawClassicalTailBoundary 1 0 0 0 (@Sampling.packedPESel 1 0 0) 0
    else .leaf Measurement.lateSelectionAbortSystem) = _
  rw [Equiv.apply_symm_apply, if_neg h]

/-- The accepting final exit has Alice's and Bob's locally owned key multipartite system. -/
theorem final_accept_system (ℓ : ℕ) :
    (FinalStage.boundary ℓ).system (⟨0, ()⟩ : (FinalStage.boundary ℓ).Exit) =
      FinalStage.keySystem ℓ := by
  rfl

/-- The aborting final exit has the key-free Unit/Unit multipartite system. -/
theorem final_abort_system (ℓ : ℕ) :
    (FinalStage.boundary ℓ).system (⟨1, ()⟩ : (FinalStage.boundary ℓ).Exit) =
      FinalStage.abortSystem := by
  rfl

/-- The final layout names the two local key owners and assigns the accepted key length. -/
theorem final_accept_localOwnership (ℓ : ℕ) :
    (FinalStage.outputLayout ℓ).alice = Party.alice ∧
      (FinalStage.outputLayout ℓ).bob = Party.bob ∧
      (FinalStage.outputLayout ℓ).disposition
          (⟨0, ()⟩ : (FinalStage.boundary ℓ).Exit) =
        BoundaryKeyLayout.Disposition.accept ℓ := by
  exact ⟨rfl, rfl, rfl⟩

/-- The final abort flag is recorded as key-free. -/
theorem final_abort_disposition (ℓ : ℕ) :
    (FinalStage.outputLayout ℓ).disposition
        (⟨1, ()⟩ : (FinalStage.boundary ℓ).Exit) =
      BoundaryKeyLayout.Disposition.abort := by
  rfl

/-- Transport a complete exit backward along an equality of public boundaries. -/
def exitOfBoundaryEq {B C : Boundary Party} (h : B = C) (e : C.Exit) : B.Exit :=
  h.symm ▸ e

/-- The complete outer graft delegates disposition to the quota-dependent child layout. -/
theorem weightedLayout_delegates
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (c : (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e).Exit) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm ⟨e, c⟩) =
      (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC e).disposition c := by
  let g := (Measurement.lateSelectionBoundary N nK mZ mX).graftExitEquiv
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
  have hg : g (g.symm ⟨e, c⟩) = ⟨e, c⟩ := g.apply_symm_apply ⟨e, c⟩
  unfold QKD.BB84.outputLayout QKD.BB84.exitEquiv
    QKD.OutputLayout.graftFixedParties
  dsimp only
  change (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
      (g (g.symm ⟨e, c⟩)).1).disposition (g (g.symm ⟨e, c⟩)).2 = _
  rw [hg]

/-- Boundary transport reads disposition at the correspondingly transported exit. -/
theorem transport_disposition
    {B C : Boundary Party} (h : B = C) (L : QKD.OutputLayout B) (e : C.Exit) :
    (QKD.OutputLayout.transport h L).disposition e =
      L.disposition (h.symm ▸ e) := by
  subst C
  rfl

/-- On shortage, the new outer grafted layout records abort rather than a key-bearing leaf. -/
theorem weightedLayout_shortage_abort
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (h : ¬ Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX e))
    (c : (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e).Exit) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm ⟨e, c⟩) =
      BoundaryKeyLayout.Disposition.abort := by
  rw [weightedLayout_delegates]
  unfold QKD.BB84.completeContinuationOutputLayout
  split
  · contradiction
  · rw [transport_disposition]
    rfl

/-- The unique exit of the final flag-dependent leaf. -/
def finalFlagLeafExit (ℓ : ℕ) (flag : Fin 2) :
    (FinalStage.flagBoundary ℓ flag).Exit := by
  unfold FinalStage.flagBoundary
  split <;> exact ()

/-- One complete raw-tail exit whose final semantic flag is explicit. -/
def rawTailFlagExit (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (pre : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (flag : Fin 2) : (QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).Exit :=
  (Boundary.graftExitEquiv _ _).symm ⟨pre, flag, finalFlagLeafExit ℓ flag⟩

/-- The raw-tail graft delegates the final semantic accept flag to the retained local-key
layout. -/
theorem rawTailFlagZero_accepts
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (pre : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).disposition
        (rawTailFlagExit n m ℓ ℓEV peSel leakEC pre 0) =
      BoundaryKeyLayout.Disposition.accept ℓ := by
  simp [QKD.BB84.rawClassicalTailOutputLayout, rawTailFlagExit,
    QKD.OutputLayout.graftFixedParties, FinalStage.outputLayout, FinalStage.disposition]

/-- The raw-tail graft delegates the final semantic abort flag to the key-free layout. -/
theorem rawTailFlagOne_aborts
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (pre : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).disposition
        (rawTailFlagExit n m ℓ ℓEV peSel leakEC pre 1) =
      BoundaryKeyLayout.Disposition.abort := by
  simp [QKD.BB84.rawClassicalTailOutputLayout, rawTailFlagExit,
    QKD.OutputLayout.graftFixedParties, FinalStage.outputLayout, FinalStage.disposition]

/-- The complete physical program is the late-selection program grafted with its actual
quota-dependent classical continuation. -/
theorem weightedProgram_shape
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    QKD.BB84.program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q =
      (Measurement.weightedLatePublicSelectionProgram pA pB N nK mZ mX).graft
        (QKD.BB84.completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q) := by
  rfl

/-- The final package uses the complete program and its heterogeneous local output layout. -/
theorem weightedBB84_fields
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).program =
        QKD.BB84.program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q ∧
      (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).layout =
        QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC := by
  exact ⟨rfl, rfl⟩

end ClassicalTailAudit

