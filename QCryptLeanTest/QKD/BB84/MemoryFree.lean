import QCryptLean.QKD.BB84.CompleteOutput
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the complete measure-first BB84 classical tail

The fixtures inspect the explicit packed masks, local private-basis erasure, chronological decoder,
quota branches, natural key registers, and protocol constructors.
-/

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84 QKD.BB84.FiniteKey QKD.BB84.Measurement

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
    selectedZ.2 = selectedX.2 := by
  rfl

/-- The retained selected bit is read directly from its bit string. -/
theorem selectedZ_bit_readback :
    selectedZ.2 0 = 1 := by
  rfl

/-- Alice erases her basis copy with the actual function-and-forget instrument. -/
theorem forgetAliceBases_constructor (N n : ℕ) :
    forgetAliceBases (B := Measurement.SelectedLocalRecord N n) N n =
      PrivateAction.ofInstrument
        (R := system (Measurement.SelectedLocalRecord N n) (Measurement.SelectedLocalRecord N n))
        .alice (Instrument.functionAndForget (fun q : Measurement.SelectedLocalRecord N n => q.2))
          := rfl

/-- Both erasure actions accept a named continuation at its natural raw system. -/
theorem forgetBases_shape (N n : ℕ)
    (k : Program (system (Measurement.Bits n) (Measurement.Bits n))) :
    ((forgetAliceBases N n).then ((forgetBobBases N n).then k)).boundary = k.boundary := rfl

/-- A two-cell raw PE record with nonconstant Bob and Alice values. -/
def nonconstantRawTwo
    (fused : QKD.BB84.FusedPublic 2 0 0 (fun _ => false) 0) :
    QKD.BB84.PreDecisionRaw (min 2 2)
      (QKD.BB84.FusedPublic 2 0 0 (fun _ => false) 0) where
  bobPERaw i := if i.val = 0 then 0 else 1
  alicePERaw i := if i.val = 0 then 1 else 0
  fusedRaw := fused

/-- The first PE coordinate in the concrete two-cell decoder fixture. -/
def peIndexZero : Fin (min 2 2) :=
  ⟨0, by simp⟩

/-- The second PE coordinate in the concrete two-cell decoder fixture. -/
def peIndexOne : Fin (min 2 2) :=
  ⟨1, by simp⟩

/-- The semantic decoder reads Bob's and Alice's values from their distinct chronological
coordinates without swapping the two parties. -/
theorem nonconstantRawTwo_chronology
    (fused : QKD.BB84.FusedPublic 2 0 0 (fun _ => false) 0) :
    let d := QKD.BB84.classicalTailRawDataEquiv 2 2 0 0 (fun _ => false) 0
      (nonconstantRawTwo fused)
    d.bobPE peIndexZero = 0 ∧
      d.bobPE peIndexOne = 1 ∧
      d.alicePE peIndexZero = 1 ∧
      d.alicePE peIndexOne = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A literal two-round transcript with Bob/Alice cells `0/1` then `1/0`, followed by the fused
raw cell.  It is constructed without using either decoder inverse. -/
def literalTranscriptTwo
    (fused : QKD.BB84.FusedPublic 2 0 0 (fun _ => false) 0) :
    Transcript (QKD.BB84.classicalTailWord 2 2 0 0 (fun _ => false) 0) :=
  (0, (1, (1, (0, (fused, ())))))

/-- The actual transcript-to-raw-to-semantic path preserves the literal Bob-then-Alice cell
chronology. -/
theorem literalTranscriptTwo_decoder_path
    (fused : QKD.BB84.FusedPublic 2 0 0 (fun _ => false) 0) :
    let d := QKD.BB84.classicalTailDataEquiv 2 2 0 0 (fun _ => false) 0
      (literalTranscriptTwo fused)
    d.bobPE peIndexZero = 0 ∧
      d.bobPE peIndexOne = 1 ∧
      d.alicePE peIndexZero = 1 ∧
      d.alicePE peIndexOne = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A semantic record with no PE cells and explicitly supplied fused values. -/
def fusedSemanticZero (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Measurement.Bits ℓEV) (syn : Measurement.Bits leakEC) :
    QKD.BB84.ClassicalTailData 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC where
  alicePE i := Fin.elim0 i
  bobPE i := Fin.elim0 i
  seedPair := seedPair
  evTag := tag
  syndrome := syn

/-- A literal zero-PE transcript cell using the natural public values, independently of the
semantic decoder inverse. -/
noncomputable def literalFusedTranscript (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Measurement.Bits ℓEV) (syn : Measurement.Bits leakEC) :
    Transcript (QKD.BB84.classicalTailWord 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC) :=
  ((seedPair, tag, syn), ())

/-- The literal fused transcript decoder recovers its supplied seed pair,
verification tag, and syndrome coordinates exactly. -/
theorem fusedTranscript_decoder_values (ℓ ℓEV leakEC : ℕ)
    (seedPair : KeyHashSeedPairEV 0 ℓ ℓEV (fun i => Fin.elim0 i))
    (tag : Measurement.Bits ℓEV) (syn : Measurement.Bits leakEC) :
    let d := QKD.BB84.classicalTailDataEquiv 0 0 ℓ ℓEV (fun i => Fin.elim0 i) leakEC
      (literalFusedTranscript ℓ ℓEV leakEC seedPair tag syn)
    d.seedPair = seedPair ∧ d.evTag = tag ∧ d.syndrome = syn := by
  exact ⟨rfl, rfl, rfl⟩

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
  rw [Equiv.apply_symm_apply, ite_eq_left h]

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
  rw [Equiv.apply_symm_apply, ite_eq_right h]

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

/-- The final package uses the complete program and its heterogeneous local output layout. -/
theorem weightedBB84_fields
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).program =
        QKD.BB84.construction pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q ∧
      (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).layout =
        (QKD.BB84.construction pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).outputLayout
          (by decide) := by
  exact ⟨rfl, rfl⟩

end ClassicalTailAudit

