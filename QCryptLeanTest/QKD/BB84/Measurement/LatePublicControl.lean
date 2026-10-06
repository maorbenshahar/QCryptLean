import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import Mathlib.Util.AssertNoSorry

/-!
# Tests for late public basis control and quota selection

The probes below inspect actual action/program constructors, public metadata, quota branches, and
the classical readout and discard instruments.  Direct instrument coherence probes do not
invoke either whole-program branch theorem.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Measurement
open QKD.BB84.Sampling

namespace LatePublicControlAudit

/-- Rebuilding a completed stream from chronological records makes the stored basis string
directly visible to the late readout. -/
theorem completedBasisString_rebuilt {N : ℕ} (r : Fin N → StoredRecord) :
    completedBasisString N
        ((finishAccEquiv Unit N).symm ((), r), fun i => Fin.elim0 i) =
      storedBasisString r := by
  simp [completedBasisString]

/-- Alice's basis announcement is the actual nondemolition readout with the identity public map. -/
theorem completedBasisAliceAnnouncement_constructor (N : ℕ) :
    completedBasisAliceAnnouncement N =
      AnnouncedAction.ofInstrument Party.alice
        (Instrument.nondemolitionReadout (completedBasisString N)) id := by
  rfl

/-- Bob's basis announcement is the analogous local readout, not a resampled basis string. -/
theorem completedBasisBobAnnouncement_constructor (N : ℕ) (a : Fin N → Basis) :
    completedBasisBobAnnouncement N a =
      AnnouncedAction.ofInstrument Party.bob
        (Instrument.nondemolitionReadout (completedBasisString N)) id := by
  rfl

/-- Each basis-readout raw outcome is announced unchanged. -/
theorem basisAnnouncement_is_id (N : ℕ) (a : Fin N → Basis) :
    (completedBasisAliceAnnouncement N).announce a = a ∧
      (completedBasisBobAnnouncement N a).announce a = a := by
  exact ⟨rfl, rfl⟩

/-- The dependent shuffle instrument is literally uniform choice followed by a one-outcome
nondemolition readout. -/
theorem uniformShuffleInstrument_constructor (N : ℕ)
    (a b : Fin N → Basis) :
    uniformShuffleInstrument N a b =
      Instrument.uniformChoice (fun _ : Shuffle a b =>
        Instrument.nondemolitionReadout (fun _ : CompletedLocalRecord N => ())) := by
  rfl

/-- A sampled shuffle is announced without alteration. -/
theorem shuffleAnnouncement_exact_order (N : ℕ)
    (a b : Fin N → Basis) (order : Shuffle a b) :
    (shuffleAnnouncement N a b).announce (order, ()) = order := by
  rfl

/-- The operation in one sampled shuffle branch carries the exact reciprocal-cardinality
coefficient and does not alter the completed local record. -/
theorem uniformShuffleInstrument_operation (N : ℕ)
    (a b : Fin N → Basis) (order : Shuffle a b) :
    (uniformShuffleInstrument N a b).operation (order, ()) =
      (Fintype.card (Shuffle a b) : ℂ)⁻¹ •
        (Instrument.nondemolitionReadout
          (fun _ : CompletedLocalRecord N => ())).operation () := by
  exact Instrument.uniformChoice_operation _ order ()

/-- Alice's shortage action is the real certified local discard instrument. -/
theorem discardCompletedAliceAction_constructor (N : ℕ) :
    discardCompletedAliceAction N =
      PrivateAction.ofInstrument Party.alice
        (Instrument.discardToUnit (CompletedLocalRecord N)) := by
  rfl

/-- Bob's shortage action is the real certified local discard instrument. -/
theorem discardCompletedBobAction_constructor (N : ℕ) :
    discardCompletedBobAction N =
      PrivateAction.ofInstrument Party.bob
        (Instrument.discardToUnit (CompletedLocalRecord N)) := by
  rfl

/-- The shortage continuation contains exactly two private discards in Alice-then-Bob order. -/
theorem discardCompletedRecords_shape (N : ℕ) :
    HEq (discardCompletedRecords N)
      (Program.priv (discardCompletedAliceAction N)
        (Program.priv (discardCompletedBobAction N) Program.done)) := by
  unfold discardCompletedRecords
  exact cast_heq _ _

/-- The public-control program has the exact Alice-basis, Bob-basis, shuffle order and then uses
the corresponding raw control without resampling either basis string. -/
theorem latePublicSelectionProgram_shape (N nK mZ mX : ℕ) :
    latePublicSelectionProgram N nK mZ mX =
      Program.announced (completedBasisAliceAnnouncement N) fun a =>
        Program.announced (completedBasisBobAnnouncement N a) fun b =>
          Program.announced (shuffleAnnouncement N a b) fun order =>
            cast (by
              apply congrArg (fun R =>
                Program R (lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩))
              change weightedStreamSystem (finishAcc Unit N) 0 =
                (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
                  (CompletedLocalRecord N)).set .bob (CompletedLocalRecord N)).set .alice
                  (CompletedLocalRecord N)
              rw [weightedStreamSystem, TwoParty.set_alice, TwoParty.set_bob,
                TwoParty.set_alice]) (quotaSelectionContinuation N nK mZ mX ⟨a, b, order⟩) := by
  rfl

/-- The physical late-control program is the actual weighted measurement schedule with the
public-control continuation grafted at its unique exit. -/
theorem weightedLatePublicSelectionProgram_shape
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) :
    weightedLatePublicSelectionProgram pA pB N nK mZ mX =
      (weightedMeasurementSchedule pA pB N).graft
        (fun _ => latePublicSelectionProgram N nK mZ mX) := by
  rfl

/-- The canonical empty raw control. -/
def emptyControl : RawControl 0 := defaultRawControl 0

/-- At zero rounds, zero quotas select the successful leaf. -/
theorem emptyControl_zeroQuotas : HasQuotas 0 0 0 emptyControl := by
  decide

/-- At zero rounds, a positive key quota selects the shortage leaf. -/
theorem emptyControl_positiveQuota : ¬ HasQuotas 1 0 0 emptyControl := by
  decide

/-- The zero-round, zero-quota boundary really is the selected-record leaf. -/
theorem emptyControl_successLeaf :
    lateSelectionLeaf 0 0 0 0 emptyControl =
      .leaf (weightedSelectedRecordSystem 0 0) := by
  simp [lateSelectionLeaf, emptyControl_zeroQuotas]

/-- The zero-round positive-quota boundary really is the key-free abort leaf. -/
theorem emptyControl_abortLeaf :
    lateSelectionLeaf 0 1 0 0 emptyControl = .leaf lateSelectionAbortSystem := by
  simp [lateSelectionLeaf, emptyControl_positiveQuota]

/-- Opposite one-round bases with their unique empty shuffle. -/
def mismatchControl : RawControl 1 :=
  ⟨(fun _ => Basis.z), (fun _ => Basis.x),
    increasingShuffle (fun _ => Basis.z) (fun _ => Basis.x)⟩

/-- An all-mismatched one-round control cannot supply a positive key quota. -/
theorem mismatchControl_aborts : ¬ HasQuotas 1 0 0 mismatchControl := by
  decide

/-- The mismatched shortage exit retains Alice's bases, Bob's bases, and the exact empty shuffle. -/
theorem mismatchAbortExit_metadata :
    let e := lateSelectionExit 1 1 0 0 mismatchControl
    e.1 = mismatchControl.a ∧ e.2.1 = mismatchControl.b ∧
      e.2.2.1 = mismatchControl.order := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal two-round Z bases with the increasing matched order. -/
def twoZControl : RawControl 2 := defaultRawControl 2

/-- This control supplies one key position while retaining a strict subset of the two rounds. -/
theorem twoZControl_hasStrictQuota : HasQuotas 1 0 0 twoZControl := by
  decide

/-- The actual selected embedding computed from the successful strict-quota control. -/
def strictSelectedEmbedding : Fin 1 ↪ Fin 2 :=
  selectedEmbedding twoZControl twoZControl_hasStrictQuota

/-- A concrete two-round bit string distinguishing the selected and unselected positions. -/
def twoBits (i : Fin 2) : Bit := if i = 0 then 1 else 0

/-- Concrete all-Z two-round stored records. -/
def twoZStored : Fin 2 → StoredRecord :=
  fun i => ((), (Basis.z, twoBits i))

/-- The strict continuation retains all bases but only the bit chosen by the actual selected
embedding. -/
theorem strictSelection_localProjection :
    selectedLocalRecord strictSelectedEmbedding
        ((finishAccEquiv Unit 2).symm ((), twoZStored), fun i => Fin.elim0 i) =
      ((fun _ => Basis.z), fun i => twoBits (strictSelectedEmbedding i)) := by
  apply Prod.ext
  · funext i
    simp [selectedLocalRecord, twoZStored, storedBasisString]
  · funext i
    simp [selectedLocalRecord, twoZStored, strictSelectedEmbedding]

/-- Read the three public control coordinates from a late-selection output row. -/
noncomputable def lateOutputControl (N nK mZ mX : ℕ)
    (x : (lateSelectionBoundary N nK mZ mX).space) : RawControl N :=
  let xa := Boundary.publicSpaceEquiv (P := Party)
    (fun a : Fin N → Basis =>
      .announce (Fin N → Basis) fun b =>
        .announce (Shuffle a b) fun order =>
          lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩) x
  let xb := Boundary.publicSpaceEquiv (P := Party)
    (fun b : Fin N → Basis =>
      .announce (Shuffle xa.1 b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨xa.1, b, order⟩) xa.2
  let xo := Boundary.publicSpaceEquiv (P := Party)
    (fun order : Shuffle xa.1 xb.1 =>
      lateSelectionLeaf N nK mZ mX ⟨xa.1, xb.1, order⟩) xb.2
  ⟨xa.1, xb.1, xo.1⟩

/-- Read the same three public control coordinates from a late-selection exit. -/
def lateExitControl (N nK mZ mX : ℕ)
    (e : (lateSelectionBoundary N nK mZ mX).Exit) : RawControl N :=
  ⟨e.1, e.2.1, e.2.2.1⟩

/-- The explicit public exit constructor encodes exactly its input raw control. -/
theorem lateSelectionExit_control (N nK mZ mX : ℕ) (omega : RawControl N) :
    lateExitControl N nK mZ mX (lateSelectionExit N nK mZ mX omega) = omega := by
  rcases omega with ⟨a, b, order⟩
  rfl

/-- The successful output constructor and its specified exit carry the same strict-selection raw
control. -/
theorem strictSuccessAt_metadata
    (q : SelectedLocalRecord 2 1 × SelectedLocalRecord 2 1) :
    lateOutputControl 2 1 0 0
        (lateSelectionSuccessAt 2 1 0 0 twoZControl
          twoZControl_hasStrictQuota q) = twoZControl ∧
      lateExitControl 2 1 0 0 (lateSelectionExit 2 1 0 0 twoZControl) =
        twoZControl := by
  constructor
  · rfl
  · exact lateSelectionExit_control 2 1 0 0 twoZControl

/-- The shortage output constructor and its specified exit likewise carry the full mismatched raw
control before both local records are discarded. -/
theorem mismatchAbortAt_metadata :
    lateOutputControl 1 1 0 0
        (lateSelectionAbortAt 1 1 0 0 mismatchControl mismatchControl_aborts) =
        mismatchControl ∧
      lateExitControl 1 1 0 0 (lateSelectionExit 1 1 0 0 mismatchControl) =
        mismatchControl := by
  constructor
  · rfl
  · exact lateSelectionExit_control 1 1 0 0 mismatchControl

/-- Two completed records with the same basis string and different local outcomes. -/
def sameBasisRecord (x : Bit) : CompletedLocalRecord 1 :=
  ((finishAccEquiv Unit 1).symm
    ((), fun _ => ((), (Basis.x, x))), fun i => Fin.elim0 i)

/-- A one-way coherent matrix entry between two records in the same announced basis fibre. -/
def withinBasisCoherentInput : Op (CompletedLocalRecord 1) :=
  fun q q' => if q = sameBasisRecord 0 ∧ q' = sameBasisRecord 1 then 3 else 0

/-- Direct nondemolition basis readout preserves the nonzero coherent entry inside one basis
fibre.  This is an instrument-level check, not a whole physical-program theorem. -/
theorem basisReadout_preserves_withinBasis_coherence :
    ((Instrument.nondemolitionReadout (completedBasisString 1)).operation
      (fun _ => Basis.x) withinBasisCoherentInput)
        (sameBasisRecord 0) (sameBasisRecord 1) = 3 := by
  have hzero : completedBasisString 1 (sameBasisRecord 0) =
      (fun _ => Basis.x) := by
    funext i
    simp [completedBasisString, sameBasisRecord, storedBasisString]
  have hone : completedBasisString 1 (sameBasisRecord 1) =
      (fun _ => Basis.x) := by
    funext i
    simp [completedBasisString, sameBasisRecord, storedBasisString]
  rw [Instrument.nondemolitionReadout_operation_apply]
  simp [hzero, hone, withinBasisCoherentInput]

/-- Direct nondemolition basis readout removes an entry whose row is outside the announced basis
fibre. -/
theorem basisReadout_kills_crossBasis_block :
    ((Instrument.nondemolitionReadout (completedBasisString 1)).operation
      (fun _ => Basis.z) withinBasisCoherentInput)
        (sameBasisRecord 0) (sameBasisRecord 1) = 0 := by
  have hzero : completedBasisString 1 (sameBasisRecord 0) =
      (fun _ => Basis.x) := by
    funext i
    simp [completedBasisString, sameBasisRecord, storedBasisString]
  have hne : (fun _ : Fin 1 => Basis.x) ≠ (fun _ => Basis.z) := by
    intro h
    have := congrFun h 0
    simp at this
  rw [Instrument.nondemolitionReadout_operation_apply]
  simp [hzero, hne]

/-- A pure-Z law has zero support on the one-round all-X announced string. -/
theorem pureZ_zeroSupport_Xstring :
    basisStringLaw 1 (PMF.pure Basis.z) (fun _ => Basis.x) = 0 := by
  simp [basisStringLaw_apply]

/-- Unequal degenerate basis laws keep their separate unit-mass factors. -/
theorem unequalPureBasisFactors :
    ((basisStringLaw 1 (PMF.pure Basis.z) (fun _ => Basis.z)).toReal : ℂ) *
      ((basisStringLaw 1 (PMF.pure Basis.x) (fun _ => Basis.x)).toReal : ℂ) = 1 := by
  simp [basisStringLaw_apply]

end LatePublicControlAudit
