import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.LOCC.Typed.Instrument.Discard
import QCryptLean.LOCC.Typed.Program.GraftDenotation

/-!
# Stage 2 of measure-first BB84: public basis information and classical sifting

The destructive measurement schedule of the Measurement.Weighted module has already run, so
each party holds a completed local record — a basis string together with the outcome bit it
produced — and no signal register survives.  This module is the next stage, in the order a
physicist reads it:

1. Alice announces the basis string stored in her own record, and Bob announces his
   (`completedBasisAliceAnnouncement`, `completedBasisBobAnnouncement`).  Both readouts are
   nondestructive: the announced value *is* the stored string, and nothing else changes.
2. Alice samples one uniform ordering of the rounds where the two announced strings agree, and
   announces exactly that ordering (`shuffleAnnouncement`).
3. Those three public values form the late-public control `Sampling.RawControl`.  If it supplies
   the `nK` key, `mZ` Z-test and `mX` X-test quotas, both parties keep exactly the selected
   outcome bits (`quotaSelectionContinuation` via `selectedRecordContinuation`); otherwise both
   locally discard their complete records and the branch ends with no key register
   (`discardCompletedRecords`).

`lateSelectionBoundary` is the resulting public transcript tree and `latePublicSelectionProgram`
the stage itself; `weightedLatePublicSelectionProgram` is the measurement schedule followed by it.
Because the quota test is a predicate of the announced control alone, the announced values select
the continuation: `lateSelectionLeaf` is that `if`, and `quotaSelectionContinuation` branches on the
same test.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates measurement before basis
announcement and classical sifting.  Pfister et al., arXiv:1506.07502v3, Sections IV--V motivates
fixed-batch basis choices and late public selection.  The exact constructions below are finite
statements about the explicit typed program; neither paper is cited as stating them.
Parameter estimation, error correction, privacy amplification, and security are not included here;
the exact arbitrary-operator value of each public branch of this stage is in the
LatePublicControl.BranchValues module.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Sampling

/-! ## What each party holds when the stage begins -/

/-- A completed local stream contains the nested chronological record accumulator and the unique
empty residual bit stream. -/
abbrev CompletedLocalRecord (N : ℕ) :=
  streamRegister (finishAcc Unit N) 0

/-- Read the basis string already stored in a completed local measurement record. -/
def completedBasisString (N : ℕ) (q : CompletedLocalRecord N) :
    Fin N → Basis :=
  storedBasisString ((finishedStreamEquiv Unit N q).2)

/-! ## The two public basis announcements -/

/-- Alice nondestructively announces the actual basis string in her completed local record. -/
def completedBasisAliceAnnouncement (N : ℕ) :
    AnnouncedAction (weightedStreamSystem (finishAcc Unit N) 0) (Fin N → Basis) :=
  AnnouncedAction.ofInstrument Party.alice
    (Instrument.nondemolitionReadout (completedBasisString N)) id

/-- After Alice's announcement, Bob announces the basis string in his completed local record. -/
def completedBasisBobAnnouncement (N : ℕ) (a : Fin N → Basis) :
    AnnouncedAction ((completedBasisAliceAnnouncement N).out a) (Fin N → Basis) :=
  AnnouncedAction.ofInstrument Party.bob
    (Instrument.nondemolitionReadout (completedBasisString N)) id

/-- Alice's basis announcement is Alice's own action. -/
@[simp] theorem completedBasisAliceAnnouncement_actor (N : ℕ) :
    (completedBasisAliceAnnouncement N).actor = Party.alice := rfl

/-- Bob's basis announcement is Bob's own action. -/
@[simp] theorem completedBasisBobAnnouncement_actor (N : ℕ) (a : Fin N → Basis) :
    (completedBasisBobAnnouncement N a).actor = Party.bob := rfl

/-- **The announced basis string is the stored one.**  The announcement map is the identity on the
readout's observed value, so the public transcript cell carries the actual string and not an
internal encoding of it. -/
@[simp] theorem completedBasisAliceAnnouncement_announce (N : ℕ) (a : Fin N → Basis) :
    (completedBasisAliceAnnouncement N).announce a = a := rfl

/-- The same for Bob's announcement. -/
@[simp] theorem completedBasisBobAnnouncement_announce (N : ℕ) (a b : Fin N → Basis) :
    (completedBasisBobAnnouncement N a).announce b = b := rfl

/-- **The basis announcement is the nondestructive readout of `completedBasisString`.**  Its
single Kraus matrix at the announced value `a` is the projector onto the completed records whose
stored basis string is exactly `a`, so the record itself is retained. -/
theorem completedBasisAliceAnnouncement_kraus (N : ℕ) (a : Fin N → Basis)
    (r : (completedBasisAliceAnnouncement N).krausIndex a) :
    (completedBasisAliceAnnouncement N).kraus a r =
      Instrument.nondemolitionReadoutKraus (completedBasisString N) a := rfl

/-- The same for Bob's announcement. -/
theorem completedBasisBobAnnouncement_kraus (N : ℕ) (a b : Fin N → Basis)
    (r : (completedBasisBobAnnouncement N a).krausIndex b) :
    (completedBasisBobAnnouncement N a).kraus b r =
      Instrument.nondemolitionReadoutKraus (completedBasisString N) b := rfl

/-! ## The announced uniform shuffle of the matched rounds -/

/-- Uniformly sample one ordering of the matched identifiers without changing Alice's completed
local record.  The observed outcome is the sampled order paired with the unique readout value. -/
noncomputable def uniformShuffleInstrument (N : ℕ)
    (a b : Fin N → Basis) :
    Instrument (CompletedLocalRecord N) (CompletedLocalRecord N)
      (Shuffle a b × Unit) :=
  Instrument.uniformChoice (fun _ : Shuffle a b =>
    Instrument.nondemolitionReadout (fun _ : CompletedLocalRecord N => ()))

/-- Alice publicly announces the very ordering sampled by `uniformShuffleInstrument`. -/
noncomputable def shuffleAnnouncement (N : ℕ)
    (a b : Fin N → Basis) :
    AnnouncedAction ((completedBasisBobAnnouncement N a).out b) (Shuffle a b) :=
  AnnouncedAction.ofInstrument Party.alice
    (uniformShuffleInstrument N a b) Prod.fst

/-- The shuffle is sampled and announced by Alice. -/
@[simp] theorem shuffleAnnouncement_actor (N : ℕ) (a b : Fin N → Basis) :
    (shuffleAnnouncement N a b).actor = Party.alice := rfl

/-- **The announced ordering is exactly the one sampled.**  The observed outcome of
`uniformShuffleInstrument` is a sampled order paired with the unique readout value, and the
announcement is its first component. -/
@[simp] theorem shuffleAnnouncement_announce (N : ℕ) (a b : Fin N → Basis)
    (o : Shuffle a b × Unit) :
    (shuffleAnnouncement N a b).announce o = o.1 := rfl

/-! ## Quota selection or shortage discard -/

/-- Key-free terminal multipartite system for a quota-shortage branch. -/
abbrev lateSelectionAbortSystem : MultipartiteSystem Party := system Unit Unit

/-- Alice locally discards her complete measurement record on shortage. -/
def discardCompletedAliceAction (N : ℕ) :
    PrivateAction (weightedStreamSystem (finishAcc Unit N) 0) :=
  PrivateAction.ofInstrument .alice
    (Instrument.discardToUnit (CompletedLocalRecord N))

/-- Bob locally discards his complete measurement record after Alice on shortage. -/
def discardCompletedBobAction (N : ℕ) :
    PrivateAction (discardCompletedAliceAction N).out :=
  PrivateAction.ofInstrument .bob
    (Instrument.discardToUnit (CompletedLocalRecord N))

/-- Two private local discards, Alice then Bob, ending in the key-free shortage multipartite system.
-/
def discardCompletedRecords (N : ℕ) :
    Program (weightedStreamSystem (finishAcc Unit N) 0)
      (.leaf lateSelectionAbortSystem) :=
  cast (by
    apply congrArg (fun R => Program (weightedStreamSystem (finishAcc Unit N) 0) (.leaf R))
    change ((weightedStreamSystem (finishAcc Unit N) 0).set .alice Unit).set .bob Unit = _
    rw [weightedStreamSystem, TwoParty.set_alice, TwoParty.set_bob])
    ((discardCompletedAliceAction N).then (discardCompletedBobAction N).run)

/-- Quota-dependent terminal boundary for one fully public raw control. -/
def lateSelectionLeaf (N nK mZ mX : ℕ)
    (omega : RawControl N) : Boundary Party :=
  if HasQuotas nK mZ mX omega then
    .leaf (weightedSelectedRecordSystem N (nK + mZ + mX))
  else .leaf lateSelectionAbortSystem

/-- Complete late-public transcript: Alice's bases, Bob's bases, and the dependent matched-round
ordering, followed by the quota-dependent terminal leaf. -/
noncomputable def lateSelectionBoundary (N nK mZ mX : ℕ) : Boundary Party :=
  .announce (Fin N → Basis) fun a =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩

/-- Continue from one already public raw control: retain exactly its selected local records when
quotas are available, or discard both complete records on shortage. -/
def quotaSelectionContinuation (N nK mZ mX : ℕ)
    (omega : RawControl N) :
    Program (weightedStreamSystem (finishAcc Unit N) 0)
      (lateSelectionLeaf N nK mZ mX omega) := by
  by_cases h : HasQuotas nK mZ mX omega
  · simpa [lateSelectionLeaf, h] using
      selectedRecordContinuation (selectedEmbedding omega h)
  · simpa [lateSelectionLeaf, h] using discardCompletedRecords N

/-! ## The stage, and the measure-first program it continues -/

/-- Announce the two stored basis strings and one uniform dependent shuffle, then run the
quota-dependent selected-record or discard continuation. -/
noncomputable def latePublicSelectionProgram (N nK mZ mX : ℕ) :
    Program (weightedStreamSystem (finishAcc Unit N) 0)
      (lateSelectionBoundary N nK mZ mX) :=
  (completedBasisAliceAnnouncement N).then fun a =>
    (completedBasisBobAnnouncement N a).then fun b =>
      (shuffleAnnouncement N a b).then fun order =>
        cast (by
          apply congrArg (fun R => Program R (lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩))
          change weightedStreamSystem (finishAcc Unit N) 0 =
            (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
              (CompletedLocalRecord N)).set .bob (CompletedLocalRecord N)).set .alice
              (CompletedLocalRecord N)
          rw [weightedStreamSystem, TwoParty.set_alice, TwoParty.set_bob, TwoParty.set_alice])
          (quotaSelectionContinuation N nK mZ mX ⟨a, b, order⟩)

/-- The physical destructive weighted measurement schedule grafted to late public basis/shuffle
control and quota-dependent record erasure. -/
noncomputable def weightedLatePublicSelectionProgram
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) :
    Program (weightedStreamSystem Unit N)
      (lateSelectionBoundary N nK mZ mX) :=
  (weightedMeasurementSchedule pA pB N).graft
    (fun _ => latePublicSelectionProgram N nK mZ mX)

/-! ## Reading one complete public branch of the stage -/

/-- The complete public exit determined by a raw control, including its basis strings and exact
shuffle. -/
def lateSelectionExit (N nK mZ mX : ℕ)
    (omega : RawControl N) :
    (lateSelectionBoundary N nK mZ mX).Exit := by
  rcases omega with ⟨a, b, order⟩
  change Σ a : Fin N → Basis, Σ b : Fin N → Basis,
    Σ order : Shuffle a b,
      (lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).Exit
  refine ⟨a, b, order, ?_⟩
  by_cases h : HasQuotas nK mZ mX ⟨a, b, order⟩
  · rw [lateSelectionLeaf, ite_eq_left h]
    exact ()
  · rw [lateSelectionLeaf, ite_eq_right h]
    exact ()

/-- Embed a successful selected-record row into the complete late-public output space at the
specified raw-control exit. -/
noncomputable def lateSelectionSuccessAt
    (N nK mZ mX : ℕ) (omega : RawControl N)
    (h : HasQuotas nK mZ mX omega)
    (q : SelectedLocalRecord N (nK + mZ + mX) ×
      SelectedLocalRecord N (nK + mZ + mX)) :
    (lateSelectionBoundary N nK mZ mX).space := by
  unfold lateSelectionBoundary
  refine (Boundary.publicSpaceEquiv (P := Party) (fun a : Fin N → Basis =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩)).symm ⟨omega.a, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party) (fun b : Fin N → Basis =>
    .announce (Shuffle omega.a b) fun order =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, b, order⟩)).symm ⟨omega.b, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party)
    (fun order : Shuffle omega.a omega.b =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, omega.b, order⟩)).symm
        ⟨omega.order, ?_⟩
  have hleaf : lateSelectionLeaf N nK mZ mX omega =
      .leaf (weightedSelectedRecordSystem N (nK + mZ + mX)) := by
    simp [lateSelectionLeaf, h]
  exact cast (congrArg Boundary.space hleaf).symm
    ((Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv
          (SelectedLocalRecord N (nK + mZ + mX))
          (SelectedLocalRecord N (nK + mZ + mX))).symm q))

/-- Embed the unique key-free shortage row into the complete late-public output space at the
specified raw-control exit. -/
noncomputable def lateSelectionAbortAt
    (N nK mZ mX : ℕ) (omega : RawControl N)
    (h : ¬ HasQuotas nK mZ mX omega) :
    (lateSelectionBoundary N nK mZ mX).space := by
  unfold lateSelectionBoundary
  refine (Boundary.publicSpaceEquiv (P := Party) (fun a : Fin N → Basis =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩)).symm ⟨omega.a, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party) (fun b : Fin N → Basis =>
    .announce (Shuffle omega.a b) fun order =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, b, order⟩)).symm ⟨omega.b, ?_⟩
  refine (Boundary.publicSpaceEquiv (P := Party)
    (fun order : Shuffle omega.a omega.b =>
      lateSelectionLeaf N nK mZ mX ⟨omega.a, omega.b, order⟩)).symm
        ⟨omega.order, ?_⟩
  have hleaf : lateSelectionLeaf N nK mZ mX omega =
      .leaf lateSelectionAbortSystem := by
    simp [lateSelectionLeaf, h]
  exact cast (congrArg Boundary.space hleaf).symm
    ((Boundary.leafSpaceEquiv lateSelectionAbortSystem).symm
      ((TwoParty.pairEquiv Unit Unit).symm ((), ())))

/-- Reconstruct one complete chronological stored-record vector from a basis string and a bit
string. -/
def completeStoredRecords {N : ℕ}
    (a : Fin N → Basis) (x : Fin N → Bit) : Fin N → StoredRecord :=
  fun i => ((), (a i, x i))

end QKD.BB84.Measurement
