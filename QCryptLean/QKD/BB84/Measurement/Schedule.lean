import QCryptLean.LOCC.Typed.Instrument.OnFactor
import QCryptLean.QKD.BB84.Measurement.Weighted

/-!
# Finite sequential destructive BB84 measurement schedule

This module constructs a private measurement schedule for `N` BB84 signal pairs.  At each signal
pair Alice and Bob separately apply the fixed local PMF-weighted destructive instrument to the head
qubit of their remaining stream, retain one `StoredRecord`, and recurse on the tail.  There are no
announced program nodes and no Eve register parameter.

The sequential local-instrument tree follows Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2.  Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates the
prepare-and-measure order but does not prove an arbitrary-input batch identity.  Pfister et al.,
arXiv:1506.07502v3, Sections IV--V motivate fixed per-party basis laws and late announcement.

This module constructs only the sequential destructive factor schedule.  Its auxiliary
accumulator is an untouched finite factor, not a classicality assertion.  Full-record CQ,
batch-channel, sampling, memory-freedom, and security statements are separate obligations.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

/-! ## Chronological accumulator -/

/-- Accumulator type after appending `N` stored records on the right. -/
def finishAcc (F : Type) (N : ℕ) : Type :=
  match N with
  | 0 => F
  | n + 1 => finishAcc (F × StoredRecord) n

/-- Explicit nonempty instance for a finished accumulator. -/
def finishAccNonempty (F : Type) [hF : Nonempty F] (N : ℕ) :
    Nonempty (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => finishAccNonempty (F × StoredRecord) n

instance (F : Type) [Nonempty F] (N : ℕ) : Nonempty (finishAcc F N) :=
  finishAccNonempty F N

/-- Explicit finite instance for a finished accumulator. -/
def finishAccFintype (F : Type) [hF : Fintype F] (N : ℕ) :
    Fintype (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => finishAccFintype (F × StoredRecord) n

instance (F : Type) [Fintype F] (N : ℕ) : Fintype (finishAcc F N) :=
  finishAccFintype F N

/-- Explicit decidable-equality instance for a finished accumulator. -/
def finishAccDecidableEq (F : Type) [hF : DecidableEq F] (N : ℕ) :
    DecidableEq (finishAcc F N) :=
  match N with
  | 0 => hF
  | n + 1 => finishAccDecidableEq (F × StoredRecord) n

instance (F : Type) [DecidableEq F] (N : ℕ) : DecidableEq (finishAcc F N) :=
  finishAccDecidableEq F N

/-- Read a nested finished accumulator as its initial value and chronological record vector. -/
def finishAccForward (F : Type) (N : ℕ) (x : finishAcc F N) :
    F × (Fin N → StoredRecord) :=
  match N, x with
  | 0, f => (f, fun i => Fin.elim0 i)
  | n + 1, x =>
      let q := finishAccForward (F × StoredRecord) n x
      (q.1.1, Fin.cons q.1.2 q.2)

/-- Rebuild the nested accumulator from its initial value and chronological record vector. -/
def finishAccBackward (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) : finishAcc F N :=
  match N, q with
  | 0, q => q.1
  | n + 1, q =>
      finishAccBackward (F × StoredRecord) n
        ((q.1, q.2 0), Fin.tail q.2)

/-- Rebuilding after reading a finished accumulator is the identity. -/
theorem finishAccBackward_forward (F : Type) (N : ℕ) (x : finishAcc F N) :
    finishAccBackward F N (finishAccForward F N x) = x := by
  induction N generalizing F with
  | zero => rfl
  | succ n ih =>
      exact ih (F × StoredRecord) x

/-- Reading after rebuilding a chronological vector is the identity. -/
theorem finishAccForward_backward (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) :
    finishAccForward F N (finishAccBackward F N q) = q := by
  induction N generalizing F with
  | zero =>
      rcases q with ⟨f, records⟩
      have hrecords : records = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      subst records
      rfl
  | succ n ih =>
      rcases q with ⟨f, records⟩
      simp only [finishAccBackward, finishAccForward, ih]
      exact Prod.ext rfl (Fin.cons_self_tail records)

/-- Explicit equivalence between the nested accumulator and chronological records. -/
def finishAccEquiv (F : Type) (N : ℕ) :
    finishAcc F N ≃ F × (Fin N → StoredRecord) where
  toFun := finishAccForward F N
  invFun := finishAccBackward F N
  left_inv := finishAccBackward_forward F N
  right_inv := finishAccForward_backward F N

/-- The first coordinate read at a successor stage is the earliest appended record. -/
theorem finishAccEquiv_succ_head (F : Type) (n : ℕ)
    (x : finishAcc F (n + 1)) :
    (finishAccEquiv F (n + 1) x).2 0 =
      (finishAccEquiv (F × StoredRecord) n x).1.2 := by
  rfl

/-- The tail read at a successor stage is the recursively accumulated chronological tail. -/
theorem finishAccEquiv_succ_tail (F : Type) (n : ℕ)
    (x : finishAcc F (n + 1)) :
    Fin.tail (finishAccEquiv F (n + 1) x).2 =
      (finishAccEquiv (F × StoredRecord) n x).2 := by
  simp [finishAccEquiv, finishAccForward, Fin.tail_cons]

/-- Remove a leading `Unit` factor without using the distinct `PUnit` type. -/
def unitProdEquiv (T : Type) : Unit × T ≃ T where
  toFun q := q.2
  invFun x := ((), x)
  left_inv q := by rcases q with ⟨⟨⟩, x⟩; rfl
  right_inv _ := rfl

/-- Chronological record equivalence for the physical top-level Unit accumulator. -/
def finishAccUnitEquiv (N : ℕ) : finishAcc Unit N ≃ (Fin N → StoredRecord) :=
  (finishAccEquiv Unit N).trans (unitProdEquiv (Fin N → StoredRecord))

/-! ## One destructive head step -/

/-- An untouched accumulator paired with the remaining qubit stream. -/
abbrev streamRegister (F : Type) (n : ℕ) : Type :=
  F × (Fin n → Bit)

/-- Split the head qubit from the untouched accumulator and tail stream. -/
def streamInputSplit (F : Type) (n : ℕ) :
    streamRegister F (n + 1) ≃ Bit × streamRegister F n where
  toFun q := (q.2 0, (q.1, Fin.tail q.2))
  invFun q := (q.2.1, Fin.cons q.1 q.2.2)
  left_inv q := by
    rcases q with ⟨f, xs⟩
    simp only
    exact Prod.ext rfl (Fin.cons_self_tail xs)
  right_inv q := by
    rcases q with ⟨x, f, xs⟩
    simp [Fin.tail_cons]

/-- Reassociate a newly stored record in front of the unchanged accumulator and tail. -/
def streamOutputSplit (F : Type) (n : ℕ) :
    streamRegister (F × StoredRecord) n ≃ StoredRecord × streamRegister F n where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv q := by rcases q with ⟨⟨f, r⟩, xs⟩; rfl
  right_inv q := by rcases q with ⟨r, f, xs⟩; rfl

/-- Apply the weighted destructive BB84 instrument to the stream head and preserve the tail. -/
def weightedStreamStep (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) :
    Instrument (streamRegister F (n + 1))
      (streamRegister (F × StoredRecord) n) Record :=
  Instrument.onFactor (streamInputSplit F n) (streamOutputSplit F n)
    (weightedMeasureAndRecord p)

/-- Exact Kraus entry of one weighted destructive stream-head step.

The entry is supported only when the accumulator and tail are unchanged and the stored record
matches the observed branch.  This is the one-factor `K ⊗ 1` entry law from arXiv:1210.4583,
Section 2, specialized to the weighted BB84 row instrument. -/
theorem weightedStreamStep_kraus_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (fOut fIn : F) (stored : StoredRecord)
    (tailOut : Fin n → Bit) (xs : Fin (n + 1) → Bit) :
    (weightedStreamStep p F n).kraus observed ()
        ((fOut, stored), tailOut) (fIn, xs) =
      if (fOut, tailOut) = (fIn, Fin.tail xs) ∧ stored.2 = observed then
        (Real.sqrt (p observed.1).toReal : ℂ) *
          basisUnitary observed.1 observed.2 (xs 0)
      else 0 := by
  simp [weightedStreamStep, streamInputSplit, streamOutputSplit,
    Instrument.onFactorKraus_apply, weightedMeasureAndRecord_kraus_apply]
  by_cases h : fOut = fIn ∧ tailOut = Fin.tail xs <;> simp [h]

/-- Exact arbitrary-operator operation of one weighted destructive stream-head step.

The output spectator row `(fOut,tailOut)` and column `(fOut',tailOut')` remain independent; no
positivity, trace, self-adjointness, or equality assumption is made about `rho` or those two
coordinates. -/
theorem weightedStreamStep_operation_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (rho : Op (streamRegister F (n + 1)))
    (fOut fOut' : F) (stored stored' : StoredRecord)
    (tailOut tailOut' : Fin n → Bit) :
    ((weightedStreamStep p F n).operation observed rho)
        ((fOut, stored), tailOut) ((fOut', stored'), tailOut') =
      ((weightedMeasureAndRecord p).operation observed
        (rho.submatrix
          (fun j => (fOut, Fin.cons j tailOut))
          (fun j => (fOut', Fin.cons j tailOut'))))
        stored stored' := by
  rw [weightedStreamStep, Instrument.onFactor_operation_apply]
  rfl

/-- One stream-head branch makes the newly appended record diagonal while leaving both
accumulator coordinates and both unread-tail coordinates independent. -/
theorem weightedStreamStep_operation_newRecordDiagonal
    (p : PMF Basis) (F : Type) [Fintype F] [DecidableEq F] (n : ℕ)
    (observed : Record) (rho : Op (streamRegister F (n + 1)))
    (f f' : F) (stored stored' : StoredRecord)
    (tail tail' : Fin n → Bit) (hne : stored ≠ stored') :
    ((weightedStreamStep p F n).operation observed rho)
        ((f, stored), tail) ((f', stored'), tail') = 0 := by
  rw [weightedStreamStep_operation_apply]
  exact weightedMeasureAndRecord_operation_storedDiagonal p observed _ stored stored' hne

/-! ## Two-party recursive program -/

/-- The two-party multipartite system before both laboratories process a stream of length `n`. -/
def weightedStreamSystem (F : Type) [Nonempty F] [Fintype F] [DecidableEq F]
    (n : ℕ) : MultipartiteSystem Party :=
  system (streamRegister F n) (streamRegister F n)

/-- Alice's private destructive head step, with Bob's stream left untouched. -/
def weightedStreamAliceAction (pA : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    PrivateAction (weightedStreamSystem F (n + 1)) :=
  PrivateAction.ofInstrument .alice
    (weightedStreamStep pA F n)

/-- Bob's separate private destructive head step after Alice's step. -/
def weightedStreamBobAction (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    PrivateAction (weightedStreamAliceAction pA F n).out :=
  PrivateAction.ofInstrument .bob
    (weightedStreamStep pB F n)

/-- After Alice and Bob act, both accumulators gain a stored record and both streams lose a head. -/
@[simp] theorem weightedStreamBobAction_out (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamBobAction pA pB F n).out = weightedStreamSystem (F × StoredRecord) n := by
  simp only [weightedStreamBobAction, weightedStreamAliceAction, PrivateAction.out_ofInstrument,
    weightedStreamSystem, TwoParty.set_alice, TwoParty.set_bob]

/-- Transport from the next stream system preserves Alice's and Bob's output coordinates. -/
@[simp] theorem weightedStreamBobAction_out_cast_pairEquiv_symm (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (a b : streamRegister (F × StoredRecord) n) :
    cast (congrArg MultipartiteSystem.total (weightedStreamBobAction_out pA pB F n).symm)
        ((TwoParty.pairEquiv _ _).symm (a, b)) =
      (weightedStreamBobAction pA pB F n).out.pairEquiv.symm (a, b) := by
  change cast (congrArg MultipartiteSystem.total (weightedStreamBobAction_out pA pB F n).symm)
    ((weightedStreamSystem (F × StoredRecord) n).pairEquiv.symm (a, b)) = _
  rw [MultipartiteSystem.cast_pairEquiv_symm (weightedStreamBobAction_out pA pB F n).symm]
  rfl

/-- Recursive private schedule with an arbitrary untouched initial accumulator factor.

At a successor, Alice acts, then Bob acts, then the schedule recurses on the tail with one stored
record appended to each laboratory's accumulator. -/
def weightedMeasurementScheduleAux (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    Program (weightedStreamSystem F n)
      (.leaf (weightedStreamSystem (finishAcc F n) 0)) :=
  match n with
  | 0 => .done
  | n + 1 =>
      (weightedStreamAliceAction pA F n).then
        ((weightedStreamBobAction pA pB F n).then (cast (by
          simp only [weightedStreamBobAction_out]
          rfl)
            (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n)))

/-- The zero-round auxiliary schedule is immediate termination. -/
theorem weightedMeasurementScheduleAux_zero (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] :
    weightedMeasurementScheduleAux pA pB F 0 = Program.done := by
  rfl

/-- The successor auxiliary schedule is Alice, then Bob, then recursion on the tail. -/
theorem weightedMeasurementScheduleAux_succ (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    weightedMeasurementScheduleAux pA pB F (n + 1) =
      Program.priv (weightedStreamAliceAction pA F n)
        (Program.priv (weightedStreamBobAction pA pB F n) (cast (by
          simp only [weightedStreamBobAction_out]
          rfl)
            (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n))) := by
  rfl

/-- Private schedule for `N` BB84 signal pairs, starting with the physical singleton accumulator. -/
def weightedMeasurementSchedule (pA pB : PMF Basis) (N : ℕ) :
    Program (weightedStreamSystem Unit N)
      (.leaf (weightedStreamSystem (finishAcc Unit N) 0)) :=
  weightedMeasurementScheduleAux pA pB Unit N

end QKD.BB84.Measurement
