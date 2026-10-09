import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the selected-record continuation and comparison law

Constructor and projection fixtures below inspect the actual local actions and grafted program.
The matrix fixtures inspect only the explicit right-hand-side comparison law and the already
proved selected-input marginal; they do not use the physical-program equality.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84 QKD.BB84.Measurement

local instance (N : ℕ) : DecidableEq (Fin N → Basis) :=
  Fintype.decidablePiFintype

local instance (N : ℕ) : DecidableEq (Fin N → Bit) :=
  Fintype.decidablePiFintype

namespace SelectedRecordsAudit

/-- The strict-subset embedding selecting the second coordinate of a two-round record. -/
def selectSecond : Fin 1 ↪ Fin 2 where
  toFun _ := 1
  inj' _ _ _ := Subsingleton.elim _ _

/-- Full selection with the selected coordinates in reverse order. -/
def reverseTwo : Fin 2 ↪ Fin 2 where
  toFun i := ⟨1 - i, by omega⟩
  inj' a b h := by
    apply Fin.ext
    simp only [Fin.mk.injEq] at h ⊢
    omega

/-- The empty selection into a one-round record. -/
def selectNoneOne : Fin 0 ↪ Fin 1 where
  toFun i := Fin.elim0 i
  inj' i := Fin.elim0 i

/-- The unique embedding between empty finite types. -/
def selectNoneNone : Fin 0 ↪ Fin 0 where
  toFun i := Fin.elim0 i
  inj' i := Fin.elim0 i

/-- A two-round basis string whose entries distinguish chronological order. -/
def twoBases (i : Fin 2) : Basis :=
  if i = 0 then .z else .x

/-- A two-round bit string whose entries distinguish chronological order. -/
def twoBits (i : Fin 2) : Bit :=
  if i = 0 then 0 else 1

/-- Concrete completed two-round stored records. -/
def twoStored : Fin 2 → StoredRecord :=
  fun i => ((), (twoBases i, twoBits i))

/-- Concrete completed local stream representing `twoStored`. -/
def completedTwo : streamRegister (finishAcc Unit 2) 0 :=
  ((finishAccEquiv Unit 2).symm ((), twoStored), fun i => Fin.elim0 i)

/-- Strict selection retains the entire basis string. -/
theorem strictSelection_retains_all_bases :
    (selectedLocalRecord selectSecond completedTwo).1 = twoBases := by
  change storedBasisString (finishedStreamEquiv Unit 2 completedTwo).2 = twoBases
  rw [show (finishedStreamEquiv Unit 2 completedTwo).2 = twoStored by
    simp [completedTwo]]
  rfl

/-- Strict selection reads only the bit at the second chronological coordinate. -/
theorem strictSelection_reads_second_bit :
    (selectedLocalRecord selectSecond completedTwo).2 0 = 1 := by
  change twoBits (selectSecond 0) = 1
  change (if (1 : Fin 2) = 0 then (0 : Bit) else 1) = 1
  exact ite_eq_right (by decide)

/-- Full reversed selection preserves all bases but reverses the retained bit order. -/
theorem reversedFullSelection_bits :
    (selectedLocalRecord reverseTwo completedTwo).2 = fun i => twoBits (reverseTwo i) := by
  simp [selectedLocalRecord, completedTwo, twoStored]

/-- The empty selection retains the one-round basis and has the unique empty selected-bit
coordinate. -/
theorem emptySelection_one_round
    (r : Fin 1 → StoredRecord) :
    selectedLocalRecord selectNoneOne
        ((finishAccEquiv Unit 1).symm ((), r), fun i => Fin.elim0 i) =
      (storedBasisString r, fun i => Fin.elim0 i) := by
  apply Prod.ext
  · simp [selectedLocalRecord]
  · funext i
    exact Fin.elim0 i

/-- At zero rounds both retained functions are the unique empty functions. -/
theorem emptySelection_zero_round
    (q : streamRegister (finishAcc Unit 0) 0) :
    selectedLocalRecord selectNoneNone q =
      ((fun i => Fin.elim0 i), fun i => Fin.elim0 i) := by
  apply Prod.ext <;> funext i <;> exact Fin.elim0 i

/-- The selected stored-record reconstruction retains each selected basis and selected bit. -/
theorem selectedStoredRecords_apply {n N : ℕ} (f : Fin n ↪ Fin N)
    (a : Fin N → Basis) (u : Fin n → Bit) (i : Fin n) :
    selectedStoredRecords f a u i = ((), (a (f i), u i)) := by
  rfl

/-- Alice's constructor is the requested local function-and-forget action. -/
theorem selectedRecordAliceAction_constructor {n N : ℕ} (f : Fin n ↪ Fin N) :
    (retainAlice (B := CompletedLocalRecord N) f) =
      PrivateAction.ofInstrument .alice
        (Instrument.functionAndForget (selectedLocalRecord f)) := by
  rfl

/-- Bob's constructor is the requested local function-and-forget action. -/
theorem selectedRecordBobAction_constructor {n N : ℕ} (f : Fin n ↪ Fin N) :
    (retainBob (A := SelectedLocalRecord N n) f) =
      PrivateAction.ofInstrument .bob
        (Instrument.functionAndForget (selectedLocalRecord f)) := by
  rfl

/-- The two direct retention actions compose at their natural systems. -/
theorem selectedRecordContinuation_shape {n N : ℕ} (f : Fin n ↪ Fin N)
    (k : Program (weightedSelectedRecordSystem N n)) :
    (retainAlice f).then ((retainBob f).then k) =
      Program.priv (retainAlice f) (Program.priv (retainBob f) k) := rfl

end SelectedRecordsAudit
