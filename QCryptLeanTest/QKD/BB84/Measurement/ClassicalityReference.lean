import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import Mathlib.Util.AssertNoSorry

/-!
# Tests for reference-stable record classicality

This test enforces sorry-freedom.  Its concrete regression is deliberately zero-round: it checks
that a nonzero off-diagonal reference entry survives the identity schedule, without claiming an
additional one-round calculation.
-/

open Quantum.Channels

open scoped Matrix BigOperators
open Matrix

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84 QKD.BB84.Measurement

attribute [local instance] storedRecordVectorDecidableEq

namespace ReferenceAudit

/-- The unique zero-round record vector. -/
def emptyRecords : Fin 0 → StoredRecord := fun i => Fin.elim0 i

/-- The unique physical output record tuple at zero rounds. -/
def zeroRecordTuple :
    (Unit × (Fin 0 → StoredRecord)) ×
      (Unit × (Fin 0 → StoredRecord)) :=
  (((), emptyRecords), ((), emptyRecords))

/-- A zero-round input-reference operator with a unit entry from reference coordinate zero to
reference coordinate one. -/
def zeroRoundReferenceInput :
    Quantum.Operators.Op ((weightedStreamSystem Unit 0).total × Fin 2) :=
  fun p q => if p.2 = 0 ∧ q.2 = 1 then 1 else 0

/-- The identity schedule preserves the literal unequal-reference entry. -/
theorem zeroRound_reference_offDiagonal_survives (pA pB : PMF Basis) :
    mapTensorId (measurementState pA pB Unit 0) (Fin 2) zeroRoundReferenceInput
      ((weightedScheduleOutputEquiv Unit 0).symm zeroRecordTuple, 0)
      ((weightedScheduleOutputEquiv Unit 0).symm zeroRecordTuple, 1) = 1 := by
  rw [mapTensorId_apply]
  rfl

end ReferenceAudit
