import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import Mathlib.Util.AssertNoSorry

/-!
# Tests for reference-stable record classicality

This test enforces sorry-freedom.  Its concrete regression is deliberately zero-round: it checks
that a nonzero off-diagonal reference entry survives the identity schedule, without claiming an
additional one-round calculation.
-/

open scoped Matrix BigOperators
open Matrix

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Measurement

attribute [local instance] storedRecordVectorDecidableEq
attribute [local instance] weightedStreamInputCardNeZero
attribute [local instance] weightedScheduleRecordCardNeZero

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
    Quantum.Operators.Op
      (Fintype.card (weightedStreamSystem Unit 0).total * 2) :=
  fun p q =>
    if (finProdFinEquiv.symm p).2 = (0 : Fin 2) ∧
        (finProdFinEquiv.symm q).2 = (1 : Fin 2)
    then 1 else 0

/-- At zero rounds, adjoining the identity reference does not dephase the explicit nonzero
off-diagonal reference entry. -/
theorem zeroRound_reference_offDiagonal_survives (pA pB : PMF Basis) :
    let eIn := Fintype.equivFin (weightedStreamSystem Unit 0).total
    let eRecords := Fintype.equivFin
      ((Unit × (Fin 0 → StoredRecord)) ×
        (Unit × (Fin 0 → StoredRecord)))
    let eOut := (weightedScheduleOutputEquiv Unit 0).trans eRecords
    Quantum.Channels.mapTensorId
        (coordinateLinear eIn eOut
          (weightedMeasurementSchedule pA pB 0).denote)
        zeroRoundReferenceInput
        (finProdFinEquiv (eRecords zeroRecordTuple, (0 : Fin 2)))
        (finProdFinEquiv (eRecords zeroRecordTuple, (1 : Fin 2))) = 1 := by
  dsimp only
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  have hblock :
      (Matrix.of fun i j =>
        zeroRoundReferenceInput
          (finProdFinEquiv (i, (0 : Fin 2)))
          (finProdFinEquiv (j, (1 : Fin 2)))) =
        Matrix.reindex (Fintype.equivFin (weightedStreamSystem Unit 0).total)
          (Fintype.equivFin (weightedStreamSystem Unit 0).total)
          (fun _ _ => (1 : ℂ)) := by
    ext i j
    change (if (finProdFinEquiv.symm (finProdFinEquiv (i, (0 : Fin 2)))).2 = 0 ∧
      (finProdFinEquiv.symm (finProdFinEquiv (j, (1 : Fin 2)))).2 = 1 then 1 else 0) = (1 : ℂ)
    simp only [Equiv.symm_apply_apply, and_self, ite_true]
  rw [hblock]
  have hcoord := coordinateLinear_reindex_apply
    (Fintype.equivFin (weightedStreamSystem Unit 0).total)
    ((weightedScheduleOutputEquiv Unit 0).trans
      (Fintype.equivFin
        ((Unit × (Fin 0 → StoredRecord)) ×
          (Unit × (Fin 0 → StoredRecord)))))
    (weightedMeasurementSchedule pA pB 0).denote
    (fun _ _ => (1 : ℂ))
    ((weightedScheduleOutputEquiv Unit 0).symm zeroRecordTuple)
    ((weightedScheduleOutputEquiv Unit 0).symm zeroRecordTuple)
  refine hcoord.trans ?_
  exact congrFun (congrFun (LinearMap.congr_fun
    (Program.denote_done (R := weightedStreamSystem Unit 0))
    (fun _ _ => (1 : ℂ))) _) _

end ReferenceAudit
