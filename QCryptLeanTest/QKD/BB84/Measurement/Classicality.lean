import QCryptLean.QKD.BB84.Measurement.Classicality
import Mathlib.Util.AssertNoSorry

/-!
# Tests for schedule record classicality

This test enforces sorry-freedom.  Coordinate and zero-round coherence probes are kernel checked
independently; chronology probes that use the packaged schedule equivalences inherit only
already-proved production infrastructure.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Measurement

attribute [local instance] storedRecordVectorDecidableEq

namespace ClassicalityAudit

/-- The unique zero-round chronological record vector. -/
def emptyRecords : Fin 0 → StoredRecord := fun i => Fin.elim0 i

/-- At one round the finished-stream coordinates expose the single appended record. -/
theorem finishedStream_one (F : Type) (f : F) (r : StoredRecord) :
    (finishedStreamEquiv F 1 (((f, r)), fun i => Fin.elim0 i)).2 0 = r := by
  rfl

/-- At two rounds the finished-stream coordinates retain chronological append order. -/
theorem finishedStream_two_second (F : Type) (f : F) (r0 r1 : StoredRecord) :
    (finishedStreamEquiv F 2 ((((f, r0), r1)), fun i => Fin.elim0 i)).2 1 = r1 := by
  rfl

/-- A coordinate operator with one nonzero off-diagonal initial-accumulator entry. -/
def coherentAccumulatorSigma :
    Op (Boundary.leaf (weightedStreamSystem (finishAcc (Fin 2) 0) 0)).space :=
  fun q q' =>
    if q = (weightedScheduleOutputEquiv (Fin 2) 0).symm
          (((0, emptyRecords), (0, emptyRecords))) ∧
        q' = (weightedScheduleOutputEquiv (Fin 2) 0).symm
          (((1, emptyRecords), (0, emptyRecords)))
    then 1 else 0

/-- The coherent accumulator example has a nonzero row/column entry with Alice `F` coordinates
`0` and `1`; the record vectors remain the unique zero-round vectors. -/
theorem coherentAccumulatorSigma_offDiagonal_nonzero :
    (reindexOp (weightedScheduleOutputEquiv (Fin 2) 0) coherentAccumulatorSigma)
      ((0, emptyRecords), (0, emptyRecords))
      ((1, emptyRecords), (0, emptyRecords)) = 1 := by
  change coherentAccumulatorSigma
    ((weightedScheduleOutputEquiv (Fin 2) 0).symm
      ((0, emptyRecords), (0, emptyRecords)))
    ((weightedScheduleOutputEquiv (Fin 2) 0).symm
      ((1, emptyRecords), (0, emptyRecords))) = 1
  unfold coherentAccumulatorSigma
  exact ite_eq_left ⟨rfl, rfl⟩

/-- Zero-round record diagonality is vacuous and therefore permits the explicit coherent
off-diagonal accumulator entry above. -/
theorem coherentAccumulatorSigma_recordsDiagonal :
    ScheduleRecordsDiagonal (Fin 2) 0 coherentAccumulatorSigma := by
  intro fA fA' fB fB' rA rA' rB rB' h
  exfalso
  apply h.elim
  · intro hA
    apply hA
    funext i
    exact Fin.elim0 i
  · intro hB
    apply hB
    funext i
    exact Fin.elim0 i

/- The physical zero-round theorem has the expected fully general operator input surface. -/

end ClassicalityAudit
