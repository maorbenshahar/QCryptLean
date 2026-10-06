import QCryptLean.QKD.BB84.Measurement.Schedule
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the finite destructive measurement schedule

This test enforces sorry-freedom for the schedule laws.  Concrete `N = 0,1,2` constructor and
chronology probes use kernel reduction; the deterministic-basis branch probe separately exercises
the step-entry law.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Measurement

namespace ScheduleAudit

/-- Kernel reduction confirms that the top-level zero-round schedule terminates immediately. -/
theorem schedule_zero_constructor (pA pB : PMF Basis) :
    weightedMeasurementSchedule pA pB 0 = Program.done := by
  rfl

/-- Kernel reduction exposes Alice then Bob for the unique signal pair. -/
theorem schedule_one_constructor (pA pB : PMF Basis) :
    weightedMeasurementSchedule pA pB 1 =
      Program.priv (weightedStreamAliceAction pA Unit 0)
        (Program.priv (weightedStreamBobAction pA pB Unit 0)
          (cast (by
            simp only [weightedStreamBobAction_out]
            rfl) (weightedMeasurementScheduleAux pA pB (Unit × StoredRecord) 0))) := by
  rfl

/-- The first private node is owned by Alice. -/
theorem aliceAction_actor (pA : PMF Basis) (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamAliceAction pA F n).actor = .alice := by
  rfl

/-- The second private node is owned by Bob. -/
theorem bobAction_actor (pA pB : PMF Basis) (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamBobAction pA pB F n).actor = .bob := by
  rfl

/-- For two rounds, the explicit accumulator equivalence reads the first appended record first. -/
theorem finishAcc_two_first (r0 r1 : StoredRecord) :
    (finishAccEquiv Unit 2 ((((), r0), r1))).2 0 = r0 := by
  rfl

/-- For two rounds, the explicit accumulator equivalence reads the second appended record second. -/
theorem finishAcc_two_second (r0 r1 : StoredRecord) :
    (finishAccEquiv Unit 2 ((((), r0), r1))).2 1 = r1 := by
  rfl

/-- A pure-Z basis law kills an observed X branch of the actual stream-head Kraus matrix. -/
theorem pureZ_stream_x_kraus_zero (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (x : Bit) (fOut fIn : F) (stored : StoredRecord)
    (tailOut : Fin n → Bit) (xs : Fin (n + 1) → Bit) :
    (weightedStreamStep (PMF.pure Basis.z) F n).kraus (Basis.x, x) ()
        ((fOut, stored), tailOut) (fIn, xs) = 0 := by
  rw [weightedStreamStep_kraus_apply]
  simp

end ScheduleAudit
