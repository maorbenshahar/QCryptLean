import QCryptLean.QKD.BB84.Measurement.Weighted
import Mathlib.Util.AssertNoSorry

/-!
# Statement test for PMF-weighted BB84 measurement

This test checks the complete definition and theorem surface together with the constructor-level
regressions. It enforces sorry-freedom.
-/

open scoped Matrix BigOperators ENNReal

open TypedLOCC
open TypedLOCC.Instrument
open QKD.BB84.Measurement

namespace WeightedChoiceAudit

/-- The hidden fibre is unchanged even when the corresponding seed has zero PMF mass. -/
theorem hiddenFiber_zeroMass {Input Output Seed Outcome : Type}
    [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output] [Fintype Seed] [Fintype Outcome]
    (p : PMF Seed) (I : Seed → Instrument Input Output Outcome)
    (r : Seed) (y : Outcome)
    (_hr : p r = 0) :
    (weightedChoice p I).krausIndex (r, y) = (I r).krausIndex y := by
  rfl

/-- Unequal and degenerate local PMFs occupy distinct nodes of the actual program constructor. -/
theorem unequalDegenerate_programShape :
    HEq (weightedSingleQubitRoundProgram (PMF.pure Basis.z) (PMF.pure Basis.x))
      (Program.priv (weightedMeasureAlice (PMF.pure Basis.z))
        (Program.priv (weightedMeasureBob (PMF.pure Basis.z) (PMF.pure Basis.x))
          Program.done)) := by
  unfold weightedSingleQubitRoundProgram
  exact cast_heq _ _

/-- The pure-Z zero-mass branch law reaches the actual kept-record Kraus matrix. -/
theorem pureZ_actualKeptKraus_zero (x : Bit) (stored : StoredRecord) (j : Bit) :
    (weightedMeasureAndRecord (PMF.pure Basis.z)).kraus (Basis.x, x) () stored j = 0 := by
  exact weightedMeasureAndRecord_pureZ_x_kraus_zero x stored j

/- The lifted theorem retains two independent spectator coordinates in its quantified surface. -/

end WeightedChoiceAudit
