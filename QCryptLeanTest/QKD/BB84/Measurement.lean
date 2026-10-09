import QCryptLean.QKD.BB84.Measurement
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the uniform BB84 measurement

A one-round program in which Alice and then Bob measure privately, and two checks of the recorded
Kraus matrices. This test enforces sorry-freedom.
-/

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84 QKD.BB84.Measurement

noncomputable section

namespace MeasurementAudit

/-- Alice measures her qubit privately. -/
def measureAlice : PrivateAction inputSystem :=
  measureAliceWithSpectator Bit

/-- Bob measures his qubit privately after Alice. -/
def measureBob : PrivateAction (system StoredRecord Bit) :=
  PrivateAction.ofInstrument .bob uniformMeasureAndRecord

/-- One round: Alice measures privately, Bob measures privately, then the program ends. -/
def singleQubitRoundProgram : Program inputSystem :=
  measureAlice.then (measureBob.then (.done PUnit.unit))

/-- The program is two private nodes followed by termination. -/
theorem singleQubitRoundProgram_shape :
    singleQubitRoundProgram =
      Program.priv measureAlice (Program.priv measureBob (Program.done PUnit.unit)) := rfl

/-- The fixed-basis Kraus matrix is a single row of the basis change. -/
theorem fixedBasisKraus_is_row (theta : Basis) (x j : Bit) :
    fixedBasisKraus theta x () j = basisUnitary theta x j := by
  rfl

/-- The recorded Kraus matrix has no support in a different stored-record block. -/
theorem uniformMeasureAndRecord_wrongStored_zero
    (observed : Record) (stored : StoredRecord) (j : Bit)
    (h : stored.2 ≠ observed) :
    uniformMeasureAndRecord.kraus observed () stored j = 0 := by
  simp [uniformMeasureAndRecord, Instrument.keeping, h]

end MeasurementAudit

assert_no_sorry MeasurementAudit.singleQubitRoundProgram_shape
assert_no_sorry MeasurementAudit.fixedBasisKraus_is_row
assert_no_sorry MeasurementAudit.uniformMeasureAndRecord_wrongStored_zero
