import QCryptLean.LOCC.Typed.Program.Denotation
import QCryptLean.LOCC.Typed.Program.Classical
import QCryptLean.LOCC.Typed.TwoParty
import QCryptLean.LOCC.Typed.Instrument.TwoParty
import QCryptLean.LOCC.Typed.Transcript.Coordinates
import QCryptLean.LOCC.Typed.Instrument.Classical
import QCryptLean.LOCC.Typed.Instrument.ClassicalTransition
import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import QCryptLean.LOCC.Typed.Instrument.MatrixConj
import QCryptLean.LOCC.Typed.ChannelCoordinates.Numbering
import QCryptLean.LOCC.Typed.ChannelCoordinates.TensorId
import QCryptLean.QKD.Ideal.BoundaryKey.Hom
import QCryptLean.QKD.Protocol
import QCryptLean.LOCC.Typed.Program.ExitWeight
import QCryptLean.LOCC.Typed.Program.TwoPartyClassicalReplacement
import QCryptLean.QKD.Acceptance

/-!
# TypedLOCC author umbrella

The focused surface for authors of typed LOCC and generic QKD protocols. Regression fixtures
and protocol-specific BB84 developments have separate entry points.

Explicit numeral coordinates are `TypedLOCC.Numbering`: one record numbering an ordered pair of
typed registers, with the transport, composition, subtraction, norm-invariance and
CPTP-invariance laws stated once. `QKD.Protocol.NumeralCoordinates` specializes it to a
protocol's input and heterogeneous output registers.
-/
