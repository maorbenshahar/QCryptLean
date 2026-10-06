import QCryptLean.QKD.BB84.RealIdeal
import QCryptLeanTest.QKD.ProtocolProbes
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.Program

/-!
# Tests for the proved memory-free real/ideal interface

The fixtures below configure actual experiments, inspect the protocol they build and the explicit
numeral coordinates that the transport chain uses, and check that the public interface needs
neither.  The protocol probes distinguish computational-key classicality from a secrecy or
uniformity claim.
-/

noncomputable section

open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Engine

namespace RealIdealAudit

/-- An error-correction package sufficient to instantiate the source protocol at any finite
parameter values; no correctness property is part of `ECScheme`. -/
def identityEC (n leakEC : ℕ) (peSel : Fin n → Bool) :
    ECScheme n peSel leakEC :=
  ⟨fun _ => 0, fun b _ => b⟩

/-- Zero-round, zero-quota error-correction data. -/
def zeroEC : ECScheme 0 (@packedPESel 0 0 0) 0 :=
  identityEC 0 0 (@packedPESel 0 0 0)

/-- Error-correction data for a quota that is impossible at zero physical rounds. -/
def impossibleQuotaEC : ECScheme 1 (@packedPESel 1 0 0) 0 :=
  identityEC 1 0 (@packedPESel 1 0 0)

/-- A nondegenerate Alice basis law with mass `1/3` on `X` and `2/3` on `Z`. -/
noncomputable def biasedBasisLaw : PMF Basis :=
  PMF.map (fun b : Bool => if b then Basis.x else Basis.z)
    (PMF.bernoulli ⟨(1 : ℝ) / 3, by positivity⟩ (by
      change (1 : ℝ) / 3 ≤ 1
      norm_num))

/-- The zero-round, zero-quota configuration. -/
noncomputable def zeroParameters : Parameters where
  aliceBasis := PMF.pure Basis.z
  bobBasis := PMF.pure Basis.z
  rounds := 0
  keyRounds := 0
  zTests := 0
  xTests := 0
  keyLength := 0
  tagLength := 0
  leak := 0
  ec := zeroEC
  tolerance := 0
  errorRate := 0

/-- A configuration whose quota cannot be met by its physical round count. -/
noncomputable def impossibleQuotaParameters : Parameters where
  aliceBasis := PMF.pure Basis.z
  bobBasis := PMF.pure Basis.x
  rounds := 0
  keyRounds := 1
  zTests := 0
  xTests := 0
  keyLength := 0
  tagLength := 0
  leak := 0
  ec := impossibleQuotaEC
  tolerance := 0
  errorRate := 0

/-- A one-round configuration with a biased Alice law and a zero-support Bob law. -/
noncomputable def biasedZeroSupportParameters : Parameters where
  aliceBasis := biasedBasisLaw
  bobBasis := PMF.pure Basis.z
  rounds := 1
  keyRounds := 0
  zTests := 0
  xTests := 0
  keyLength := 0
  tagLength := 0
  leak := 0
  ec := zeroEC
  tolerance := 0
  errorRate := 0

/-- Explicit coordinates for the zero-round, zero-quota protocol. -/
noncomputable def zeroCoordinates := zeroParameters.coordinates

/-- Explicit coordinates remain well-formed when the requested quota exceeds the physical round
count. -/
noncomputable def impossibleQuotaCoordinates := impossibleQuotaParameters.coordinates

/-- Biased and zero-support per-party laws remain distinct inputs to the coordinate package. -/
noncomputable def biasedZeroSupportCoordinates := biasedZeroSupportParameters.coordinates

/-- The low-level coordinate package is the one the transport chain uses, at the configured
parameters. -/
theorem coordinates_eq (p : Parameters) :
    p.coordinates =
      QKD.BB84.coordinates p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests
        p.xTests p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate := rfl

/-- The coordinate input dimension is definitionally the cardinality of the actual input
multipartite system. -/
theorem coordinates_inputDim (p : Parameters) :
    p.coordinates.inputDim = Fintype.card (weightedStreamSystem Unit p.rounds).total := rfl

/-- The coordinate output dimension is definitionally the cardinality of the actual complete
boundary. -/
theorem coordinates_outputDim (p : Parameters) :
    p.coordinates.outputDim =
      Fintype.card (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak).space := rfl

/-- The explicit input numbering has its actual inverse on every physical input multipartite system.
-/
theorem coordinates_inputEquiv_roundtrip (p : Parameters)
    (x : (weightedStreamSystem Unit p.rounds).total) :
    p.coordinates.inputEquiv.symm (p.coordinates.inputEquiv x) = x :=
  Equiv.symm_apply_apply _ x

/-- The explicit output numbering has its actual inverse on every complete output boundary. -/
theorem coordinates_outputEquiv_roundtrip (p : Parameters)
    (x : (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak).space) :
    p.coordinates.outputEquiv.symm (p.coordinates.outputEquiv x) = x :=
  Equiv.symm_apply_apply _ x

/-- The actual zero-round protocol starts at the source-defined stream multipartite system. -/
theorem zeroProtocol_start : zeroParameters.protocol.start = weightedStreamSystem Unit 0 := rfl

/-- The configured protocol uses the source-defined complete program, not a detached channel
supplied by its coordinate package. -/
theorem zeroProtocol_program :
    zeroParameters.protocol.program =
      QKD.BB84.program
        (PMF.pure Basis.z) (PMF.pure Basis.z) 0 0 0 0 0 0 0 zeroEC 0 0 := rfl

/-- Impossible quota data changes no initial physical coordinate type. -/
theorem impossibleQuota_inputDim :
    impossibleQuotaCoordinates.inputDim = zeroCoordinates.inputDim := rfl

/-- The biased/zero-support fixture still uses the actual one-round stream multipartite system. -/
theorem biasedZeroSupport_start :
    biasedZeroSupportParameters.protocol.start = weightedStreamSystem Unit 1 := rfl

/-- **The public distance needs no coordinate package**: the configured protocol's real/ideal
diamond distance is half the diamond norm the low-level coordinates compute, for every configuration
including the infeasible-quota one. -/
theorem impossibleQuota_realIdealDistance_eq :
    impossibleQuotaParameters.protocol.realIdealDistance =
      (1 / 2) * Quantum.Channels.diamondNorm impossibleQuotaCoordinates.difference :=
  impossibleQuotaParameters.realIdealDistance_eq_coordinates

/-- Accepted-key classicality holds for a configuration whose quota is infeasible, where the
experiment takes its shortage branch. -/
theorem impossibleQuota_acceptedKeyClassical :
    impossibleQuotaParameters.protocol.AcceptedKeyClassical :=
  impossibleQuotaParameters.protocol_acceptedKeyClassical

/-! The existing executable protocol probes show the exact logical scope of
`AcceptedKeyClassical`: abort and zero-bit accept pass, while an accepting `Program.done` retaining
a mismatched-key matrix unit fails. None of these assertions states key uniformity or reference
independence. -/

end RealIdealAudit

