import QCryptLean.QKD.BB84.RealIdeal
import QCryptLeanTest.QKD.ProtocolProbes
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Tests for the proved memory-free real/ideal interface

The fixtures below configure actual experiments and inspect their typed real/ideal interface.
The protocol probes distinguish computational-key classicality from a secrecy or uniformity claim.
-/

noncomputable section

open _root_.LOCC
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.FiniteKey

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
    (ProbabilityTheory.bernoulliMeasure true false
      ⟨(1 : ℝ) / 3, by constructor <;> norm_num⟩).toPMF

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

/-- The actual zero-round protocol starts at the source-defined stream multipartite system. -/
theorem zeroProtocol_start : zeroParameters.protocol.start = weightedStreamSystem Unit 0 := rfl

/-- The configured protocol uses the source-defined complete program, not a detached channel
supplied by its coordinate package. -/
theorem zeroProtocol_program :
    zeroParameters.protocol.program =
      QKD.BB84.construction
        (PMF.pure Basis.z) (PMF.pure Basis.z) 0 0 0 0 0 0 0 zeroEC 0 0 := rfl

/-- Impossible quotas preserve the actual physical input system. -/
theorem impossibleQuota_start :
    impossibleQuotaParameters.protocol.start = zeroParameters.protocol.start := rfl

/-- The biased/zero-support fixture still uses the actual one-round stream multipartite system. -/
theorem biasedZeroSupport_start :
    biasedZeroSupportParameters.protocol.start = weightedStreamSystem Unit 1 := rfl

/-- The impossible-quota fixture uses the direct typed distance on its actual maps. -/
theorem impossibleQuota_realIdealDistance_eq :
    impossibleQuotaParameters.protocol.realIdealDistance =
      (1 / 2) * Quantum.Channels.diamondNorm
        impossibleQuotaParameters.protocol.difference := rfl

/-- Accepted-key classicality holds for a configuration whose quota is infeasible, where the
experiment takes its shortage branch. -/
theorem impossibleQuota_acceptedKeyClassical :
    impossibleQuotaParameters.protocol.AcceptedKeyClassical :=
  impossibleQuotaParameters.acceptedKeyClassical_protocol

/-! The existing executable protocol probes show the exact logical scope of
`AcceptedKeyClassical`: abort and zero-bit accept pass, while an accepting `Program.done` retaining
a mismatched-key matrix unit fails. None of these assertions states key uniformity or reference
independence. -/

end RealIdealAudit

