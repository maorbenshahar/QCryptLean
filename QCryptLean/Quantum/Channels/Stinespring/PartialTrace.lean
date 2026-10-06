import QCryptLean.Quantum.Channels.Stinespring.Minimal.Basic
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP

/-!
# Stinespring Partial-Trace Marginals — passive ancilla dilations and Kraus marginal CPTP

This file records generic finite-dimensional facts about tracing out an output
environment after a Stinespring or Kraus representation.

## Main statements
- `isCPTP_krausMapFintype`: the linear map induced by a complete Kraus representation is CPTP.
- `isCPTP_partialTraceB_krausMapFintype`: tracing out the environment of a Kraus channel is CPTP.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The linear `krausMapFintype` induced by a complete Kraus representation is CPTP. -/
lemma isCPTP_krausMapFintype {n m : ℕ} [NeZero n] [NeZero m]
    (kr : KrausRepresentation n m) :
    IsCPTP (⇑(krausMapFintype kr.operators)) := by
  exact kr.is_cptp

/-- The Bob marginal obtained by tracing out the environment of a Kraus channel is
CPTP. -/
theorem isCPTP_partialTraceB_krausMapFintype
    {B E : ℕ} [NeZero B] [NeZero E] [NeZero (B * E)]
    (kr : KrausRepresentation B (B * E)) :
    IsCPTP (fun A : Op B => partialTraceB (krausMapFintype kr.operators A)) := by
  have hcomp := cptp_comp
    (partialTraceB : Op (B * E) → Op B)
    (⇑(krausMapFintype kr.operators))
    (isCPTP_partialTraceB (n := B) (m := E))
    (isCPTP_krausMapFintype kr)
  exact hcomp

end Quantum.Channels

end -- noncomputable section
