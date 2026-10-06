import QCryptLean.QKD.BB84.Model.Measurement
import QCryptLean.QKD.BB84.Model.BellMeasurement
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic

/-!
# The internal EPR source

The entanglement-based building block of the analytical model: one Bell pair per round.

## Main definitions

* `bb84EPRSingle` — the single-pair internal EPR state `|Φ⁺⟩⟨Φ⁺|` on the 4-dimensional round
  register, built from the Bell vector `bb84BellState 0`.

## References

Bennett–Brassard 1984; Shor–Preskill 2000 (the EB↔P&M reduction); Renner 2005 §5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`) `main.tex:268`–`:401` (Main Result: Theorem
`\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-- The single-pair internal EPR state `|Φ⁺⟩⟨Φ⁺|` on the `4`-dim round register, built from the
Bell vector `bb84BellState 0 = |β₀₀⟩ = (|00⟩ + |11⟩)/√2`. -/
def bb84EPRSingle : DensityOp signalDim :=
  DensityOp.fromPure (bb84BellState 0) (bb84BellState_normalized 0)

end QKD.BB84.Model

end
