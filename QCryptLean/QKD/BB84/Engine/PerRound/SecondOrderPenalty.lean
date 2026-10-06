import QCryptLean.QKD.BB84.Engine.PerRound.DevetakWinter
import QCryptLean.InfoTheory.Renyi.SmoothMinFromRenyi
import QCryptLean.InfoTheory.Renyi.VonNeumannBridge
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants

/-!
# Conditional von Neumann entropy at the BB84 component state

The identification of the conditional von Neumann entropy of the BB84 per-round Alice-`Z` CQ
state with the Devetak–Winter rate `bb84ComponentAliceZRate`, supporting a Rényi-entropy route to
the Devetak–Winter rate (Dupuis–Fawzi 2018,
arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex`, Corollary IV.2). The scalar
numeric bound this route also needs, `one_lt_logb_two_div_sq`, has no quantum content and lives in
`Engine/Budgets/SecondOrderSharpPenalty.lean`.

## Main results

- `QKD.BB84.Engine.condVonNeumann_bb84ComponentAliceZCQState_eq_rate`: the identification.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`); Tomamichel 2015 (`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`
`\label{pr:min-renyi}`); Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}`
(`main.tex:4561`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open InfoTheory.Renyi
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- **`H(X|B)` at the BB84 component state is the Devetak–Winter rate.**

The `L2` bridge `condVonNeumann_eq_vonNeumannEntropy_sub_div_log_two` instantiated at
`ρ = bb84ComponentAliceZCQState σ`, whose right-hand side is `bb84ComponentAliceZRate σ`
(`DevetakWinter.lean`) verbatim.  This is the identification that lets the Rényi route land on the
same expression the Bennett row's AEP lift produces. -/
theorem condVonNeumann_bb84ComponentAliceZCQState_eq_rate (σ : DensityOp signalDim) :
    condVonNeumann (bb84ComponentAliceZCQState σ) = bb84ComponentAliceZRate σ := by
  have hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have hjoint : NeZero (signalDim * Fintype.card (Fin 2)) := ⟨by simp [signalDim]⟩
  exact condVonNeumann_eq_vonNeumannEntropy_sub_div_log_two (bb84ComponentAliceZCQState σ)
    (bb84ComponentAliceZCQState_norm σ)

end QKD.BB84.Engine

end -- noncomputable section
