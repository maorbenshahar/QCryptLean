import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired

/-!
# BB84 τ Post-Measurement Trace Bridges

Focused helper facts relating the τ-induced Eve-reference blocks to the ordinary
post-measurement Eve blocks after tracing out the CKR reference register.
-/

open Quantum.Operators Matrix Quantum.TensorProducts Quantum.Channels
open InfoTheory.SmoothMinEntropy
open scoped ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- On product-indexed Eve-reference inputs, the τ embedding factors through the
    ordinary outcome/Eve embedding and the reference index. -/
lemma bb84TauOutcomeEveRefEmbedding_finProd {n eveDim dimR : ℕ}
    (ωIdx : Fin (4 ^ n)) (a : Fin eveDim) (r : Fin dimR) :
    bb84TauOutcomeEveRefEmbedding (n := n) (eveDim := eveDim) (dimR := dimR)
        ωIdx (finProdFinEquiv (a, r)) =
      finProdFinEquiv
        (bb84OutcomeEveEmbedding (n := n) (eveDim := eveDim) ωIdx a, r) := by
  simp [bb84TauOutcomeEveRefEmbedding, bb84OutcomeEveEmbedding]

end QKD.BB84.Engine

end -- noncomputable section
