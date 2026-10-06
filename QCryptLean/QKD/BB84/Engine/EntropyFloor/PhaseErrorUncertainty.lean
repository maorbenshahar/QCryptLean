import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQCore
import QCryptLean.QKD.BB84.Model.Measurement
import QCryptLean.InfoTheory.BellDiagonal.Entropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ClassicalCoarsening
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.EntropicUncertainty
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning

/-!
# BB84 Alice-Z coarsening of the single-round CQ state

The two-outcome Alice Z-bit CQ state obtained by coarsening the four-outcome BB84 single-round CQ
state, and its blockwise origin as a projector sandwich of the tripartite round state.

## Main definitions
- `bb84AliceZCQState`: the Alice Z-bit CQ state, coarsening `bb84SingleRoundCQState` by
  `bb84AliceBitMap`.

## Main results
- `bb84AliceZCQState_origin`: each block of `bb84AliceZCQState` is the Alice-Bob partial trace of
  the Alice Z-bit projector sandwich of the tripartite round state.
-/

open Quantum.Operators Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy Math.ClassicalEntropy
open InfoTheory.QuantumLHL
open QKD.BB84.Engine
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace QKD.BB84.Engine

open InfoTheory.SmoothMinEntropy
open QKD.BB84.Model

/-!
## Two-outcome Alice-Z CQ state
-/

/-- The Alice Z-bit CQ state obtained by coarsening the four-outcome BB84
single-round CQ state of a tripartite round state `Ψ` on Alice-Bob ⊗ Eve. -/
noncomputable def bb84AliceZCQState (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) :
    CQState (Fin 2) dE :=
  CQState.coarsen bb84AliceBitMap
    (bb84SingleRoundCQState dE Ψ :
      CQState (Fin signalDim) dE)

/-- The coarsened Alice-Z CQ blocks arise by sandwiching the tripartite round
state with the Alice Z-bit projector and tracing out Alice-Bob. -/
lemma bb84AliceZCQState_origin (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) (z : Fin 2) :
    ((bb84AliceZCQState dE Ψ).stateMap z).toOp =
      partialTraceA
        (Op.tensor (bb84AliceZProjector z) (1 : Op dE) *
          Ψ.toOp *
          Op.tensor (bb84AliceZProjector z) (1 : Op dE)) := by
  ext a b
  rw [bb84AliceZProjector_eq_diagonal z]
  suffices
      (∑ k : Fin signalDim,
          (if bb84AliceBitMap k = z then
            ((bb84SingleRoundCQState dE Ψ).stateMap k).toOp
          else 0) a b) =
        ∑ k : Fin signalDim,
          (if bb84AliceBitMap k = z then (1 : ℂ) else 0) *
            Ψ.toOp (finProdFinEquiv (k, a)) (finProdFinEquiv (k, b)) *
            (if bb84AliceBitMap k = z then (1 : ℂ) else 0) by
    simpa [bb84AliceZCQState, partialTraceA_sandwich_tensor_diagonal_one,
      Matrix.sum_apply] using this
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : bb84AliceBitMap k = z
  · simp [hk, bb84SingleRoundCQState_stateMap_toOp_apply]
  · simp [hk]

end QKD.BB84.Engine

end -- noncomputable section
