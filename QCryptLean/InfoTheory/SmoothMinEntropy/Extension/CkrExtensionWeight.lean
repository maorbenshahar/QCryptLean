import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQStateRecovery

/-!
# CKR extension weight and feasible-scalar positivity

Generic CQ-state facts for a `dE ⊗ dR` blockwise partial-trace extension of a
`dE` CQ marginal: equal total weights, transfer of positive weight, and
positivity of the feasible scalar against the max-mixed product reference.

Salvaged verbatim from the retired BB84 CKR extension-penalty route; these
statements are stated over generic `CQState`/`DensityOp` objects.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder Pointwise

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- If a `dE ⊗ dR` extension matches a `dE` CQ-state block by block under the
`B`-partial trace, then their total weights (summed traces) coincide. -/
theorem cqState_weight_eq_of_partialTraceB_blocks
    {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp) :
    (∑ x : X, (ρER.stateMap x).trace) = ∑ x : X, (ρE.stateMap x).trace := by
  apply Finset.sum_congr rfl
  intro x _
  unfold SubDensityOp.trace
  rw [← hblocks x, trace_partialTraceB]

/-- Positive total weight transfers from a CQ marginal to any blockwise
partial-trace extension of it. -/
lemma cqState_weight_pos_of_partialTraceB_blocks
    {X : Type*} [Fintype X]
    {dE dR : ℕ}
    (ρER : CQState X (dE * dR))
    (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hweight : 0 < ∑ x : X, (ρE.stateMap x).trace) :
    0 < ∑ x : X, (ρER.stateMap x).trace := by
  have hweight_eq :
      (∑ x : X, (ρER.stateMap x).trace) =
        ∑ x : X, (ρE.stateMap x).trace :=
    cqState_weight_eq_of_partialTraceB_blocks ρER ρE hblocks
  rwa [hweight_eq]

/-- A blockwise extension of positive total weight has positive feasible scalar
against the max-mixed product reference when the second reference is full rank. -/
lemma minFeasibleLambda_maxMixed_tensor_pos_of_partialTraceB_blocks
    {X : Type*} [Fintype X]
    {dR dE : ℕ} [NeZero dE]
    (σR : DensityOp dR)
    (ρER : CQState X (dE * dR))
    (ρE : CQState X dE)
    (hσR_posDef : σR.toOp.PosDef)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hweight : 0 < ∑ x : X, (ρE.stateMap x).trace) :
    0 < minFeasibleLambda ρER
      (DensityOp.toSubDensityOp
        (DensityOp.tensor (DensityOp.maxMixed dE) σR)) :=
  minFeasibleLambda_pos_of_posDef_of_weight_pos
    ρER
    (DensityOp.toSubDensityOp
      (DensityOp.tensor (DensityOp.maxMixed dE) σR))
    (maxMixed_tensor_toSubDensityOp_posDef σR hσR_posDef)
    (cqState_weight_pos_of_partialTraceB_blocks ρER ρE hblocks hweight)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
