import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalizedCastDim

/-!
# Post-Measurement CQ-State Transport Helpers

Small transport lemmas for moving post-measurement CQ states across equal Eve
dimensions.  The lemmas here keep block and cast calculations out of the
high-level finite-size protocol assembly.
-/

open Quantum.Operators Matrix Quantum.TensorProducts Quantum.Channels
open InfoTheory.SmoothMinEntropy
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

namespace CQState

/-- Lift per-outcome casts of a CQ state's blocks to the joint-density operator. -/
theorem toJointDensity_castDim_eq_of_stateMap_castDim_eq
    {α : Type*} [Fintype α] [DecidableEq α] {d d' : ℕ}
    (h_dim : d = d') (ρ : CQState α d) (ρ' : CQState α d')
    (h_state : ∀ x : α, SubDensityOp.castDim h_dim (ρ.stateMap x) = ρ'.stateMap x) :
    SubDensityOp.castDim (congrArg (fun q => q * Fintype.card α) h_dim) ρ.toJointDensity =
      ρ'.toJointDensity := by
  cases h_dim
  apply SubDensityOp.ext
  have h_stateMap : ρ.stateMap = ρ'.stateMap := by
    funext x
    simpa [SubDensityOp.castDim] using h_state x
  simp [SubDensityOp.castDim, CQState.toJointDensity, CQState.toJointOp, h_stateMap]

end CQState

end InfoTheory.SmoothMinEntropy

end
