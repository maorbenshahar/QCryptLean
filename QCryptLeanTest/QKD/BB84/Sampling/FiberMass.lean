import QCryptLean.QKD.BB84.Sampling.FiberMass
import Mathlib.Util.AssertNoSorry

/-!
# BB84 selected-injection fiber-mass test

This test retains the constructor probes and checks the finite-embedding and fiber-mass surfaces.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace Math.FiniteEmbedding

/-- The transport permutation is literally the composite of the two explicit splits. -/
theorem embeddingTransportPerm_constructor {n N : ℕ} (f g : Fin n ↪ Fin N) :
    embeddingTransportPerm f g = (embeddingSplitEquiv f).symm.trans (embeddingSplitEquiv g) := by
  rfl

end Math.FiniteEmbedding

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- The success mass is literally the finite sum over quota-sufficient raw controls. -/
theorem selectionSuccessMass_constructor (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N nK mZ mX pA pB =
      ∑ omega : RawControl N,
        if HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0 := by
  rfl

/-- A fiber mass is literally the finite sum over raw controls selecting its fixed injection. -/
theorem selectedInjectionFiberMass_constructor
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) :
    selectedInjectionFiberMass N nK mZ mX pA pB f =
      ∑ omega : RawControl N,
        if select nK mZ mX omega = some f then rawControlLaw N pA pB omega else 0 := by
  rfl

end QKD.BB84.Sampling

