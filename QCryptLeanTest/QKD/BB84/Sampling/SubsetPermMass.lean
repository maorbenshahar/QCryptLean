import QCryptLean.QKD.BB84.Sampling.SubsetPermMass
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Util.AssertNoSorry

/-!
# BB84 subset/permutation sampling test

This test retains the finite coordinate probes and checks the subset/permutation mass surface.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace Math.FiniteEmbedding

/-- The forward map is literally the image subset paired with the inverse-rank permutation. -/
theorem embeddingSubsetPermForward_apply {n N : ℕ} (f : Fin n ↪ Fin N) :
    embeddingSubsetPermForward f = (imageSubset f, embeddingPermutation f) := by
  rfl

/-- The unique empty subset of `Fin 0`, used to check the zero-size construction. -/
def emptySubset : Set.powersetCard (Fin 0) 0 :=
  ⟨∅, rfl⟩

/-- The zero-size join has the unique empty embedding behavior. -/
theorem joinSubsetPerm_zero_apply (π : Equiv.Perm (Fin 0)) :
    ∀ k : Fin 0, joinSubsetPerm emptySubset π k = k := by
  intro k
  exact Fin.elim0 k

/-- The full three-element subset used for the non-involutive orientation regression. -/
def fullSubsetThree : Set.powersetCard (Fin 3) 3 :=
  ⟨Finset.univ, by simp⟩

/-- For the three-cycle, `join` indexes the increasing enumeration at inverse-cycle values
`2,0,1`, not at forward-cycle values `1,2,0`. -/
theorem joinSubsetPerm_finRotate_three_orientation :
    joinSubsetPerm fullSubsetThree (finRotate 3) 0 =
        (increasingSubsetEquiv fullSubsetThree 2).1 ∧
      joinSubsetPerm fullSubsetThree (finRotate 3) 1 =
        (increasingSubsetEquiv fullSubsetThree 0).1 ∧
      joinSubsetPerm fullSubsetThree (finRotate 3) 2 =
        (increasingSubsetEquiv fullSubsetThree 1).1 := by
  simp [joinSubsetPerm, Fin.ext_iff]

end Math.FiniteEmbedding

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement
open Math.FiniteEmbedding

/-- The transformed selector is literally `Option.map` of the actual selector. -/
theorem selectSubsetPerm_constructor {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    selectSubsetPerm nK mZ mX omega =
      (select nK mZ mX omega).map
        (embeddingSubsetPermEquiv (nK + mZ + mX) N) := by
  rfl

/-- The pair mass is literally the finite raw-control sum over the transformed selector fiber. -/
theorem selectedSubsetPermMass_constructor
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (π : Equiv.Perm (Fin (nK + mZ + mX))) :
    selectedSubsetPermMass N nK mZ mX pA pB S π =
      ∑ omega : RawControl N,
        if selectSubsetPerm nK mZ mX omega = some (S, π)
        then rawControlLaw N pA pB omega
        else 0 := by
  rfl

end QKD.BB84.Sampling

