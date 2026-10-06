import QCryptLean.QKD.BB84.Reduction.SymmetrizationPrefix
import QCryptLeanTest.QKD.BB84.SeedTagSyndrome
import Mathlib.Tactic.NormNum
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the analytical symmetrization prefix

These fixtures exercise the uniform-choice permutation instrument, its public map and the
local-action lifts of `QKD.BB84.Reduction.alicePermutationAnnouncement` and
`QKD.BB84.Reduction.bobSiftUnitAnnouncement`.  They include distinct communicated permutations,
the exact uniform weights, the literal singleton cell, and the statement that Bob and the
continuation use the permutation Alice announced.  The two branch reductions reuse the generic
lifting calculation of `QCryptLeanTest.BB84.SeedTagSyndrome` with its raw-system
instances.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QCryptLeanTest.BB84.Reduction.SymmetrizationPrefix

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.Engine
open QKD.BB84.Reduction

/-! ## Permutation outcomes, weights, and the shared public value -/

def falseSelector {n : ℕ} : Fin n → Bool := fun _ => false

def identityPermutationTwo : Equiv.Perm (Fin 2) := Equiv.refl _
def swapPermutationTwo : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem two_permutations_distinct : identityPermutationTwo ≠ swapPermutationTwo := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) h
  simp [identityPermutationTwo, swapPermutationTwo] at h0

theorem alice_raw_permutation_outcomes_distinct :
    (identityPermutationTwo, ()) ≠ (swapPermutationTwo, ()) := by
  intro h
  exact two_permutations_distinct (congrArg Prod.fst h)

theorem alice_announcement_is_sampled_permutation
    (π : Equiv.Perm (Fin 2)) :
    (alicePermutationAnnouncement 2 falseSelector falseSelector).announce (π, ()) = π := rfl

theorem alice_public_permutations_distinct :
    (alicePermutationAnnouncement 2 falseSelector falseSelector).announce
        (identityPermutationTwo, ()) ≠
      (alicePermutationAnnouncement 2 falseSelector falseSelector).announce
        (swapPermutationTwo, ()) := by
  intro h
  change identityPermutationTwo = swapPermutationTwo at h
  exact two_permutations_distinct h

theorem permutation_card_zero :
    Fintype.card (Equiv.Perm (Fin 0)) = 1 := by
  simp

theorem permutation_card_two :
    Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
  simp [Fintype.card_perm]

theorem permutation_weight_zero :
    (Fintype.card (Equiv.Perm (Fin 0)) : ℂ)⁻¹ = 1 := by
  rw [permutation_card_zero]
  norm_num

theorem permutation_weight_two :
    (Fintype.card (Equiv.Perm (Fin 2)) : ℂ)⁻¹ = 1 / 2 := by
  rw [permutation_card_two]
  norm_num

theorem siftPermutation_member_operation
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op (Fin (2 ^ n))) :
    (siftPermutationInstrument n peSel xSel π).operation () rho =
      matrixConjLinear (QKD.BB84.Model.siftPermHalf n peSel xSel π) rho := by
  change (∑ _ : Unit, matrixConjLinear (Model.siftPermHalf n peSel xSel π) rho) = _
  exact Fintype.sum_unique _

theorem alicePermutation_localOperation_weight
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (alicePermutationInstrument n peSel xSel).operation (π, ()) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
        matrixConjLinear (QKD.BB84.Model.siftPermHalf n peSel xSel π) := by
  unfold alicePermutationInstrument
  rw [Instrument.uniformChoice_operation]
  congr 1
  ext rho a b
  simp [siftPermutation_member_operation]

theorem bob_unit_is_literal
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (bobSiftUnitAnnouncement n peSel xSel π).announce () = () := rfl

/-- The value sampled and announced by Alice is definitionally the value used by Bob and passed
to the continuation; there is no separately supplied shared permutation. -/
theorem permutationStage_uses_same_public_permutation
    (n : ℕ) (peSel xSel : Fin n → Bool)
    {B : Equiv.Perm (Fin n) → Boundary Party}
    (k : ∀ π, Program (FinalStage.rawSystem n) (B π)) :
    permutationStage n peSel xSel k =
      (alicePermutationAnnouncement n peSel xSel).then fun π =>
        (bobSiftUnitAnnouncement n peSel xSel π).then fun _ =>
          cast (by
            apply congrArg (fun R => Program R (B π))
            change FinalStage.rawSystem n =
              ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n))
            rw [TwoParty.set_alice, TwoParty.set_bob]) (k π) := rfl

/-! ## Branch reductions with independent spectator coordinates -/

section BranchReductions

attribute [local instance] SeedTagSyndrome.rawSystemRegFintype
  SeedTagSyndrome.rawSystemRegDecidableEq

theorem alicePermutation_branch_reduces_to_local
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : ((alicePermutationAnnouncement n peSel xSel).out π).total) :
    ((alicePermutationAnnouncement n peSel xSel).liftedOperation (π, ()) rho) q q' =
      ((alicePermutationInstrument n peSel xSel).operation (π, ())
        (rho.submatrix
          (fun x => ((FinalStage.rawSystem n).splitAt .alice).symm
            (x, (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))) q).2))
          (fun y => ((FinalStage.rawSystem n).splitAt .alice).symm
            (y, (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))) q').2))))
        (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))) q).1
        (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))) q').1 := by
  exact SeedTagSyndrome.announcedLiftedOperation_eq_local n .alice
    (alicePermutationInstrument n peSel xSel) Prod.fst (π, ()) rho q q'

theorem bobPermutation_branch_reduces_to_local
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op ((alicePermutationAnnouncement n peSel xSel).out π).total)
    (q q' : ((bobSiftUnitAnnouncement n peSel xSel π).out ()).total) :
    ((bobSiftUnitAnnouncement n peSel xSel π).liftedOperation () rho) q q' =
      ((siftPermutationInstrument n peSel xSel π).operation ()
        (rho.submatrix
          (fun x => (((alicePermutationAnnouncement n peSel xSel).out π).splitAt .bob).symm
            (x, ((((alicePermutationAnnouncement n peSel xSel).out π).splitAtSet
              .bob (Fin (2 ^ n))) q).2))
          (fun y => (((alicePermutationAnnouncement n peSel xSel).out π).splitAt .bob).symm
            (y, ((((alicePermutationAnnouncement n peSel xSel).out π).splitAtSet
              .bob (Fin (2 ^ n))) q').2))))
        ((((alicePermutationAnnouncement n peSel xSel).out π).splitAtSet
          .bob (Fin (2 ^ n))) q).1
        ((((alicePermutationAnnouncement n peSel xSel).out π).splitAtSet
          .bob (Fin (2 ^ n))) q').1 := by
  exact Instrument.liftAt_operation_apply (R := (alicePermutationAnnouncement n peSel xSel).out π)
    .bob (siftPermutationInstrument n peSel xSel π) () rho q q'

end BranchReductions

end QCryptLeanTest.BB84.Reduction.SymmetrizationPrefix
