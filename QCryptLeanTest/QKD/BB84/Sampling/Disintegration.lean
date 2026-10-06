import QCryptLean.QKD.BB84.Sampling.Disintegration
import Mathlib.Util.AssertNoSorry

/-!
# Status-tagged disintegration test

This test checks the disintegration construction and its edge cases for sorry-freedom.
-/

open scoped ENNReal BigOperators

namespace QKD.BB84.Sampling
open TypedLOCC

open QKD.BB84.Measurement
open Math.FiniteEmbedding

noncomputable section

/-- The initial retained subset is literally the image of the initial-segment embedding. -/
theorem initialRetainedSubset_constructor
    {N nK mZ mX : ℕ} (hN : nK + mZ + mX ≤ N) :
    initialRetainedSubset hN =
      Set.powersetCard.ofFinEmb (nK + mZ + mX) (Fin N) (Fin.castLEEmb hN) := by
  rfl

/-- The original tagged law stores both the actual status and the complete raw control. -/
theorem taggedRawControlLaw_constructor
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    taggedRawControlLaw N nK mZ mX pA pB =
      (rawControlLaw N pA pB).map fun omega =>
        (decide (HasQuotas nK mZ mX omega), omega) := by
  rfl

/-- The reconstructed law is literally the status bind with the explicit success and failure
branches. -/
theorem reconstructedStatusRawLaw_constructor
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    reconstructedStatusRawLaw N nK mZ mX pA pB hN =
      (selectionStatusLaw N nK mZ mX pA pB).bind fun status =>
        if status then
          (uniformRetainedSubset hN).bind fun S =>
            (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
              (selectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π)).bind
                fun omega => PMF.pure (true, omega)
        else
          (failureControlKernel N nK mZ mX pA pB).bind fun omega =>
            PMF.pure (false, omega) := by
  rfl

end

end QKD.BB84.Sampling

namespace QKD.BB84.Sampling.DisintegrationAudit
open TypedLOCC

open QKD.BB84.Measurement
open QKD.BB84.Sampling

noncomputable section

/-- Zero quotas have total success mass one and failure mass zero. -/
theorem zeroQuotaMasses (N : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N 0 0 0 pA pB = 1 ∧
      selectionFailureMass N 0 0 0 pA pB = 0 := by
  exact ⟨selectionSuccessMass_zero_quotas N pA pB,
    selectionFailureMass_zero_quotas N pA pB⟩

/-- At `N = 0` and zero quotas, the explicit status PMF has masses one on success and zero on
failure. -/
theorem zeroRoundStatusLaw (pA pB : PMF Basis) :
    selectionStatusLaw 0 0 0 0 pA pB true = 1 ∧
      selectionStatusLaw 0 0 0 0 pA pB false = 0 := by
  simp [selectionStatusLaw_apply, selectionStatusWeight,
    selectionSuccessMass_zero_quotas, selectionFailureMass_zero_quotas]

/-- Degenerate all-Z basis law used to exercise a zero-success selected kernel with a valid
one-round embedding. -/
def pureZBasisLaw : PMF Basis :=
  PMF.pure Basis.z

/-- The explicit valid embedding used for the one-round zero-success fiber. -/
def oneRoundEmbedding : Fin 1 ↪ Fin 1 :=
  Fin.castLEEmb (Nat.le_refl 1)

-- `pureZ_oneX_successMass_zero` (the fact that this fiber has zero success mass under an
-- all-Z law) is checked once, in
-- `QKD.BB84.Reduction.PreprocessorAudit.pureZ_oneX_successMass_zero`
-- (`QCryptLeanTest/QKD/BB84/Reduction/Preprocessor.lean`).

/-- The valid selected kernel exercises its explicit fallback branch when the requested X fiber
has zero support under the all-Z law. -/
theorem pureZ_oneX_selectedKernel_fallback :
    selectedControlKernel 1 0 0 1 pureZBasisLaw pureZBasisLaw oneRoundEmbedding =
      PMF.pure (defaultRawControl 1) := by
  apply PMF.filterOrPure_eq_pure
  rintro ⟨omega, homega, hsupp⟩
  have hselect : select 0 0 1 omega = some oneRoundEmbedding := homega
  have hq : HasQuotas 0 0 1 omega :=
    (select_isSome_iff 0 0 1 omega).mp (by simp [hselect])
  have hxLength : 0 < (xOrder omega).length :=
    lt_of_lt_of_le Nat.zero_lt_one hq.2
  let i : Fin 1 := (xOrder omega).get ⟨0, hxLength⟩
  have hi : i ∈ xOrder omega := List.get_mem _ _
  rw [xOrder] at hi
  have hxi : omega.a i = Basis.x :=
    of_decide_eq_true (List.mem_filter.mp hi).2
  have hp : pureZBasisLaw (omega.a i) = 0 := by
    simp [pureZBasisLaw, hxi]
  have hprod : (∏ j : Fin 1, pureZBasisLaw (omega.a j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hp
  have hmass : rawControlLaw 1 pureZBasisLaw pureZBasisLaw omega = 0 := by
    rw [rawControlLaw_apply]
    rw [hprod]
    simp
  exact (PMF.mem_support_iff _ _).mp hsupp hmass

end

end QKD.BB84.Sampling.DisintegrationAudit
