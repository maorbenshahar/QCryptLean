import QCryptLean.QKD.BB84.Sampling.TotalKernels
import Mathlib.Util.AssertNoSorry

/-!
# Tests for structurally valid total BB84 sampling kernels

The independent fixtures inspect the explicit fallback controls, embedding orientation, zero-size
reconstruction, and the distinction between weighted and unweighted fallback equality.  The eight
proved theorem surfaces are checked for sorries and their axiom rosters are printed separately.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace QKD.BB84.Sampling.TotalKernelsAudit
open TypedLOCC

open QKD.BB84.Measurement
open QKD.BB84.Sampling
open Math.FiniteEmbedding

/-- Degenerate all-Z basis law used to exercise a zero-success selected fibre. -/
def pureZBasisLaw : PMF Basis := PMF.pure Basis.z

/-- The identity one-round embedding. -/
def oneRoundEmbedding : Fin 1 ↪ Fin 1 := Fin.castLEEmb (Nat.le_refl 1)

/-- Under all-Z basis choices, requesting one X-test round has zero success mass. -/
theorem pureZ_oneX_successMass_zero :
    selectionSuccessMass 1 0 0 1 pureZBasisLaw pureZBasisLaw = 0 := by
  rw [selectionSuccessMass]
  apply Finset.sum_eq_zero
  intro omega _
  by_cases hq : HasQuotas 0 0 1 omega
  · simp only [hq, if_true]
    have hxLength : 0 < (xOrder omega).length :=
      lt_of_lt_of_le Nat.zero_lt_one hq.2
    let i : Fin 1 := (xOrder omega).get ⟨0, hxLength⟩
    have hi : i ∈ xOrder omega := List.get_mem _ _
    rw [xOrder] at hi
    have hxi : omega.a i = Basis.x :=
      of_decide_eq_true (List.mem_filter.mp hi).2
    rw [rawControlLaw_apply]
    have hp : pureZBasisLaw (omega.a i) = 0 := by
      simp [pureZBasisLaw, hxi]
    have hprod : (∏ j : Fin 1, pureZBasisLaw (omega.a j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hp
    rw [hprod]
    simp
  · simp [hq]

/-- The zero-success selected fallback is nevertheless structurally in the requested fibre.

The mass calculation is independent; the selector conjunct deliberately exercises the named
`selectFiberDefault` theorem. -/
theorem pureZ_oneX_zeroMass_validFallback :
    selectionSuccessMass 1 0 0 1 pureZBasisLaw pureZBasisLaw = 0 ∧
      select 0 0 1
          (fiberDefaultRawControl (nK := 0) (mZ := 0) (mX := 1) oneRoundEmbedding) =
        some oneRoundEmbedding := by
  exact ⟨pureZ_oneX_successMass_zero,
    selectFiberDefault (nK := 0) (mZ := 0) (mX := 1) oneRoundEmbedding⟩

/-- Non-involutive selected order: packed positions `0,1` are sent to physical positions `2,0`. -/
def reverseSkipEmbedding : Fin 2 ↪ Fin 3 where
  toFun k := ![2, 0] k
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- The explicit order follows the embedding orientation and then its increasing complement. -/
theorem reverseSkipOrder_orientation :
    fiberDefaultOrderEquiv (nK := 1) (mZ := 0) (mX := 1)
        reverseSkipEmbedding (0 : Fin 3) = (2 : Fin 3) ∧
      fiberDefaultOrderEquiv (nK := 1) (mZ := 0) (mX := 1)
          reverseSkipEmbedding (1 : Fin 3) = (0 : Fin 3) ∧
      fiberDefaultOrderEquiv (nK := 1) (mZ := 0) (mX := 1)
          reverseSkipEmbedding (2 : Fin 3) =
        (embeddingComplementEquiv reverseSkipEmbedding 0).1 := by
  constructor
  · exact fiberDefaultOrderEquiv_apply_selected
      (nK := 1) (mZ := 0) (mX := 1) reverseSkipEmbedding 0
  constructor
  · exact fiberDefaultOrderEquiv_apply_selected
      (nK := 1) (mZ := 0) (mX := 1) reverseSkipEmbedding 1
  · exact fiberDefaultOrderEquiv_apply_complement
      (nK := 1) (mZ := 0) (mX := 1) reverseSkipEmbedding 0

/-- The failure fallback stores the all-Z/all-X strings and therefore has no matched identifiers. -/
theorem failureFallback_strings_and_emptyMatched
    {N nK mZ mX : ℕ} (j : Fin (nK + mZ + mX)) :
    (failureDefaultRawControl (N := N) j).a = constantZ N ∧
      (failureDefaultRawControl (N := N) j).b = constantX N ∧
      (Matched (failureDefaultRawControl (N := N) j).a
        (failureDefaultRawControl (N := N) j).b).card = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  · simp [failureDefaultRawControl, Matched, constantZ, constantX]

/-- At zero rounds and zero quota the totalized law consists solely of its selected branch. -/
theorem totalized_zero_constructor (pA pB : PMF Basis) :
    totalizedReconstructedStatusRawLaw 0 0 0 0 pA pB (Nat.le_refl 0) =
      (uniformRetainedSubset (Nat.le_refl 0)).bind fun S =>
        (uniformInnerPerm 0).bind fun π =>
          (totalSelectedControlKernel 0 0 0 0 pA pB (joinSubsetPerm S π)).bind
            fun omega => PMF.pure (true, omega) := by
  simp [totalizedReconstructedStatusRawLaw]

/-- Empty filtering with two different fallbacks gives different unweighted kernels, while the
zero-weighted values agree. -/
theorem zeroWeight_not_unweightedFallbackEquality :
    PMF.filterOrPure (PMF.pure true) (∅ : Set Bool) false false ≠
        PMF.filterOrPure (PMF.pure true) ∅ true false ∧
      (0 : ℝ≥0∞) * PMF.filterOrPure (PMF.pure true) ∅ false false =
        (0 : ℝ≥0∞) * PMF.filterOrPure (PMF.pure true) ∅ true false := by
  simp [PMF.filterOrPure_empty]

end QKD.BB84.Sampling.TotalKernelsAudit
