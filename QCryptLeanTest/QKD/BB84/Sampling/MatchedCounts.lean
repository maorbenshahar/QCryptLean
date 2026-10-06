import QCryptLean.QKD.BB84.Sampling.MatchedCounts
import Mathlib.Util.AssertNoSorry

/-!
# Matched-count law test

Edge cases of the matched-basis count law: a witness that the two counts can be dependent, the
non-strict quota endpoint, degenerate basis laws, `N = 0`, zero and infeasible quotas, and
agreement with the published zero-quota lemma.  Checked for sorry-freedom.
-/

open scoped ENNReal BigOperators
open Finset

namespace QKD.BB84.Sampling.MatchedCountsAudit
open TypedLOCC

open QKD.BB84.Measurement
open QKD.BB84.Sampling

noncomputable section

/-- The uniform basis law. -/
def uniformBasis : PMF Basis :=
  PMF.uniformOfFintype Basis

/-- The all-Z basis law. -/
def pureZBasis : PMF Basis :=
  PMF.pure Basis.z

theorem uniformBasis_apply (θ : Basis) : uniformBasis θ = 2⁻¹ := by
  simp [uniformBasis, PMF.uniformOfFintype_apply, cardBasis]

/-- **The matched counts are dependent at uniform bases.**  In one uniform round both counts
equal one with probability zero, although each equals one with positive probability. -/
theorem matchedCounts_dependent :
    (rawControlLaw 1 uniformBasis uniformBasis).map matchedCounts (1, 1) = 0 ∧
      (rawControlLaw 1 uniformBasis uniformBasis).map
          (fun omega => (MatchedZ omega.a omega.b).card) 1 *
        (rawControlLaw 1 uniformBasis uniformBasis).map
          (fun omega => (MatchedX omega.a omega.b).card) 1 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [rawControlLaw_map_matchedCounts_apply]
    simp [matchedCountMass]
  · rw [rawControlLaw_map_card_matchedZ_apply, rawControlLaw_map_card_matchedX_apply]
    simp [matchedProb, uniformBasis_apply]

/-- The quota event ignores the sampled ordering of the matched rounds. -/
example {N : ℕ} (a b : Fin N → Basis) (o o' : Shuffle a b) (nK mZ mX : ℕ) :
    HasQuotas nK mZ mX ⟨a, b, o⟩ ↔ HasQuotas nK mZ mX ⟨a, b, o'⟩ := by
  rw [hasQuotas_iff, hasQuotas_iff]

/-- The exact failure formula reproduces the published zero-quota lemma. -/
example (N : ℕ) (pA pB : PMF Basis) :
    selectionFailureMass N 0 0 0 pA pB = 0 := by
  rw [selectionFailureMass_eq_sum]
  simp

/-- With no rounds, an X quota of one and a key quota of one fail surely while zero quotas never
fail; `selectionFailureMass_eq_one_of_lt` covers every positive quota. -/
theorem zeroRounds (pA pB : PMF Basis) :
    selectionFailureMass 0 0 0 1 pA pB = 1 ∧ selectionFailureMass 0 1 0 0 pA pB = 1 ∧
      selectionFailureMass 0 0 0 0 pA pB = 0 :=
  ⟨selectionFailureMass_eq_one_of_lt pA pB (by norm_num),
    selectionFailureMass_eq_one_of_lt pA pB (by norm_num),
    selectionFailureMass_zero_quotas 0 pA pB⟩

/-- **Non-strict endpoint.**  With both parties always choosing Z, two rounds meet a Z quota of
exactly two, while a Z quota of three is infeasible. -/
theorem pureZ_endpoint :
    selectionFailureMass 2 1 1 0 pureZBasis pureZBasis = 0 ∧
      selectionFailureMass 2 1 2 0 pureZBasis pureZBasis = 1 := by
  refine ⟨le_antisymm ?_ (zero_le _), selectionFailureMass_eq_one_of_lt _ _ (by norm_num)⟩
  refine (selectionFailureMass_le_add 2 1 1 0 pureZBasis pureZBasis).trans (le_of_eq ?_)
  simp [matchedShortfallMass, matchedProb, pureZBasis, Finset.sum_range_succ]

/-- **Degenerate basis law.**  If Alice never chooses X, every positive X quota fails surely, for
every Bob basis law and every number of rounds. -/
theorem pureZ_positiveX_fails (N nK mZ mX : ℕ) (pB : PMF Basis) :
    selectionFailureMass N nK mZ (mX + 1) pureZBasis pB = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← selectionSuccessMass_add_failureMass N nK mZ (mX + 1) pureZBasis pB]
    exact le_add_self
  · refine le_trans (le_of_eq ?_)
      (matchedShortfallMass_x_le_selectionFailureMass N nK mZ (mX + 1) pureZBasis pB)
    rw [matchedShortfallMass, Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp [matchedProb, pureZBasis]
    · intro k _ hk
      simp [matchedProb, pureZBasis, zero_pow hk]

/-- The per-round sifting outcome is a probability law for arbitrary basis laws. -/
example (pA pB : PMF Basis) :
    matchedProb pA pB .z + mismatchProb pA pB + matchedProb pA pB .x = 1 :=
  matchedProb_add_mismatchProb_add_matchedProb pA pB

end

end QKD.BB84.Sampling.MatchedCountsAudit
