import QCryptLean.QKD.BB84.Sampling.QuotaFailure
import QCryptLeanTest.QKD.BB84.Sampling.MatchedCounts
import QCryptLean.QKD.BB84.Parameters

/-!
# Quota-failure bound test

A nonvacuity instance of the linear-slack bound at uniform basis choices, a degenerate law at
which the Hoeffding premise fails and failure is sure, edge values of the strict binomial lower
tail, and a use of the bounds through the configured experiment's fields.
-/

open scoped ENNReal BigOperators

namespace QKD.BB84.Sampling.QuotaFailureAudit
open _root_.LOCC

open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Sampling.MatchedCountsAudit
open Math.Concentration.BinomialLowerTail

noncomputable section

theorem matchedProb_uniform_toReal (θ : Basis) :
    (matchedProb uniformBasis uniformBasis θ).toReal = 1 / 4 :=
  matchedProb_uniformOfFintype_toReal θ

/-- **Nonvacuity at uniform bases.**  With 400 raw rounds, a Z quota of 50 (for example 25 key
and 25 test rounds) and an X quota of 50, both a fraction `1/8` below the expected 100 matched
rounds, the quota-failure probability is below `10⁻⁴`. -/
theorem uniform_quotaFailure_lt :
    (selectionFailureMass 400 25 25 50 uniformBasis uniformBasis).toReal < 1 / 10000 := by
  have hbound := selectionFailureMass_toReal_le_two_exp (N := 400) (nK := 25) (mZ := 25)
    (mX := 50) (pA := uniformBasis) (pB := uniformBasis) (η := 1 / 8) (by norm_num)
    (by rw [matchedProb_uniform_toReal]; norm_num)
    (by rw [matchedProb_uniform_toReal]; norm_num)
  refine hbound.trans_lt ?_
  have he : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h12 : (27 / 10 : ℝ) ^ 12 < Real.exp 12 := by
    have := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (12 : ℕ) ≠ 0)
    rwa [← Real.exp_nat_mul, show ((12 : ℕ) : ℝ) * 1 = 12 by norm_num] at this
  have hexp : Real.exp (-2 * (1 / 8) ^ 2 * ((400 : ℕ) : ℝ)) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hneg : Real.exp (-12) = (Real.exp 12)⁻¹ := Real.exp_neg 12
  have hinv : (Real.exp 12)⁻¹ < ((27 / 10 : ℝ) ^ 12)⁻¹ :=
    inv_strictAnti₀ (by positivity) h12
  have hsmall : ((27 / 10 : ℝ) ^ 12)⁻¹ < 1 / 20000 := by norm_num
  linarith

/-- **A degenerate law fails the Hoeffding premise.**  If Alice never chooses X, the X premise of
the Hoeffding bound fails for every positive X quota; the exact failure probability is one
(QKD.BB84.Sampling.MatchedCountsAudit.pureZ_positiveX_fails). -/
theorem pureZ_no_hoeffding_premise (N mX : ℕ) (pB : PMF Basis) :
    ¬(((mX + 1 : ℕ) : ℝ) - 1 < N * (matchedProb pureZBasis pB .x).toReal) := by
  simp [matchedProb, pureZBasis]

/-- Edge values of the strict lower tail: zero quota, quota beyond the trials, and the
degenerate success probabilities. -/
example (n : ℕ) (p : ℝ) :
    binomialLowerTail n 0 p = 0 ∧ binomialLowerTail n (n + 1) p = 1 ∧
      binomialLowerTail n (n + 1) 0 = 1 ∧ binomialLowerTail n n 1 = 0 :=
  ⟨binomialLowerTail_zero_quota n p, binomialLowerTail_of_lt (Nat.lt_succ_self n) p,
    binomialLowerTail_prob_zero (Nat.succ_pos n), binomialLowerTail_prob_one le_rfl⟩

/-- The bounds apply verbatim to the fields of a configured measure-first experiment. -/
example (p : QKD.BB84.Parameters) {η : ℝ} (hη : 0 ≤ η)
    (hZ : (p.keyRounds + p.zTests : ℝ) ≤
      ((matchedProb p.aliceBasis p.bobBasis .z).toReal - η) * p.rounds)
    (hX : (p.xTests : ℝ) ≤ ((matchedProb p.aliceBasis p.bobBasis .x).toReal - η) * p.rounds) :
    (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests p.aliceBasis
        p.bobBasis).toReal ≤ 2 * Real.exp (-2 * η ^ 2 * p.rounds) :=
  selectionFailureMass_toReal_le_two_exp hη hZ hX

end

end QKD.BB84.Sampling.QuotaFailureAudit
