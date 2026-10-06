import QCryptLean.QKD.BB84.Robustness
import QCryptLean.QKD.BB84.Sampling.QuotaFailure

/-!
# Quantitative honest-abort bounds for measure-first BB84

`Parameters.abortProbability_honestSource_le_of_mem_band` bounds the physical program's honest
abort probability by the exact quota-failure mass plus the parameter-estimation and
error-correction completeness budget.  This module eliminates that remaining exact mass using the
matched-count laws of the Sampling.QuotaFailure module.

The resulting statements concern the honest abort probability of the same
`Parameters.protocol` used by both security analyses.  They do not assert a composable
real--ideal robustness distance or positive key yield. The source estimates hold on `q ∈ [0,1]`;
the canonical source itself is positive on `[0,1/2]`. `Measurement.HonestOperation` supplies the
broader physical input class and derives its own rate bounds.

`Parameters.QuotaSlack` records slack below the actual matched-probability means.
`bb84HonestAbortBudget` combines quota failure, parameter estimation, and decoding.
`Parameters.one_sub_honestAbortBudget_le_acceptProbability_of_honestOperation` gives the
corresponding acceptance guarantee for every input in the physical class.  The relative-entropy
counterpart `bb84HonestAbortBudgetKL` prices every tail — quota shortfall, both PE-band
failures, decoding — at the Bernoulli relative-entropy rate;
`one_sub_honestAbortBudgetKL_le_acceptProbability_of_honestOperation` is the corresponding
acceptance guarantee.

The robustness terminology is from Portmann--Renner, arXiv:2102.00021,
`qkd.tex:845`--`:850`.  The quota estimates used here are the project's strict binomial lower-tail,
Hoeffding, and Bernoulli-KL Chernoff bounds for the actual matched-round counts.
-/

open scoped ENNReal

noncomputable section

namespace QKD.BB84

/-- Total honest abort budget: quota shortfall, two parameter-estimation tails, and decoding. -/
def bb84HonestAbortBudget (N mZ mX : ℕ) (ηS η εEC : ℝ) : ℝ :=
  2 * Real.exp (-2 * ηS ^ 2 * N) + bb84CompletenessBudget mZ mX η εEC

/-- Total honest abort budget at the relative-entropy rate: the two quota-failure Chernoff tails
at the exact strict-shortfall endpoints `(nK + mZ - 1)/N` and `(mX - 1)/N`, plus the KL
completeness budget `bb84CompletenessBudgetKL`.  Every tail in it is priced by the Bernoulli
relative entropy `klBer` (Chernoff bound; Cover--Thomas, *Elements of Information Theory*,
§11.1); no margin `ηS` or `η` enters. -/
def bb84HonestAbortBudgetKL (N nK mZ mX : ℕ) (pZ pX Q δ q εEC : ℝ) : ℝ :=
  Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((nK + mZ : ℝ) - 1) / N) pZ) +
    Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((mX : ℝ) - 1) / N) pX) +
    bb84CompletenessBudgetKL mZ mX Q δ q εEC

namespace Parameters

open TypedLOCC
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Engine
open Math.Concentration.BinomialLowerTail

/-- Both configured quotas lie below their matched-count means by the same nonnegative slack. -/
structure QuotaSlack (p : Parameters) (ηS : ℝ) : Prop where
  /-- The slack fraction is nonnegative. -/
  slack_nonneg : 0 ≤ ηS
  /-- Z matches cover the key rounds and Z tests after subtracting slack. -/
  zQuota_le : (p.keyRounds + p.zTests : ℝ) ≤
    ((Sampling.matchedProb p.aliceBasis p.bobBasis .z).toReal - ηS) * p.rounds
  /-- X matches cover the X tests after subtracting slack. -/
  xQuota_le : (p.xTests : ℝ) ≤
    ((Sampling.matchedProb p.aliceBasis p.bobBasis .x).toReal - ηS) * p.rounds

variable (p : Parameters)

/-- The honest abort probability is bounded by the two exact binomial shortfall probabilities plus
the tail-completeness budget.  The two matched-round counts need not be independent: the proof uses
the union bound for their joint quota-failure event. -/
theorem abortProbability_honestSource_le_binomialLowerTail_of_mem_band
    (q εEC η : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hB : p.HonestBand q η εEC) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      binomialLowerTail p.rounds (p.keyRounds + p.zTests)
          (matchedProb p.aliceBasis p.bobBasis .z).toReal +
        binomialLowerTail p.rounds p.xTests
          (matchedProb p.aliceBasis p.bobBasis .x).toReal +
        bb84CompletenessBudget p.zTests p.xTests η εEC := by
  calc
    p.protocol.abortProbability (honestSource p.rounds q) ≤
        (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
            p.aliceBasis p.bobBasis).toReal +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      p.abortProbability_honestSource_le_of_mem_band q εEC η hq0 hq hB
    _ ≤ (binomialLowerTail p.rounds (p.keyRounds + p.zTests)
            (matchedProb p.aliceBasis p.bobBasis .z).toReal +
          binomialLowerTail p.rounds p.xTests
            (matchedProb p.aliceBasis p.bobBasis .x).toReal) +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      add_le_add
        (selectionFailureMass_toReal_le_add p.rounds p.keyRounds p.zTests p.xTests
          p.aliceBasis p.bobBasis) le_rfl

/-- Hoeffding's quantitative honest-abort bound at the exact strict-shortfall endpoints.  For a
positive quota its largest failing matched count is one below the quota; a zero quota has no failing
count.  The displayed endpoint premises place the two algebraic thresholds below their respective
expectations. -/
theorem abortProbability_honestSource_le_hoeffding_of_mem_band
    (q εEC η : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hB : p.HonestBand q η εEC)
    (hZ : (p.keyRounds + p.zTests : ℝ) - 1 <
      p.rounds * (matchedProb p.aliceBasis p.bobBasis .z).toReal)
    (hX : (p.xTests : ℝ) - 1 <
      p.rounds * (matchedProb p.aliceBasis p.bobBasis .x).toReal) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      Real.exp (-2 * (p.rounds * (matchedProb p.aliceBasis p.bobBasis .z).toReal -
          (p.keyRounds + p.zTests) + 1) ^ 2 / p.rounds) +
        Real.exp (-2 * (p.rounds * (matchedProb p.aliceBasis p.bobBasis .x).toReal -
          p.xTests + 1) ^ 2 / p.rounds) +
        bb84CompletenessBudget p.zTests p.xTests η εEC := by
  calc
    p.protocol.abortProbability (honestSource p.rounds q) ≤
        (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
            p.aliceBasis p.bobBasis).toReal +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      p.abortProbability_honestSource_le_of_mem_band q εEC η hq0 hq hB
    _ ≤ (Real.exp (-2 *
            (p.rounds * (matchedProb p.aliceBasis p.bobBasis .z).toReal -
              (p.keyRounds + p.zTests) + 1) ^ 2 / p.rounds) +
          Real.exp (-2 *
            (p.rounds * (matchedProb p.aliceBasis p.bobBasis .x).toReal -
              p.xTests + 1) ^ 2 / p.rounds)) +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      add_le_add (selectionFailureMass_toReal_le_exp hZ hX) le_rfl

/-- Linear-slack quantitative honest-abort bound.  If each quota is at most its expected matched
count minus `ηS * rounds`, where `ηS` is a nonnegative fraction of the total number of rounds, the
quota-failure contribution is at most `2 * exp (-2 * ηS^2 * rounds)`. -/
theorem abortProbability_honestSource_le_two_exp_of_mem_band
    (q εEC η ηS : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hB : p.HonestBand q η εEC)
    (hS : p.QuotaSlack ηS) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      bb84HonestAbortBudget p.rounds p.zTests p.xTests ηS η εEC := by
  calc
    p.protocol.abortProbability (honestSource p.rounds q) ≤
        (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
            p.aliceBasis p.bobBasis).toReal +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      p.abortProbability_honestSource_le_of_mem_band q εEC η hq0 hq hB
    _ ≤ 2 * Real.exp (-2 * ηS ^ 2 * p.rounds) +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      add_le_add
        (selectionFailureMass_toReal_le_two_exp hS.slack_nonneg hS.zQuota_le hS.xQuota_le) le_rfl

/-- **The honest-abort bound at the relative-entropy quota rate**: the two quota-shortfall tails
are priced by the Bernoulli KL Chernoff exponents of the matched-Z and matched-X shortfalls
directly, while the completeness term stays Hoeffding-priced (`bb84CompletenessBudget … η εEC`,
the margin `η` enters as in `abortProbability_honestSource_le_hoeffding_of_mem_band`).  For the
fully KL-priced budget see `bb84HonestAbortBudgetKL`,
`abortProbability_honestSource_le_honestAbortBudgetKL_of_strict_band`, and
`one_sub_honestAbortBudgetKL_le_acceptProbability_of_honestOperation`. -/
theorem abortProbability_honestSource_le_klBer_of_mem_band
    (q εEC η : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hB : p.HonestBand q η εEC)
    (hZ : ((p.keyRounds + p.zTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .z).toReal)
    (hZ1 : (matchedProb p.aliceBasis p.bobBasis .z).toReal < 1)
    (hX : ((p.xTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .x).toReal)
    (hX1 : (matchedProb p.aliceBasis p.bobBasis .x).toReal < 1) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      Real.exp (-(p.rounds : ℝ) * Math.Concentration.BernoulliKL.klBer
          (((p.keyRounds + p.zTests : ℝ) - 1) / p.rounds)
          (matchedProb p.aliceBasis p.bobBasis .z).toReal) +
        Real.exp (-(p.rounds : ℝ) * Math.Concentration.BernoulliKL.klBer
          (((p.xTests : ℝ) - 1) / p.rounds)
          (matchedProb p.aliceBasis p.bobBasis .x).toReal) +
        bb84CompletenessBudget p.zTests p.xTests η εEC := by
  calc
    p.protocol.abortProbability (honestSource p.rounds q) ≤
        (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
            p.aliceBasis p.bobBasis).toReal +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      p.abortProbability_honestSource_le_of_mem_band q εEC η hq0 hq hB
    _ ≤ (Real.exp (-(p.rounds : ℝ) * Math.Concentration.BernoulliKL.klBer
            (((p.keyRounds + p.zTests : ℝ) - 1) / p.rounds)
            (matchedProb p.aliceBasis p.bobBasis .z).toReal) +
          Real.exp (-(p.rounds : ℝ) * Math.Concentration.BernoulliKL.klBer
            (((p.xTests : ℝ) - 1) / p.rounds)
            (matchedProb p.aliceBasis p.bobBasis .x).toReal)) +
          bb84CompletenessBudget p.zTests p.xTests η εEC :=
      add_le_add (selectionFailureMass_toReal_le_exp_klBer hZ hZ1 hX hX1) le_rfl

/-- **The configured tail accepts the honest channel with probability at least `1 - ε_c^KL`**,
the relative-entropy counterpart of
`one_sub_completenessBudget_le_honestTailAcceptance_of_mem_band`: the PE-band failures are priced
by the Bernoulli KL divergence (`bb84_completeness_of_mem_band_klBer`; Chernoff bound,
Cover--Thomas, *Elements of Information Theory*, §11.1), so only the strict window
`|q - p.errorRate| < p.tolerance` is needed — no margin inside the window. -/
theorem one_sub_completenessBudgetKL_le_honestTailAcceptance_of_strict_band
    (q εEC : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hband : |q - p.errorRate| < p.tolerance)
    (hdec : p.ec.DecodesWhp (bb84HonestKeyErrWeight p.sifted q p.peSel p.xSel) εEC) :
    1 - bb84CompletenessBudgetKL p.zTests p.xTests p.errorRate p.tolerance q εEC ≤
      p.honestTailAcceptance q := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hband
  have h := one_sub_bb84CompletenessBudgetKL_le_honestTailAcceptance_of_strict_band p.sifted p.tests
    p.keyLength p.tagLength p.leak p.peSel p.xSel p.ec q p.errorRate p.tolerance εEC
    (QKD.BB84.Reduction.packedPESel_keyCount p.keyRounds p.zTests p.xTests) hq0 hq1
    (by linarith) (by linarith) hdec
  rwa [QKD.BB84.Reduction.packedZTestSampleSize, QKD.BB84.Reduction.packedXTestSampleSize] at h

/-- **The honest-abort bound at the relative-entropy rate**: at every honest QBER strictly inside
the acceptance band, the experiment aborts with probability at most `bb84HonestAbortBudgetKL`,
whose every tail — quota shortfall, both PE-band failures, and decoding — is priced by the
Bernoulli relative entropy `klBer` (Chernoff bound; Cover--Thomas, *Elements of Information
Theory*, §11.1). -/
theorem abortProbability_honestSource_le_honestAbortBudgetKL_of_strict_band
    (q εEC : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hband : |q - p.errorRate| < p.tolerance)
    (hdec : p.ec.DecodesWhp (bb84HonestKeyErrWeight p.sifted q p.peSel p.xSel) εEC)
    (hZ : ((p.keyRounds + p.zTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .z).toReal)
    (hZ1 : (matchedProb p.aliceBasis p.bobBasis .z).toReal < 1)
    (hX : ((p.xTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .x).toReal)
    (hX1 : (matchedProb p.aliceBasis p.bobBasis .x).toReal < 1) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      bb84HonestAbortBudgetKL p.rounds p.keyRounds p.zTests p.xTests
        (matchedProb p.aliceBasis p.bobBasis .z).toReal
        (matchedProb p.aliceBasis p.bobBasis .x).toReal
        p.errorRate p.tolerance q εEC := by
  rw [p.abortProbability_honestSource]
  have htail := p.one_sub_completenessBudgetKL_le_honestTailAcceptance_of_strict_band q εEC
    hq0 hq1 hband hdec
  have hF := selectionFailureMass_toReal_le_exp_klBer hZ hZ1 hX hX1
  have hmass := selectionMass_toReal_add p.rounds p.keyRounds p.zTests p.xTests p.aliceBasis
    p.bobBasis
  have hle : p.honestTailAcceptance q ≤ 1 :=
    honestTailAcceptance_le_one p.sifted p.tests p.keyLength p.tagLength p.peSel p.xSel p.leak
      p.ec p.tolerance p.errorRate hq0.le hq1.le
  have hS0 : 0 ≤ (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
      p.aliceBasis p.bobBasis).toReal := ENNReal.toReal_nonneg
  have hF0 : 0 ≤ (selectionFailureMass p.rounds p.keyRounds p.zTests p.xTests
      p.aliceBasis p.bobBasis).toReal := ENNReal.toReal_nonneg
  have hT : 0 ≤ 1 - p.honestTailAcceptance q := by linarith
  -- The success mass is at most one, so the rejected-tail term is at most `1 - tailAcceptance`,
  -- which the KL completeness budget bounds.
  have hstep : (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
      p.aliceBasis p.bobBasis).toReal * (1 - p.honestTailAcceptance q) ≤
      bb84CompletenessBudgetKL p.zTests p.xTests p.errorRate p.tolerance q εEC := by
    have hS1 : (selectionSuccessMass p.rounds p.keyRounds p.zTests p.xTests
        p.aliceBasis p.bobBasis).toReal ≤ 1 := by linarith
    exact (mul_le_mul_of_nonneg_right hS1 hT).trans (by linarith)
  unfold bb84HonestAbortBudgetKL
  linarith [hF, hstep]

/-- Honest acceptance is at least one minus the relative-entropy abort budget, for every input
in the physical honest-operation class.  Every tail in the budget is at the Bernoulli KL
Chernoff rate. -/
theorem one_sub_honestAbortBudgetKL_le_acceptProbability_of_honestOperation
    (ρ : Op (weightedStreamSystem Unit p.rounds).total) (q εEC : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hband : |q - p.errorRate| < p.tolerance)
    (hdec : p.ec.DecodesWhp (bb84HonestKeyErrWeight p.sifted q p.peSel p.xSel) εEC)
    (hZ : ((p.keyRounds + p.zTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .z).toReal)
    (hZ1 : (matchedProb p.aliceBasis p.bobBasis .z).toReal < 1)
    (hX : ((p.xTests : ℝ) - 1) / p.rounds <
      (matchedProb p.aliceBasis p.bobBasis .x).toReal)
    (hX1 : (matchedProb p.aliceBasis p.bobBasis .x).toReal < 1)
    (h : HonestOperation p.rounds q ρ) :
    1 - bb84HonestAbortBudgetKL p.rounds p.keyRounds p.zTests p.xTests
        (matchedProb p.aliceBasis p.bobBasis .z).toReal
        (matchedProb p.aliceBasis p.bobBasis .x).toReal
        p.errorRate p.tolerance q εEC ≤
      p.protocol.acceptProbability ρ := by
  have habort := p.abortProbability_honestSource_le_honestAbortBudgetKL_of_strict_band q εEC
    hq0 hq1 hband hdec hZ hZ1 hX hX1
  rw [← p.abortProbability_eq_honestSource_of_honestOperation ρ q h] at habort
  have hsplit := p.protocol.acceptProbability_add_abortProbability ρ
  rw [h.trace_eq_one, Complex.one_re] at hsplit
  linarith

/-- Honest acceptance is at least one minus the total abort budget under matched-probability
quota slack. The physical input law supplies normalization and both error-rate bounds. -/
theorem one_sub_honestAbortBudget_le_acceptProbability_of_honestOperation
    (ρ : Op (weightedStreamSystem Unit p.rounds).total) (q εEC η ηS : ℝ)
    (hB : p.HonestBand q η εEC) (hS : p.QuotaSlack ηS)
    (h : HonestOperation p.rounds q ρ) :
    1 - bb84HonestAbortBudget p.rounds p.zTests p.xTests ηS η εEC ≤
      p.protocol.acceptProbability ρ := by
  have habort := p.abortProbability_honestSource_le_two_exp_of_mem_band q εEC η ηS
    h.rate_nonneg h.rate_le_one hB hS
  rw [← p.abortProbability_eq_honestSource_of_honestOperation ρ q h] at habort
  have hsplit := p.protocol.acceptProbability_add_abortProbability ρ
  rw [h.trace_eq_one, Complex.one_re] at hsplit
  linarith

end Parameters

end QKD.BB84
