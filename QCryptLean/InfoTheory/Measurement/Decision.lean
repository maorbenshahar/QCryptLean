import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.Main
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.KLCoarsening
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Decision Success — correctness coarsening, binary KL, and four-outcome bounds

This file packages the finite classical part of converting a labeled
measurement channel into a mutual-information lower bound.  The main event is
whether the decision label equals the input label.

## Main definitions

- `binaryKL`: binary KL divergence with the repository's totalized convention.
- `decisionSuccess`: success probability of the diagonal decision rule.
- `decisionProductSuccess`: product-marginal mass of the diagonal event.
- `uniformInput`: uniform distribution on `Fin k`.
- `uniformDecisionSuccess`: diagonal success probability for uniform inputs.
- `correctnessEvent`: coarsening of flat joint outcomes into correct/incorrect.

## Main statements

- `binaryKL_decisionSuccess_le_mutualInfo`: correctness KL is bounded by mutual
  information.
- `binaryKL_uniformDecisionSuccess_le_mutualInfo`: uniform-input specialization.
- `binaryKL_four_le_imp_le_exp_sub_log_two`: four-outcome binary-KL inversion.
- `uniformDecisionSuccess_fin4_le_exp_mutualInfo`: four-outcome success bound
  from mutual information.
- `uniformDecisionSuccess_fin4_le_exp_vonNeumannEntropy_average`: four-outcome
  success bound from Holevo and von Neumann entropy.
-/

open Quantum.Operators
open scoped BigOperators

noncomputable section

namespace InfoTheory.Measurement

/-- Binary KL divergence with the same totalized zero convention used elsewhere
in this repository. -/
def binaryKL (p q : ℝ) : ℝ :=
  (if p = 0 then 0 else p * Real.log (p / q)) +
    (if 1 - p = 0 then 0 else (1 - p) * Real.log ((1 - p) / (1 - q)))

/-- Success probability of the diagonal decision rule for a labeled
measurement channel. -/
def decisionSuccess {n k : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n k) : ℝ :=
  ∑ x, jointProb probs states M x x

/-- The corresponding success mass under the product of the input and output
marginals. -/
def decisionProductSuccess {n k : ℕ} (probs : Fin k → ℝ)
    (states : Fin k → DensityOp n) (M : POVM n k) : ℝ :=
  ∑ x, probs x * marginalProbY probs states M x

/-- Uniform input distribution on `Fin k`. -/
def uniformInput (k : ℕ) : Fin k → ℝ :=
  fun _ => (1 : ℝ) / k

/-- Diagonal decision success for the uniform input distribution. -/
def uniformDecisionSuccess {n k : ℕ} (states : Fin k → DensityOp n) (M : POVM n k) :
    ℝ :=
  decisionSuccess (uniformInput k) states M

/-- The correctness/incorrectness coarsening of the flat joint distribution. -/
def correctnessEvent {k : ℕ} (j : Fin (k * k)) : Fin 2 :=
  if j.divNat = j.modNat then 0 else 1

lemma uniformInput_nonneg (k : ℕ) : ∀ i : Fin k, 0 ≤ uniformInput k i := by
  intro _
  unfold uniformInput
  positivity

lemma uniformInput_sum {k : ℕ} [NeZero k] : ∑ i : Fin k, uniformInput k i = 1 := by
  unfold uniformInput
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne k)]

lemma decisionProductSuccess_uniform_eq_inv_card {n k : ℕ} [NeZero k]
    (states : Fin k → DensityOp n) (M : POVM n k) :
    decisionProductSuccess (uniformInput k) states M = (1 : ℝ) / k := by
  unfold decisionProductSuccess uniformInput
  rw [show (∑ x : Fin k, (1 / (k : ℝ)) * marginalProbY (fun _ : Fin k => 1 / (k : ℝ))
        states M x) =
      (1 / (k : ℝ)) * ∑ x : Fin k,
        marginalProbY (fun _ : Fin k => 1 / (k : ℝ)) states M x by
    rw [Finset.mul_sum]]
  rw [marginalProbY_sum]
  · ring
  · exact uniformInput_sum (k := k)

lemma flatJoint_nonneg_of_input_nonneg {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (j : Fin (k * m)) :
    0 ≤ flatJoint probs states M j := by
  unfold flatJoint jointProb
  exact mul_nonneg (hprobs_nonneg _) (M.prob_nonneg _ _)

lemma flatProduct_nonneg_of_input_nonneg {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (j : Fin (k * m)) :
    0 ≤ flatProduct probs states M j := by
  unfold flatProduct
  exact mul_nonneg (hprobs_nonneg _)
    (marginalProbY_nonneg probs states M hprobs_nonneg _)

lemma flatProduct_zero_imp_flatJoint_zero {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (j : Fin (k * m)) :
    flatProduct probs states M j = 0 → flatJoint probs states M j = 0 := by
  unfold flatProduct flatJoint jointProb
  intro hprod
  by_cases hp : probs j.divNat = 0
  · simp [hp]
  · have hp_pos : 0 < probs j.divNat :=
      lt_of_le_of_ne (hprobs_nonneg _) (Ne.symm hp)
    have hmarg_zero : marginalProbY probs states M j.modNat = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left hp
    have hterm_nonneg :
        ∀ x : Fin k, 0 ≤ jointProb probs states M x j.modNat :=
      fun x => jointProb_nonneg probs states M hprobs_nonneg x j.modNat
    have hdiag_zero :
        jointProb probs states M j.divNat j.modNat = 0 := by
      unfold marginalProbY at hmarg_zero
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hterm_nonneg x) |>.mp hmarg_zero j.divNat (Finset.mem_univ _)
    unfold jointProb at hdiag_zero
    exact hdiag_zero

lemma correctnessEvent_eq_zero_iff {k : ℕ} (j : Fin (k * k)) :
    correctnessEvent j = 0 ↔ j.divNat = j.modNat := by
  unfold correctnessEvent
  by_cases h : j.divNat = j.modNat <;> simp [h]

lemma correctnessEvent_eq_one_iff {k : ℕ} (j : Fin (k * k)) :
    correctnessEvent j = 1 ↔ j.divNat ≠ j.modNat := by
  unfold correctnessEvent
  by_cases h : j.divNat = j.modNat <;> simp [h]

/-- The zero fiber of `correctnessEvent` is the diagonal. -/
lemma correctness_event_zero_filter_eq_diagonal {k : ℕ} :
    Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 0) =
      Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat) := by
  ext j
  simp [correctnessEvent_eq_zero_iff]

/-- The one fiber of `correctnessEvent` is the off-diagonal. -/
lemma correctness_event_one_filter_eq_off_diagonal {k : ℕ} :
    Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 1) =
      Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat) := by
  ext j
  simp [correctnessEvent_eq_one_iff]

lemma correct_flatJoint_mass_eq_decisionSuccess {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
        flatJoint probs states M j) =
      decisionSuccess probs states M := by
  unfold decisionSuccess flatJoint
  rw [show
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          jointProb probs states M j.divNat j.modNat) =
        ∑ x : Fin k, jointProb probs states M x x from by
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          jointProb probs states M j.divNat j.modNat)
          = ∑ j : Fin (k * k),
              if j.divNat = j.modNat then
                jointProb probs states M j.divNat j.modNat
              else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ x : Fin k, ∑ y : Fin k,
              if x = y then jointProb probs states M x y else 0 := by
            exact
              flat_sum_eq_double_sum (k := k) (m := k)
                (fun x y => if x = y then jointProb probs states M x y else 0)
      _ = ∑ x : Fin k, jointProb probs states M x x := by
            simp]

lemma correct_flatProduct_mass_eq_decisionProductSuccess {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
        flatProduct probs states M j) =
      decisionProductSuccess probs states M := by
  unfold decisionProductSuccess flatProduct
  rw [show
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          probs j.divNat * marginalProbY probs states M j.modNat) =
        ∑ x : Fin k, probs x * marginalProbY probs states M x from by
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          probs j.divNat * marginalProbY probs states M j.modNat)
          = ∑ j : Fin (k * k),
              if j.divNat = j.modNat then
                probs j.divNat * marginalProbY probs states M j.modNat
              else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ x : Fin k, ∑ y : Fin k,
              if x = y then probs x * marginalProbY probs states M y else 0 := by
            exact
              flat_sum_eq_double_sum (k := k) (m := k)
                (fun x y =>
                  if x = y then probs x * marginalProbY probs states M y else 0)
      _ = ∑ x : Fin k, probs x * marginalProbY probs states M x := by
            simp]

lemma incorrect_flatJoint_mass_eq_one_sub_decisionSuccess {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_sum : ∑ i, probs i = 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat),
        flatJoint probs states M j) =
      1 - decisionSuccess probs states M := by
  have hpartition :
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          flatJoint probs states M j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat),
          flatJoint probs states M j) =
        ∑ j : Fin (k * k), flatJoint probs states M j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
      (fun j : Fin (k * k) => j.divNat = j.modNat) (flatJoint probs states M)]
  have htotal : ∑ j : Fin (k * k), flatJoint probs states M j = 1 := by
    unfold flatJoint
    exact
      (flat_sum_eq_double_sum (k := k) (m := k)
        (fun x y => jointProb probs states M x y)).trans (by
      unfold jointProb
      calc ∑ x : Fin k, ∑ y : Fin k, probs x * M.prob (states x) y
        = ∑ x : Fin k, probs x * (∑ y : Fin k, M.prob (states x) y) := by
            congr 1
            ext x
            rw [← Finset.mul_sum]
      _ = ∑ x : Fin k, probs x := by simp [M.prob_sum]
      _ = 1 := hprobs_sum)
  rw [correct_flatJoint_mass_eq_decisionSuccess] at hpartition
  linarith

lemma incorrect_flatProduct_mass_eq_one_sub_decisionProductSuccess {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_sum : ∑ i, probs i = 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat),
        flatProduct probs states M j) =
      1 - decisionProductSuccess probs states M := by
  have hpartition :
      (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat = j.modNat),
          flatProduct probs states M j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat),
          flatProduct probs states M j) =
        ∑ j : Fin (k * k), flatProduct probs states M j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
      (fun j : Fin (k * k) => j.divNat = j.modNat) (flatProduct probs states M)]
  have htotal : ∑ j : Fin (k * k), flatProduct probs states M j = 1 := by
    unfold flatProduct
    exact
      (flat_sum_eq_double_sum (k := k) (m := k)
        (fun x y => probs x * marginalProbY probs states M y)).trans (by
      calc ∑ x : Fin k, ∑ y : Fin k, probs x * marginalProbY probs states M y
        = ∑ x : Fin k, probs x * (∑ y : Fin k, marginalProbY probs states M y) := by
            congr 1
            ext x
            rw [← Finset.mul_sum]
      _ = ∑ x : Fin k, probs x := by
            rw [marginalProbY_sum probs states M hprobs_sum]
            simp
      _ = 1 := hprobs_sum)
  rw [correct_flatProduct_mass_eq_decisionProductSuccess] at hpartition
  linarith

lemma correctnessEvent_zero_flatJoint_mass_eq_decisionSuccess {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 0),
        flatJoint probs states M j) =
      decisionSuccess probs states M := by
  rw [correctness_event_zero_filter_eq_diagonal]
  exact correct_flatJoint_mass_eq_decisionSuccess probs states M

lemma correctnessEvent_zero_flatProduct_mass_eq_decisionProductSuccess {n k : ℕ}
    [NeZero k] (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 0),
        flatProduct probs states M j) =
      decisionProductSuccess probs states M := by
  rw [correctness_event_zero_filter_eq_diagonal]
  exact correct_flatProduct_mass_eq_decisionProductSuccess probs states M

lemma correctnessEvent_one_flatJoint_mass_eq_one_sub_decisionSuccess {n k : ℕ}
    [NeZero k] (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_sum : ∑ i, probs i = 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 1),
        flatJoint probs states M j) =
      1 - decisionSuccess probs states M := by
  rw [correctness_event_one_filter_eq_off_diagonal]
  exact incorrect_flatJoint_mass_eq_one_sub_decisionSuccess probs states M hprobs_sum

lemma correctnessEvent_one_flatProduct_mass_eq_one_sub_decisionProductSuccess {n k : ℕ}
    [NeZero k] (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_sum : ∑ i, probs i = 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => correctnessEvent j = 1),
        flatProduct probs states M j) =
      1 - decisionProductSuccess probs states M := by
  rw [correctness_event_one_filter_eq_off_diagonal]
  exact incorrect_flatProduct_mass_eq_one_sub_decisionProductSuccess probs states M hprobs_sum

/-- The KL of correctness and error probabilities is the KL expression obtained
by coarsening the flat distributions along `correctnessEvent`. -/
lemma binary_kl_eq_correctness_event_kl_coarsening {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_sum : ∑ i, probs i = 1) :
    binaryKL (decisionSuccess probs states M)
        (decisionProductSuccess probs states M) =
      ∑ y : Fin 2,
        let py :=
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (k * k) => correctnessEvent j = y),
            flatJoint probs states M j
        let qy :=
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (k * k) => correctnessEvent j = y),
            flatProduct probs states M j
        if py = 0 then 0 else py * Real.log (py / qy) := by
  rw [Fin.sum_univ_two]
  unfold binaryKL
  dsimp
  rw [correctnessEvent_zero_flatJoint_mass_eq_decisionSuccess]
  rw [correctnessEvent_zero_flatProduct_mass_eq_decisionProductSuccess]
  rw [correctnessEvent_one_flatJoint_mass_eq_one_sub_decisionSuccess
    (hprobs_sum := hprobs_sum)]
  rw [correctnessEvent_one_flatProduct_mass_eq_one_sub_decisionProductSuccess
    (hprobs_sum := hprobs_sum)]

/-- Coarsening the joint/product distributions to the event
`decision = input` gives a binary KL lower bound on mutual information. -/
theorem binaryKL_decisionSuccess_le_mutualInfo {n k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n k)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    binaryKL (decisionSuccess probs states M)
        (decisionProductSuccess probs states M) ≤
      mutualInfo probs states M := by
  have hcoarse :=
    InfoTheory.RelativeEntropy.kl_divergence_coarsening
      (flatJoint probs states M)
      (flatProduct probs states M)
      (flatJoint_nonneg_of_input_nonneg probs states M hprobs_nonneg)
      (flatProduct_nonneg_of_input_nonneg probs states M hprobs_nonneg)
      (correctnessEvent (k := k))
      (flatProduct_zero_imp_flatJoint_zero probs states M hprobs_nonneg)
  have hmi :=
    mutual_info_eq_kl_divergence probs states M hprobs_nonneg hprobs_sum
  unfold mutualInfo
  rw [hmi]
  exact le_trans
    (le_of_eq
      (binary_kl_eq_correctness_event_kl_coarsening probs states M hprobs_sum))
    hcoarse

/-- Uniform-input specialization of the binary correctness KL lower bound. -/
theorem binaryKL_uniformDecisionSuccess_le_mutualInfo {n k : ℕ} [NeZero k]
    (states : Fin k → DensityOp n) (M : POVM n k) :
    binaryKL (uniformDecisionSuccess states M) ((1 : ℝ) / k) ≤
      mutualInfo (uniformInput k) states M := by
  simpa [uniformDecisionSuccess, decisionProductSuccess_uniform_eq_inv_card]
    using binaryKL_decisionSuccess_le_mutualInfo
      (uniformInput k) states M (uniformInput_nonneg k) (uniformInput_sum (k := k))

private def binaryDecisionDist (p : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then p else 1 - p

private def binaryDecisionAlphaLogThree : Fin 2 → ℝ :=
  fun i => if i = 0 then Real.log 3 else 0

private lemma binaryDecisionDist_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ binaryDecisionDist p i := by
  intro i
  fin_cases i <;> simp [binaryDecisionDist, hp0, sub_nonneg.mpr hp1]

private lemma binaryDecisionDist_sum {p : ℝ} :
    ∑ i, binaryDecisionDist p i = 1 := by
  simp [binaryDecisionDist]

private lemma binaryEntropy_add_mul_log_three_le_log_four {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Math.ClassicalEntropy.binaryEntropy p + p * Real.log 3 ≤ Real.log 4 := by
  have hg :=
    Math.ClassicalEntropy.classical_gibbs_variational
      (binaryDecisionDist p) binaryDecisionAlphaLogThree
      (binaryDecisionDist_nonneg hp0 hp1) (binaryDecisionDist_sum (p := p))
  have hsum_exp :
      ∑ i, Real.exp (binaryDecisionAlphaLogThree i) = (4 : ℝ) := by
    rw [Fin.sum_univ_two]
    simp [binaryDecisionAlphaLogThree, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  rw [hsum_exp] at hg
  simpa [binaryDecisionDist, binaryDecisionAlphaLogThree,
    Math.ClassicalEntropy.binaryEntropy, Math.ClassicalEntropy.shannonEntropy] using hg

private lemma binaryKL_four_eq_log_four_sub_binaryEntropy_sub {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryKL p ((1 : ℝ) / 4) =
      Real.log 4 - Math.ClassicalEntropy.binaryEntropy p - (1 - p) * Real.log 3 := by
  by_cases hp : p = 0
  · subst p
    simp only [binaryKL, Math.ClassicalEntropy.binaryEntropy,
      Math.ClassicalEntropy.entropyTerm, one_div, sub_zero, one_mul, ↓reduceIte,
      Real.log_one, mul_zero, zero_add]
    rw [show (1 : ℝ) - 4⁻¹ = 3 / 4 by norm_num]
    rw [Real.log_inv]
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  · by_cases h1p : 1 - p = 0
    · have hp_eq : p = 1 := by linarith
      subst p
      norm_num [binaryKL, Math.ClassicalEntropy.binaryEntropy,
        Math.ClassicalEntropy.entropyTerm]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
      have h1p_pos : 0 < 1 - p := lt_of_le_of_ne (sub_nonneg.mpr hp1) (Ne.symm h1p)
      unfold binaryKL Math.ClassicalEntropy.binaryEntropy Math.ClassicalEntropy.entropyTerm
      simp only [hp, h1p, one_div, div_inv_eq_mul, neg_mul, neg_sub, ↓reduceIte]
      rw [Real.log_mul (ne_of_gt hp_pos) (by norm_num : (4 : ℝ) ≠ 0)]
      rw [show (1 : ℝ) - 4⁻¹ = 3 / 4 by norm_num]
      rw [Real.log_div (ne_of_gt h1p_pos) (by norm_num : ((3 : ℝ) / 4) ≠ 0)]
      rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
      ring_nf

lemma binaryKL_four_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryKL p ((1 : ℝ) / 4) := by
  rw [binaryKL_four_eq_log_four_sub_binaryEntropy_sub hp0 hp1]
  have hle := binaryEntropy_add_mul_log_three_le_log_four
    (p := 1 - p) (sub_nonneg.mpr hp1) (by linarith)
  rw [← Math.ClassicalEntropy.binaryEntropy_symm p] at hle
  linarith

lemma binaryKL_four_ge_mul_log_nine_sub_log_three {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.log 9 - Real.log 3 ≤ binaryKL p ((1 : ℝ) / 4) := by
  rw [binaryKL_four_eq_log_four_sub_binaryEntropy_sub hp0 hp1]
  have hle := binaryEntropy_add_mul_log_three_le_log_four hp0 hp1
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog9]
  linarith

lemma log_two_mul_le_binaryKL_four {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.log (2 * p) ≤ binaryKL p ((1 : ℝ) / 4) := by
  by_cases hp_half_le : p ≤ (1 : ℝ) / 2
  · have hmul_pos : 0 < 2 * p := by positivity
    have hmul_le : 2 * p ≤ 1 := by nlinarith
    have hlog_nonpos : Real.log (2 * p) ≤ 0 :=
      Real.log_nonpos hmul_pos.le hmul_le
    exact hlog_nonpos.trans (binaryKL_four_nonneg hp0.le hp1)
  · have hp_half : (1 : ℝ) / 2 ≤ p := le_of_lt (not_le.mp hp_half_le)
    have hvar := binaryKL_four_ge_mul_log_nine_sub_log_three hp0.le hp1
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three.le
    have hnonneg : 0 ≤ 2 * p - 1 := by nlinarith
    have hlog_le_linear : Real.log (2 * p) ≤ 2 * p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hlinear_le : 2 * p - 1 ≤ (2 * p - 1) * Real.log 3 :=
      le_mul_of_one_le_right hnonneg hlog3_ge_one
    have hlog9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog9] at hvar
    linarith

theorem binaryKL_four_le_imp_le_exp_sub_log_two {p I : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hkl : binaryKL p ((1 : ℝ) / 4) ≤ I) :
    p ≤ Real.exp (I - Real.log 2) := by
  by_cases hp : p = 0
  · subst p
    positivity
  · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hlog_le : Real.log (2 * p) ≤ I :=
      (log_two_mul_le_binaryKL_four hp_pos hp1).trans hkl
    have h_exp : 2 * p ≤ Real.exp I := by
      have h := Real.exp_le_exp.mpr hlog_le
      simpa [Real.exp_log (by positivity : 0 < 2 * p)] using h
    calc
      p = (2 * p) / 2 := by ring
      _ ≤ Real.exp I / 2 := by linarith
      _ = Real.exp (I - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma uniformDecisionSuccess_nonneg {n k : ℕ}
    (states : Fin k → DensityOp n) (M : POVM n k) :
    0 ≤ uniformDecisionSuccess states M := by
  unfold uniformDecisionSuccess decisionSuccess
  apply Finset.sum_nonneg
  intro x _
  exact jointProb_nonneg (uniformInput k) states M (uniformInput_nonneg k) x x

lemma uniformDecisionSuccess_le_one {n k : ℕ} [NeZero k]
    (states : Fin k → DensityOp n) (M : POVM n k) :
    uniformDecisionSuccess states M ≤ 1 := by
  have hinc_eq :=
    incorrect_flatJoint_mass_eq_one_sub_decisionSuccess
      (uniformInput k) states M (uniformInput_sum (k := k))
  have hinc_nonneg :
      0 ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin (k * k) => j.divNat ≠ j.modNat),
          flatJoint (uniformInput k) states M j := by
    apply Finset.sum_nonneg
    intro j _
    exact flatJoint_nonneg_of_input_nonneg
      (uniformInput k) states M (uniformInput_nonneg k) j
  have hsub : 0 ≤ 1 - decisionSuccess (uniformInput k) states M := by
    simpa [hinc_eq] using hinc_nonneg
  simpa [uniformDecisionSuccess] using sub_nonneg.mp hsub

theorem uniformDecisionSuccess_fin4_le_exp_mutualInfo {n : ℕ}
    (states : Fin 4 → DensityOp n) (M : POVM n 4) :
    uniformDecisionSuccess states M ≤
      Real.exp (mutualInfo (uniformInput 4) states M - Real.log 2) := by
  apply binaryKL_four_le_imp_le_exp_sub_log_two
  · exact uniformDecisionSuccess_nonneg states M
  · exact uniformDecisionSuccess_le_one states M
  · simpa using binaryKL_uniformDecisionSuccess_le_mutualInfo states M

theorem uniformDecisionSuccess_fin4_le_exp_vonNeumannEntropy_average {n : ℕ}
    [NeZero n] (states : Fin 4 → DensityOp n) (M : POVM n 4) :
    uniformDecisionSuccess states M ≤
      Real.exp
        (InfoTheory.VonNeumannEntropy.vonNeumannEntropy
            (DensityOp.fromEnsemble (uniformInput 4) states (uniformInput_nonneg 4)
              (uniformInput_sum (k := 4))) -
          Real.log 2) := by
  exact
    (uniformDecisionSuccess_fin4_le_exp_mutualInfo states M).trans
      (Real.exp_le_exp.mpr (by
        have hmi_chi :=
          holevo_bound (uniformInput 4) states (uniformInput_nonneg 4)
            (uniformInput_sum (k := 4)) M
        have hchi_ent :=
          holevoChi_le_entropy (uniformInput 4) states (uniformInput_nonneg 4)
            (uniformInput_sum (k := 4))
        linarith))

end InfoTheory.Measurement

end
