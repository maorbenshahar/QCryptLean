import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.Math.Probability.Bhattacharyya

/-!
# Smooth conditional min-entropy

`smoothMinEntropy` is the `ENNReal` supremum of conditional min-entropy over the purified-distance
ball. It is monotone in the radius and equals `⊤` when the ball contains the zero state.
Infeasible references contribute zero. `smoothMinEntropyOpt` also optimizes over references.

`smoothMinEntropyReal` is the signed real supremum used for signed tensor arithmetic and finite
compactness arguments. Below the zero-state threshold, its positive part equals
`smoothMinEntropy`. The finite `toReal` bridges require an explicit finiteness guard or the
strict weight bound `ε² < weight(ρ)`.

The candidate predicate `isInSmoothedSetReal` and its boundedness results describe the signed
real supremum. `epsilonBall` describes the underlying geometric ball of subnormalized states.

References: Tomamichel 2016, §6.2, Definitions 6.4–6.5, with the zero-state boundary included.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## The ε-Ball

Tomamichel 2016, §6.2.1, Definition 6.4:
  B^ε(A; ρ) := {τ ∈ S•(A) : P(τ, ρ) ≤ ε}
-/

/-- The ε-ball of sub-normalized states around ρ in purified distance.

    Tomamichel 2016, Definition 6.4:
      B^ε(A; ρ) := {τ ∈ S•(A) : P(τ, ρ) ≤ ε}. -/
def epsilonBall {n : ℕ} [NeZero n] (ρ : SubDensityOp n) (ε : ℝ) : Set (SubDensityOp n) :=
  setOf (fun τ => purifiedDistance ρ τ ≤ ε)

/-- The ε-ball always contains ρ itself (when ε ≥ 0). -/
theorem epsilonBall_self_mem {n : ℕ} [NeZero n] (ρ : SubDensityOp n) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ ∈ epsilonBall ρ ε := by
  change purifiedDistance ρ ρ ≤ ε
  rw [purifiedDistance_self_zero]; exact hε

/-- The ε-ball is nonempty when ε ≥ 0. -/
theorem epsilonBall_nonempty {n : ℕ} [NeZero n] (ρ : SubDensityOp n) {ε : ℝ} (hε : 0 ≤ ε) :
    (epsilonBall ρ ε).Nonempty :=
  ⟨ρ, epsilonBall_self_mem ρ hε⟩

/-- The ε-ball is monotone: ε ≤ ε' implies B^ε(ρ) ⊆ B^ε'(ρ). -/
theorem epsilonBall_mono {n : ℕ} [NeZero n] (ρ : SubDensityOp n) {ε ε' : ℝ} (h : ε ≤ ε') :
    epsilonBall ρ ε ⊆ epsilonBall ρ ε' := fun _ hτ => le_trans hτ h

/-!
## Smooth Min-Entropy

Tomamichel 2016, §6.2.2, Definition 6.5:
  H_min^ε(X|A)_ρ := max_{ρ̃ ∈ B^ε(ρ_{XA})} H_min(X|A)_{ρ̃|σ}

The ε-ball is over the full CQ joint state (Def 6.4), not just the quantum marginal.
The signed `smoothMinEntropyReal` uses `sSup` on a set of reals, optimizing over
`conditionalMinEntropyReal`. The canonical `smoothMinEntropy` is the `ENNReal` supremum of
`conditionalMinEntropy` over the same ball.
-/

/-- Predicate for smooth min-entropy candidates: rho2 is close to ρ and achieves
    real conditional min-entropy value h.

    Tomamichel 2016, Def 6.5: the ε-ball is over the full CQ joint state,
    not just the quantum marginal (Def 6.4). Uses `conditionalMinEntropyReal` (ℝ
    variant) for the sSup arithmetic. -/
def isInSmoothedSetReal {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) (h : ℝ) : Prop :=
  ∃ rho2 : CQState X n,
    h = conditionalMinEntropyReal rho2 σ ∧
    CQState.purifiedDistance ρ rho2 ≤ ε

/-- The smooth min-entropy optimization set contains the center state when the
smoothing radius is nonnegative. -/
theorem smoothedSetReal_nonempty
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : CQState X n) (σ : SubDensityOp n) :
    (setOf (isInSmoothedSetReal ε ρ σ)).Nonempty :=
  ⟨conditionalMinEntropyReal ρ σ, ρ, rfl, by
    rw [CQState.purifiedDistance_self_zero]; exact hε⟩

/-- If every element of `A`, after subtracting `c`, is bounded by some element
of `B`, then the same comparison holds between their conditional suprema. -/
theorem csSup_sub_le_csSup_of_forall_exists_sub_le
    (A B : Set ℝ) (c : ℝ) (hA : A.Nonempty) (hB : BddAbove B)
    (h : ∀ a ∈ A, ∃ b ∈ B, a - c ≤ b) :
    sSup A - c ≤ sSup B := by
  rw [sub_le_iff_le_add]
  apply csSup_le hA
  intro a ha
  obtain ⟨b, hb_mem, hab⟩ := h a ha
  have hb_le : b ≤ sSup B := le_csSup hB hb_mem
  exact sub_le_iff_le_add.mp (le_trans hab hb_le)

/-- If a CQ state `ρ` is normalized (its per-outcome traces sum to 1) and `ρ'` is within
    purified distance `ε` of `ρ`, then the per-outcome traces of `ρ'` sum to at least
    `1 - ε²`. -/
lemma CQState.sum_stateMap_trace_ge_of_purifiedDistance
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {ρ ρ' : CQState X n} {ε : ℝ} (hε : 0 ≤ ε)
    (hρnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε) :
    1 - ε ^ 2 ≤ ∑ x : X, (ρ'.stateMap x).trace := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hρ_joint_trace : ρ.toJointDensity.trace = 1 := by
    rw [CQState.toJointDensity_trace_eq_sum]; exact hρnorm
  have h_joint_ge : 1 - ε ^ 2 ≤ ρ'.toJointDensity.trace :=
    SubDensityOp.trace_ge_of_purifiedDistance_of_normalized
      ρ.toJointDensity ρ'.toJointDensity hρ_joint_trace hε hd
  rw [← CQState.toJointDensity_trace_eq_sum]; exact h_joint_ge

/-- If the center of a smoothed CQ ball has total trace at least `η + 2ε`, then every
    `ε`-close candidate has total trace at least `η`.

This subnormalized replacement for
`CQState.sum_stateMap_trace_ge_of_purifiedDistance` uses the generalized trace distance
term `|tr ρ - tr ρ'| / 2 ≤ P(ρ, ρ')`, so the trace-loss budget is `2ε`. -/
lemma CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {ρ ρ' : CQState X n} {ε η : ℝ}
    (hρ_lower : η + 2 * ε ≤ ∑ x : X, (ρ.stateMap x).trace)
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε) :
    η ≤ ∑ x : X, (ρ'.stateMap x).trace := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hD_le :
      Quantum.Metrics.traceDistanceGen
          ρ.toJointDensity.toOp ρ'.toJointDensity.toOp ≤ ε := by
    exact le_trans
      (traceDistanceGen_le_purifiedDistance ρ.toJointDensity ρ'.toJointDensity)
      (by simpa [CQState.purifiedDistance] using hd)
  have htrace_abs :
      |((ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re)| ≤
        2 * ε := by
    unfold Quantum.Metrics.traceDistanceGen at hD_le
    have htn_nonneg :
        0 ≤ Quantum.Metrics.traceNorm
          (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
      unfold Quantum.Metrics.traceNorm
      positivity
    have hleft_nonneg :
        0 ≤ (1 / 2 : ℝ) *
          Quantum.Metrics.traceNorm
            (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) :=
      mul_nonneg (by norm_num) htn_nonneg
    nlinarith [hD_le, hleft_nonneg]
  have htrace_le :
      (∑ x : X, (ρ.stateMap x).trace) -
          (∑ x : X, (ρ'.stateMap x).trace) ≤ 2 * ε := by
    have hρ_trace :
        (trace ρ.toJointDensity.toOp).re =
          ∑ x : X, (ρ.stateMap x).trace := by
      simpa [SubDensityOp.trace] using
        (CQState.toJointDensity_trace_eq_sum (ρ := ρ))
    have hρ'_trace :
        (trace ρ'.toJointDensity.toOp).re =
          ∑ x : X, (ρ'.stateMap x).trace := by
      simpa [SubDensityOp.trace] using
        (CQState.toJointDensity_trace_eq_sum (ρ := ρ'))
    have htrace_abs' :
        |(∑ x : X, (ρ.stateMap x).trace) -
            (∑ x : X, (ρ'.stateMap x).trace)| ≤ 2 * ε := by
      simpa [Complex.sub_re, hρ_trace, hρ'_trace] using htrace_abs
    exact le_trans (le_abs_self _) htrace_abs'
  linarith

/-- The smooth min-entropy optimization set is bounded above.

    Under the hypotheses `ε < 1` and `∑_x tr(ρ.stateMap x) = 1` (normalization of ρ),
    every element of the set is at most `log₂(|X| / (1 - ε²))`. The normalization
    hypothesis is essential: for sub-normalized ρ with small weight, the set can be
    genuinely unbounded above. The `ε < 1` hypothesis is essential: at ε = 1 the
    ε-ball contains states ρ̃ with arbitrarily small trace, for which
    `H_min(X|A)_{ρ̃|σ}` diverges. -/
theorem smoothMinEntropyReal_bddAbove {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ}
    [NeZero n] (ε : ℝ) (hε1 : ε < 1) (ρ : CQState X n)
    (hρnorm : ∑ x : X, (ρ.stateMap x).trace = 1) (σ : SubDensityOp n) :
    BddAbove (setOf (isInSmoothedSetReal ε ρ σ)) := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hcard_ge_one : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Case split on whether `0 ≤ ε`.  If `ε < 0`, the ε-ball is empty and the set is
  -- trivially bounded.  If `0 ≤ ε`, we use the explicit upper bound
  --   M = log₂(|X| / (1 - ε²)).
  by_cases hε_nn : 0 ≤ ε
  · -- Main case.
    have hε_sq_lt_one : ε ^ 2 < 1 := by nlinarith [hε_nn, hε1]
    have hone_sub_pos : (0 : ℝ) < 1 - ε ^ 2 := by linarith
    have hone_sub_le_one : 1 - ε ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ε]
    set M : ℝ := Real.log ((Fintype.card X : ℝ) / (1 - ε ^ 2)) / Real.log 2
    refine ⟨M, ?_⟩
    intro h hh
    obtain ⟨rho2, hh_eq, hd⟩ := hh
    have h_sum_ge : 1 - ε ^ 2 ≤ ∑ x : X, (rho2.stateMap x).trace :=
      CQState.sum_stateMap_trace_ge_of_purifiedDistance hε_nn hρnorm hd
    -- Bound h above, case-splitting on `minFeasibleLambda rho2 σ`.
    by_cases hm_pos : 0 < minFeasibleLambda rho2 σ
    · -- Nontrivial case.
      have hmlam_lb : (1 - ε ^ 2) / (Fintype.card X : ℝ) ≤ minFeasibleLambda rho2 σ := by
        calc (1 - ε ^ 2) / (Fintype.card X : ℝ)
            ≤ (∑ x : X, (rho2.stateMap x).trace) / (Fintype.card X : ℝ) := by
              exact div_le_div_of_nonneg_right h_sum_ge hcard_pos.le
          _ ≤ minFeasibleLambda rho2 σ :=
              minFeasibleLambda_ge_weight_div_card rho2 σ hm_pos
      have h_lb_pos : (0 : ℝ) < (1 - ε ^ 2) / (Fintype.card X : ℝ) :=
        div_pos hone_sub_pos hcard_pos
      -- Take -log, divide by log 2.
      have hlog_le : Real.log ((1 - ε ^ 2) / (Fintype.card X : ℝ))
          ≤ Real.log (minFeasibleLambda rho2 σ) :=
        Real.log_le_log h_lb_pos hmlam_lb
      have hlog_rewrite :
          Real.log ((1 - ε ^ 2) / (Fintype.card X : ℝ))
            = -Real.log ((Fintype.card X : ℝ) / (1 - ε ^ 2)) := by
        rw [Real.log_div hone_sub_pos.ne' (by exact_mod_cast Fintype.card_ne_zero),
            Real.log_div (by exact_mod_cast Fintype.card_ne_zero) hone_sub_pos.ne']
        ring
      rw [hh_eq]
      unfold conditionalMinEntropyReal
      rw [hlog_rewrite] at hlog_le
      have h_neg :
          -Real.log (minFeasibleLambda rho2 σ)
            ≤ Real.log ((Fintype.card X : ℝ) / (1 - ε ^ 2)) := by linarith
      exact div_le_div_of_nonneg_right h_neg hlog2.le
    · -- Degenerate case: minFeasibleLambda = 0, so h = 0.
      push Not at hm_pos
      have hm_zero : minFeasibleLambda rho2 σ = 0 :=
        le_antisymm hm_pos (minFeasibleLambda_nonneg rho2 σ)
      rw [hh_eq]
      unfold conditionalMinEntropyReal
      rw [hm_zero, Real.log_zero, neg_zero, zero_div]
      -- Need 0 ≤ M.
      have h_ratio_ge_one : (1 : ℝ) ≤ (Fintype.card X : ℝ) / (1 - ε ^ 2) := by
        rw [le_div_iff₀ hone_sub_pos]
        nlinarith [hone_sub_le_one, hcard_ge_one, hone_sub_pos]
      exact div_nonneg (Real.log_nonneg h_ratio_ge_one) hlog2.le
  · -- Vacuous case: ε < 0 implies the ε-ball is empty.
    push Not at hε_nn
    refine ⟨0, ?_⟩
    intro h hh
    obtain ⟨rho2, _, hd⟩ := hh
    -- hd : CQState.purifiedDistance ρ rho2 ≤ ε < 0, but purifiedDistance ≥ 0.
    have hd_joint : purifiedDistance ρ.toJointDensity rho2.toJointDensity ≤ ε := hd
    have hP_nn := purifiedDistance_nonneg ρ.toJointDensity rho2.toJointDensity
    linarith

/-- Explicit total-weight floor forced by an `ε` purified-distance ball whose center
has total weight `weight`.

For traces `weight` and `weight'`, generalized fidelity is bounded above by the
classical two-point fidelity
`√(weight * weight') + √((1 - weight) * (1 - weight'))`.  Solving the resulting
one-dimensional boundary gives this floor when `ε² < weight`. -/
noncomputable def purifiedDistanceWeightFloor (ε weight : ℝ) : ℝ :=
  (Real.sqrt weight * Real.sqrt (1 - ε ^ 2) -
      Real.sqrt (1 - weight) * ε) ^ 2

/-- The explicit purified-distance weight floor is positive below the exact
boundary `ε² < weight`. -/
theorem purifiedDistanceWeightFloor_pos
    {ε weight : ℝ}
    (hε_nn : 0 ≤ ε)
    (hweight_le_one : weight ≤ 1)
    (hε_sq_lt_weight : ε ^ 2 < weight) :
    0 < purifiedDistanceWeightFloor ε weight := by
  unfold purifiedDistanceWeightFloor
  apply sq_pos_of_pos
  have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hweight_pos : 0 < weight := lt_of_le_of_lt hε_sq_nonneg hε_sq_lt_weight
  have hweight_nonneg : 0 ≤ weight := le_of_lt hweight_pos
  have hone_sub_weight_nonneg : 0 ≤ 1 - weight := sub_nonneg.mpr hweight_le_one
  have hε_sq_lt_one : ε ^ 2 < 1 := lt_of_lt_of_le hε_sq_lt_weight hweight_le_one
  have hone_sub_eps_sq_pos : 0 < 1 - ε ^ 2 := sub_pos.mpr hε_sq_lt_one
  have hone_sub_eps_sq_nonneg : 0 ≤ 1 - ε ^ 2 := le_of_lt hone_sub_eps_sq_pos
  have hleft_nonneg : 0 ≤ Real.sqrt weight * Real.sqrt (1 - ε ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.sqrt (1 - weight) * ε :=
    mul_nonneg (Real.sqrt_nonneg _) hε_nn
  have hsq_lt :
      (Real.sqrt (1 - weight) * ε) ^ 2 <
        (Real.sqrt weight * Real.sqrt (1 - ε ^ 2)) ^ 2 := by
    have hright_sq : (Real.sqrt (1 - weight) * ε) ^ 2 = (1 - weight) * ε ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hone_sub_weight_nonneg]
    have hleft_sq :
        (Real.sqrt weight * Real.sqrt (1 - ε ^ 2)) ^ 2 =
          weight * (1 - ε ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hweight_nonneg, Real.sq_sqrt hone_sub_eps_sq_nonneg]
    rw [hright_sq, hleft_sq]
    nlinarith [hε_sq_lt_weight]
  have hdiff_pos :
      0 < Real.sqrt weight * Real.sqrt (1 - ε ^ 2) - Real.sqrt (1 - weight) * ε := by
    exact sub_pos.mpr ((sq_lt_sq₀ hright_nonneg hleft_nonneg).mp hsq_lt)
  exact hdiff_pos

/-- Scalar inversion for the purified-distance total-weight floor.

For two weights `w,w' ∈ [0,1]`, a Bhattacharyya lower bound at radius `ε`
forces `w'` to lie above the explicit floor. -/
theorem purifiedDistanceWeightFloor_le_of_bhattacharyya_lower
    {ε w w' : ℝ}
    (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (hw' : w' ∈ Set.Icc (0 : ℝ) 1)
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_w : ε ^ 2 < w)
    (hB :
      Real.sqrt (1 - ε ^ 2) ≤
        Real.sqrt (w * w') + Real.sqrt ((1 - w) * (1 - w'))) :
    purifiedDistanceWeightFloor ε w ≤ w' := by
  unfold purifiedDistanceWeightFloor
  obtain ⟨hw_nonneg, hw_le_one⟩ := hw
  obtain ⟨hw'_nonneg, hw'_le_one⟩ := hw'
  have hone_sub_w_nonneg : 0 ≤ 1 - w := sub_nonneg.mpr hw_le_one
  have hone_sub_w'_nonneg : 0 ≤ 1 - w' := sub_nonneg.mpr hw'_le_one
  have hε_sq_lt_one : ε ^ 2 < 1 := lt_of_lt_of_le hε_sq_lt_w hw_le_one
  have hone_sub_eps_sq_nonneg : 0 ≤ 1 - ε ^ 2 := by
    linarith
  have hB_coord :
      Real.sqrt (1 - ε ^ 2) ≤
        Real.sqrt w * Real.sqrt w' + Real.sqrt (1 - w) * Real.sqrt (1 - w') := by
    calc
      Real.sqrt (1 - ε ^ 2)
          ≤ Real.sqrt (w * w') + Real.sqrt ((1 - w) * (1 - w')) := hB
      _ = Real.sqrt w * Real.sqrt w' + Real.sqrt (1 - w) * Real.sqrt (1 - w') := by
        rw [Real.sqrt_mul hw_nonneg, Real.sqrt_mul hone_sub_w_nonneg]
  have hab :
      (Real.sqrt w) ^ 2 + (Real.sqrt (1 - w)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hw_nonneg, Real.sq_sqrt hone_sub_w_nonneg]
    ring
  have hcs :
      (Real.sqrt (1 - ε ^ 2)) ^ 2 + ε ^ 2 = 1 := by
    rw [Real.sq_sqrt hone_sub_eps_sq_nonneg]
    ring
  have hxy :
      (Real.sqrt w') ^ 2 + (Real.sqrt (1 - w')) ^ 2 = 1 := by
    rw [Real.sq_sqrt hw'_nonneg, Real.sq_sqrt hone_sub_w'_nonneg]
    ring
  have hε_sq_lt_sqrt_w_sq : ε ^ 2 < (Real.sqrt w) ^ 2 := by
    rwa [Real.sq_sqrt hw_nonneg]
  have hcoord :
      (Real.sqrt w * Real.sqrt (1 - ε ^ 2) -
          Real.sqrt (1 - w) * ε) ^ 2 ≤
        (Real.sqrt w') ^ 2 :=
    Real.bhattacharyya_floor_sq_le_sq_of_coord
      (a := Real.sqrt w)
      (b := Real.sqrt (1 - w))
      (c := Real.sqrt (1 - ε ^ 2))
      (s := ε)
      (x := Real.sqrt w')
      (y := Real.sqrt (1 - w'))
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      hε_nn
      (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
      hab
      hcs
      hxy
      hε_sq_lt_sqrt_w_sq
      hB_coord
  rwa [Real.sq_sqrt hw'_nonneg] at hcoord

/-- Purified-distance closeness gives the scalar Bhattacharyya lower bound on
the traces of two sub-density operators. -/
theorem SubDensityOp.sqrt_one_sub_eps_sq_le_trace_bhattacharyya_of_purifiedDistance
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n) {ε : ℝ}
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_trace : ε ^ 2 < ρ.trace)
    (hP : purifiedDistance ρ τ ≤ ε) :
    Real.sqrt (1 - ε ^ 2) ≤
      Real.sqrt (ρ.trace * τ.trace) +
        Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
  have hP_nn : 0 ≤ purifiedDistance ρ τ := purifiedDistance_nonneg ρ τ
  have hP_sq_le : purifiedDistance ρ τ ^ 2 ≤ ε ^ 2 := by
    exact sq_le_sq' (by linarith [hε_nn, hP_nn]) hP
  have hP_sq_eq : purifiedDistance ρ τ ^ 2 = 1 - fidelityGen ρ τ ^ 2 :=
    purifiedDistance_sq ρ τ
  have h_one_sub_eps_sq_le_fidelity_sq : 1 - ε ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
    rw [hP_sq_eq] at hP_sq_le
    linarith
  have hε_sq_lt_one : ε ^ 2 < 1 := lt_of_lt_of_le hε_sq_lt_trace ρ.trace_le_one
  have h_one_sub_eps_sq_nonneg : 0 ≤ 1 - ε ^ 2 := by
    linarith
  have h_sqrt_le_fidelityGen :
      Real.sqrt (1 - ε ^ 2) ≤ fidelityGen ρ τ := by
    have hsq :
        Real.sqrt (1 - ε ^ 2) ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
      rwa [Real.sq_sqrt h_one_sub_eps_sq_nonneg]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (fidelityGen_nonneg ρ τ)).mp hsq
  have h_fidelity_le_sqrt :
      Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ≤
        Real.sqrt (ρ.trace * τ.trace) := by
    have hF_sq_le :
        Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ^ 2 ≤
          ρ.trace * τ.trace := fidelity_sq_le_trace_mul_trace ρ τ
    have hF_nn :
        0 ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
      Quantum.Metrics.fidelity_nonneg_posSemidefOp ρ.toPosSemidefOp τ.toPosSemidefOp
    have hsqrt := Real.sqrt_le_sqrt hF_sq_le
    rwa [Real.sqrt_sq hF_nn] at hsqrt
  have h_fidelityGen_le_bhattacharyya :
      fidelityGen ρ τ ≤
        Real.sqrt (ρ.trace * τ.trace) +
          Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
    unfold fidelityGen
    exact add_le_add h_fidelity_le_sqrt (le_refl _)
  exact le_trans h_sqrt_le_fidelityGen h_fidelityGen_le_bhattacharyya

/-- Operator-level total-trace floor for an `ε` purified-distance ball. -/
theorem SubDensityOp.trace_ge_purifiedDistanceWeightFloor
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n) {ε : ℝ}
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_trace : ε ^ 2 < ρ.trace)
    (hP : purifiedDistance ρ τ ≤ ε) :
    purifiedDistanceWeightFloor ε ρ.trace ≤ τ.trace := by
  exact purifiedDistanceWeightFloor_le_of_bhattacharyya_lower
    ρ.trace_mem_unit_interval
    τ.trace_mem_unit_interval
    hε_nn
    hε_sq_lt_trace
    (SubDensityOp.sqrt_one_sub_eps_sq_le_trace_bhattacharyya_of_purifiedDistance
      ρ τ hε_nn hε_sq_lt_trace hP)

/-- Candidate total-weight floor for a CQ purified-distance ball.

If `P(ρ, ρ') ≤ ε` and `ε²` is strictly below the total weight of `ρ`, then the
candidate `ρ'` has total weight at least the explicit
`purifiedDistanceWeightFloor ε weight(ρ)`. -/
theorem CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {ρ ρ' : CQState X n} {ε : ℝ}
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_weight : ε ^ 2 < ∑ x : X, (ρ.stateMap x).trace)
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε) :
    purifiedDistanceWeightFloor ε (∑ x : X, (ρ.stateMap x).trace) ≤
      ∑ x : X, (ρ'.stateMap x).trace := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hε_sq_lt_joint : ε ^ 2 < ρ.toJointDensity.trace := by
    simpa [CQState.toJointDensity_trace_eq_sum] using hε_sq_lt_weight
  have hd_joint :
      InfoTheory.SmoothMinEntropy.purifiedDistance
        ρ.toJointDensity ρ'.toJointDensity ≤ ε := by
    simpa [CQState.purifiedDistance] using hd
  have h_joint :
      purifiedDistanceWeightFloor ε ρ.toJointDensity.trace ≤
        ρ'.toJointDensity.trace :=
    SubDensityOp.trace_ge_purifiedDistanceWeightFloor
      ρ.toJointDensity ρ'.toJointDensity hε_nn hε_sq_lt_joint hd_joint
  simpa [CQState.toJointDensity_trace_eq_sum] using h_joint

/-- Subnormalized real min-entropy upper bound from a positive total-weight floor.

If a CQ state has total weight at least `η > 0`, then every reference operator gives
real min-entropy at most `-log₂(η / |X|)`. -/
lemma conditionalMinEntropyReal_le_of_weight_floor
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {η : ℝ}
    (hη_pos : 0 < η)
    (hη_le_weight : η ≤ ∑ x : X, (ρ.stateMap x).trace) :
    conditionalMinEntropyReal ρ σ ≤
      -Real.log (η / (Fintype.card X : ℝ)) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold conditionalMinEntropyReal
  by_cases hm_pos : 0 < minFeasibleLambda ρ σ
  · have hmlam_lb :
        η / (Fintype.card X : ℝ) ≤ minFeasibleLambda ρ σ := by
      calc
        η / (Fintype.card X : ℝ)
            ≤ (∑ x : X, (ρ.stateMap x).trace) /
                (Fintype.card X : ℝ) := by
              exact div_le_div_of_nonneg_right hη_le_weight hcard_pos.le
        _ ≤ minFeasibleLambda ρ σ :=
              minFeasibleLambda_ge_weight_div_card ρ σ hm_pos
    have h_lb_pos : 0 < η / (Fintype.card X : ℝ) :=
      div_pos hη_pos hcard_pos
    have hlog_le :
        Real.log (η / (Fintype.card X : ℝ)) ≤
          Real.log (minFeasibleLambda ρ σ) :=
      Real.log_le_log h_lb_pos hmlam_lb
    exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le
  · push Not at hm_pos
    have hm_zero : minFeasibleLambda ρ σ = 0 :=
      le_antisymm hm_pos (minFeasibleLambda_nonneg ρ σ)
    rw [hm_zero, Real.log_zero, neg_zero, zero_div]
    have hcard_ge_one : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    have hη_le_one : η ≤ 1 := le_trans hη_le_weight ρ.weight_le_one
    have hη_le_card : η ≤ (Fintype.card X : ℝ) :=
      le_trans hη_le_one hcard_ge_one
    have h_ratio_le_one : η / (Fintype.card X : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hcard_pos]
      simpa using hη_le_card
    have h_ratio_nonneg : 0 ≤ η / (Fintype.card X : ℝ) :=
      (div_pos hη_pos hcard_pos).le
    have hlog_nonpos : Real.log (η / (Fintype.card X : ℝ)) ≤ 0 :=
      Real.log_nonpos h_ratio_nonneg h_ratio_le_one
    exact div_nonneg (by linarith) hlog2.le

/-- The smooth min-entropy optimization set is bounded above once every candidate
in the purified-distance ball has a uniform positive total-weight floor. -/
theorem smoothMinEntropyReal_bddAbove_of_candidate_weight_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ}
    [NeZero n] (ε η : ℝ) (hη_pos : 0 < η) (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hfloor : ∀ ρ' : CQState X n,
      CQState.purifiedDistance ρ ρ' ≤ ε →
        η ≤ ∑ x : X, (ρ'.stateMap x).trace) :
    BddAbove (setOf (isInSmoothedSetReal ε ρ σ)) := by
  refine ⟨-Real.log (η / (Fintype.card X : ℝ)) / Real.log 2, ?_⟩
  intro h hh
  obtain ⟨rho2, hh_eq, hd⟩ := hh
  rw [hh_eq]
  exact conditionalMinEntropyReal_le_of_weight_floor rho2 σ hη_pos (hfloor rho2 hd)

/-- Signed real ε-smooth conditional min-entropy of X given A relative to reference σ.

    Tomamichel 2016, Definition 6.5 (eq. 6.34):
      H_min^ε(X|A)_{ρ|σ} := sup_{ρ̃ ∈ B^ε(ρ_{XA})} H_min(X|A)_{ρ̃|σ}

    where B^ε is the ε-ball in purified distance over the full CQ state.
    The supremum is over `conditionalMinEntropyReal`; it retains negative values.
    Mathlib totalizes an unbounded real supremum to zero. Use the canonical
    `smoothMinEntropy` for the infinite-entropy boundary. -/
noncomputable def smoothMinEntropyReal {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) : ℝ :=
  sSup (setOf (isInSmoothedSetReal ε ρ σ))

namespace CQState

/-- Relabel the finite classical register of a CQ state by an equivalence. -/
noncomputable def relabel {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) (ρ : CQState Y n) : CQState X n where
  stateMap := fun x => ρ.stateMap (e x)
  weight_le_one := by
    calc
      ∑ x : X, (ρ.stateMap (e x)).trace
          = ∑ y : Y, (ρ.stateMap y).trace := by
            exact Fintype.sum_equiv e
              (fun x => (ρ.stateMap (e x)).trace)
              (fun y => (ρ.stateMap y).trace)
              (fun _ => rfl)
      _ ≤ 1 := ρ.weight_le_one

@[simp] lemma relabel_stateMap {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) (ρ : CQState Y n) (x : X) :
    (CQState.relabel e ρ).stateMap x = ρ.stateMap (e x) :=
  rfl

/-- Relabelling the classical register preserves the quantum marginal. -/
@[simp] lemma relabel_quantumMarginal {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) (ρ : CQState Y n) :
    (CQState.relabel e ρ).quantumMarginal = ρ.quantumMarginal := by
  apply SubDensityOp.ext
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end CQState

/-- Feasibility depends only on `stateMap`, so equal `stateMap`s give equal
    `minFeasibleLambda`. -/
lemma minFeasibleLambda_congr_stateMap {X : Type*} [Fintype X] {n : ℕ}
    {ρ ρ' : CQState X n} (σ : SubDensityOp n) (h : ρ.stateMap = ρ'.stateMap) :
    minFeasibleLambda ρ σ = minFeasibleLambda ρ' σ := by
  unfold minFeasibleLambda
  congr 1
  ext t
  unfold isFeasible
  rw [h]

/-- The real conditional min-entropy depends only on the joint density of ρ. -/
lemma conditionalMinEntropyReal_congr_toJointDensity {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} {ρ ρ' : CQState X n} (σ : SubDensityOp n)
    (h : ρ.toJointDensity = ρ'.toJointDensity) :
    conditionalMinEntropyReal ρ σ = conditionalMinEntropyReal ρ' σ := by
  unfold conditionalMinEntropyReal
  rw [minFeasibleLambda_congr_stateMap σ (CQState.toJointDensity_injective h)]

/-- The feasible-lambda optimum is invariant under a finite relabeling of the
classical register. -/
lemma minFeasibleLambda_relabel {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) (ρ : CQState Y n) (σ : SubDensityOp n) :
    minFeasibleLambda (CQState.relabel e ρ) σ = minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  congr 1
  ext t
  unfold isFeasible
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    intro y
    simpa using ht.2 (e.symm y)
  · intro ht
    refine ⟨ht.1, ?_⟩
    intro x
    simpa using ht.2 (e x)

/-- Real conditional min-entropy is invariant under a finite relabeling of the
classical register, with the same quantum reference. -/
lemma conditionalMinEntropyReal_relabel {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) (ρ : CQState Y n) (σ : SubDensityOp n) :
    conditionalMinEntropyReal (CQState.relabel e ρ) σ =
      conditionalMinEntropyReal ρ σ := by
  unfold conditionalMinEntropyReal
  rw [minFeasibleLambda_relabel e ρ σ]

/-- Real conditional min-entropy is unchanged when two CQ states differ only by a
finite equivalence of their classical labels. -/
lemma conditionalMinEntropyReal_congr_classicalEquiv
    {X Y : Type*} [Fintype X] [Fintype Y] {n : ℕ}
    (e : X ≃ Y) {ρ : CQState X n} {ρ' : CQState Y n} (σ : SubDensityOp n)
    (h_state : ∀ x : X, ρ.stateMap x = ρ'.stateMap (e x)) :
    conditionalMinEntropyReal ρ σ = conditionalMinEntropyReal ρ' σ := by
  have h_stateMap : ρ.stateMap = (CQState.relabel e ρ').stateMap := by
    funext x
    exact h_state x
  calc
    conditionalMinEntropyReal ρ σ =
        conditionalMinEntropyReal (CQState.relabel e ρ') σ := by
          unfold conditionalMinEntropyReal
          rw [minFeasibleLambda_congr_stateMap σ h_stateMap]
    _ = conditionalMinEntropyReal ρ' σ :=
        conditionalMinEntropyReal_relabel e ρ' σ

/-- Smooth min-entropy at ε = 0 equals the real unsmoothed min-entropy.

    The ε-ball at ε = 0 collapses to the singleton `{ρ}` (purified distance is a
    metric: `P(ρ, ρ̃) ≤ 0` plus nonnegativity forces `ρ.toJointDensity =
    ρ̃.toJointDensity`, hence `conditionalMinEntropyReal ρ σ = conditionalMinEntropyReal ρ̃ σ`).
    Then `sSup` of a singleton is its element. -/
theorem smoothMinEntropyReal_zero_eq {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropyReal 0 ρ σ = conditionalMinEntropyReal ρ σ := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  unfold smoothMinEntropyReal
  -- Show the smoothed set is the singleton {conditionalMinEntropyReal ρ σ}.
  have hset : setOf (isInSmoothedSetReal 0 ρ σ) = {conditionalMinEntropyReal ρ σ} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · -- ρ itself witnesses membership.
      refine ⟨ρ, rfl, ?_⟩
      rw [CQState.purifiedDistance_self_zero]
    · -- Uniqueness: any element equals conditionalMinEntropyReal ρ σ.
      rintro h ⟨rho2, rfl, hd⟩
      -- `hd : CQState.purifiedDistance ρ rho2 ≤ 0`.
      have hd_joint : purifiedDistance ρ.toJointDensity rho2.toJointDensity ≤ 0 := hd
      have hd_nn := purifiedDistance_nonneg ρ.toJointDensity rho2.toJointDensity
      have hd_zero : purifiedDistance ρ.toJointDensity rho2.toJointDensity = 0 :=
        le_antisymm hd_joint hd_nn
      have hjoint_eq : ρ.toJointDensity = rho2.toJointDensity :=
        (purifiedDistance_eq_zero_iff _ _).mp hd_zero
      exact (conditionalMinEntropyReal_congr_toJointDensity σ hjoint_eq).symm
  rw [hset, csSup_singleton]

/-- Smooth min-entropy lower bound via an explicit approximator, with the
boundedness of the smoothed optimization set supplied by the caller.

This is the membership step behind `smoothMinEntropy_ge_of_hmin_approx` without
assuming that the center state is normalized.  It is useful for subnormalized
postselection filters, where boundedness is a separate side condition. -/
theorem smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (k : ℝ)
    (ρ' : CQState X n)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ)))
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε)
    (hk : k ≤ conditionalMinEntropyReal ρ' σ) :
    k ≤ smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  apply le_trans hk
  apply le_csSup_of_le hbdd
  · exact ⟨ρ', rfl, hd⟩
  · exact le_refl _

/-- Approximate maximizer extraction for smooth min-entropy.

    If k is strictly below the smooth min-entropy, there exists a state ρ̃ in the
    ε-ball of ρ (in purified distance) whose real conditional min-entropy exceeds k.

    Tomamichel 2016, §6.2.2: the smooth min-entropy is defined as a supremum; this
    lemma is the standard sSup-approximation step that extracts a near-maximizer.
    The strict hypothesis `k < smoothMinEntropyReal ε ρ σ` is the correct form:
    sSup need not be attained, but every value strictly below sSup is achieved by
    some element of the set. -/
theorem smoothMinEntropyReal_exists_approx {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (k : ℝ) (hk : k < smoothMinEntropyReal ε ρ σ) :
    ∃ ρ' : CQState X n, CQState.purifiedDistance ρ ρ' ≤ ε ∧ k ≤ conditionalMinEntropyReal ρ' σ := by
  unfold smoothMinEntropyReal at hk
  have hne : (setOf (isInSmoothedSetReal ε ρ σ)).Nonempty :=
    smoothedSetReal_nonempty hε ρ σ
  obtain ⟨h, hmem, hlt⟩ := exists_lt_of_lt_csSup hne hk
  obtain ⟨rho2, hh_eq, hd⟩ := hmem
  refine ⟨rho2, hd, ?_⟩
  rw [← hh_eq]
  exact hlt.le

/-- The signed real smoothing set is bounded above below the zero-state threshold. The sharp
purified-distance weight floor is positive when `ε² < weight(ρ)`. -/
theorem smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight
    {Xc : Type*} [Fintype Xc] [DecidableEq Xc] [Nonempty Xc] {m : ℕ} [NeZero m]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState Xc m) (σ : SubDensityOp m)
    (hweight_gt : ε ^ 2 < ∑ x : Xc, (ρ.stateMap x).trace) :
    BddAbove (setOf (isInSmoothedSetReal ε ρ σ)) :=
  smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε
    (purifiedDistanceWeightFloor ε (∑ x : Xc, (ρ.stateMap x).trace))
    (purifiedDistanceWeightFloor_pos hε_nn ρ.weight_le_one hweight_gt) ρ σ
    (fun _ hd => CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor hε_nn hweight_gt hd)

section ENNReal

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]

/-- Extended nonnegative smooth fixed-reference min-entropy: the supremum of the positive
parts over the purified-distance ball (Tomamichel 2016, Definitions 6.4–6.5). Infeasible
references contribute zero; zero witnesses contribute `⊤`. Negative radii give zero. -/
noncomputable def smoothMinEntropy (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) :
    ENNReal :=
  ⨆ τ : CQState X n, ⨆ (_ : CQState.purifiedDistance ρ τ ≤ ε), conditionalMinEntropy τ σ

/-- Extended smooth min-entropy optimized over references
(Tomamichel 2016, Definitions 6.2 and 6.5). -/
noncomputable def smoothMinEntropyOpt (ε : ℝ) (ρ : CQState X n) : ENNReal :=
  ⨆ σ : SubDensityOp n, smoothMinEntropy ε ρ σ

/-- Every state in the smoothing ball contributes its entropy to the supremum
(Tomamichel 2016, Definition 6.5). -/
theorem conditionalMinEntropy_le_smoothMinEntropy
    {ε : ℝ} (ρ τ : CQState X n) (σ : SubDensityOp n)
    (hd : CQState.purifiedDistance ρ τ ≤ ε) :
    conditionalMinEntropy τ σ ≤ smoothMinEntropy ε ρ σ := by
  exact le_iSup_of_le τ (le_iSup_of_le hd le_rfl)

/-- Insert an extended entropy floor from a witness in the ball, with no weight restriction
(Tomamichel 2016, Definition 6.5). -/
theorem smoothMinEntropy_ge_of_hmin_approx
    {ε : ℝ} (ρ τ : CQState X n) (σ : SubDensityOp n) (k : ℝ)
    (hd : CQState.purifiedDistance ρ τ ≤ ε)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy τ σ) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ :=
  hk.trans (conditionalMinEntropy_le_smoothMinEntropy ρ τ σ hd)

/-- Insert an operator-domination certificate into the extended smoothing supremum
(Tomamichel 2016, Definitions 6.2 and 6.5). -/
theorem smoothMinEntropy_ge_of_isFeasible
    {ε : ℝ} (ρ τ : CQState X n) (σ : SubDensityOp n) (k : ℝ)
    (hd : CQState.purifiedDistance ρ τ ≤ ε) (h : isFeasible τ σ (2 ^ (-k))) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ :=
  smoothMinEntropy_ge_of_hmin_approx ρ τ σ k hd
    (ofReal_le_conditionalMinEntropy_of_isFeasible τ σ k h)

/-- Ball inclusion gives entropy comparison without boundedness assumptions
(Tomamichel 2016, §6.2.1, property ii). -/
theorem smoothMinEntropy_le_of_ball_subset
    {ε δ : ℝ} (ρ ρ' : CQState X n) (σ : SubDensityOp n)
    (hball : ∀ τ, CQState.purifiedDistance ρ τ ≤ ε →
      CQState.purifiedDistance ρ' τ ≤ δ) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy δ ρ' σ := by
  exact iSup_le fun τ => iSup_le fun hd =>
    conditionalMinEntropy_le_smoothMinEntropy ρ' τ σ (hball τ hd)

/-- Enlarging the radius increases extended smooth min-entropy
(Tomamichel 2016, §6.2.1, property ii). -/
theorem smoothMinEntropy_mono_eps {ε δ : ℝ} (h : ε ≤ δ)
    (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy δ ρ σ :=
  smoothMinEntropy_le_of_ball_subset ρ ρ σ (fun _ hd => hd.trans h)

/-- Changing the centre costs at most its purified distance in smoothing radius, by the
triangle inequality (Tomamichel 2016, §3.4 and Definition 6.4). -/
theorem smoothMinEntropy_change_center {ε δ : ℝ}
    (ρ ρ' : CQState X n) (σ : SubDensityOp n)
    (hd : CQState.purifiedDistance ρ' ρ ≤ δ) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy (δ + ε) ρ' σ := by
  apply smoothMinEntropy_le_of_ball_subset
  intro τ hτ
  exact (CQState.purifiedDistance_triangle ρ' ρ τ).trans (add_le_add hd hτ)

/-- The centre itself witnesses the unsmoothed entropy lower bound at nonnegative radius
(Tomamichel 2016, Definitions 6.4–6.5). -/
theorem smoothMinEntropy_ge_conditionalMinEntropy {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : CQState X n) (σ : SubDensityOp n) :
    conditionalMinEntropy ρ σ ≤ smoothMinEntropy ε ρ σ := by
  apply conditionalMinEntropy_le_smoothMinEntropy
  simpa only [CQState.purifiedDistance_self_zero] using hε

/-- At radius zero the ball is a singleton, including for infeasible references
(Tomamichel 2016, §6.2.1, property ii, and §6.2.2). -/
@[simp] theorem smoothMinEntropy_zero_eq (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy 0 ρ σ = conditionalMinEntropy ρ σ := by
  apply le_antisymm
  · refine iSup_le fun τ => iSup_le fun hd => ?_
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    have hzero : purifiedDistance ρ.toJointDensity τ.toJointDensity = 0 :=
      le_antisymm hd (purifiedDistance_nonneg _ _)
    have hstates := CQState.toJointDensity_injective
      ((purifiedDistance_eq_zero_iff _ _).mp hzero)
    have hρτ : ρ = τ := by
      cases ρ
      cases τ
      cases hstates
      rfl
    rw [hρτ]
  · exact smoothMinEntropy_ge_conditionalMinEntropy le_rfl ρ σ

/-- When the ball reaches zero its extended entropy is infinite, including equality at
`ε² = weight(ρ)`. This extends Tomamichel 2016, Definition 6.4 beyond its finite regime. -/
theorem smoothMinEntropy_eq_top_of_weight_le_eps_sq
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (hweight : ∑ x, (ρ.stateMap x).trace ≤ ε ^ 2) :
    smoothMinEntropy ε ρ σ = ⊤ := by
  apply top_unique
  have hd : CQState.purifiedDistance ρ zeroCQ ≤ ε := by
    rw [CQState.purifiedDistance_zeroCQ]
    exact (Real.sqrt_le_iff).mpr ⟨hε, hweight⟩
  simpa only [conditionalMinEntropy_zeroCQ] using
    conditionalMinEntropy_le_smoothMinEntropy ρ zeroCQ σ hd

/-- Every level strictly below the extended supremum has a feasible witness in the ball.
Strict positivity above the level excludes infeasible references automatically
(Tomamichel 2016, §6.2.2). -/
theorem smoothMinEntropy_exists_approx {ε : ℝ}
    (ρ : CQState X n) (σ : SubDensityOp n) (k : ENNReal)
    (hk : k < smoothMinEntropy ε ρ σ) :
    ∃ τ : CQState X n, CQState.purifiedDistance ρ τ ≤ ε ∧ hasFeasibleLambda τ σ ∧
      k < conditionalMinEntropy τ σ := by
  obtain ⟨τ, hτ⟩ := lt_iSup_iff.mp hk
  obtain ⟨hd, hlt⟩ := lt_iSup_iff.mp hτ
  refine ⟨τ, hd, ?_, hlt⟩
  by_contra hfeas
  rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda τ σ hfeas] at hlt
  exact (not_lt_of_ge (zero_le)) hlt

/-- A fixed reference is bounded by the optimized smooth entropy
(Tomamichel 2016, Definitions 6.2 and 6.5). -/
theorem smoothMinEntropy_le_smoothMinEntropyOpt
    (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropyOpt ε ρ :=
  le_iSup (fun σ => smoothMinEntropy ε ρ σ) σ

/-- Optimizing the reference and smoothing commute, giving the supremum of optimized
conditional entropies over the ball (Tomamichel 2016, Definition 6.5). -/
theorem smoothMinEntropyOpt_eq_iSup (ε : ℝ) (ρ : CQState X n) :
    smoothMinEntropyOpt ε ρ =
      ⨆ τ : CQState X n, ⨆ (_ : CQState.purifiedDistance ρ τ ≤ ε),
        conditionalMinEntropyOpt τ := by
  simp only [smoothMinEntropyOpt, smoothMinEntropy, conditionalMinEntropyOpt_eq_iSup]
  rw [iSup_comm]
  congr 1
  funext τ
  exact iSup_comm

/-- Optimized smoothing at radius zero is the optimized conditional entropy
(Tomamichel 2016, §6.2.2). -/
@[simp] theorem smoothMinEntropyOpt_zero_eq (ρ : CQState X n) :
    smoothMinEntropyOpt 0 ρ = conditionalMinEntropyOpt ρ := by
  simp only [smoothMinEntropyOpt, smoothMinEntropy_zero_eq,
    conditionalMinEntropyOpt_eq_iSup]

/-- The optimized extended entropy is infinite when its ball reaches zero
(Tomamichel 2016, Definition 6.4, extended to its boundary). -/
theorem smoothMinEntropyOpt_eq_top_of_weight_le_eps_sq
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n)
    (hweight : ∑ x, (ρ.stateMap x).trace ≤ ε ^ 2) :
    smoothMinEntropyOpt ε ρ = ⊤ := by
  apply top_unique
  have h := smoothMinEntropy_le_smoothMinEntropyOpt ε ρ (0 : SubDensityOp n)
  rwa [smoothMinEntropy_eq_top_of_weight_le_eps_sq hε ρ _ hweight] at h

/-- The positive part of signed real smoothing is below the extended value on a nonempty ball
(Tomamichel 2016, Definition 6.5). This also holds for a totalized unbounded real supremum. -/
theorem ofReal_smoothMinEntropyReal_le_smoothMinEntropy
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n) :
    ENNReal.ofReal (smoothMinEntropyReal ε ρ σ) ≤ smoothMinEntropy ε ρ σ := by
  by_cases htop : smoothMinEntropy ε ρ σ = ⊤
  · rw [htop]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    apply csSup_le (smoothedSetReal_nonempty hε ρ σ)
    rintro _ ⟨τ, rfl, hd⟩
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    exact (ofReal_conditionalMinEntropyReal_le τ σ).trans
      (conditionalMinEntropy_le_smoothMinEntropy ρ τ σ hd)

/-- Below the zero-state threshold, extended smoothing is the positive part of the signed
real value, even at singular references (Tomamichel 2016, Definitions 6.4–6.5). Positive
candidate weight excludes feasible zero optima, and infeasible references contribute zero. -/
theorem smoothMinEntropy_eq_ofReal_of_eps_sq_lt_weight
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (hweight : ε ^ 2 < ∑ x, (ρ.stateMap x).trace) :
    smoothMinEntropy ε ρ σ = ENNReal.ofReal (smoothMinEntropyReal ε ρ σ) := by
  apply le_antisymm
  · refine iSup_le fun τ => iSup_le fun hd => ?_
    by_cases hfeas : hasFeasibleLambda τ σ
    · have hτweight : 0 < ∑ x, (τ.stateMap x).trace :=
        (purifiedDistanceWeightFloor_pos hε ρ.weight_le_one hweight).trans_le
          (CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor hε hweight hd)
      have hpos := minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos τ σ
        hτweight hfeas
      rw [conditionalMinEntropy, if_pos hpos]
      apply ENNReal.ofReal_le_ofReal
      exact le_csSup
        (smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight ε hε ρ σ hweight) ⟨τ, rfl, hd⟩
    · rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda τ σ hfeas]
      exact zero_le
  · exact ofReal_smoothMinEntropyReal_le_smoothMinEntropy hε ρ σ

/-- The extended value is finite below the zero-state threshold at every reference
(Tomamichel 2016, Definitions 6.4–6.5). -/
theorem smoothMinEntropy_ne_top_of_eps_sq_lt_weight
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (hweight : ε ^ 2 < ∑ x, (ρ.stateMap x).trace) :
    smoothMinEntropy ε ρ σ ≠ ⊤ := by
  rw [smoothMinEntropy_eq_ofReal_of_eps_sq_lt_weight hε ρ σ hweight]
  exact ENNReal.ofReal_ne_top

/-- A finite extended smoothing value admits ordinary real lower-bound comparisons.
The finiteness guard avoids the totalized value `toReal ⊤ = 0`
(Tomamichel 2016, §6.2.2). -/
theorem ofReal_le_smoothMinEntropy_iff {ε : ℝ}
    (ρ : CQState X n) (σ : SubDensityOp n) (k : ℝ)
    (hfinite : smoothMinEntropy ε ρ σ ≠ ⊤) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ ↔
      k ≤ (smoothMinEntropy ε ρ σ).toReal :=
  ENNReal.ofReal_le_iff_le_toReal hfinite

/-- Under the finite-ball guards, the real view agrees with the signed value when that
value is nonnegative (Tomamichel 2016, §6.2.2). -/
theorem smoothMinEntropy_toReal_eq_of_eps_sq_lt_weight
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (hweight : ε ^ 2 < ∑ x, (ρ.stateMap x).trace)
    (hH : 0 ≤ smoothMinEntropyReal ε ρ σ) :
    (smoothMinEntropy ε ρ σ).toReal = smoothMinEntropyReal ε ρ σ := by
  rw [smoothMinEntropy_eq_ofReal_of_eps_sq_lt_weight hε ρ σ hweight]
  exact ENNReal.toReal_ofReal hH

/-- Transporting each ball witness and its feasible coefficients increases extended smooth
entropy, including zero witnesses and empty balls. -/
theorem smoothMinEntropy_le_of_transport
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y] {m : ℕ} [NeZero m]
    {ε δ : ℝ} (ρ : CQState X n) (τ : CQState Y m)
    (σ : SubDensityOp n) (ω : SubDensityOp m)
    (h : ∀ ρ', CQState.purifiedDistance ρ ρ' ≤ ε →
      ∃ τ', CQState.purifiedDistance τ τ' ≤ δ ∧
        ∀ t, isFeasible ρ' σ t → isFeasible τ' ω t) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy δ τ ω := by
  refine iSup_le fun ρ' => iSup_le fun hd => ?_
  obtain ⟨τ', hτ', hfeas⟩ := h ρ' hd
  exact (conditionalMinEntropy_le_of_isFeasible_imp ρ' τ' σ ω hfeas).trans
    (conditionalMinEntropy_le_smoothMinEntropy τ τ' ω hτ')

/-- Transporting signed exponential coefficients across the smoothing balls gives an
extended smooth entropy comparison with the positive part of a real penalty. -/
theorem smoothMinEntropy_le_add_of_transport
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y] {m : ℕ} [NeZero m]
    {ε δ : ℝ} (ρ : CQState X n) (τ : CQState Y m)
    (σ : SubDensityOp n) (ω : SubDensityOp m) (p : ℝ)
    (h : ∀ ρ', CQState.purifiedDistance ρ ρ' ≤ ε →
      ∃ τ', CQState.purifiedDistance τ τ' ≤ δ ∧
        ∀ k : ℝ, isFeasible ρ' σ (2 ^ (-k)) → isFeasible τ' ω (2 ^ (-(k - p)))) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy δ τ ω + ENNReal.ofReal p := by
  refine iSup_le fun ρ' => iSup_le fun hd => ?_
  obtain ⟨τ', hτ', hfeas⟩ := h ρ' hd
  exact (conditionalMinEntropy_le_add_of_isFeasible_imp ρ' τ' σ ω p hfeas).trans
    (add_le_add (conditionalMinEntropy_le_smoothMinEntropy τ τ' ω hτ') le_rfl)

/-- Extended smooth entropy is the supremum of nonnegative finite levels certified by an
exponential feasible coefficient in the ball. -/
theorem smoothMinEntropy_eq_iSup_feasibleFloor
    (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy ε ρ σ =
      ⨆ k : NNReal, ⨆ (_ : ∃ τ : CQState X n, CQState.purifiedDistance ρ τ ≤ ε ∧
        isFeasible τ σ (2 ^ (-(k : ℝ)))), (k : ENNReal) := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro k hk hlt
    obtain ⟨τ, hd, _, hτ⟩ := smoothMinEntropy_exists_approx ρ σ k hlt
    have hfloor : ENNReal.ofReal (k : ℝ) ≤ conditionalMinEntropy τ σ := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hτ.le
    exact le_iSup_of_le k (le_iSup_of_le
      ⟨τ, hd, isFeasible_of_ofReal_le_conditionalMinEntropy τ σ hk hfloor⟩ le_rfl)
  · refine iSup_le fun k => iSup_le fun h => ?_
    obtain ⟨τ, hd, hfeas⟩ := h
    simpa only [ENNReal.ofReal_coe_nnreal] using
      smoothMinEntropy_ge_of_isFeasible ρ τ σ k hd hfeas

end ENNReal


/-- For a normalized center and radius `0 ≤ ε < 1`, signed smooth min-entropy is at least the
center's signed conditional min-entropy. -/
theorem smoothMinEntropyReal_ge_conditionalMinEntropyReal {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {n : ℕ}
    [NeZero n] (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) (ρ : CQState X n)
    (hρnorm : ∑ x : X, (ρ.stateMap x).trace = 1) (σ : SubDensityOp n) :
    conditionalMinEntropyReal ρ σ ≤ smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  apply le_csSup_of_le (smoothMinEntropyReal_bddAbove ε hε1 ρ hρnorm σ)
  · exact ⟨ρ, rfl, by
      show CQState.purifiedDistance ρ ρ ≤ ε
      rw [CQState.purifiedDistance_self_zero]
      exact hε⟩
  · exact le_refl _

/-- Signed smooth min-entropy of a normalized center is monotone in the smoothing radius below
one. -/
theorem smoothMinEntropyReal_mono_eps {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ}
    [NeZero n] {ε ε' : ℝ} (hε : 0 ≤ ε) (h : ε ≤ ε') (hε'1 : ε' < 1) (ρ : CQState X n)
    (hρnorm : ∑ x : X, (ρ.stateMap x).trace = 1) (σ : SubDensityOp n) :
    smoothMinEntropyReal ε ρ σ ≤ smoothMinEntropyReal ε' ρ σ := by
  unfold smoothMinEntropyReal
  apply csSup_le_csSup (smoothMinEntropyReal_bddAbove ε' hε'1 ρ hρnorm σ)
  · exact ⟨conditionalMinEntropyReal ρ σ, ρ, rfl, by
      rw [CQState.purifiedDistance_self_zero]
      exact hε⟩
  · intro v hv
    obtain ⟨rho2, hh, hd⟩ := hv
    exact ⟨rho2, hh, le_trans hd h⟩

/-- Increasing the reference operator increases signed smooth min-entropy under feasibility,
positive target optima, and boundedness of the target smoothing set. -/
theorem smoothMinEntropyReal_mono_sigma_of_bddAbove
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X n) (σ σ' : SubDensityOp n)
    (hσσ' : ∀ v : Fin n → ℂ, (quadraticForm σ.toOp v).re ≤ (quadraticForm σ'.toOp v).re)
    (hfeas : ∀ ρ' : CQState X n, CQState.purifiedDistance ρ ρ' ≤ ε → hasFeasibleLambda ρ' σ)
    (hpos_sigma_prime : ∀ ρ' : CQState X n, CQState.purifiedDistance ρ ρ' ≤ ε →
        0 < minFeasibleLambda ρ' σ')
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ'))) :
    smoothMinEntropyReal ε ρ σ ≤ smoothMinEntropyReal ε ρ σ' := by
  unfold smoothMinEntropyReal
  apply csSup_le
  · exact ⟨conditionalMinEntropyReal ρ σ, ρ, rfl, by
      rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  · intro v hv
    obtain ⟨ρ', hv_eq, hd⟩ := hv
    apply le_csSup_of_le hbdd
    · exact ⟨ρ', rfl, hd⟩
    · rw [hv_eq]
      exact conditionalMinEntropyReal_antitone_sigma ρ' σ' σ hσσ' (hfeas ρ' hd)
        (hpos_sigma_prime ρ' hd)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
