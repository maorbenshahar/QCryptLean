import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloor

/-!
# Weighted finite-mixture entropy floors

Finite submixtures combine component-dependent feasible coefficients and nearby witnesses. Signed
real exponential rates are summed before the final `ENNReal.ofReal` conversion. A nonpositive
component floor can therefore contribute to a positive mixture floor.
-/

open Quantum.Operators
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Weighted sub-probability feasibility of a mixture (W1).**

The weighted analogue of `isFeasible_subMixture`.  If each component `comp z` of a nonnegative
sub-convex combination `ρ = ∑_z p_z · comp z` admits its **own** feasible scalar `t z ≥ 0`, then
the mixture admits the weighted sum `∑_z p_z · t z`:
`∑_z p_z · (comp z)_A(x) ≤ ∑_z p_z · t z · σ`, blockwise in the semidefinite order.

**Difference from the unweighted lemma, and why it matters.**  `isFeasible_subMixture` spends
`∑_z p_z ≤ 1` on the final step, collapsing `(∑_z p_z)·t ≤ t` and returning the *constant* `t`.
Here the conclusion is the honest weighted sum, which is what lets a low-weight component
contribute a small multiplier instead of being charged the worst component's.  Consequently no
bound `∑_z p_z ≤ 1` is needed: the lemma holds for every nonnegative weight family. -/
lemma isFeasible_subMixture_weighted {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (t : Z → ℝ)
    (ht_nonneg : ∀ z, 0 ≤ t z)
    (ht : ∀ z, isFeasible (comp z) σ (t z)) :
    isFeasible ρ σ (∑ z, p z * t z) := by
  refine ⟨Finset.sum_nonneg (fun z _ => mul_nonneg (hp_nonneg z) (ht_nonneg z)), fun x => ?_⟩
  rw [hmix x]
  have hstep : opLe (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
      (∑ z, (p z : ℂ) • (Complex.ofReal (t z) • σ.toOp)) := by
    apply Quantum.Channels.opLe_sum
    intro z
    exact opLe_smul_nonneg (hp_nonneg z) ((ht z).2 x)
  have hsum_eq : (∑ z, (p z : ℂ) • (Complex.ofReal (t z) • σ.toOp))
      = (Complex.ofReal (∑ z, p z * t z)) • σ.toOp := by
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [smul_smul, Complex.ofReal_mul]
  rw [hsum_eq] at hstep
  exact hstep

/-- **Weighted `λ` sub-additivity for a sub-probability mixture (W2).**

At a positive-definite reference the feasible-lambda optimum of a sub-convex combination is
bounded by the weighted sum of the components' optima:
`λ(∑_z p_z · comp z, σ) ≤ ∑_z p_z · λ(comp z, σ)` (for any nonnegative weights; no bound on
`∑_z p_z` is needed).

At a positive-definite reference, `λ` is `max_x ‖σ^{−1/2} ρ_x σ^{−1/2}‖_∞`.
The weighted bound can be tighter than the uniform worst-component bound when the components
have different optima. -/
theorem minFeasibleLambda_le_weighted_subMixture
    {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef) :
    minFeasibleLambda ρ σ ≤ ∑ z, p z * minFeasibleLambda (comp z) σ :=
  minFeasibleLambda_le_of_isFeasible ρ σ
    (isFeasible_subMixture_weighted p hp_nonneg comp ρ hmix σ
      (fun z => minFeasibleLambda (comp z) σ)
      (fun z => minFeasibleLambda_nonneg (comp z) σ)
      (fun z => isFeasible_minFeasibleLambda_of_posDef (comp z) σ hσ))

/-- Weighted feasible-optimum bounds give an extended conditional entropy floor, including
zero mixtures. The signed scalar comparison is completed before casting the entropy floor. -/
theorem conditionalMinEntropy_ge_of_weighted_subMixture
    {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef)
    (k : ℝ) (lam : Z → ℝ)
    (hlam : ∀ z, minFeasibleLambda (comp z) σ ≤ lam z)
    (hk : ∑ z, p z * lam z ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ := by
  apply ofReal_le_conditionalMinEntropy_of_isFeasible
  apply isFeasible_mono_t (isFeasible_subMixture_weighted p hp_nonneg comp ρ hmix σ lam
    (fun z => (minFeasibleLambda_nonneg (comp z) σ).trans (hlam z))
    (fun z => isFeasible_mono_t
      (isFeasible_minFeasibleLambda_of_posDef (comp z) σ hσ) (hlam z))) hk

/-- Component smoothing witnesses with signed exponential feasibility certificates assemble
through the weighted exponential comparison. Negative component levels can give positive mixture
floors; zero witnesses require no positive-weight or boundedness guard. -/
theorem smoothMinEntropy_subMixture_ge_weighted
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ) (kz : Z → ℝ)
    (hwitness : ∀ z, ∃ τ : CQState X n,
      CQState.purifiedDistance (comp z) τ ≤ ε ∧ isFeasible τ σ (2 ^ (-(kz z))))
    (hk : ∑ z, p z * (2 : ℝ) ^ (-(kz z)) ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  classical
  choose comp' hd ht using hwitness
  let ρ' := finMixSub p hp_nonneg hp_sum_le comp'
  have hρ'mix := finMixSub_stateMap_toOp p hp_nonneg hp_sum_le comp'
  have hpd := purifiedDistance_subMixture_le_max p hp_nonneg hp_sum_le
    comp comp' ρ ρ' hmix hρ'mix hε hd
  exact smoothMinEntropy_ge_of_isFeasible ρ ρ' σ k hpd
    (isFeasible_mono_t (isFeasible_subMixture_weighted p hp_nonneg comp' ρ' hρ'mix σ
      (fun z => (2 : ℝ) ^ (-(kz z))) (fun _ => Real.rpow_nonneg (by norm_num) _) ht) hk)

/-- A constant family of feasible smoothing floors gives the same floor for a submixture. -/
example {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hwitness : ∀ z, ∃ τ : CQState X n,
      CQState.purifiedDistance (comp z) τ ≤ ε ∧ isFeasible τ σ (2 ^ (-k))) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  refine smoothMinEntropy_subMixture_ge_weighted ε hε p hp_nonneg hp_sum_le comp ρ hmix σ
    k (fun _ => k) hwitness ?_
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (-k) := Real.rpow_nonneg (by norm_num) _
  calc ∑ z, p z * (2 : ℝ) ^ (-k)
      = (∑ z, p z) * (2 : ℝ) ^ (-k) := by rw [← Finset.sum_mul]
    _ ≤ 1 * (2 : ℝ) ^ (-k) := mul_le_mul_of_nonneg_right hp_sum_le hpow
    _ = (2 : ℝ) ^ (-k) := one_mul _


/-- A weighted bound on the component optima with sum at most `2 ^ (-k)` gives a positive-weight
mixture the signed conditional floor `k`. -/
theorem conditionalMinEntropyReal_ge_of_weighted_subMixture
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef)
    (hweight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (k : ℝ) (lam : Z → ℝ)
    (hlam : ∀ z, minFeasibleLambda (comp z) σ ≤ lam z)
    (hk : ∑ z, p z * lam z ≤ (2 : ℝ) ^ (-k)) :
    k ≤ conditionalMinEntropyReal ρ σ := by
  have hle : minFeasibleLambda ρ σ ≤ ∑ z, p z * lam z :=
    le_trans (minFeasibleLambda_le_weighted_subMixture p hp_nonneg comp ρ hmix σ hσ)
      (Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (hlam z) (hp_nonneg z)))
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k ρ σ k
    (minFeasibleLambda_pos_of_posDef_of_weight_pos ρ σ hσ hweight_pos)
    (le_trans hle hk)

/-- Strict signed smooth component floors combine through their weighted exponentials to give
the signed mixture floor `k`. -/
theorem smoothMinEntropyReal_subMixture_ge_weighted
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef)
    (hρ_weight : ε ^ 2 < ∑ x : X, (ρ.stateMap x).trace)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ)))
    (k : ℝ) (kz : Z → ℝ)
    (hfloor : ∀ z, kz z < smoothMinEntropyReal ε (comp z) σ)
    (hk : ∑ z, p z * (2 : ℝ) ^ (-(kz z)) ≤ (2 : ℝ) ^ (-k)) :
    k ≤ smoothMinEntropyReal ε ρ σ := by
  classical
  -- Step 1: per-component approximants, a plain `choose` over the finite index `Z`.
  have hex : ∀ z, ∃ ρ' : CQState X n,
      CQState.purifiedDistance (comp z) ρ' ≤ ε ∧ kz z ≤ conditionalMinEntropyReal ρ' σ :=
    fun z => smoothMinEntropyReal_exists_approx ε hε (comp z) σ (kz z) (hfloor z)
  choose comp' hd he using hex
  -- Step 2: assemble the approximant sub-mixture.
  set ρ' : CQState X n := finMixSub p hp_nonneg hp_sum_le comp' with hρ'_def
  have hρ'_mix : ∀ x : X, (ρ'.stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((comp' z).stateMap x).toOp :=
    fun x => finMixSub_stateMap_toOp p hp_nonneg hp_sum_le comp' x
  -- Step 4 (needed before step 3's consumer): the mixture stays inside the ε-ball.
  have hpd : CQState.purifiedDistance ρ ρ' ≤ ε :=
    purifiedDistance_subMixture_le_max p hp_nonneg hp_sum_le comp comp' ρ ρ'
      hmix hρ'_mix hε hd
  -- Step 5: the approximant mixture has positive weight.
  have hρ'_weight_pos : 0 < ∑ x : X, (ρ'.stateMap x).trace :=
    lt_of_lt_of_le
      (purifiedDistanceWeightFloor_pos hε ρ.weight_le_one hρ_weight)
      (CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor hε hρ_weight hpd)
  -- Step 3: each approximant's λ is below its own multiplier.
  have hlam : ∀ z, minFeasibleLambda (comp' z) σ ≤ (2 : ℝ) ^ (-(kz z)) := fun z =>
    minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le (comp' z) σ (kz z) (he z)
  -- Step 6: the weighted unsmoothed floor on the approximant mixture.
  have hfloor' : k ≤ conditionalMinEntropyReal ρ' σ :=
    conditionalMinEntropyReal_ge_of_weighted_subMixture p hp_nonneg comp' ρ' hρ'_mix
      σ hσ hρ'_weight_pos k (fun z => (2 : ℝ) ^ (-(kz z))) hlam hk
  -- Step 7: membership in the smoothed set.
  exact smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε ρ σ k ρ' hbdd hpd hfloor'

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
