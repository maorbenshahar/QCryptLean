import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ClassicalExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ClassicalCoarsening

/-!
# Feasible coefficients for reference changes and coarsening

Löwner domination transfers feasible coefficients across references. Classical coarsening compares
feasible coefficients and yields a signed conditional entropy inequality for positive-definite
references.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **(c-S1)** Feasibility transfers across a Löwner-dominated reference change with
a multiplicative penalty: if `σ ≼ g · σ'` and `t` is feasible for `(ρ, σ)`, then
`g · t` is feasible for `(ρ, σ')`. -/
lemma isFeasible_smul_ref_of_opLe
    {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ σ' : SubDensityOp d) {g : ℝ} (hg0 : 0 ≤ g)
    (hdom : opLe σ.toOp ((g : ℂ) • σ'.toOp))
    {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible ρ σ' (g * t) := by
  refine ⟨mul_nonneg hg0 ht.1, fun x => ?_⟩
  have h1 : opLe (ρ.stateMap x).toOp ((Complex.ofReal t) • σ.toOp) := ht.2 x
  have h2 : opLe ((Complex.ofReal t) • σ.toOp)
      ((Complex.ofReal t) • ((g : ℂ) • σ'.toOp)) :=
    opLe_smul_nonneg ht.1 hdom
  have hchain : opLe (ρ.stateMap x).toOp
      ((Complex.ofReal t) • ((g : ℂ) • σ'.toOp)) :=
    opLe_trans h1 h2
  have hrw : ((Complex.ofReal t) • ((g : ℂ) • σ'.toOp) : Op d) =
      (Complex.ofReal (g * t)) • σ'.toOp := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_comm]
  rwa [hrw] at hchain

/-! ## Lemma (d): smooth fixed-reference classical-coarsening DPI -/

/-- **(d1 feasibility transfer)** A feasible scalar for the coarsened CQ state is
feasible for the fine state: each fine block is dominated by its fiber-sum coarse
block (`povmCoarsen_self_opLe`), which is in turn dominated by `t · σ`. -/
lemma isFeasible_of_isFeasible_coarsen
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {d : ℕ}
    (g : X → Y) (ρ : CQState X d) (σ : SubDensityOp d) {t : ℝ}
    (ht : isFeasible (CQState.coarsen g ρ) σ t) :
    isFeasible ρ σ t := by
  refine ⟨ht.1, fun x => ?_⟩
  have hM : ∀ x : X, ((ρ.stateMap x).toOp).PosSemidef := fun x =>
    posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have hblock : opLe (ρ.stateMap x).toOp ((CQState.coarsen g ρ).stateMap (g x)).toOp := by
    rw [CQState.coarsen_stateMap_toOp]
    exact povmCoarsen_self_opLe g hM x
  exact opLe_trans hblock (ht.2 (g x))

/-- **(d1 zero-transfer)** If `0` is feasible for the fine CQ state (i.e. every fine
block is `≼ 0`, equivalently `ρ = 0`), then `0` is feasible for the coarsened state:
coarsening preserves the quantum marginal, which is `≼ 0`. -/
lemma isFeasible_zero_coarsen_of_isFeasible_zero
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {d : ℕ}
    (g : X → Y) (ρ : CQState X d) (σ : SubDensityOp d)
    (h : isFeasible ρ σ 0) :
    isFeasible (CQState.coarsen g ρ) σ 0 := by
  refine InfoTheory.SmoothMinEntropy.isFeasible_of_quantumMarginalOp_dominated _ σ (le_refl 0) ?_
  rw [CQState.coarsen_quantumMarginalOp]
  intro v
  have hrhs0 : (quadraticForm (Complex.ofReal (0 : ℝ) • σ.toOp) v).re = 0 := by
    rw [Complex.ofReal_zero, zero_smul]
    simp [quadraticForm, Matrix.zero_mulVec, dotProduct]
  rw [hrhs0]
  have hsum : (quadraticForm ρ.quantumMarginalOp v).re =
      ∑ x : X, (quadraticForm (ρ.stateMap x).toOp v).re := by
    unfold CQState.quantumMarginalOp quadraticForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [hsum]
  apply Finset.sum_nonpos
  intro x _
  have hx := h.2 x v
  rwa [hrhs0] at hx

/-- **(d1) pointwise classical-coarsening DPI.**

Finite classical coarsening cannot increase the (fixed-reference) real conditional
min-entropy: `H(coarsen g ρ | σ) ≤ H(ρ | σ)`.

Stated with `σ` positive definite, which makes both feasible sets nonempty and lets
the `minFeasibleLambda = 0` sentinel corner be discharged by the zero-transfer
lemma (a vanishing fine optimum forces a vanishing coarse optimum). -/
lemma conditionalMinEntropyReal_coarsen_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {d : ℕ} [NeZero d]
    (g : X → Y) (ρ : CQState X d) (σ : SubDensityOp d) (hσ : σ.toOp.PosDef) :
    conditionalMinEntropyReal (CQState.coarsen g ρ) σ ≤ conditionalMinEntropyReal ρ σ := by
  have hfeas_coarse : hasFeasibleLambda (CQState.coarsen g ρ) σ :=
    hasFeasibleLambda_of_posDef _ σ hσ
  -- `minFeasibleLambda ρ σ ≤ minFeasibleLambda (coarse) σ` from the subset of feasible sets.
  have hle : minFeasibleLambda ρ σ ≤ minFeasibleLambda (CQState.coarsen g ρ) σ := by
    unfold minFeasibleLambda
    obtain ⟨t, ht⟩ := hfeas_coarse
    exact csInf_le_csInf (minFeasibleLambda_bddBelow ρ σ) ⟨t, ht⟩
      (fun s hs => isFeasible_of_isFeasible_coarsen g ρ σ hs)
  by_cases hpos : 0 < minFeasibleLambda ρ σ
  · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog_le : Real.log (minFeasibleLambda ρ σ) ≤
        Real.log (minFeasibleLambda (CQState.coarsen g ρ) σ) :=
      Real.log_le_log hpos hle
    unfold conditionalMinEntropyReal
    exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le
  · push Not at hpos
    have hfzero : minFeasibleLambda ρ σ = 0 :=
      le_antisymm hpos (minFeasibleLambda_nonneg ρ σ)
    have h0fine : isFeasible ρ σ 0 := by
      have h := isFeasible_minFeasibleLambda_of_posDef ρ σ hσ
      rwa [hfzero] at h
    have h0coarse : isFeasible (CQState.coarsen g ρ) σ 0 :=
      isFeasible_zero_coarsen_of_isFeasible_zero g ρ σ h0fine
    have hczero : minFeasibleLambda (CQState.coarsen g ρ) σ = 0 :=
      le_antisymm (minFeasibleLambda_le_of_isFeasible _ σ h0coarse)
        (minFeasibleLambda_nonneg _ σ)
    unfold conditionalMinEntropyReal
    rw [hfzero, hczero]


/-- If the reference dominates the marginal and is dominated by `g` times the target reference,
transferring signed smooth min-entropy costs at most `log g / log 2`. -/
theorem smoothMinEntropyReal_ge_of_smul_opLe_of_marginalDominated
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (g : ℝ) (hg : 1 ≤ g)
    (hmarg : opLe ρ.quantumMarginalOp σ.toOp)
    (hdom : opLe σ.toOp ((g : ℂ) • σ'.toOp))
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ'))) :
    smoothMinEntropyReal ε ρ σ - Real.log g / Real.log 2 ≤ smoothMinEntropyReal ε ρ σ' := by
  have hg0 : 0 ≤ g := le_trans zero_le_one hg
  have hlog_g_nonneg : 0 ≤ Real.log g := Real.log_nonneg hg
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfeas_center_σ : isFeasible ρ σ 1 := by
    refine InfoTheory.SmoothMinEntropy.isFeasible_of_quantumMarginalOp_dominated ρ σ (by norm_num)
        ?_
    rwa [Complex.ofReal_one, one_smul]
  have hfeas_center_σ' : isFeasible ρ σ' g := by
    have h := isFeasible_smul_ref_of_opLe ρ σ σ' hg0 hdom hfeas_center_σ
    simpa [mul_one] using h
  have hlamσ'_le_g : minFeasibleLambda ρ σ' ≤ g :=
    minFeasibleLambda_le_of_isFeasible ρ σ' hfeas_center_σ'
  have hcenter : -Real.log g / Real.log 2 ≤ conditionalMinEntropyReal ρ σ' := by
    unfold conditionalMinEntropyReal
    have hlamσ'_nn : 0 ≤ minFeasibleLambda ρ σ' := minFeasibleLambda_nonneg ρ σ'
    rcases eq_or_lt_of_le hlamσ'_nn with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, zero_div]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg hlog_g_nonneg) hlog2_pos.le
    · have hlog_le : Real.log (minFeasibleLambda ρ σ') ≤ Real.log g :=
        Real.log_le_log hpos hlamσ'_le_g
      have hnum : -Real.log g ≤ -Real.log (minFeasibleLambda ρ σ') := by linarith
      exact div_le_div_of_nonneg_right hnum hlog2_pos.le
  apply csSup_sub_le_csSup_of_forall_exists_sub_le _ _ _
    (smoothedSetReal_nonempty hε_nn ρ σ) hbdd
  intro a ha
  obtain ⟨ρ', rfl, hd⟩ := ha
  by_cases hfeasA : hasFeasibleLambda ρ' σ
  · -- Feasible witness: use the scaling host.
    refine ⟨conditionalMinEntropyReal ρ' σ', ⟨ρ', rfl, hd⟩, ?_⟩
    exact conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling_sameState
      ρ' σ σ' hg hfeasA
      (fun {t} ht => isFeasible_smul_ref_of_opLe ρ' σ σ' hg0 hdom ht)
  · -- Junk witness: sentinel `0`, covered by the center witness.
    refine ⟨conditionalMinEntropyReal ρ σ',
      ⟨ρ, rfl, by rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩, ?_⟩
    have ha0 : conditionalMinEntropyReal ρ' σ = 0 := by
      unfold conditionalMinEntropyReal
      rw [minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda ρ' σ hfeasA,
        Real.log_zero, neg_zero, zero_div]
    rw [ha0, zero_sub, ← neg_div]
    exact hcenter

/-- Lifting every coarsened smoothing candidate to the original ball bounds the coarsened signed
smooth min-entropy by the original one. -/
theorem smoothMinEntropyReal_coarsen_le_of_exists_lift
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {d : ℕ} [NeZero d]
    (g : X → Y) (ρ : CQState X d) (σ : SubDensityOp d) (hσ : σ.toOp.PosDef)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ)))
    (hlift : ∀ τ : CQState Y d, CQState.purifiedDistance (CQState.coarsen g ρ) τ ≤ ε →
      ∃ τ' : CQState X d, CQState.purifiedDistance ρ τ' ≤ ε ∧ CQState.coarsen g τ' = τ) :
    smoothMinEntropyReal ε (CQState.coarsen g ρ) σ ≤ smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  apply csSup_le (smoothedSetReal_nonempty hε_nn (CQState.coarsen g ρ) σ)
  intro a ha
  obtain ⟨τ, rfl, hτ⟩ := ha
  obtain ⟨τ', hτ'_dist, hτ'_coarsen⟩ := hlift τ hτ
  rw [← hτ'_coarsen]
  refine le_trans (conditionalMinEntropyReal_coarsen_le g τ' σ hσ) ?_
  exact le_csSup hbdd ⟨τ', rfl, hτ'_dist⟩

end InfoTheory.SmoothMinEntropy

end
