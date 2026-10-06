import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.GoodBranch

/-!
# Weighted integral entropy floors

Component-dependent feasible coefficients integrate to a mixture coefficient. Signed exponential
rates are combined before taking the extended entropy floor; no clipping of individual rates
enters the coefficient calculation.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- **Weighted feasibility integration.**  The λ-integral replacement for the accept-split's
uniform floor `isFeasible_of_ae_minFeasibleLambda_le_of_integral_subprob`: instead of charging
every component the same scalar `B` (which forces bad components to be discarded before the
infimum is finite), each component `f τ` is charged its own multiplier `lam τ`, and the Bochner
mixture is feasible at the integral `∫ lam`.

`Integrable lam ν` is load-bearing: without it `∫ lam` is the junk value `0`
(`MeasureTheory.integral_undef`) and the statement is false. -/
theorem isFeasible_integral_weight_of_ae_minFeasibleLambda_le
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE)
    (f : α → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    (lam : α → ℝ)
    (hlam_int : MeasureTheory.Integrable lam ν)
    (hlam_nn : ∀ τ, 0 ≤ lam τ)
    (h_ae : ∀ᵐ τ ∂ν, minFeasibleLambda (f τ) σ_ref ≤ lam τ) :
    isFeasible ρ_mix σ_ref (∫ τ : α, lam τ ∂ν) := by
  classical
  refine ⟨integral_nonneg hlam_nn, ?_⟩
  intro x v
  have hσ_qf_nonneg : 0 ≤ (quadraticForm σ_ref.toOp v).re := σ_ref.pos_semidef v
  rw [hf_qf_lin x v]
  have h_ae_le :
      (fun τ : α => (quadraticForm ((f τ).stateMap x).toOp v).re) ≤ᵐ[ν]
        fun τ : α => lam τ * (quadraticForm σ_ref.toOp v).re := by
    filter_upwards [h_ae] with τ hτ
    have hτ_feas := isFeasible_minFeasibleLambda_of_posDef (f τ) σ_ref hσ_ref
    have hτ_dom := hτ_feas.2 x v
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hτ_dom
    exact hτ_dom.trans (mul_le_mul_of_nonneg_right hτ hσ_qf_nonneg)
  have h_integral_le :
      ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν
        ≤ ∫ τ : α, lam τ * (quadraticForm σ_ref.toOp v).re ∂ν := by
    refine integral_mono_of_nonneg ?_ (hlam_int.mul_const _) h_ae_le
    exact ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v
  calc
    ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν
        ≤ ∫ τ : α, lam τ * (quadraticForm σ_ref.toOp v).re ∂ν := h_integral_le
    _ = (∫ τ : α, lam τ ∂ν) * (quadraticForm σ_ref.toOp v).re := by
        rw [integral_mul_const]
    _ = (quadraticForm (Complex.ofReal (∫ τ : α, lam τ ∂ν) • σ_ref.toOp) v).re := by
        rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]

/-- **The weighted mixture floor in λ form.**  Corollary of
`isFeasible_integral_weight_of_ae_minFeasibleLambda_le`: the Bochner mixture's feasible optimum is
bounded by the integral of the component multipliers.

This is the weighted replacement for `minFeasibleLambda_le_of_ae_le_of_integral_subprob` (uniform
scalar `B`) and for `minFeasibleLambda_le_essSup_of_integral` (unweighted essential supremum):
a component with a bad rate is charged its own large `lam τ` weighted by its measure, instead of
being discarded into a bad branch and paid for in purified distance. -/
theorem minFeasibleLambda_le_integral_weight_of_ae_le
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE)
    (f : α → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    (lam : α → ℝ)
    (hlam_int : MeasureTheory.Integrable lam ν)
    (hlam_nn : ∀ τ, 0 ≤ lam τ)
    (h_ae : ∀ᵐ τ ∂ν, minFeasibleLambda (f τ) σ_ref ≤ lam τ) :
    minFeasibleLambda ρ_mix σ_ref ≤ ∫ τ : α, lam τ ∂ν :=
  minFeasibleLambda_le_of_isFeasible ρ_mix σ_ref
    (isFeasible_integral_weight_of_ae_minFeasibleLambda_le
      ρ_mix f σ_ref hσ_ref hf_qf_lin lam hlam_int hlam_nn h_ae)

/-- **Non-vacuity check: the weighted floor recovers its own unweighted incumbent.**

Instantiating `isFeasible_integral_weight_of_ae_minFeasibleLambda_le` at the constant multiplier
`lam ≡ B` over a subprobability measure reproduces the conclusion of
`isFeasible_of_ae_minFeasibleLambda_le_of_integral_subprob` under its own hypotheses, since
`∫ B ∂ν = B * (ν univ).toReal ≤ B`.  A weighted lemma that could not recover the uniform bound it
replaces would be suspect.  (The statement below is the incumbent's, hypothesis for hypothesis.) -/
example
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α} [IsFiniteMeasure ν]
    {dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE)
    (f : α → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hν_le_one : ν Set.univ ≤ 1)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (h_ae : ∀ᵐ τ ∂ν, minFeasibleLambda (f τ) σ_ref ≤ B) :
    isFeasible ρ_mix σ_ref B := by
  have hmass_le_one : (ν Set.univ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hν_le_one
  have hweighted : isFeasible ρ_mix σ_ref (∫ _τ : α, B ∂ν) :=
    isFeasible_integral_weight_of_ae_minFeasibleLambda_le ρ_mix f σ_ref hσ_ref hf_qf_lin
      (fun _ => B) (integrable_const B) (fun _ => hB_nonneg) h_ae
  have hconst : ∫ _τ : α, B ∂ν = B * (ν Set.univ).toReal := by
    rw [integral_const]
    simp [MeasureTheory.Measure.real]
    ring
  rw [hconst] at hweighted
  exact isFeasible_mono_t hweighted (by nlinarith [hmass_le_one, hB_nonneg])

/-- **Weighted good-branch domination.**  The λ-integral analogue of
`goodBranchBlockOp_opLe_of_ae_bound`: almost-everywhere domination of each retained component by
its *own* multiple `lam τ • σ_ref` integrates to domination of the restricted good-branch block by
`(∫_{good} lam) • σ_ref`.

The incumbent charges every retained component the same `t`, which is precisely the uniform floor
that the BB84 accept split exists to make finite.  Here the components are charged individually,
so nothing needs to be discarded.

Unlike the incumbent, no sign condition on the multiplier is needed: the dominating integral is
taken over the same restricted measure as the dominated one, so the incumbent's step comparing
`∫_{good} c` with `∫_{univ} c` (which needed `0 ≤ c`) disappears.

`IntegrableOn lam goodSet μ.measure` is load-bearing: without it the right-hand side is the junk
value `0` (`MeasureTheory.integral_undef`). -/
lemma goodBranchBlockOp_opLe_integral_weight_of_ae_bound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE)
    (lam : DensityOp d → ℝ)
    (hlam_int : MeasureTheory.IntegrableOn lam goodSet μ.measure)
    (h_bound :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        opLe ((f τ).stateMap x).toOp (Complex.ofReal (lam τ) • σ_ref.toOp)) :
    opLe (goodBranchBlockOp μ f goodSet x)
      (Complex.ofReal (∫ τ in goodSet, lam τ ∂μ.measure) • σ_ref.toOp) := by
  haveI : IsProbabilityMeasure μ.measure := μ.isProbability
  intro v
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int.restrict]
  rw [Quantum.Operators.quadraticForm_re_setIntegral goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int.restrict v]
  have hσ_qf_nonneg : 0 ≤ (quadraticForm σ_ref.toOp v).re := σ_ref.pos_semidef v
  have h_nonneg :
      0 ≤ᵐ[μ.measure.restrict goodSet]
        fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re :=
    ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v
  have h_ae_le :
      (fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re)
        ≤ᵐ[μ.measure.restrict goodSet]
          fun τ : DensityOp d => lam τ * (quadraticForm σ_ref.toOp v).re := by
    filter_upwards [h_bound] with τ hτ
    have hτ_dom := hτ v
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hτ_dom
    exact hτ_dom
  have h_integral_le :
      ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ τ in goodSet, lam τ * (quadraticForm σ_ref.toOp v).re ∂μ.measure :=
    MeasureTheory.integral_mono_of_nonneg h_nonneg (hlam_int.mul_const _) h_ae_le
  calc
    ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ τ in goodSet, lam τ * (quadraticForm σ_ref.toOp v).re ∂μ.measure :=
          h_integral_le
    _ = (∫ τ in goodSet, lam τ ∂μ.measure) * (quadraticForm σ_ref.toOp v).re := by
        rw [integral_mul_const]
    _ = (quadraticForm
          (Complex.ofReal (∫ τ in goodSet, lam τ ∂μ.measure) • σ_ref.toOp) v).re := by
        rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]

/-- **The weighted good-branch floor in λ form.**  The good-branch CQ state built from the
retained components has feasible optimum at most the good-branch λ-integral.

This is the weighted replacement for the uniform-`k` step inside
`conditionalMinEntropy_ge_of_goodBranch_ae`: there, a single `k` must hold for a.e. retained
`τ`, and every component that fails it must be moved into the bad branch and paid for in purified
distance (the `√`).  Here each component is charged its own `lam τ`. -/
theorem minFeasibleLambda_le_integral_weight_of_goodBranch_ae
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) (hσ_ref : σ_ref.toOp.PosDef)
    (lam : DensityOp d → ℝ)
    (hlam_int : MeasureTheory.IntegrableOn lam goodSet μ.measure)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        minFeasibleLambda (f τ) σ_ref ≤ lam τ) :
    minFeasibleLambda ρ_good σ_ref ≤ ∫ τ in goodSet, lam τ ∂μ.measure := by
  have hlam_nn : 0 ≤ ∫ τ in goodSet, lam τ ∂μ.measure :=
    integral_nonneg_of_ae (hgood_ae.mono fun τ hτ =>
      (minFeasibleLambda_nonneg (f τ) σ_ref).trans hτ)
  refine minFeasibleLambda_le_of_isFeasible ρ_good σ_ref ⟨hlam_nn, ?_⟩
  intro x
  rw [hρ_good_eq x]
  refine goodBranchBlockOp_opLe_integral_weight_of_ae_bound
    μ f goodSet x (h_int x) σ_ref lam hlam_int ?_
  filter_upwards [hgood_ae] with τ hτ
  intro v
  have hτ_feas := isFeasible_minFeasibleLambda_of_posDef (f τ) σ_ref hσ_ref
  have hτ_dom := hτ_feas.2 x v
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hτ_dom
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact hτ_dom.trans (mul_le_mul_of_nonneg_right hτ (σ_ref.pos_semidef v))

/-- An integrated scalar bound on the retained branch certifies an extended entropy floor.
The signed weighted comparison precedes the cast, and zero retained mass is admitted. -/
theorem conditionalMinEntropy_ge_of_goodBranch_ae_integral_weight
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE) (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) (hσ_ref : σ_ref.toOp.PosDef)
    (lam : DensityOp d → ℝ)
    (hlam_int : MeasureTheory.IntegrableOn lam goodSet μ.measure)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hgood_ae : ∀ᵐ τ ∂μ.measure.restrict goodSet,
      minFeasibleLambda (f τ) σ_ref ≤ lam τ)
    (k : ℝ) (hk : ∫ τ in goodSet, lam τ ∂μ.measure ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ_good σ_ref := by
  apply ofReal_le_conditionalMinEntropy_of_isFeasible
  apply isFeasible_mono_t (t := ∫ τ in goodSet, lam τ ∂μ.measure) _ hk
  refine ⟨integral_nonneg_of_ae ?_, fun x => ?_⟩
  · exact hgood_ae.mono fun τ hτ => (minFeasibleLambda_nonneg (f τ) σ_ref).trans hτ
  · rw [hρ_good_eq x]
    apply goodBranchBlockOp_opLe_integral_weight_of_ae_bound
      μ f goodSet x (h_int x) σ_ref lam hlam_int
    exact hgood_ae.mono fun τ hτ =>
      (isFeasible_mono_t (isFeasible_minFeasibleLambda_of_posDef (f τ) σ_ref hσ_ref) hτ).2 x


/-- An integrable bound on the component optima with integral at most `2 ^ (-k)` gives a
positive-weight good branch the signed conditional floor `k`. -/
theorem conditionalMinEntropyReal_ge_of_goodBranch_ae_integral_weight
    {d dE : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) (hσ_ref : σ_ref.toOp.PosDef)
    (lam : DensityOp d → ℝ)
    (hlam_int : MeasureTheory.IntegrableOn lam goodSet μ.measure)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        minFeasibleLambda (f τ) σ_ref ≤ lam τ)
    (k : ℝ)
    (hk : ∫ τ in goodSet, lam τ ∂μ.measure ≤ (2 : ℝ) ^ (-k)) :
    k ≤ conditionalMinEntropyReal ρ_good σ_ref := by
  have hlam_le : minFeasibleLambda ρ_good σ_ref ≤ (2 : ℝ) ^ (-k) :=
    (minFeasibleLambda_le_integral_weight_of_goodBranch_ae
      μ f goodSet h_int σ_ref hσ_ref lam hlam_int ρ_good hρ_good_eq hgood_ae).trans hk
  have hpos : 0 < minFeasibleLambda ρ_good σ_ref :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos ρ_good σ_ref hσ_ref hweight_pos
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
    ρ_good σ_ref k hpos hlam_le

end InfoTheory.SmoothMinEntropy

end
