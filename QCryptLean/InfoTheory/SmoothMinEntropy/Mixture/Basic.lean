import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.DeFinetti.Measure
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.EssSup

/-!
# Feasible coefficients of subprobability mixtures

Pointwise or almost-everywhere domination integrates to a feasible coefficient for a CQ mixture.
The associated conditional entropy floor is extended-valued and includes zero mixtures.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- An almost-everywhere upper bound for a pointwise nonnegative real function
over a nonzero measure is itself nonnegative. -/
lemma nonneg_of_ae_le_const_of_forall_nonneg
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (hμ_univ_ne_zero : μ Set.univ ≠ 0)
    {f : α → ℝ} {b : ℝ}
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (h_ae : ∀ᵐ a ∂μ, f a ≤ b) :
    0 ≤ b := by
  by_contra hb_not
  have hb_lt : b < 0 := lt_of_not_ge hb_not
  have hfalse : ∀ᵐ a ∂μ, False := h_ae.mono fun a hle =>
    (not_le_of_gt hb_lt) ((hf_nonneg a).trans hle)
  have hzero_univ : μ Set.univ = 0 := by
    simpa using (ae_iff.mp hfalse)
  exact hμ_univ_ne_zero hzero_univ

/-- If component feasible optima are a.e. bounded by `B`, then the
subprobability Bochner mixture is feasible at `B`. -/
lemma isFeasible_of_ae_minFeasibleLambda_le_of_integral_subprob
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
  classical
  have hmass_le_one : (ν Set.univ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hν_le_one
  refine ⟨hB_nonneg, ?_⟩
  intro x v
  have hσ_qf_nonneg : 0 ≤ (quadraticForm σ_ref.toOp v).re := σ_ref.pos_semidef v
  rw [hf_qf_lin x v]
  have h_ae_le :
      (fun τ : α =>
          (quadraticForm ((f τ).stateMap x).toOp v).re) ≤ᵐ[ν]
        fun _ : α => B * (quadraticForm σ_ref.toOp v).re := by
    filter_upwards [h_ae] with τ hτ
    have hτ_feas := isFeasible_minFeasibleLambda_of_posDef (f τ) σ_ref hσ_ref
    have hτ_dom := hτ_feas.2 x v
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hτ_dom
    calc (quadraticForm ((f τ).stateMap x).toOp v).re
        ≤ minFeasibleLambda (f τ) σ_ref * (quadraticForm σ_ref.toOp v).re :=
          hτ_dom
      _ ≤ B * (quadraticForm σ_ref.toOp v).re :=
          mul_le_mul_of_nonneg_right hτ hσ_qf_nonneg
  have h_integral_le :
      ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν
        ≤ ∫ _τ : α, B * (quadraticForm σ_ref.toOp v).re ∂ν := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) h_ae_le
    exact ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v
  calc
    ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν
        ≤ ∫ _τ : α, B * (quadraticForm σ_ref.toOp v).re ∂ν := h_integral_le
    _ = B * (quadraticForm σ_ref.toOp v).re * (ν Set.univ).toReal := by
        rw [integral_const]
        simp [MeasureTheory.Measure.real]
        ring
    _ ≤ B * (quadraticForm σ_ref.toOp v).re := by
        have hconst_nonneg : 0 ≤ B * (quadraticForm σ_ref.toOp v).re :=
          mul_nonneg hB_nonneg hσ_qf_nonneg
        calc
          B * (quadraticForm σ_ref.toOp v).re * (ν Set.univ).toReal
              ≤ B * (quadraticForm σ_ref.toOp v).re * 1 :=
                mul_le_mul_of_nonneg_left hmass_le_one hconst_nonneg
          _ = B * (quadraticForm σ_ref.toOp v).re := by ring
    _ = (quadraticForm (Complex.ofReal B • σ_ref.toOp) v).re := by
        rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]

/-- If a CQ state `ρ_mix` is obtained blockwise as the Bochner integral of CQ
states `f τ`, then its feasible-lambda optimum is bounded by the essential
supremum of the component optima.

The linearity hypothesis is stated on conditioned quantum-block quadratic forms.
This is the exact form needed by the SDP domination argument.  Entrywise
Bochner-integral decompositions can be used to discharge it once the relevant
measurability/integrability side conditions are available. -/
theorem minFeasibleLambda_le_essSup_of_integral
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : DensityOp d,
          (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure) :
    minFeasibleLambda ρ_mix σ_ref ≤
      essSup (fun τ : DensityOp d => minFeasibleLambda (f τ) σ_ref) μ.measure := by
  classical
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  let lam : DensityOp d → ℝ := fun τ => minFeasibleLambda (f τ) σ_ref
  apply le_csInf
  · obtain ⟨C, _, hC_feas⟩ :=
      exists_uniform_isFeasible_of_posDef (X := X) σ_ref hσ_ref
    refine ⟨C, ?_⟩
    change ∀ᶠ n in
      Filter.map (fun τ => minFeasibleLambda (f τ) σ_ref) (ae μ.measure), n ≤ C
    rw [Filter.eventually_map]
    exact ae_of_all _ fun τ =>
      csInf_le (minFeasibleLambda_bddBelow (f τ) σ_ref) (hC_feas (f τ))
  · intro b hb
    have hb_ae : ∀ᵐ τ ∂μ.measure, lam τ ≤ b := by
      simpa [lam, Filter.eventually_map] using hb
    have hμ_univ : μ.measure Set.univ = 1 := μ.isProbability.measure_univ
    have hb_nonneg : 0 ≤ b := by
      refine nonneg_of_ae_le_const_of_forall_nonneg (μ := μ.measure) ?_
        (fun τ => minFeasibleLambda_nonneg (f τ) σ_ref) ?_
      · rw [hμ_univ]
        norm_num
      · simpa [lam] using hb_ae
    have hμ_le_one : μ.measure Set.univ ≤ 1 := by
      rw [hμ_univ]
    have hfeas_mix : isFeasible ρ_mix σ_ref b :=
      isFeasible_of_ae_minFeasibleLambda_le_of_integral_subprob
        ρ_mix f σ_ref hσ_ref hμ_le_one hf_qf_lin hb_nonneg
        (by simpa [lam] using hb_ae)
    exact csInf_le (minFeasibleLambda_bddBelow ρ_mix σ_ref) hfeas_mix

/-- Subprobability version of the feasible-lambda mixture bound with a concrete
almost-everywhere scalar upper bound.  If the mixture blocks are Bochner
integrals of component blocks over a finite measure of total mass at most one,
and the component feasible optima are a.e. bounded by a nonnegative scalar `B`,
then the mixture optimum is also bounded by `B`. -/
theorem minFeasibleLambda_le_of_ae_le_of_integral_subprob
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
    minFeasibleLambda ρ_mix σ_ref ≤ B := by
  exact csInf_le (minFeasibleLambda_bddBelow ρ_mix σ_ref)
    (isFeasible_of_ae_minFeasibleLambda_le_of_integral_subprob
      ρ_mix f σ_ref hσ_ref hν_le_one hf_qf_lin hB_nonneg h_ae)

/-- Subprobability/restricted-measure version of
`minFeasibleLambda_le_essSup_of_integral`. -/
theorem minFeasibleLambda_le_essSup_of_integral_subprob
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α} [IsFiniteMeasure ν]
    {dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE)
    (f : α → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hν_univ_ne_zero : ν Set.univ ≠ 0)
    (hν_le_one : ν Set.univ ≤ 1)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν) :
    minFeasibleLambda ρ_mix σ_ref ≤
      essSup (fun τ : α => minFeasibleLambda (f τ) σ_ref) ν := by
  classical
  let lam : α → ℝ := fun τ => minFeasibleLambda (f τ) σ_ref
  apply le_csInf
  · obtain ⟨C, _, hC_feas⟩ :=
      exists_uniform_isFeasible_of_posDef (X := X) σ_ref hσ_ref
    refine ⟨C, ?_⟩
    change ∀ᶠ n in
      Filter.map (fun τ => minFeasibleLambda (f τ) σ_ref) (ae ν), n ≤ C
    rw [Filter.eventually_map]
    exact ae_of_all _ fun τ =>
      csInf_le (minFeasibleLambda_bddBelow (f τ) σ_ref) (hC_feas (f τ))
  · intro B hB
    have hB_ae : ∀ᵐ τ ∂ν, lam τ ≤ B := by
      simpa [lam, Filter.eventually_map] using hB
    have hB_nonneg : 0 ≤ B := by
      refine nonneg_of_ae_le_const_of_forall_nonneg (μ := ν) hν_univ_ne_zero
        (fun τ => minFeasibleLambda_nonneg (f τ) σ_ref) ?_
      simpa [lam] using hB_ae
    exact minFeasibleLambda_le_of_ae_le_of_integral_subprob
      ρ_mix f σ_ref hσ_ref hν_le_one hf_qf_lin hB_nonneg (by simpa [lam] using hB_ae)

/-- Almost-everywhere feasible coefficients pass to a subprobability integral, including
zero measures and singular references. The integral identity is stated on quadratic forms. -/
lemma isFeasible_of_ae_isFeasible_of_integral_subprob
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {dE : ℕ} {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE) (f : α → CQState X dE) (σ_ref : SubDensityOp dE)
    (hν_le_one : ν Set.univ ≤ 1)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (h_ae : ∀ᵐ τ ∂ν, isFeasible (f τ) σ_ref B) :
    isFeasible ρ_mix σ_ref B := by
  let : IsFiniteMeasure ν := ⟨hν_le_one.trans_lt ENNReal.one_lt_top⟩
  have hmass : (ν Set.univ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hν_le_one
  refine ⟨hB_nonneg, fun x v => ?_⟩
  rw [hf_qf_lin x v]
  have hbound : (fun τ : α => (quadraticForm ((f τ).stateMap x).toOp v).re) ≤ᵐ[ν]
      fun _ => B * (quadraticForm σ_ref.toOp v).re := by
    filter_upwards [h_ae] with τ hτ
    simpa only [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hτ.2 x v
  calc
    ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν
        ≤ ∫ _τ : α, B * (quadraticForm σ_ref.toOp v).re ∂ν :=
      integral_mono_of_nonneg (ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v)
        (integrable_const _) hbound
    _ = (ν Set.univ).toReal * (B * (quadraticForm σ_ref.toOp v).re) := by
      simp only [integral_const, Measure.real, smul_eq_mul]
    _ ≤ B * (quadraticForm σ_ref.toOp v).re :=
      mul_le_of_le_one_left (mul_nonneg hB_nonneg (σ_ref.pos_semidef v)) hmass
    _ = (quadraticForm (Complex.ofReal B • σ_ref.toOp) v).re := by
      rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]

/-- Almost-everywhere extended conditional entropy floors pass to a subprobability integral.
Zero total mass gives infinite entropy and needs no separate positive-weight hypothesis. -/
theorem conditionalMinEntropy_ge_of_ae_ge_of_integral_subprob
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {dE : ℕ} {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE) (f : α → CQState X dE) (σ_ref : SubDensityOp dE)
    (hν_le_one : ν Set.univ ≤ 1)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    {k : ℝ} (hk_ae : ∀ᵐ τ ∂ν, ENNReal.ofReal k ≤ conditionalMinEntropy (f τ) σ_ref) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ_mix σ_ref := by
  by_cases hk : k ≤ 0
  · simp only [ENNReal.ofReal_of_nonpos hk, zero_le]
  · exact ofReal_le_conditionalMinEntropy_of_isFeasible ρ_mix σ_ref k
      (isFeasible_of_ae_isFeasible_of_integral_subprob ρ_mix f σ_ref hν_le_one hf_qf_lin
        (Real.rpow_nonneg (by norm_num) _) (hk_ae.mono fun τ hτ =>
          isFeasible_of_ofReal_le_conditionalMinEntropy (f τ) σ_ref (lt_of_not_ge hk) hτ))


/-- An integral over a subprobability measure inherits an almost-everywhere signed conditional
entropy floor against a positive-definite reference when its weight is positive. -/
theorem conditionalMinEntropyReal_ge_of_ae_ge_of_integral_subprob
    {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α} [IsFiniteMeasure ν]
    {dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (ρ_mix : CQState X dE)
    (f : α → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hν_le_one : ν Set.univ ≤ 1)
    (hρ_weight_pos : 0 < ∑ x : X, (ρ_mix.stateMap x).trace)
    (hf_qf_lin : ∀ (x : X) (v : Fin dE → ℂ),
      (quadraticForm (ρ_mix.stateMap x).toOp v).re =
        ∫ τ : α, (quadraticForm ((f τ).stateMap x).toOp v).re ∂ν)
    {k : ℝ}
    (hk_ae : ∀ᵐ τ ∂ν, k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ conditionalMinEntropyReal ρ_mix σ_ref := by
  classical
  have hlam_ae :
      ∀ᵐ τ ∂ν, minFeasibleLambda (f τ) σ_ref ≤ (2 : ℝ) ^ (-k) :=
    hk_ae.mono fun τ hτ =>
      minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le (f τ) σ_ref k hτ
  have hlam_mix_le :
      minFeasibleLambda ρ_mix σ_ref ≤ (2 : ℝ) ^ (-k) :=
    minFeasibleLambda_le_of_ae_le_of_integral_subprob
      ρ_mix f σ_ref hσ_ref hν_le_one hf_qf_lin
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hlam_ae
  have hlam_mix_pos :
      0 < minFeasibleLambda ρ_mix σ_ref :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos
      ρ_mix σ_ref hσ_ref hρ_weight_pos
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
    ρ_mix σ_ref k hlam_mix_pos hlam_mix_le

end InfoTheory.SmoothMinEntropy

end
