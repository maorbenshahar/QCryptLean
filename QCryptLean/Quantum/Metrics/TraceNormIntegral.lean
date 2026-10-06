import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import Mathlib.Analysis.Convex.Integral

/-!
# Trace-Norm Bounds for Bochner Integrals — continuity and Jensen inequalities

This file proves Jensen-type inequalities comparing the trace norm of a
Bochner integral with the integral or average of the pointwise trace norms.
It first treats probability and finite measures, then extends the bound to
arbitrary measures by monotone finite-measure truncations.

## Main definitions
- None: this file is theorem-only infrastructure for trace-norm integration bounds

## Main statements
- `traceNorm_continuous`: continuity of the trace norm on finite-dimensional operator spaces
- `traceNorm_integral_le_integral_traceNorm_of_isProbability`: Jensen bound for probability measures
- `traceNorm_average_le_average_traceNorm`: Jensen bound for finite-measure averages
- `traceNorm_integral_le_integral_traceNorm_of_isFiniteMeasure`: Jensen bound for finite measures
- `traceNorm_integral_le_integral_traceNorm`: Jensen bound for arbitrary measures
-/

open Quantum.Operators Quantum.Channels MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace Quantum.Metrics

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- The trace norm is nonnegative. -/
lemma traceNorm_nonneg {n : ℕ} [NeZero n] (A : Op n) :
    0 ≤ traceNorm A := by
  unfold traceNorm
  exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _

private lemma traceNorm_le_sqrt_natCast_mul_norm {n : ℕ} [NeZero n] (A : Op n) :
    traceNorm A ≤ Real.sqrt n * ‖A‖ := by
  calc
    traceNorm A ≤ Real.sqrt n * Real.sqrt ((A† * A).trace.re) :=
      traceNorm_le_sqrt_dim_mul_sqrt_frobenius A
    _ = Real.sqrt n * Real.sqrt (∑ i, ∑ j, ‖A j i‖ ^ 2) := by
      rw [Quantum.Channels.trace_conjTranspose_mul_self_re]
    _ = Real.sqrt n * Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
      congr 1
      rw [Finset.sum_comm]
    _ = Real.sqrt n * Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
      congr 1
      simp
    _ = Real.sqrt n * ‖A‖ := by
      rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]

private noncomputable def traceNormSeminorm (n : ℕ) [NeZero n] : Seminorm ℂ (Op n) :=
  Seminorm.ofSMulLE traceNorm (Quantum.Channels.traceNorm_zero (n := n))
    traceNorm_add_le fun c A => by
      rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]

/-- The trace norm is continuous on finite-dimensional operator spaces. -/
lemma traceNorm_continuous {n : ℕ} [NeZero n] :
    Continuous (traceNorm : Op n → ℝ) := by
  let q : Seminorm ℂ (Op n) := NNReal.sqrt n • normSeminorm ℂ (Op n)
  have hp_le : traceNormSeminorm n ≤ q := by
    intro A
    change traceNorm A ≤ (NNReal.sqrt n : ℝ) * ‖A‖
    simpa using traceNorm_le_sqrt_natCast_mul_norm A
  have hq_cont : Continuous q := by
    simpa [q, Seminorm.coe_smul, coe_normSeminorm] using
      (continuous_const.mul continuous_norm)
  simpa [traceNormSeminorm] using
    (Seminorm.continuous_of_le hq_cont hp_le : Continuous (traceNormSeminorm n))

private lemma integrable_traceNorm_comp
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    {n : ℕ} [NeZero n] {f : α → Op n}
    (hf : Integrable f μ) :
    Integrable (fun x => traceNorm (f x)) μ := by
  refine Integrable.mono' ((hf.norm).const_mul (Real.sqrt n))
    ((traceNorm_continuous (n := n)).comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  filter_upwards with x
  have hle := traceNorm_le_sqrt_natCast_mul_norm (f x)
  have hnn : 0 ≤ traceNorm (f x) := traceNorm_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnn] using hle

/-- Jensen-type trace-norm bound for probability measures:
the trace norm of the Bochner integral is bounded by the integral of the trace norms. -/
theorem traceNorm_integral_le_integral_traceNorm_of_isProbability
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n]
    (f : α → Op n) (hf : Integrable f μ) :
    traceNorm (∫ x, f x ∂μ) ≤ ∫ x, traceNorm (f x) ∂μ := by
  let p : Seminorm ℂ (Op n) := traceNormSeminorm n
  have hp_cont : Continuous p := by
    simpa [p, traceNormSeminorm] using traceNorm_continuous (n := n)
  have hgi : Integrable (fun x => p (f x)) μ := by
    simpa [p, traceNormSeminorm] using integrable_traceNorm_comp μ hf
  simpa [p, traceNormSeminorm] using
    ConvexOn.map_integral_le (μ := μ) (s := Set.univ) (f := f) (g := p)
      p.convexOn hp_cont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun x => Set.mem_univ (f x)) hf hgi

/-- Jensen-type trace-norm bound for finite nonzero measures, expressed in terms of averages. -/
theorem traceNorm_average_le_average_traceNorm
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] [NeZero μ] {n : ℕ} [NeZero n]
    (f : α → Op n) (hf : Integrable f μ) :
    traceNorm (⨍ x, f x ∂μ) ≤ ⨍ x, traceNorm (f x) ∂μ := by
  let p : Seminorm ℂ (Op n) := traceNormSeminorm n
  have hp_cont : Continuous p := by
    simpa [p, traceNormSeminorm] using traceNorm_continuous (n := n)
  have hgi : Integrable (fun x => p (f x)) μ := by
    simpa [p, traceNormSeminorm] using integrable_traceNorm_comp μ hf
  simpa [p, traceNormSeminorm] using
    ConvexOn.map_average_le (μ := μ) (s := Set.univ) (f := f) (g := p)
      p.convexOn hp_cont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun x => Set.mem_univ (f x)) hf hgi

/-- Jensen-type trace-norm bound for finite measures:
the trace norm of the Bochner integral is bounded by the integral of the trace norms. -/
theorem traceNorm_integral_le_integral_traceNorm_of_isFiniteMeasure
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] {n : ℕ} [NeZero n]
    (f : α → Op n) (hf : Integrable f μ) :
    traceNorm (∫ x, f x ∂μ) ≤ ∫ x, traceNorm (f x) ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ, Quantum.Channels.traceNorm_zero]
  · haveI : NeZero μ := ⟨hμ⟩
    have havg :=
      traceNorm_average_le_average_traceNorm (μ := μ) (f := f) hf
    have hμnn : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    calc
      traceNorm (∫ x, f x ∂μ)
        = traceNorm (μ.real Set.univ • ⨍ x, f x ∂μ) := by
            rw [← MeasureTheory.measure_smul_average (μ := μ) (f := f)]
      _ = traceNorm (((μ.real Set.univ : ℂ)) • ⨍ x, f x ∂μ) := by
            simp
      _ = ‖(μ.real Set.univ : ℂ)‖ * traceNorm (⨍ x, f x ∂μ) := by
            rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
      _ = μ.real Set.univ * traceNorm (⨍ x, f x ∂μ) := by
            simp [hμnn]
      _ ≤ μ.real Set.univ * (⨍ x, traceNorm (f x) ∂μ) :=
            mul_le_mul_of_nonneg_left havg hμnn
      _ = ∫ x, traceNorm (f x) ∂μ := by
            simpa [smul_eq_mul] using
              (MeasureTheory.measure_smul_average (μ := μ) (f := fun x => traceNorm (f x)))

private lemma iUnion_norm_gt_inv_succ_eq_pos {α β : Type*} [Norm β] (g : α → β) :
    (⋃ N : ℕ, {x | (1 / (N + 1 : ℝ)) < ‖g x‖}) = {x | 0 < ‖g x‖} := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨N, hN⟩
    exact lt_trans (by positivity : (0 : ℝ) < 1 / (N + 1 : ℝ)) hN
  · intro hx
    have hx' : 0 < ‖g x‖ := by simpa using hx
    rcases exists_nat_one_div_lt hx' with ⟨N, hN⟩
    exact Set.mem_iUnion.mpr ⟨N, hN⟩

private lemma setIntegral_eq_integral_of_ae_zero_off_compl
    {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {s : Set α} {f : α → E} (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ, x ∈ sᶜ → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  rw [← MeasureTheory.integral_indicator hs]
  exact integral_congr_ae <|
    indicator_ae_eq_of_restrict_compl_ae_eq_zero hs ((ae_restrict_iff' hs.compl).2 hf)

/-- Jensen-type trace-norm bound for arbitrary measures:
the trace norm of the Bochner integral is bounded by the integral of the trace norms. -/
theorem traceNorm_integral_le_integral_traceNorm
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    {n : ℕ} [NeZero n]
    (f : α → Op n) (hf : Integrable f μ) :
    traceNorm (∫ x, f x ∂μ) ≤ ∫ x, traceNorm (f x) ∂μ := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg_int : Integrable g μ := hf.congr hfg
  have hg_trace_int : Integrable (fun x => traceNorm (g x)) μ :=
    integrable_traceNorm_comp μ hg_int
  have hg_sm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  let s : ℕ → Set α := fun N => {x | (1 / (N + 1 : ℝ)) < ‖g x‖}
  have hs_meas : ∀ N, MeasurableSet (s N) := by
    intro N
    exact (stronglyMeasurable_const.measurableSet_lt hg_sm.norm)
  have hs_mono : Monotone s := by
    intro i j hij x hx
    have hle : (1 / (j + 1 : ℝ)) ≤ 1 / (i + 1 : ℝ) := by
      simpa using (Nat.one_div_le_one_div (α := ℝ) hij)
    exact lt_of_le_of_lt hle hx
  have hs_finite : ∀ N, μ (s N) < ⊤ := by
    intro N
    have hpos : 0 < (1 / (N + 1 : ℝ)) := by positivity
    simpa [s] using hg_int.measure_norm_gt_lt_top hpos
  have hset :
      ∀ N, traceNorm (∫ x in s N, g x ∂μ) ≤ ∫ x in s N, traceNorm (g x) ∂μ := by
    intro N
    haveI : Fact (μ (s N) < ⊤) := ⟨hs_finite N⟩
    simpa using
      traceNorm_integral_le_integral_traceNorm_of_isFiniteMeasure
        (μ := μ.restrict (s N)) (f := g)
        (by simpa [MeasureTheory.IntegrableOn] using
          (hg_int.integrableOn : MeasureTheory.IntegrableOn g (s N) μ))
  have hleft :
      Filter.Tendsto (fun N => ∫ x in s N, g x ∂μ) Filter.atTop
        (nhds (∫ x in ⋃ N, s N, g x ∂μ)) :=
    MeasureTheory.tendsto_setIntegral_of_monotone hs_meas hs_mono hg_int.integrableOn
  have hright :
      Filter.Tendsto (fun N => ∫ x in s N, traceNorm (g x) ∂μ) Filter.atTop
        (nhds (∫ x in ⋃ N, s N, traceNorm (g x) ∂μ)) :=
    MeasureTheory.tendsto_setIntegral_of_monotone hs_meas hs_mono hg_trace_int.integrableOn
  have htrace_left :
      Filter.Tendsto (fun N => traceNorm (∫ x in s N, g x ∂μ)) Filter.atTop
        (nhds (traceNorm (∫ x in ⋃ N, s N, g x ∂μ))) :=
    ((traceNorm_continuous (n := n)).tendsto _).comp hleft
  have h_union_le :
      traceNorm (∫ x in ⋃ N, s N, g x ∂μ) ≤ ∫ x in ⋃ N, s N, traceNorm (g x) ∂μ := by
    exact le_of_tendsto_of_tendsto' htrace_left hright hset
  have h_union_eq : (⋃ N, s N) = {x | 0 < ‖g x‖} := by
    simpa [s] using iUnion_norm_gt_inv_succ_eq_pos g
  have h_zero_off_union :
      ∀ᵐ x ∂μ, x ∈ (⋃ N, s N)ᶜ → g x = 0 := by
    filter_upwards with x
    intro hx
    have hnot_mem : x ∉ ⋃ N, s N := by simpa using hx
    have hnot_pos : ¬ 0 < ‖g x‖ := by
      simpa [h_union_eq] using hnot_mem
    exact norm_eq_zero.mp <| le_antisymm (le_of_not_gt hnot_pos) (norm_nonneg _)
  have h_trace_zero_off_union :
      ∀ᵐ x ∂μ, x ∈ (⋃ N, s N)ᶜ → traceNorm (g x) = 0 := by
    filter_upwards [h_zero_off_union] with x hx hxmem
    rw [hx hxmem, Quantum.Channels.traceNorm_zero]
  have h_union_meas : MeasurableSet (⋃ N, s N) := MeasurableSet.iUnion hs_meas
  have h_integral_eq :
      ∫ x in ⋃ N, s N, g x ∂μ = ∫ x, g x ∂μ :=
    setIntegral_eq_integral_of_ae_zero_off_compl h_union_meas h_zero_off_union
  have h_trace_integral_eq :
      ∫ x in ⋃ N, s N, traceNorm (g x) ∂μ = ∫ x, traceNorm (g x) ∂μ :=
    setIntegral_eq_integral_of_ae_zero_off_compl h_union_meas h_trace_zero_off_union
  have h_integral_congr : ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
    integral_congr_ae hfg
  have h_trace_congr :
      ∫ x, traceNorm (f x) ∂μ = ∫ x, traceNorm (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    simp [hx]
  rw [h_integral_congr, h_trace_congr]
  rw [← h_integral_eq, ← h_trace_integral_eq]
  exact h_union_le

end Quantum.Metrics
