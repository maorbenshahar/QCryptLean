import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothApprox
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.GoodBranch
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.ContinuousMixture

/-!
# Post-filter mixture entropy

Almost-everywhere feasible coefficient bounds give conditional and smooth entropy floors for post-
filtered mixtures. Good-branch approximators pay the stated trace-gap smoothing charge, including
subnormalized and zero-weight mixtures.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) :=
  SeminormedAddGroup.toContinuousENorm

/-- Pointwise extended entropy floors pass to the retained branch, including zero retained mass. -/
lemma conditionalMinEntropy_ge_of_goodBranch_forall
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE)
    (k : ℝ)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hgood : ∀ τ ∈ goodSet,
      ENNReal.ofReal k ≤ conditionalMinEntropy (f τ) σ_ref) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ_good σ_ref := by
  by_cases hk : k ≤ 0
  · simp only [ENNReal.ofReal_of_nonpos hk, zero_le]
  · apply ofReal_le_conditionalMinEntropy_of_isFeasible
    refine ⟨Real.rpow_nonneg (by norm_num) _, fun x => ?_⟩
    rw [hρ_good_eq x]
    exact goodBranchBlockOp_opLe_of_forall_mem_bound μ f goodSet hMeas x (h_int x)
      σ_ref (Real.rpow_nonneg (by norm_num) _) fun τ hτ =>
        (isFeasible_of_ofReal_le_conditionalMinEntropy (f τ) σ_ref
          (lt_of_not_ge hk) (hgood τ hτ)).2 x

/-- Almost-everywhere extended entropy floors pass to the retained branch without a mass guard. -/
lemma conditionalMinEntropy_ge_of_goodBranch_ae
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE)
    (k : ℝ)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        ENNReal.ofReal k ≤ conditionalMinEntropy (f τ) σ_ref) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ_good σ_ref := by
  by_cases hk : k ≤ 0
  · simp only [ENNReal.ofReal_of_nonpos hk, zero_le]
  · apply ofReal_le_conditionalMinEntropy_of_isFeasible
    refine ⟨Real.rpow_nonneg (by norm_num) _, fun x => ?_⟩
    rw [hρ_good_eq x]
    apply goodBranchBlockOp_opLe_of_ae_bound μ f goodSet x (h_int x)
      σ_ref (Real.rpow_nonneg (by norm_num) _)
    filter_upwards [hgood_ae] with τ hτ
    exact (isFeasible_of_ofReal_le_conditionalMinEntropy (f τ) σ_ref
      (lt_of_not_ge hk) hτ).2 x

/-- A subnormalized post-filter mixture inherits pointwise extended component floors at radius
`sqrt (2 * ε)`. The retained branch may have zero weight. -/
theorem smoothMinEntropy_ge_of_deFinetti_postFilter_traceNormBound
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k ε : ℝ)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hgood : ∀ τ ∈ goodSet,
      ENNReal.ofReal k ≤ conditionalMinEntropy (f τ) σ_ref) :
    ENNReal.ofReal k ≤ smoothMinEntropy (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  have hε_nonneg : 0 ≤ ε := (Finset.sum_nonneg fun x _ =>
    (Complex.nonneg_iff.mp (badBranchBlockOp_posSemidef_of_integrable
      μ f goodSet x (h_int x).restrict).trace_nonneg).1).trans h_badBranch_traceNorm
  obtain ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm
  apply smoothMinEntropy_ge_of_hmin_approx ρ_mix ρ_good σ_ref k
  · apply CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap
  · exact conditionalMinEntropy_ge_of_goodBranch_forall μ f goodSet hMeas h_int
      σ_ref k ρ_good hρ_good_eq hgood

/-- A subnormalized post-filter mixture inherits almost-everywhere extended component floors
at radius `sqrt (2 * ε)`, with no lower bound on its weight. -/
theorem smoothMinEntropy_ge_of_deFinetti_postFilter_traceNormBound_ae_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k ε : ℝ)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        ENNReal.ofReal k ≤ conditionalMinEntropy (f τ) σ_ref) :
    ENNReal.ofReal k ≤ smoothMinEntropy (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  have hε_nonneg : 0 ≤ ε := (Finset.sum_nonneg fun x _ =>
    (Complex.nonneg_iff.mp (badBranchBlockOp_posSemidef_of_integrable
      μ f goodSet x (h_int x).restrict).trace_nonneg).1).trans h_badBranch_traceNorm
  obtain ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm
  exact smoothMinEntropy_ge_of_hmin_approx ρ_mix ρ_good σ_ref k
    (CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap)
    (conditionalMinEntropy_ge_of_goodBranch_ae μ f goodSet h_int
      σ_ref k ρ_good hρ_good_eq hgood_ae)

/-- An integrable family of component smoothing witnesses gives an extended mixture floor at
radius `εBar + sqrt (2 * ε)`. Zero component and mixture witnesses need no mass guards. -/
theorem smoothMinEntropy_ge_of_deFinetti_postFilter_smoothFloor_ae_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f g : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hg_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hg_ball :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        CQState.purifiedDistance (f τ) (g τ) ≤ εBar)
    (hg_floor :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        ENNReal.ofReal k ≤ conditionalMinEntropy (g τ) σ_ref) :
    ENNReal.ofReal k ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  have hε_nonneg : 0 ≤ ε := (Finset.sum_nonneg fun x _ =>
    (Complex.nonneg_iff.mp (badBranchBlockOp_posSemidef_of_integrable
      μ f goodSet x (h_int x).restrict).trace_nonneg).1).trans h_badBranch_traceNorm
  obtain ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm
  have hcenter :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap
  obtain ⟨ρ_good', hρ_good'_eq, hdist'⟩ :=
    exists_continuousMixtureGoodBranch_purifiedDistance_le_of_integrable
      μ f g goodSet h_int hg_int ρ_good hρ_good_eq hεBar_nonneg hg_ball
  apply smoothMinEntropy_ge_of_hmin_approx ρ_mix ρ_good' σ_ref k
  · calc
      CQState.purifiedDistance ρ_mix ρ_good'
          ≤ CQState.purifiedDistance ρ_mix ρ_good +
              CQState.purifiedDistance ρ_good ρ_good' :=
        CQState.purifiedDistance_triangle ρ_mix ρ_good ρ_good'
      _ ≤ Real.sqrt (2 * ε) + εBar := add_le_add hcenter hdist'
      _ = εBar + Real.sqrt (2 * ε) := add_comm _ _
  · exact conditionalMinEntropy_ge_of_goodBranch_ae μ g goodSet hg_int
      σ_ref k ρ_good' hρ_good'_eq hg_floor


/-- The trace-gap parameter is below the weight when twice its smoothing radius is below that
weight and the parameter is less than one half. -/
private lemma epsilon_lt_weight_of_two_sqrt_lt_weight {ε W : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (hW : 2 * Real.sqrt (2 * ε) < W) :
    ε < W := by
  have harg_nonneg : 0 ≤ 2 * ε := by nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * ε) := Real.sqrt_nonneg _
  have hsqrt_lt_one : Real.sqrt (2 * ε) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith
  have hsqrt_sq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε :=
    Real.sq_sqrt harg_nonneg
  have hε_le_two_sqrt : ε ≤ 2 * Real.sqrt (2 * ε) := by
    nlinarith
  exact lt_of_le_of_lt hε_le_two_sqrt hW

/-- A positive-weight good branch inherits a signed conditional entropy floor holding on every
accepting component. -/
lemma conditionalMinEntropyReal_ge_of_goodBranch_forall
    {d dE : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) (hσ_ref : σ_ref.toOp.PosDef)
    (k : ℝ)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace)
    (hgood : ∀ τ ∈ goodSet,
      k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ conditionalMinEntropyReal ρ_good σ_ref := by
  have ht_nonneg : 0 ≤ (2 : ℝ) ^ (-k) :=
    Real.rpow_nonneg (by norm_num) _
  refine conditionalMinEntropyReal_ge_of_isFeasible_pow_neg_of_weight_pos
    ρ_good σ_ref hσ_ref k hweight_pos ?_
  refine ⟨ht_nonneg, ?_⟩
  intro x
  rw [hρ_good_eq x]
  exact goodBranchBlockOp_opLe_of_forall_mem_bound
    μ f goodSet hMeas x (h_int x) σ_ref ht_nonneg
    (fun τ hτ =>
      stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le
        (f τ) σ_ref hσ_ref (hgood τ hτ) x)

/-- A positive-weight good branch inherits an almost-everywhere signed conditional entropy floor
from the accepting components. -/
lemma conditionalMinEntropyReal_ge_of_goodBranch_ae
    {d dE : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) (hσ_ref : σ_ref.toOp.PosDef)
    (k : ℝ)
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ conditionalMinEntropyReal ρ_good σ_ref := by
  have ht_nonneg : 0 ≤ (2 : ℝ) ^ (-k) :=
    Real.rpow_nonneg (by norm_num) _
  refine conditionalMinEntropyReal_ge_of_isFeasible_pow_neg_of_weight_pos
    ρ_good σ_ref hσ_ref k hweight_pos ?_
  refine ⟨ht_nonneg, ?_⟩
  intro x
  rw [hρ_good_eq x]
  exact goodBranchBlockOp_opLe_of_ae_bound
    μ f goodSet x (h_int x) σ_ref ht_nonneg
    (by
      filter_upwards [hgood_ae] with τ hτ
      exact stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le
        (f τ) σ_ref hσ_ref hτ x)

/-- A signed conditional floor on the accepting components gives a normalized mixture the same
signed smooth floor at radius `sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_deFinetti_postFilter_traceNormBound
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hρ_norm : ∑ x, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hgood : ∀ τ ∈ goodSet,
      k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  rcases exists_goodBranchCQState_of_integrable_traceNormBound
      μ ρ_mix f goodSet hMeas hρ_norm h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_deficit⟩
  have hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by
    have htrace_lt_one : 1 - (∑ x : X, (ρ_good.stateMap x).trace) < 1 := by
      linarith
    linarith
  have hk_good : k ≤ conditionalMinEntropyReal ρ_good σ_ref :=
    conditionalMinEntropyReal_ge_of_goodBranch_forall
      μ f goodSet hMeas h_int σ_ref hσ_ref k ρ_good
      hρ_good_eq hweight_pos hgood
  exact smoothMinEntropyReal_ge_of_goodBranch_traceDeficit
    ε hε_nonneg hε_lt_half ρ_mix hρ_norm σ_ref k ρ_good
    hρ_good_le_mix htrace_deficit hk_good

/-- An almost-everywhere signed conditional floor on the accepting components gives a normalized
mixture the same signed smooth floor at radius `sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_deFinetti_postFilter_traceNormBound_ae
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (hρ_norm : ∑ x, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  rcases exists_goodBranchCQState_of_integrable_traceNormBound
      μ ρ_mix f goodSet hMeas hρ_norm h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_deficit⟩
  have hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by
    have htrace_lt_one : 1 - (∑ x : X, (ρ_good.stateMap x).trace) < 1 := by
      linarith
    linarith
  have hk_good : k ≤ conditionalMinEntropyReal ρ_good σ_ref :=
    conditionalMinEntropyReal_ge_of_goodBranch_ae
      μ f goodSet h_int σ_ref hσ_ref k ρ_good
      hρ_good_eq hweight_pos hgood_ae
  exact smoothMinEntropyReal_ge_of_goodBranch_traceDeficit
    ε hε_nonneg hε_lt_half ρ_mix hρ_norm σ_ref k ρ_good
    hρ_good_le_mix htrace_deficit hk_good

/-- An almost-everywhere signed conditional floor on the accepting components gives a
subnormalized mixture the same signed smooth floor at radius `sqrt (2 * ε)` below the weight
threshold. -/
theorem smoothMinEntropyReal_ge_of_deFinetti_postFilter_traceNormBound_ae_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (h_subNorm : 2 * Real.sqrt (2 * ε) < ∑ x : X, (ρ_mix.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hgood_ae :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        k ≤ conditionalMinEntropyReal (f τ) σ_ref) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  rcases exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩
  have hweight_pos : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by
    have hε_lt_weight :
        ε < ∑ x : X, (ρ_mix.stateMap x).trace :=
      epsilon_lt_weight_of_two_sqrt_lt_weight
        hε_nonneg hε_lt_half h_subNorm
    linarith
  have hk_good : k ≤ conditionalMinEntropyReal ρ_good σ_ref :=
    conditionalMinEntropyReal_ge_of_goodBranch_ae
      μ f goodSet h_int σ_ref hσ_ref k ρ_good
      hρ_good_eq hweight_pos hgood_ae
  exact smoothMinEntropyReal_ge_of_goodBranch_traceGap
    ε hε_nonneg ρ_mix h_subNorm σ_ref k ρ_good
    hρ_good_le_mix htrace_gap hk_good

/-- Almost-everywhere nearby component witnesses with signed floor `k` give the mixture the same
signed floor at radius `εBar + sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_deFinetti_postFilter_smoothFloor_ae_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f g : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hg_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (hsum_lt_one : εBar + Real.sqrt (2 * ε) < 1)
    (h_subNorm : 2 * (εBar + Real.sqrt (2 * ε)) < ∑ x : X, (ρ_mix.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hg_ball :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        CQState.purifiedDistance (f τ) (g τ) ≤ εBar)
    (hg_floor :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        k ≤ conditionalMinEntropyReal (g τ) σ_ref) :
    k ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  rcases exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩
  have hε_le_two_sqrt : ε ≤ 2 * Real.sqrt (2 * ε) := by
    have harg : (0 : ℝ) ≤ 2 * ε := by linarith
    have hs : Real.sqrt (2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt harg
    have hs_lt1 : Real.sqrt (2 * ε) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]; nlinarith
    nlinarith [Real.sqrt_nonneg (2 * ε), hs, hs_lt1]
  have h_sub2 : 2 * Real.sqrt (2 * ε) < ∑ x : X, (ρ_mix.stateMap x).trace := by
    nlinarith [h_subNorm, hεBar_nonneg]
  have hε_lt_weight : ε < ∑ x : X, (ρ_mix.stateMap x).trace :=
    epsilon_lt_weight_of_two_sqrt_lt_weight hε_nonneg hε_lt_half h_sub2
  have hweight_pos_good : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by linarith
  have hcenter : CQState.purifiedDistance ρ_mix ρ_good ≤ Real.sqrt (2 * ε) :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap
  rcases exists_continuousMixtureGoodBranch_purifiedDistance_le_of_integrable
      μ f g goodSet h_int hg_int ρ_good hρ_good_eq hεBar_nonneg hg_ball with
    ⟨ρ_good', hρ_good'_eq, hdist'⟩
  have h2εBar_lt : 2 * εBar < ∑ x : X, (ρ_good.stateMap x).trace := by
    nlinarith [htrace_gap, h_subNorm, hε_le_two_sqrt]
  have hweight_pos_good' : 0 < ∑ x : X, (ρ_good'.stateMap x).trace := by
    have hlow := CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower
      (ρ := ρ_good) (ρ' := ρ_good') (ε := εBar)
      (η := (∑ x : X, (ρ_good.stateMap x).trace) - 2 * εBar)
      (by linarith) hdist'
    linarith
  have hfloor' : k ≤ conditionalMinEntropyReal ρ_good' σ_ref :=
    conditionalMinEntropyReal_ge_of_goodBranch_ae
      μ g goodSet hg_int σ_ref hσ_ref k ρ_good'
      hρ_good'_eq hweight_pos_good' hg_floor
  have htri : CQState.purifiedDistance ρ_mix ρ_good' ≤ εBar + Real.sqrt (2 * ε) := by
    calc CQState.purifiedDistance ρ_mix ρ_good'
        ≤ CQState.purifiedDistance ρ_mix ρ_good
            + CQState.purifiedDistance ρ_good ρ_good' :=
          CQState.purifiedDistance_triangle ρ_mix ρ_good ρ_good'
      _ ≤ Real.sqrt (2 * ε) + εBar := add_le_add hcenter hdist'
      _ = εBar + Real.sqrt (2 * ε) := by ring
  have hbdd : BddAbove
      (setOf (isInSmoothedSetReal (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd))
      (εBar + Real.sqrt (2 * ε))
      ((∑ x : X, (ρ_mix.stateMap x).trace) - 2 * (εBar + Real.sqrt (2 * ε)))
      (by linarith) ρ_mix (by linarith) σ_ref
  exact smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove
    (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref k ρ_good' hbdd htri hfloor'

end InfoTheory.SmoothMinEntropy

end
