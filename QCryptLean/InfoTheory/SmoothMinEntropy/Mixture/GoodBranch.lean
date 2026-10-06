import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.Basic
import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.Quantum.Operators.MatrixIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Good-Branch Mixtures — restricted de Finetti blocks and CQ-state packaging

This file defines the good and bad restricted block operators associated to a
De Finetti CQ mixture, proves the set-integral structure facts needed for those
blocks, and packages the good branch as a `CQState` under integrability and trace
side conditions.

## Main definitions
- `goodBranchBlockOp`: restricted operator block over the good branch.
- `badBranchBlockOp`: restricted operator block over the complement.

## Main statements
- `traceSetIntegral_le_of_pointwise_weight_bounds`: a pointwise weight cap bounds the
  trace of the integrated blocks over the complement of a measurable good set.
- `goodBranchBlockOp_opLe_stateMap_of_integrable`: the good branch is dominated
  by the full mixture blockwise.
- `exists_goodBranchCQState_of_integrable`: good-branch blocks form a CQ state.
- `exists_goodBranchCQState_of_integrable_traceNormBound`: normalized trace-gap
  packaging from an entrywise bad-branch bound.
- `exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized`:
  subnormalized trace-gap packaging.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- A pointwise block-weight cap `E` on the complement of a measurable good set bounds the
trace of its block integral by `E`, for a probability measure. -/
theorem traceSetIntegral_le_of_pointwise_weight_bounds {Xt : Type*} [Fintype Xt] {dE : ℕ}
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (f : α → CQState Xt dE)
    (hint : ∀ x : Xt, MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ)
    (B : Set α) (hB : MeasurableSet B)
    (E : ℝ) (hE : 0 ≤ E)
    (hbadB : ∀ a ∈ Bᶜ, ∑ x : Xt, ((f a).stateMap x).toOp.trace.re ≤ E) :
    ∑ x : Xt, ((Matrix.of fun i j : Fin dE =>
        ∫ a in Bᶜ, ((f a).stateMap x).toOp i j ∂μ : Op dE).trace).re ≤ E := by
  classical
  let entryCLM : Fin dE → Fin dE → (Op dE →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hentInt : ∀ (x : Xt) (i : Fin dE) (U : Set α),
      MeasureTheory.IntegrableOn (fun a => ((f a).stateMap x).toOp i i) U μ :=
    fun x i U => ((entryCLM i i).integrable_comp (hint x)).integrableOn
  have htrInt : ∀ (x : Xt) (U : Set α),
      MeasureTheory.IntegrableOn (fun a => ((f a).stateMap x).toOp.trace.re) U μ := by
    intro x U
    have heq : (fun a => ((f a).stateMap x).toOp.trace.re)
        = fun a => ∑ i, (((f a).stateMap x).toOp i i).re := by
      funext a; simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    rw [heq]
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      Complex.reCLM.integrable_comp (hentInt x i U)
  have hsumInt : ∀ U : Set α, MeasureTheory.IntegrableOn
      (fun a => ∑ x : Xt, ((f a).stateMap x).toOp.trace.re) U μ :=
    fun U => MeasureTheory.integrable_finsetSum _ (fun x _ => htrInt x U)
  -- Reduce the entry-integral trace sum to the set integral of the total block weight.
  have hred : ∀ U : Set α, MeasurableSet U →
      (∑ x : Xt, ((Matrix.of fun i j : Fin dE =>
          ∫ a in U, ((f a).stateMap x).toOp i j ∂μ : Op dE).trace).re)
        = ∫ a in U, (∑ x : Xt, ((f a).stateMap x).toOp.trace.re) ∂μ := by
    intro U hU
    have hperx : ∀ x : Xt,
        ((Matrix.of fun i j : Fin dE =>
            ∫ a in U, ((f a).stateMap x).toOp i j ∂μ : Op dE).trace).re =
          ∫ a in U, ((f a).stateMap x).toOp.trace.re ∂μ := by
      intro x
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.of_apply]
      rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hentInt x i U), ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (MeasureTheory.integrable_finsetSum _ (fun i _ => hentInt x i U))]
      refine MeasureTheory.setIntegral_congr_fun hU (fun a _ => ?_)
      simp only [Complex.reCLM_apply, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    rw [Finset.sum_congr rfl (fun x _ => hperx x),
      ← MeasureTheory.integral_finsetSum _ (fun x _ => htrInt x U)]
  rw [hred Bᶜ hB.compl]
  have hBcbound : (∫ a in Bᶜ, (∑ x : Xt, ((f a).stateMap x).toOp.trace.re) ∂μ) ≤ E := by
    calc ∫ a in Bᶜ, (∑ x : Xt, ((f a).stateMap x).toOp.trace.re) ∂μ
           ≤ ∫ _a in Bᶜ, E ∂μ :=
          MeasureTheory.setIntegral_mono_on (hsumInt Bᶜ)
            ((MeasureTheory.integrable_const _).integrableOn) hB.compl (fun a ha => hbadB a ha)
      _ = μ.real Bᶜ • E := MeasureTheory.setIntegral_const _
      _ = μ.real Bᶜ * E := by rw [smul_eq_mul]
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right MeasureTheory.measureReal_le_one hE
      _ = E := one_mul _
  exact hBcbound

/-- The raw `x`-block operator obtained by restricting a de Finetti CQ mixture to
the good branch.  The accompanying constructor below records the exact positivity
and trace side conditions needed before this raw operator can be packaged as a
`CQState`. -/
noncomputable def goodBranchBlockOp
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X) : Op dE :=
  Matrix.of fun i j : Fin dE =>
    ∫ τ in goodSet, ((f τ).stateMap x).toOp i j ∂μ.measure

/-- The raw `x`-block operator obtained by restricting a de Finetti CQ mixture
to the complement of the good branch. -/
noncomputable def badBranchBlockOp
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X) : Op dE :=
  Matrix.of fun i j : Fin dE =>
    ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure

/-- The entrywise definition of `goodBranchBlockOp` is the Bochner set integral
of the corresponding block operator-valued function, assuming that block
function is integrable on the restricted measure. -/
lemma goodBranchBlockOp_eq_setIntegral
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSet)) :
    goodBranchBlockOp μ f goodSet x =
      ∫ τ in goodSet, ((f τ).stateMap x).toOp ∂μ.measure := by
  rw [goodBranchBlockOp]
  exact matrix_of_setIntegral_eq_setIntegral (μ := μ.measure) goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int

/-- The entrywise definition of `badBranchBlockOp` is the Bochner set integral
of the corresponding block operator-valued function, assuming that block
function is integrable on the restricted measure. -/
lemma badBranchBlockOp_eq_setIntegral
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSetᶜ)) :
    badBranchBlockOp μ f goodSet x =
      ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp ∂μ.measure := by
  rw [badBranchBlockOp]
  exact matrix_of_setIntegral_eq_setIntegral (μ := μ.measure) goodSetᶜ
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int

/-- The restricted good-branch block is Hermitian under the block Bochner
integrability hypothesis. -/
lemma goodBranchBlockOp_isHermitian_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSet)) :
    (goodBranchBlockOp μ f goodSet x).IsHermitian := by
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int]
  exact matrix_setIntegral_isHermitian goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int
    (fun τ => ((f τ).stateMap x).isHermitian)

/-- The restricted good-branch block is PSD under the block Bochner
integrability hypothesis. -/
lemma goodBranchBlockOp_posSemidef_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSet)) :
    (goodBranchBlockOp μ f goodSet x).PosSemidef := by
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int]
  exact matrix_setIntegral_posSemidef goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int
    (fun τ =>
      Quantum.Operators.posSemidefOp_implies_mathlib
        ((f τ).stateMap x).toPosSemidefOp)

/-- The restricted bad-branch block is PSD under the block Bochner
integrability hypothesis. -/
lemma badBranchBlockOp_posSemidef_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSetᶜ)) :
    (badBranchBlockOp μ f goodSet x).PosSemidef := by
  rw [badBranchBlockOp_eq_setIntegral μ f goodSet x h_int]
  exact matrix_setIntegral_posSemidef goodSetᶜ
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int
    (fun τ =>
      Quantum.Operators.posSemidefOp_implies_mathlib
        ((f τ).stateMap x).toPosSemidefOp)

/-- The restricted good-branch block has a nonnegative quadratic form under the
block Bochner integrability hypothesis. -/
lemma goodBranchBlockOp_quadraticForm_re_nonneg_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp)
      (μ.measure.restrict goodSet)) :
    ∀ v : Fin dE → ℂ,
      0 ≤ (quadraticForm (goodBranchBlockOp μ f goodSet x) v).re := by
  intro v
  have h_psd := goodBranchBlockOp_posSemidef_of_integrable μ f goodSet x h_int
  have h := h_psd.dotProduct_mulVec_nonneg v
  simpa [quadraticForm] using (Complex.nonneg_iff.mp h).1

/-- Pointwise domination on a measurable good branch integrates to domination
of the restricted good-branch block.  The restricted measure may have total
mass below one, so a constant dominating operator still dominates the integral. -/
lemma goodBranchBlockOp_opLe_of_forall_mem_bound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) {t : ℝ} (ht : 0 ≤ t)
    (h_bound : ∀ τ ∈ goodSet,
      opLe ((f τ).stateMap x).toOp (Complex.ofReal t • σ_ref.toOp)) :
    opLe (goodBranchBlockOp μ f goodSet x)
      (Complex.ofReal t • σ_ref.toOp) := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  intro v
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int.restrict]
  rw [Quantum.Operators.quadraticForm_re_setIntegral goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int.restrict v]
  set c : ℝ := (quadraticForm (Complex.ofReal t • σ_ref.toOp) v).re
  have hc_nonneg : 0 ≤ c := by
    rw [show c = (quadraticForm (Complex.ofReal t • σ_ref.toOp) v).re by rfl]
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg ht (σ_ref.pos_semidef v)
  have h_nonneg :
      0 ≤ᵐ[μ.measure.restrict goodSet]
        fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re :=
    ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v
  have h_ae_le :
      (fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re)
        ≤ᵐ[μ.measure.restrict goodSet] fun _ : DensityOp d => c := by
    refine MeasureTheory.ae_restrict_of_forall_mem hMeas ?_
    intro τ hτ
    exact h_bound τ hτ v
  have h_integral_le_restrict :
      ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ _τ in goodSet, c ∂μ.measure :=
    MeasureTheory.integral_mono_of_nonneg h_nonneg (integrable_const c) h_ae_le
  have h_restrict_const_le :
      ∫ _τ in goodSet, c ∂μ.measure ≤ ∫ _τ : DensityOp d, c ∂μ.measure :=
    MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => hc_nonneg) (integrable_const c)
  have hμ_univ : μ.measure Set.univ = 1 := μ.isProbability.measure_univ
  calc
    ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ _τ in goodSet, c ∂μ.measure := h_integral_le_restrict
    _ ≤ ∫ _τ : DensityOp d, c ∂μ.measure := h_restrict_const_le
    _ = c := by
      rw [integral_const]
      simp [MeasureTheory.Measure.real, hμ_univ]

/-- Almost-everywhere domination on a good branch integrates to domination
of the restricted good-branch block. -/
lemma goodBranchBlockOp_opLe_of_ae_bound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (σ_ref : SubDensityOp dE) {t : ℝ} (ht : 0 ≤ t)
    (h_bound :
      ∀ᵐ τ ∂μ.measure.restrict goodSet,
        opLe ((f τ).stateMap x).toOp (Complex.ofReal t • σ_ref.toOp)) :
    opLe (goodBranchBlockOp μ f goodSet x)
      (Complex.ofReal t • σ_ref.toOp) := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  intro v
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int.restrict]
  rw [Quantum.Operators.quadraticForm_re_setIntegral goodSet
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int.restrict v]
  set c : ℝ := (quadraticForm (Complex.ofReal t • σ_ref.toOp) v).re
  have hc_nonneg : 0 ≤ c := by
    rw [show c = (quadraticForm (Complex.ofReal t • σ_ref.toOp) v).re by rfl]
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg ht (σ_ref.pos_semidef v)
  have h_nonneg :
      0 ≤ᵐ[μ.measure.restrict goodSet]
        fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re :=
    ae_of_all _ fun τ => ((f τ).stateMap x).pos_semidef v
  have h_ae_le :
      (fun τ : DensityOp d => (quadraticForm ((f τ).stateMap x).toOp v).re)
        ≤ᵐ[μ.measure.restrict goodSet] fun _ : DensityOp d => c := by
    filter_upwards [h_bound] with τ hτ
    exact hτ v
  have h_integral_le_restrict :
      ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ _τ in goodSet, c ∂μ.measure :=
    MeasureTheory.integral_mono_of_nonneg h_nonneg (integrable_const c) h_ae_le
  have h_restrict_const_le :
      ∫ _τ in goodSet, c ∂μ.measure ≤ ∫ _τ : DensityOp d, c ∂μ.measure :=
    MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun _ => hc_nonneg) (integrable_const c)
  have hμ_univ : μ.measure Set.univ = 1 := μ.isProbability.measure_univ
  calc
    ∫ τ in goodSet, (quadraticForm ((f τ).stateMap x).toOp v).re ∂μ.measure
        ≤ ∫ _τ in goodSet, c ∂μ.measure := h_integral_le_restrict
    _ ≤ ∫ _τ : DensityOp d, c ∂μ.measure := h_restrict_const_le
    _ = c := by
      rw [integral_const]
      simp [MeasureTheory.Measure.real, hμ_univ]

/-- The entrywise full-mixture hypothesis identifies each CQ block with the
Bochner integral of its component blocks. -/
lemma stateMap_toOp_eq_integral_of_hf_lin
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    (ρ_mix.stateMap x).toOp =
      ∫ τ : DensityOp d, ((f τ).stateMap x).toOp ∂μ.measure := by
  ext i j
  rw [hf_lin x i j]
  exact (matrix_integral_entry
    (fun τ : DensityOp d => ((f τ).stateMap x).toOp) h_int i j).symm

/-- The full block decomposes as good branch plus bad-complement branch. -/
lemma goodBranchBlockOp_add_badBranchBlockOp_eq_stateMap_toOp
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    goodBranchBlockOp μ f goodSet x + badBranchBlockOp μ f goodSet x =
      (ρ_mix.stateMap x).toOp := by
  rw [goodBranchBlockOp_eq_setIntegral μ f goodSet x h_int.restrict,
    badBranchBlockOp_eq_setIntegral μ f goodSet x h_int.restrict,
    stateMap_toOp_eq_integral_of_hf_lin μ ρ_mix f x h_int hf_lin]
  exact MeasureTheory.integral_add_compl hMeas h_int

/-- The good branch is blockwise dominated by the full mixture under explicit
block-integrability hypotheses. -/
lemma goodBranchBlockOp_opLe_stateMap_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    ∀ x : X, opLe (goodBranchBlockOp μ f goodSet x)
      (ρ_mix.stateMap x).toOp := by
  intro x
  refine Quantum.Operators.opLe_of_posSemidef_sub ?_
  have hsplit := goodBranchBlockOp_add_badBranchBlockOp_eq_stateMap_toOp
    μ ρ_mix f goodSet hMeas x (h_int x) hf_lin
  have hdiff :
      (ρ_mix.stateMap x).toOp - goodBranchBlockOp μ f goodSet x =
        badBranchBlockOp μ f goodSet x := by
    rw [← hsplit]
    abel
  rw [hdiff]
  exact badBranchBlockOp_posSemidef_of_integrable μ f goodSet x (h_int x).restrict

/-- Each good-branch block has trace at most one once it is dominated by the
corresponding full-mixture block. -/
lemma goodBranchBlockOp_trace_le_one_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    ∀ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1 := by
  intro x
  exact (opLe_trace_re_le
    (goodBranchBlockOp_opLe_stateMap_of_integrable
      μ ρ_mix f goodSet hMeas h_int hf_lin x)).trans
    (ρ_mix.stateMap x).trace_le_one

/-- The total trace weight of the good branch is at most one under explicit
block-integrability hypotheses. -/
lemma goodBranchBlockOp_weight_le_one_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1 := by
  calc
    ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re
        ≤ ∑ x : X, ((ρ_mix.stateMap x).toOp).trace.re := by
          exact Finset.sum_le_sum fun x _ =>
            opLe_trace_re_le
              (goodBranchBlockOp_opLe_stateMap_of_integrable
                μ ρ_mix f goodSet hMeas h_int hf_lin x)
    _ = ∑ x : X, (ρ_mix.stateMap x).trace := rfl
    _ ≤ 1 := ρ_mix.weight_le_one

/-- The real trace of each full mixture block splits into its good- and
bad-branch trace contributions. -/
lemma goodBranchBlockOp_trace_add_badBranchBlockOp_trace_eq_stateMap_trace
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    (ρ_mix.stateMap x).trace =
      (goodBranchBlockOp μ f goodSet x).trace.re +
        (badBranchBlockOp μ f goodSet x).trace.re := by
  have hsplit := goodBranchBlockOp_add_badBranchBlockOp_eq_stateMap_toOp
    μ ρ_mix f goodSet hMeas x h_int hf_lin
  calc
    (ρ_mix.stateMap x).trace
        = ((goodBranchBlockOp μ f goodSet x +
            badBranchBlockOp μ f goodSet x).trace).re := by
              rw [hsplit]
              rfl
    _ = (goodBranchBlockOp μ f goodSet x).trace.re +
        (badBranchBlockOp μ f goodSet x).trace.re := by
          rw [Matrix.trace_add, Complex.add_re]

/-- The total trace weight of the full mixture splits into good- and bad-branch
trace weights. -/
lemma goodBranchBlockOp_weight_add_badBranchBlockOp_weight_eq_stateMap_weight
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    ∑ x : X, (ρ_mix.stateMap x).trace =
      (∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re) +
        ∑ x : X, (badBranchBlockOp μ f goodSet x).trace.re := by
  rw [show (∑ x : X, (ρ_mix.stateMap x).trace) =
      ∑ x : X, ((goodBranchBlockOp μ f goodSet x).trace.re +
        (badBranchBlockOp μ f goodSet x).trace.re) from by
        exact Finset.sum_congr rfl (fun x _ =>
          goodBranchBlockOp_trace_add_badBranchBlockOp_trace_eq_stateMap_trace
            μ ρ_mix f goodSet hMeas x (h_int x) hf_lin)]
  rw [Finset.sum_add_distrib]

/-- The trace deficit of the good branch is controlled by the total bad-branch
trace mass. -/
lemma goodBranchBlockOp_trace_deficit_le_of_badBranch_trace
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (hρ_norm : ∑ x : X, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_trace :
      ∑ x : X, (badBranchBlockOp μ f goodSet x).trace.re ≤ ε) :
    1 - ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ ε := by
  have h_sum := goodBranchBlockOp_weight_add_badBranchBlockOp_weight_eq_stateMap_weight
    μ ρ_mix f goodSet hMeas h_int hf_lin
  linarith

/-- Version of the good-branch trace-deficit bound accepting the bad branch in
its entrywise `Matrix.of` form. -/
lemma goodBranchBlockOp_trace_deficit_le_of_badBranch_traceNormBound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (hρ_norm : ∑ x : X, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε) :
    1 - ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ ε := by
  exact goodBranchBlockOp_trace_deficit_le_of_badBranch_trace
    μ ρ_mix f goodSet hMeas hρ_norm h_int hf_lin
    (by simpa [badBranchBlockOp] using h_badBranch_traceNorm)

/-- Subnormalized version of the good-branch trace-gap bound: the gap is the
actual mixture weight minus the good-branch weight. -/
lemma goodBranchBlockOp_trace_gap_le_of_badBranch_trace
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_trace :
      ∑ x : X, (badBranchBlockOp μ f goodSet x).trace.re ≤ ε) :
    (∑ x : X, (ρ_mix.stateMap x).trace) -
        ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ ε := by
  have h_sum := goodBranchBlockOp_weight_add_badBranchBlockOp_weight_eq_stateMap_weight
    μ ρ_mix f goodSet hMeas h_int hf_lin
  linarith

/-- Entrywise-`Matrix.of` variant of the subnormalized good-branch trace-gap
bound. -/
lemma goodBranchBlockOp_trace_gap_le_of_badBranch_traceNormBound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε) :
    (∑ x : X, (ρ_mix.stateMap x).trace) -
        ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ ε := by
  exact goodBranchBlockOp_trace_gap_le_of_badBranch_trace
    μ ρ_mix f goodSet hMeas h_int hf_lin
    (by simpa [badBranchBlockOp] using h_badBranch_traceNorm)

/-- Package the restricted good-branch block operators as a CQ state once the
entrywise restricted integrals have been shown Hermitian, positive semidefinite,
and subnormalized. -/
theorem exists_goodBranchCQState_of_block_conditions
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_herm : ∀ x : X, (goodBranchBlockOp μ f goodSet x).IsHermitian)
    (h_psd : ∀ x : X, ∀ v : Fin dE → ℂ,
      0 ≤ (quadraticForm (goodBranchBlockOp μ f goodSet x) v).re)
    (h_trace_le_one : ∀ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1)
    (h_weight_le_one :
      ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1) :
    ∃ ρ_good : CQState X dE,
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x := by
  refine ⟨{
    stateMap := fun x => {
      toOp := goodBranchBlockOp μ f goodSet x
      isHermitian := h_herm x
      pos_semidef := h_psd x
      trace_le_one := h_trace_le_one x
    }
    weight_le_one := ?_
  }, ?_⟩
  · simpa [SubDensityOp.trace] using h_weight_le_one
  · intro x
    rfl

/-- Construct the restricted good-branch CQ state from block integrability,
and record its blockwise domination by the full mixture. -/
theorem exists_goodBranchCQState_of_integrable
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) ∧
      ∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp := by
  have h_herm : ∀ x : X, (goodBranchBlockOp μ f goodSet x).IsHermitian := fun x =>
    goodBranchBlockOp_isHermitian_of_integrable μ f goodSet x (h_int x).restrict
  have h_psd : ∀ x : X, ∀ v : Fin dE → ℂ,
      0 ≤ (quadraticForm (goodBranchBlockOp μ f goodSet x) v).re := fun x =>
    goodBranchBlockOp_quadraticForm_re_nonneg_of_integrable μ f goodSet x (h_int x).restrict
  have h_trace_le_one :
      ∀ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1 :=
    goodBranchBlockOp_trace_le_one_of_integrable
      μ ρ_mix f goodSet hMeas h_int hf_lin
  have h_weight_le_one :
      ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re ≤ 1 :=
    goodBranchBlockOp_weight_le_one_of_integrable
      μ ρ_mix f goodSet hMeas h_int hf_lin
  rcases exists_goodBranchCQState_of_block_conditions
      μ f goodSet h_herm h_psd h_trace_le_one h_weight_le_one with
    ⟨ρ_good, hρ_good_eq⟩
  refine ⟨ρ_good, hρ_good_eq, ?_⟩
  intro x
  rw [hρ_good_eq x]
  exact goodBranchBlockOp_opLe_stateMap_of_integrable
    μ ρ_mix f goodSet hMeas h_int hf_lin x

/-- The total weight of a CQ state whose blocks are the good branch is the
sum of the good-branch block traces. -/
lemma goodBranchCQState_weight_eq_of_stateMap_eq
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (ρ_good : CQState X dE)
    (hρ_good_eq :
      ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) :
    (∑ x : X, (ρ_good.stateMap x).trace) =
      ∑ x : X, (goodBranchBlockOp μ f goodSet x).trace.re := by
  apply Finset.sum_congr rfl
  intro x _
  unfold SubDensityOp.trace
  rw [hρ_good_eq x]

/-- Construct the restricted good-branch CQ state from explicit block
integrability hypotheses, together with the two facts needed by the
trace-deficit smoothing bridge. -/
theorem exists_goodBranchCQState_of_integrable_traceDeficit
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (hρ_norm : ∑ x : X, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_trace :
      ∑ x : X, (badBranchBlockOp μ f goodSet x).trace.re ≤ ε) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) ∧
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      1 - (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε := by
  rcases exists_goodBranchCQState_of_integrable
      μ ρ_mix f goodSet hMeas h_int hf_lin with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix⟩
  refine ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, ?_⟩
  · have htrace := goodBranchBlockOp_trace_deficit_le_of_badBranch_trace
      μ ρ_mix f goodSet hMeas hρ_norm h_int hf_lin h_badBranch_trace
    rw [goodBranchCQState_weight_eq_of_stateMap_eq μ f goodSet ρ_good hρ_good_eq]
    exact htrace

/-- Entrywise-`Matrix.of` variant of
`exists_goodBranchCQState_of_integrable_traceDeficit`, matching the current
de Finetti post-filter bad-branch hypothesis. -/
theorem exists_goodBranchCQState_of_integrable_traceNormBound
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (hρ_norm : ∑ x : X, (ρ_mix.stateMap x).trace = 1)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) ∧
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      1 - (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε := by
  exact exists_goodBranchCQState_of_integrable_traceDeficit
    μ ρ_mix f goodSet hMeas hρ_norm h_int hf_lin
    (by simpa [badBranchBlockOp] using h_badBranch_traceNorm)

/-- Construct the restricted good-branch CQ state for a subnormalized mixture.
The final estimate is the actual trace gap between the mixture and good branch. -/
theorem exists_goodBranchCQState_of_integrable_traceGap
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_trace :
      ∑ x : X, (badBranchBlockOp μ f goodSet x).trace.re ≤ ε) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) ∧
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      (∑ x : X, (ρ_mix.stateMap x).trace) -
          (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε := by
  rcases exists_goodBranchCQState_of_integrable
      μ ρ_mix f goodSet hMeas h_int hf_lin with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix⟩
  refine ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, ?_⟩
  · have htrace := goodBranchBlockOp_trace_gap_le_of_badBranch_trace
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_trace
    rw [goodBranchCQState_weight_eq_of_stateMap_eq μ f goodSet ρ_good hρ_good_eq]
    exact htrace

/-- Entrywise-`Matrix.of` variant of the subnormalized good-branch
construction, matching the current de Finetti post-filter bad-branch
hypothesis. -/
theorem exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
    {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    {ε : ℝ}
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x) ∧
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      (∑ x : X, (ρ_mix.stateMap x).trace) -
          (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε := by
  exact exists_goodBranchCQState_of_integrable_traceGap
    μ ρ_mix f goodSet hMeas h_int hf_lin
    (by simpa [badBranchBlockOp] using h_badBranch_traceNorm)
end InfoTheory.SmoothMinEntropy

end
