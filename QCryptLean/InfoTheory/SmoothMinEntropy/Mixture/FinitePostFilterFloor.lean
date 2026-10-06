import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.PostFilter
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.MixtureFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothCompactness
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Probability.ConditionalProbability

/-!
# Finite post-filter entropy floors

Finite mixtures of feasible smoothing witnesses give extended entropy floors. Good-branch, heavy-
component and post-filter constructions retain their actual trace-gap and distance charges; no
real-supremum boundedness or positive mixture-weight guard is required.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder ENNReal

-- Bochner integrability of `Op`-valued block maps uses the Frobenius norm on matrices, as in
-- `PostFilter.lean` / `GoodBranch.lean`.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Sum over a finite type of a function obtained by extending along an embedding `e : σ ↪ ι`,
where the extension vanishes off the range of `e`, equals the sum of the original function. -/
private lemma sum_eq_sum_of_embedding {σ ι : Type*} [Fintype σ] [Fintype ι] {M : Type*}
    [AddCommMonoid M] (e : σ ↪ ι) (g : ι → M) (gσ : σ → M)
    (hg1 : ∀ i, g (e i) = gσ i) (hg2 : ∀ j, (¬ ∃ i, e i = j) → g j = 0) :
    ∑ j, g j = ∑ i, gσ i := by
  classical
  have h2 : ∑ b ∈ Finset.univ.map e, g b = ∑ j, g j :=
    Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hg2 j (by
      rw [Finset.mem_map] at hj
      push_neg at hj
      rintro ⟨i, rfl⟩
      exact hj i (Finset.mem_univ i) rfl))
  rw [← h2, Finset.sum_map Finset.univ e g]
  exact Finset.sum_congr rfl (fun i _ => hg1 i)

/-- **Finite-dimensional Carathéodory compactness.** In a finite-dimensional real normed space the
convex hull of a compact set is compact. The convex hull is realised as the continuous image of the
compact product `stdSimplex × (range-in-s tuples)` of `d + 1` points, with `d = finrank`; the ⊆
direction is Carathéodory (`eq_pos_convex_span_of_mem_convexHull`) padded to `d + 1` points. -/
private lemma isCompact_convexHull_of_isCompact_finiteDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  set d := Module.finrank ℝ E with hd
  have hgcont : Continuous (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E) =>
      ∑ i, p.1 i • p.2 i) := by
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd)
  have hKcompact : IsCompact ((stdSimplex ℝ (Fin (d + 1))) ×ˢ
      (Set.univ.pi (fun _ : Fin (d + 1) => s))) :=
    (isCompact_stdSimplex (Fin (d + 1))).prod (isCompact_univ_pi (fun _ => hs))
  have himg : convexHull ℝ s = (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E) =>
      ∑ i, p.1 i • p.2 i) '' ((stdSimplex ℝ (Fin (d + 1))) ×ˢ
        (Set.univ.pi (fun _ : Fin (d + 1) => s))) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨σ, hσfin, z, w, hzs, haff, hwpos, hwsum, hwcomb⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      letI : Fintype σ := hσfin
      have hσne : Nonempty σ := by
        rcases isEmpty_or_nonempty σ with hE | hN
        · exfalso
          rw [Finset.univ_eq_empty, Finset.sum_empty] at hwsum
          exact one_ne_zero hwsum.symm
        · exact hN
      have hcard : Fintype.card σ ≤ Fintype.card (Fin (d + 1)) := by
        rw [Fintype.card_fin]
        have h1 := AffineIndependent.card_le_finrank_succ haff
        have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ d := by
          have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
          rwa [← hd] at this
        omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      obtain ⟨i₀⟩ := hσne
      have hpad : z i₀ ∈ s := hzs ⟨i₀, rfl⟩
      set W : Fin (d + 1) → ℝ := Function.extend (⇑e) w (fun _ => 0) with hWdef
      set Z : Fin (d + 1) → E := Function.extend (⇑e) z (fun _ => z i₀) with hZdef
      have hWe : ∀ i, W (e i) = w i := fun i => by
        rw [hWdef]; exact e.injective.extend_apply w _ i
      have hZe : ∀ i, Z (e i) = z i := fun i => by
        rw [hZdef]; exact e.injective.extend_apply z _ i
      have hWout : ∀ j, (¬ ∃ i, e i = j) → W j = 0 := fun j hj => by
        rw [hWdef]; exact Function.extend_apply' _ _ j hj
      have hZout : ∀ j, (¬ ∃ i, e i = j) → Z j = z i₀ := fun j hj => by
        rw [hZdef]; exact Function.extend_apply' _ _ j hj
      have hWnonneg : ∀ j, 0 ≤ W j := by
        intro j
        rcases em (∃ i, e i = j) with ⟨i, rfl⟩ | hj
        · rw [hWe i]; exact (hwpos i).le
        · rw [hWout j hj]
      have hWsum : ∑ j, W j = 1 := by
        rw [sum_eq_sum_of_embedding e W w hWe hWout]; exact hwsum
      have hZmem : ∀ j, Z j ∈ s := by
        intro j
        rcases em (∃ i, e i = j) with ⟨i, rfl⟩ | hj
        · rw [hZe i]; exact hzs ⟨i, rfl⟩
        · rw [hZout j hj]; exact hpad
      have hgeq : (∑ i, W i • Z i) = x :=
        calc ∑ i, W i • Z i = ∑ i, w i • z i :=
              sum_eq_sum_of_embedding e (fun j => W j • Z j) (fun i => w i • z i)
                (fun i => by change W (e i) • Z (e i) = w i • z i; rw [hWe i, hZe i])
                (fun j hj => by change W j • Z j = 0; rw [hWout j hj, zero_smul])
          _ = x := hwcomb
      exact ⟨(W, Z), ⟨⟨hWnonneg, hWsum⟩, Set.mem_univ_pi.mpr hZmem⟩, hgeq⟩
    · rintro x ⟨⟨W, Z⟩, ⟨hW, hZ⟩, rfl⟩
      have hWsum : ∑ i, W i = 1 := hW.2
      have hZmem : ∀ i, Z i ∈ s := Set.mem_univ_pi.mp hZ
      have hcm : (∑ i, W i • Z i) = Finset.univ.centerMass W Z :=
        (Finset.centerMass_eq_of_sum_1 _ Z hWsum).symm
      change (∑ i, W i • Z i) ∈ convexHull ℝ s
      rw [hcm]
      exact Finset.centerMass_mem_convexHull _ (fun i _ => hW.1 i)
        (by rw [hWsum]; exact one_pos) (fun i _ => hZmem i)
  rw [himg]
  exact hKcompact.image hgcont

/-- **Piece 1 (`[48]` finite convex decomposition of the good branch).**

The restricted Bochner integral `∫_{goodSet} ((f τ).stateMap x).toOp dμ` of a continuous,
block-operator-valued family `f` over a **closed** good set is a *finite* sub-convex combination of
the family evaluated at finitely many points **inside** the good set: there are nonnegative weights
`p : Fin N → ℝ` with `∑ p ≤ 1` and points `ψ : Fin N → DensityOp d`, each `ψ z ∈ goodSet`, with

`∫_{goodSet} ((f τ).stateMap x).toOp i j dμ = ∑ z, p_z • ((f (ψ z)).stateMap x).toOp i j`

for every classical outcome `x` and matrix entry `i, j`.

Because `DensityOp d` is compact and `goodSet ∩ P` is closed (`P` closed), it is compact; the
continuous image `f '' (goodSet ∩ P)` is then compact, so its convex hull is closed and equals its
closure.  Since `μ` is a.e. supported on the closed set `P` (`hP_ae`), the restricted–normalised
probability integral lies in this closed convex hull (`Convex.integral_mem`), and finite-dimensional
Carathéodory expresses it as a finite convex combination of points of `f '' (goodSet ∩ P)`, i.e. of
`f` evaluated at points of `goodSet ∩ P` — so each carathéodory point lies in **both** `goodSet`
**and** `P`.  Scaling the convex (sum `= 1`) weights by `μ(goodSet) ≤ 1` returns the sub-convex
(`∑ ≤ 1`) decomposition of the *unnormalised* restricted integral.

The auxiliary closed set `P` lets the consumer pin the decomposition points to the measure's support
(e.g. the closed pure-state locus `{σ | σ.IsPure}`, on which the de Finetti Haar measure is
supported
by `deFinetti_haarMeasure_isProductStateMeasure`); at `P = Set.univ` (with `hP_ae` trivial) this
recovers the bare `goodSet`-only decomposition.

Proved via the `Convex.integral_mem` + finite-dimensional Carathéodory assembly (Nahar et al. Lemma
14
`[48]`).  References: Nahar et al. 2024 (arXiv:2403.11851) App. B, Lemma 14 `[48]`; Mathlib
`Convex.integral_mem` (`Reduction.Convex.Integral`). -/
theorem integralRestrict_eq_finite_subConvexCombination
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P) :
    ∃ (N : ℕ) (p : Fin N → ℝ) (ψ : Fin N → DensityOp d),
      (∀ z, 0 ≤ p z) ∧ (∑ z, p z ≤ 1) ∧ (∀ z, ψ z ∈ goodSet) ∧ (∀ z, ψ z ∈ P) ∧
      (∀ (x : X) (i j : Fin dE),
        (∫ τ in goodSet, ((f τ).stateMap x).toOp i j ∂μ.measure)
          = ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp i j) := by
  classical
  haveI hprob : IsProbabilityMeasure μ.measure := μ.isProbability
  set F : DensityOp d → (X → Op dE) := fun τ x => ((f τ).stateMap x).toOp with hFdef
  have hFcont : Continuous F := continuous_pi hcont
  have hGoodCompact : IsCompact goodSet :=
    hClosed.isCompact
  have hPgoodCompact : IsCompact (goodSet ∩ P) :=
    (hClosed.inter hP_closed).isCompact
  have hImgCompact : IsCompact (F '' (goodSet ∩ P)) := hPgoodCompact.image hFcont
  have hHullClosed : IsClosed (convexHull ℝ (F '' (goodSet ∩ P))) :=
    (isCompact_convexHull_of_isCompact_finiteDim hImgCompact).isClosed
  have hFint_restrict : Integrable F (μ.measure.restrict goodSet) :=
    ContinuousOn.integrableOn_compact hGoodCompact hFcont.continuousOn
  by_cases hzero : μ.measure goodSet = 0
  · refine ⟨0, fun _ => 0, fun z => z.elim0, fun z => z.elim0, by simp, fun z => z.elim0,
      fun z => z.elim0, ?_⟩
    intro x i j
    rw [MeasureTheory.setIntegral_measure_zero _ hzero]
    simp
  · -- positive-mass branch
    set m : ℝ := (μ.measure goodSet).toReal with hm
    have hmne_top : μ.measure goodSet ≠ ∞ := measure_ne_top _ _
    have hmpos : 0 < m := by rw [hm]; exact ENNReal.toReal_pos hzero hmne_top
    have hmle : m ≤ 1 := by
      rw [hm]
      have hle : μ.measure goodSet ≤ 1 := by
        calc μ.measure goodSet ≤ μ.measure Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      calc (μ.measure goodSet).toReal ≤ (1 : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono (by norm_num) hle
        _ = 1 := by norm_num
    set ν : Measure (DensityOp d) :=
      (μ.measure goodSet)⁻¹ • μ.measure.restrict goodSet with hνdef
    haveI hνprob : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hzero
    have hcinv_ne_zero : (μ.measure goodSet)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmne_top
    have hcinv_ne_top : (μ.measure goodSet)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hzero
    have hFint_ν : Integrable F ν := by
      rw [hνdef]
      exact (MeasureTheory.integrable_smul_measure hcinv_ne_zero hcinv_ne_top).mpr hFint_restrict
    set Y : X → Op dE := ∫ τ in goodSet, F τ ∂μ.measure with hYdef
    have hae : ∀ᵐ τ ∂ν, F τ ∈ convexHull ℝ (F '' (goodSet ∩ P)) := by
      rw [hνdef]
      refine MeasureTheory.Measure.ae_smul_measure ?_ _
      filter_upwards [MeasureTheory.ae_restrict_mem hMeas,
        MeasureTheory.ae_restrict_of_ae hP_ae] with τ hτ hτP
      exact subset_convexHull ℝ _ (Set.mem_image_of_mem F ⟨hτ, hτP⟩)
    have hmem : (∫ τ, F τ ∂ν) ∈ convexHull ℝ (F '' (goodSet ∩ P)) :=
      Convex.integral_mem (convex_convexHull ℝ _) hHullClosed hae hFint_ν
    obtain ⟨σ, hσfin, weq, zpt, hw0, hwsum, hzmem, hcomb⟩ :=
      mem_convexHull_iff_exists_fintype.mp hmem
    letI : Fintype σ := hσfin
    choose ψ0 hψ0mem hψ0eq using hzmem
    have hintν : (∫ τ, F τ ∂ν) = m⁻¹ • Y := by
      rw [hνdef, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
    have hYeq : Y = ∑ s, (m * weq s) • F (ψ0 s) := by
      have hY0 : Y = m • (∫ τ, F τ ∂ν) := by
        rw [hintν, smul_smul, mul_inv_cancel₀ (ne_of_gt hmpos), one_smul]
      rw [hY0, ← hcomb, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [smul_smul, hψ0eq s]
    have hYentry : ∀ (x : X) (i j : Fin dE),
        Y x i j = ∫ τ in goodSet, F τ x i j ∂μ.measure := by
      intro x i j
      set L : (X → Op dE) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
        { toFun := fun g => g x i j, map_add' := fun a b => rfl, map_smul' := fun c a => rfl }
        with hLdef
      have hcomm := ContinuousLinearMap.integral_comp_comm L hFint_restrict
      exact hcomm.symm
    have hentry_σ : ∀ (x : X) (i j : Fin dE),
        Y x i j = ∑ s, (↑(m * weq s) : ℂ) • ((f (ψ0 s)).stateMap x).toOp i j := by
      intro x i j
      rw [hYeq]
      simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, hFdef]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Complex.real_smul, smul_eq_mul]
    set e : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm with hedef
    refine ⟨Fintype.card σ, fun z => m * weq (e z), fun z => ψ0 (e z), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun z => mul_nonneg hmpos.le (hw0 (e z))
    · calc ∑ z, m * weq (e z) = ∑ s, m * weq s := Equiv.sum_comp e (fun s => m * weq s)
        _ = m * ∑ s, weq s := (Finset.mul_sum _ _ _).symm
        _ = m * 1 := by rw [hwsum]
        _ = m := mul_one m
        _ ≤ 1 := hmle
    · exact fun z => (hψ0mem (e z)).1
    · exact fun z => (hψ0mem (e z)).2
    · intro x i j
      rw [show (∫ τ in goodSet, ((f τ).stateMap x).toOp i j ∂μ.measure) = Y x i j from
        (hYentry x i j).symm, hentry_σ x i j]
      exact (Equiv.sum_comp e
        (fun s => (↑(m * weq s) : ℂ) • ((f (ψ0 s)).stateMap x).toOp i j)).symm

/-! ## Sub-probability (`∑ p ≤ 1`) generalisation of the finite mixture floor

These private helpers transcribe the `∑ p = 1` mixture machinery
(`finMix`, `isFeasible_mixture`, `conditionalMinEntropy_mixture_ge_inf_component`,
`CQState.purifiedDistance_mixture_le_max`) to the sub-probability weight regime
`∑ p ≤ 1`.  The unsmoothed floor is generalised directly (scaling the reference
domination by the missing mass `1 - ∑ p ≥ 0` only **raises** the feasibility slack);
the purified-distance mixture bound is reduced to the `∑ p = 1` case by augmenting the
finite family with one extra zero-weight slack component `(zeroCQ)` of weight
`1 - ∑ p`, which contributes nothing to either mixture and trivially satisfies
`P(zeroCQ, zeroCQ) = 0 ≤ ε`.  The sub-normalization scaling inequality is
`P(Σ w_z ρ_z, Σ w_z σ_z) ≤ max_z P(ρ_z, σ_z)` for `∑ w ≤ 1`. -/

/-- Sub-probability mixture block: mirrors `finMixBlock` but with weights summing to
**at most** one. -/
def finMixSubBlock {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (x : X) : SubDensityOp n where
  toOp := ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp
  isHermitian := by
    have hpsd : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro z _
      exact (posSemidefOp_implies_mathlib ((comp z).stateMap x).toPosSemidefOp).smul
        (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
    exact hpsd.isHermitian
  pos_semidef := by
    intro v
    have hpsd : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro z _
      exact (posSemidefOp_implies_mathlib ((comp z).stateMap x).toPosSemidefOp).smul
        (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
    exact posSemidef_re_quadraticForm_nonneg hpsd v
  trace_le_one := by
    have htrace : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).trace.re
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      rw [Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    rw [htrace]
    calc ∑ z, p z * ((comp z).stateMap x).trace
        ≤ ∑ z, p z * 1 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          exact mul_le_mul_of_nonneg_left
            ((comp z).classicalMarginal_le_one x) (hp_nonneg z)
      _ = ∑ z, p z := by simp
      _ ≤ 1 := hp_sum_le

/-- Sub-probability finite mixture of CQ states (weights `∑ p ≤ 1`). -/
def finMixSub {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) : CQState X n where
  stateMap x := finMixSubBlock p hp_nonneg hp_sum_le comp x
  weight_le_one := by
    have hblock : ∀ x : X, (finMixSubBlock p hp_nonneg hp_sum_le comp x).trace
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      intro x
      change (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).trace.re
        = ∑ z, p z * ((comp z).stateMap x).trace
      rw [Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    have hswap : ∑ x : X, (finMixSubBlock p hp_nonneg hp_sum_le comp x).trace
        = ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) := by
      simp_rw [hblock, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    calc ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace)
        ≤ ∑ z, p z * 1 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          exact mul_le_mul_of_nonneg_left (comp z).weight_le_one (hp_nonneg z)
      _ = ∑ z, p z := by simp
      _ ≤ 1 := hp_sum_le

@[simp]
lemma finMixSub_stateMap_toOp {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (x : X) :
    ((finMixSub p hp_nonneg hp_sum_le comp).stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp :=
  rfl

/-- Feasibility passes to a nonnegative mixture when the target reference dominates the
weighted component references. No bound on `∑ z, p z` is needed. -/
lemma isFeasible_subMixture_of_reference_domination
    {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X,
      (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σcomp : Z → SubDensityOp n) (σ : SubDensityOp n)
    (hσdom : opLe (∑ z, (p z : ℂ) • (σcomp z).toOp) σ.toOp)
    {t : ℝ} (htnn : 0 ≤ t)
    (ht : ∀ z, isFeasible (comp z) (σcomp z) t) : isFeasible ρ σ t := by
  refine ⟨htnn, fun x => ?_⟩
  rw [hmix x]
  have hsum : opLe (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
      (∑ z, (p z : ℂ) • (Complex.ofReal t • (σcomp z).toOp)) := by
    apply Quantum.Channels.opLe_sum
    intro z
    exact opLe_smul_nonneg (hp_nonneg z) ((ht z).2 x)
  apply opLe_trans hsum
  have hswap : (∑ z, (p z : ℂ) • (Complex.ofReal t • (σcomp z).toOp)) =
      Complex.ofReal t • ∑ z, (p z : ℂ) • (σcomp z).toOp := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun z _ => smul_comm (p z : ℂ) (t : ℂ) (σcomp z).toOp)
  rw [hswap]
  exact opLe_smul_nonneg htnn hσdom

/-- **Sub-probability feasibility of a mixture.** If `t ≥ 0` is feasible for every
component of a nonnegative **sub**-convex combination (`∑ p ≤ 1`), it is feasible for
the mixture: `t·σ − ρ_A(x) = (1−∑p)·t·σ + Σ_z p_z (t·σ − (comp z)_A(x))` is a sum of
PSD blocks (the first because `1−∑p ≥ 0` and `t·σ` is PSD). -/
lemma isFeasible_subMixture {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) {t : ℝ}
    (ht : ∀ z, isFeasible (comp z) σ t) (htnn : 0 ≤ t) : isFeasible ρ σ t := by
  refine ⟨htnn, fun x => ?_⟩
  rw [hmix x]
  have hstep1 : opLe (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
      (∑ z, (p z : ℂ) • (Complex.ofReal t • σ.toOp)) := by
    apply Quantum.Channels.opLe_sum
    intro z
    exact opLe_smul_nonneg (hp_nonneg z) ((ht z).2 x)
  have hstep2 : opLe (∑ z, (p z : ℂ) • (Complex.ofReal t • σ.toOp))
      (Complex.ofReal t • σ.toOp) := by
    have hsum_eq : (∑ z, (p z : ℂ) • (Complex.ofReal t • σ.toOp))
        = (Complex.ofReal (∑ z, p z)) • (Complex.ofReal t • σ.toOp) := by
      rw [← Finset.sum_smul, Complex.ofReal_sum]
    rw [hsum_eq]
    intro v
    rw [quadraticForm_ofReal_smul]
    have hpsd_t : 0 ≤ (quadraticForm (Complex.ofReal t • σ.toOp) v).re := by
      rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg htnn (σ.pos_semidef v)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc (∑ z, p z) * (quadraticForm (Complex.ofReal t • σ.toOp) v).re
        ≤ 1 * (quadraticForm (Complex.ofReal t • σ.toOp) v).re :=
          mul_le_mul_of_nonneg_right hp_sum_le hpsd_t
      _ = (quadraticForm (Complex.ofReal t • σ.toOp) v).re := one_mul _
  exact opLe_trans hstep1 hstep2

/-- **Sub-probability purified-distance mixture bound.** The `∑ p ≤ 1` generalisation
of `CQState.purifiedDistance_mixture_le_max`, obtained by augmenting the finite family
with one zero-weight slack component (`zeroCQ`) of weight `1 - ∑ p`, which is contributed
to neither mixture and satisfies `P(zeroCQ, zeroCQ) = 0 ≤ ε`. -/
lemma purifiedDistance_subMixture_le_max
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (a b : Z → CQState X n) (ρ ρ' : CQState X n)
    (hρ : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((a z).stateMap x).toOp)
    (hρ' : ∀ x : X, (ρ'.stateMap x).toOp = ∑ z, (p z : ℂ) • ((b z).stateMap x).toOp)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomp : ∀ z, CQState.purifiedDistance (a z) (b z) ≤ ε) :
    CQState.purifiedDistance ρ ρ' ≤ ε := by
  classical
  set w0 : ℝ := 1 - ∑ z, p z with hw0
  have hw0_nn : 0 ≤ w0 := by rw [hw0]; linarith [hp_sum_le]
  set p' : Option Z → ℝ := fun o => Option.elim o w0 p with hp'def
  set a' : Option Z → CQState X n := fun o => Option.elim o zeroCQ a with ha'def
  set b' : Option Z → CQState X n := fun o => Option.elim o zeroCQ b with hb'def
  have hp'_nonneg : ∀ o, 0 ≤ p' o := by
    intro o; cases o with
    | none => exact hw0_nn
    | some z => exact hp_nonneg z
  have hp'_sum : ∑ o, p' o = 1 := by
    rw [Fintype.sum_option]
    change w0 + ∑ z, p z = 1
    rw [hw0]; ring
  have hzero_block : ∀ x : X, ((zeroCQ (X := X) (n := n)).stateMap x).toOp = 0 := fun _ => rfl
  have hρaug : ∀ x : X, (ρ.stateMap x).toOp
      = ∑ o, (p' o : ℂ) • ((a' o).stateMap x).toOp := by
    intro x
    rw [Fintype.sum_option]
    have hnone : (p' none : ℂ) • ((a' none).stateMap x).toOp = 0 := by
      change (w0 : ℂ) • ((zeroCQ (X := X) (n := n)).stateMap x).toOp = 0
      rw [hzero_block x, smul_zero]
    rw [hnone, zero_add, hρ x]
    rfl
  have hρ'aug : ∀ x : X, (ρ'.stateMap x).toOp
      = ∑ o, (p' o : ℂ) • ((b' o).stateMap x).toOp := by
    intro x
    rw [Fintype.sum_option]
    have hnone : (p' none : ℂ) • ((b' none).stateMap x).toOp = 0 := by
      change (w0 : ℂ) • ((zeroCQ (X := X) (n := n)).stateMap x).toOp = 0
      rw [hzero_block x, smul_zero]
    rw [hnone, zero_add, hρ' x]
    rfl
  have hcompaug : ∀ o, CQState.purifiedDistance (a' o) (b' o) ≤ ε := by
    intro o; cases o with
    | none =>
      change CQState.purifiedDistance (zeroCQ (X := X) (n := n))
        (zeroCQ (X := X) (n := n)) ≤ ε
      rw [CQState.purifiedDistance_self_zero]; exact hε
    | some z => exact hcomp z
  exact CQState.purifiedDistance_mixture_le_max p' hp'_nonneg hp'_sum a' b' ρ ρ'
    hρaug hρ'aug hε hcompaug

/-- A common extended conditional entropy floor passes to a mixture whenever its reference
dominates the weighted component references, including zero components and zero mixtures. -/
theorem conditionalMinEntropy_subMixture_ge_inf_component_of_reference_domination
    {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σcomp : Z → SubDensityOp n) (σ : SubDensityOp n)
    (hσdom : opLe (∑ z, (p z : ℂ) • (σcomp z).toOp) σ.toOp)
    (k : ℝ) (hfloor : ∀ z, ENNReal.ofReal k ≤ conditionalMinEntropy (comp z) (σcomp z)) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ := by
  by_cases hk : k ≤ 0
  · simp only [ENNReal.ofReal_of_nonpos hk, zero_le]
  · exact ofReal_le_conditionalMinEntropy_of_isFeasible ρ σ k
      (isFeasible_subMixture_of_reference_domination p hp_nonneg comp ρ hmix σcomp σ
        hσdom (Real.rpow_nonneg (by norm_num) _) fun z =>
          isFeasible_of_ofReal_le_conditionalMinEntropy (comp z) (σcomp z)
            (lt_of_not_ge hk) (hfloor z))

/-- A finite subprobability mixture inherits common extended smooth entropy floors.
The complete-lattice supremum includes zero witnesses and requires no mass or boundedness guard. -/
theorem smoothMinEntropy_subMixture_ge_inf_component
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hfloor : ∀ z, ENNReal.ofReal k ≤ smoothMinEntropy ε (comp z) σ) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  classical
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  have hex : ∀ z, ∃ τ : CQState X n,
      CQState.purifiedDistance (comp z) τ ≤ ε ∧ isFeasible τ σ (2 ^ (-(r : ℝ))) := by
    intro z
    obtain ⟨τ, hd, _, hτ⟩ :=
      smoothMinEntropy_exists_approx (comp z) σ r (hlt.trans_le (hfloor z))
    exact ⟨τ, hd, isFeasible_of_ofReal_le_conditionalMinEntropy τ σ hr
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hτ.le)⟩
  choose comp' hd ht using hex
  let ρ' := finMixSub p hp_nonneg hp_sum_le comp'
  have hρ'mix := finMixSub_stateMap_toOp p hp_nonneg hp_sum_le comp'
  have hpd := purifiedDistance_subMixture_le_max p hp_nonneg hp_sum_le
    comp comp' ρ ρ' hmix hρ'mix hε hd
  simpa only [ENNReal.ofReal_coe_nnreal] using
    smoothMinEntropy_ge_of_isFeasible ρ ρ' σ r hpd
      (isFeasible_subMixture p hp_nonneg hp_sum_le comp' ρ' hρ'mix σ ht
        (Real.rpow_nonneg (by norm_num) _))

/-- Extended smooth floors on components heavier than `ε²` pass to a subprobability mixture
whose reference dominates the component references. Light components use the zero witness. -/
theorem smoothMinEntropy_subMixture_ge_heavy_component
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σcomp : Z → SubDensityOp n) (σ : SubDensityOp n)
    (hσdom : opLe (∑ z, (p z : ℂ) • (σcomp z).toOp) σ.toOp)
    (k : ℝ)
    (hfloor : ∀ z, ε ^ 2 < ∑ x : X, ((comp z).stateMap x).trace →
      ENNReal.ofReal k ≤ smoothMinEntropy ε (comp z) (σcomp z)) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  classical
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  have hex : ∀ z, ∃ τ : CQState X n,
      CQState.purifiedDistance (comp z) τ ≤ ε ∧
        isFeasible τ (σcomp z) (2 ^ (-(r : ℝ))) := by
    intro z
    by_cases hz : ε ^ 2 < ∑ x : X, ((comp z).stateMap x).trace
    · obtain ⟨τ, hd, _, hτ⟩ := smoothMinEntropy_exists_approx
        (comp z) (σcomp z) r (hlt.trans_le (hfloor z hz))
      exact ⟨τ, hd, isFeasible_of_ofReal_le_conditionalMinEntropy τ (σcomp z) hr
        (by simpa only [ENNReal.ofReal_coe_nnreal] using hτ.le)⟩
    · refine ⟨zeroCQ, ?_, isFeasible_zeroCQ (σcomp z) (Real.rpow_nonneg (by norm_num) _)⟩
      rw [CQState.purifiedDistance_zeroCQ]
      exact Real.sqrt_le_iff.mpr ⟨hε, le_of_not_gt hz⟩
  choose comp' hd ht using hex
  let ρ' := finMixSub p hp_nonneg hp_sum_le comp'
  have hρ'mix := finMixSub_stateMap_toOp p hp_nonneg hp_sum_le comp'
  have hpd := purifiedDistance_subMixture_le_max p hp_nonneg hp_sum_le
    comp comp' ρ ρ' hmix hρ'mix hε hd
  simpa only [ENNReal.ofReal_coe_nnreal] using
    smoothMinEntropy_ge_of_isFeasible ρ ρ' σ r hpd
      (isFeasible_subMixture_of_reference_domination p hp_nonneg comp' ρ' hρ'mix
        σcomp σ hσdom (Real.rpow_nonneg (by norm_num) _) ht)

/-- Finite component floors give an extended entropy floor on the retained branch at radius
`εBar`, with bad-branch mass charged only to the trace gap. -/
theorem
    smoothMinEntropy_ge_goodBranch_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized_linear
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (f τ) σ_ref) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      (∑ x : X, (ρ_mix.stateMap x).trace) - (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε ∧
      ENNReal.ofReal k ≤ smoothMinEntropy εBar ρ_good σ_ref := by
  letI : IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  obtain ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hClosed.measurableSet h_int hf_lin h_badBranch_traceNorm
  refine ⟨ρ_good, hρ_good_le_mix, htrace_gap, ?_⟩
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ f goodSet hClosed.measurableSet
      hClosed hcont P hP_closed hP_ae
  have hmix : ∀ x : X, (ρ_good.stateMap x).toOp =
      ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp := by
    intro x
    ext i j
    rw [hρ_good_eq x]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp x i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  exact smoothMinEntropy_subMixture_ge_inf_component εBar hεBar_nonneg
    p hp_nonneg hp_sum_le (fun z => f (ψ z)) ρ_good hmix σ_ref k
    (fun z => hf_smoothFloor (ψ z) (hψ_mem z) (hψ_memP z))

/-- Finite component smooth floors pass to a post-filter mixture at radius
`εBar + sqrt (2 * ε)`, without a retained-mass or finite-entropy hypothesis. -/
theorem smoothMinEntropy_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (σ_ref : SubDensityOp dE)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (f τ) σ_ref) :
    ENNReal.ofReal k ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  letI : IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  have hε_nonneg : 0 ≤ ε := (Finset.sum_nonneg fun x _ =>
    (Complex.nonneg_iff.mp (badBranchBlockOp_posSemidef_of_integrable
      μ f goodSet x (h_int x).restrict).trace_nonneg).1).trans h_badBranch_traceNorm
  obtain ⟨ρ_good, hρ_good_le_mix, htrace_gap, hfloor⟩ :=
    smoothMinEntropy_ge_goodBranch_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized_linear
      μ ρ_mix f σ_ref hf_lin hcont goodSet hClosed P hP_closed hP_ae
      k εBar ε hεBar_nonneg h_badBranch_traceNorm hf_smoothFloor
  simpa only [add_comm] using hfloor.trans (smoothMinEntropy_change_center
    ρ_good ρ_mix σ_ref
    (CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap))

/-- Heavy-component floors against their own marginals give an extended post-filter floor
against the full mixture marginal. Light components and zero retained mass are admitted. -/
theorem smoothMinEntropy_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor
    {d dE : ℕ} [NeZero d] [NeZero dE]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState X dE)
    (f : DensityOp d → CQState X dE)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ)
    (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
        ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P →
      εBar ^ 2 < ∑ x : X, ((f τ).stateMap x).trace →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (f τ) (f τ).quantumMarginal) :
    ENNReal.ofReal k ≤
      smoothMinEntropy (εBar + Real.sqrt (2 * ε)) ρ_mix ρ_mix.quantumMarginal := by
  letI : IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  have hε_nonneg : 0 ≤ ε := (Finset.sum_nonneg fun x _ =>
    (Complex.nonneg_iff.mp (badBranchBlockOp_posSemidef_of_integrable
      μ f goodSet x (h_int x).restrict).trace_nonneg).1).trans h_badBranch_traceNorm
  rcases exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hClosed.measurableSet h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩
  have hcenter : CQState.purifiedDistance ρ_mix ρ_good ≤ Real.sqrt (2 * ε) :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ f goodSet hClosed.measurableSet
      hClosed hcont P hP_closed hP_ae
  have hmix : ∀ x : X, (ρ_good.stateMap x).toOp =
      ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp := by
    intro x
    ext i j
    rw [hρ_good_eq x]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp x i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hmarg : (∑ z, (p z : ℂ) • (f (ψ z)).quantumMarginal.toOp) =
      ρ_good.quantumMarginal.toOp := by
    change (∑ z, (p z : ℂ) • ∑ x, ((f (ψ z)).stateMap x).toOp) =
      ∑ x, (ρ_good.stateMap x).toOp
    simp_rw [hmix, Finset.smul_sum]
    exact Finset.sum_comm
  have hσdom : opLe (∑ z, (p z : ℂ) • (f (ψ z)).quantumMarginal.toOp)
      ρ_mix.quantumMarginal.toOp := by
    rw [hmarg]
    exact Quantum.Channels.opLe_sum _ _ hρ_good_le_mix
  have hgood_floor : ENNReal.ofReal k ≤
      smoothMinEntropy εBar ρ_good ρ_mix.quantumMarginal :=
    smoothMinEntropy_subMixture_ge_heavy_component εBar hεBar_nonneg
      p hp_nonneg hp_sum_le (fun z => f (ψ z)) ρ_good hmix
      (fun z => (f (ψ z)).quantumMarginal) ρ_mix.quantumMarginal hσdom k
      (fun z => hf_smoothFloor (ψ z) (hψ_mem z) (hψ_memP z))
  simpa only [add_comm] using hgood_floor.trans
    (smoothMinEntropy_change_center ρ_good ρ_mix ρ_mix.quantumMarginal hcenter)

/-- A nonzero subprobability mixture of feasible components inherits their common signed
conditional entropy floor. -/
private lemma conditionalMinEntropyReal_subMixture_ge_inf_component
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (hp_sum_pos : 0 < ∑ z, p z)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hfeas_comp : ∀ z, hasFeasibleLambda (comp z) σ)
    (hfloor : ∀ z, k ≤ conditionalMinEntropyReal (comp z) σ) :
    k ≤ conditionalMinEntropyReal ρ σ := by
  classical
  have htnn : (0 : ℝ) ≤ 2 ^ (-k) := Real.rpow_nonneg (by norm_num) _
  have hlamz_le : ∀ z, minFeasibleLambda (comp z) σ ≤ 2 ^ (-k) := fun z =>
    minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le
      (comp z) σ k (hfloor z)
  have hfeas_t : ∀ z, isFeasible (comp z) σ (2 ^ (-k)) := fun z =>
    isFeasible_mono_t
      (isFeasible_minFeasibleLambda_of_hasFeasibleLambda (comp z) σ (hfeas_comp z))
      (hlamz_le z)
  have hρ_feas : isFeasible ρ σ (2 ^ (-k)) :=
    isFeasible_subMixture p hp_nonneg hp_sum_le comp ρ hmix σ hfeas_t htnn
  have hρ_le : minFeasibleLambda ρ σ ≤ 2 ^ (-k) :=
    minFeasibleLambda_le_of_isFeasible ρ σ hρ_feas
  rcases lt_or_eq_of_le (minFeasibleLambda_nonneg ρ σ) with hpos | hzero
  · exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
      ρ σ k hpos hρ_le
  · have hval0 : conditionalMinEntropyReal ρ σ = 0 := by
      unfold conditionalMinEntropyReal; rw [← hzero]; simp
    rw [hval0]
    have hρ_weight_zero : ∑ x : X, (ρ.stateMap x).trace = 0 := by
      by_contra hne
      have hpos_w : 0 < ∑ x : X, (ρ.stateMap x).trace :=
        lt_of_le_of_ne (Finset.sum_nonneg fun x _ => (ρ.stateMap x).trace_nonneg)
          (Ne.symm hne)
      have hfeasρ : hasFeasibleLambda ρ σ := ⟨_, hρ_feas⟩
      have := minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρ σ hpos_w hfeasρ
      rw [← hzero] at this; exact lt_irrefl 0 this
    have hblock : ∀ x : X, (ρ.stateMap x).trace
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      intro x
      have hx := hmix x
      unfold SubDensityOp.trace
      rw [hx, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have htrace_id : (0 : ℝ) = ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) := by
      rw [← hρ_weight_zero]
      simp_rw [hblock, Finset.mul_sum]
      rw [Finset.sum_comm]
    obtain ⟨z₀, hz₀_pos⟩ : ∃ z, 0 < p z := by
      by_contra hnone
      push_neg at hnone
      have : ∑ z, p z = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        exact le_antisymm (hnone z) (hp_nonneg z)
      rw [this] at hp_sum_pos; exact lt_irrefl 0 hp_sum_pos
    have hcomp_w_zero : ∑ x : X, ((comp z₀).stateMap x).trace = 0 := by
      have hterm_nonneg : ∀ z, 0 ≤ p z * (∑ x : X, ((comp z).stateMap x).trace) :=
        fun z => mul_nonneg (hp_nonneg z)
          (Finset.sum_nonneg fun x _ => ((comp z).stateMap x).trace_nonneg)
      have hz₀_term : p z₀ * (∑ x : X, ((comp z₀).stateMap x).trace) = 0 := by
        have hsum0 : ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) = 0 :=
          htrace_id.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hterm_nonneg z)).mp hsum0
          z₀ (Finset.mem_univ z₀)
      rcases mul_eq_zero.mp hz₀_term with hp0 | hw0
      · exact absurd hp0 (ne_of_gt hz₀_pos)
      · exact hw0
    exact le_trans (hfloor z₀)
      (conditionalMinEntropyReal_le_zero_of_weight_zero (comp z₀) σ hcomp_w_zero)

/-- A positive-weight subprobability mixture inherits a common signed smooth component floor
when its smoothing set is bounded above. -/
theorem smoothMinEntropyReal_subMixture_ge_inf_component
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hρ_weight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ)))
    (hfeas_comp_ball : ∀ z, ∀ ρ' : CQState X n,
      CQState.purifiedDistance (comp z) ρ' ≤ ε → hasFeasibleLambda ρ' σ)
    (hfloor : ∀ z, k ≤ smoothMinEntropyReal ε (comp z) σ) :
    k ≤ smoothMinEntropyReal ε ρ σ := by
  classical
  have hZne : Nonempty Z := by
    rcases isEmpty_or_nonempty Z with hE | hN
    · exfalso
      have h0 : ∀ x : X, (ρ.stateMap x).toOp = 0 := by
        intro x; rw [hmix x]; simp
      have hwz : ∑ x : X, (ρ.stateMap x).trace = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        unfold SubDensityOp.trace; rw [h0 x]; simp
      rw [hwz] at hρ_weight_pos; exact lt_irrefl 0 hρ_weight_pos
    · exact hN
  have hp_sum_pos : 0 < ∑ z, p z := by
    have hblock : ∀ x : X, (ρ.stateMap x).trace
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      intro x
      unfold SubDensityOp.trace
      rw [hmix x, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have hle : ∑ x : X, (ρ.stateMap x).trace ≤ ∑ z, p z := by
      calc ∑ x : X, (ρ.stateMap x).trace
          = ∑ x, ∑ z, p z * ((comp z).stateMap x).trace :=
            Finset.sum_congr rfl (fun x _ => hblock x)
        _ = ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun z _ => (Finset.mul_sum _ _ _).symm)
        _ ≤ ∑ z, p z * 1 := Finset.sum_le_sum (fun z _ =>
            mul_le_mul_of_nonneg_left (comp z).weight_le_one (hp_nonneg z))
        _ = ∑ z, p z := by simp
    linarith [hρ_weight_pos]
  refine le_of_forall_pos_le_add (fun ν hν => ?_)
  have hex : ∀ z, ∃ ρ' : CQState X n,
      CQState.purifiedDistance (comp z) ρ' ≤ ε ∧
        k - ν ≤ conditionalMinEntropyReal ρ' σ := by
    intro z
    exact smoothMinEntropyReal_exists_approx ε hε (comp z) σ (k - ν)
      (by linarith [hfloor z])
  choose comp' hd he using hex
  set ρ' : CQState X n := finMixSub p hp_nonneg hp_sum_le comp' with hρ'_def
  have hρ'_mix : ∀ x : X, (ρ'.stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((comp' z).stateMap x).toOp := fun x =>
    finMixSub_stateMap_toOp p hp_nonneg hp_sum_le comp' x
  have hfeas' : ∀ z, hasFeasibleLambda (comp' z) σ := fun z =>
    hfeas_comp_ball z (comp' z) (hd z)
  have hfloor' : k - ν ≤ conditionalMinEntropyReal ρ' σ :=
    conditionalMinEntropyReal_subMixture_ge_inf_component
      p hp_nonneg hp_sum_le hp_sum_pos comp' ρ' hρ'_mix σ (k - ν) hfeas' he
  have hpd : CQState.purifiedDistance ρ ρ' ≤ ε :=
    purifiedDistance_subMixture_le_max p hp_nonneg hp_sum_le comp comp' ρ ρ'
      hmix hρ'_mix hε hd
  have hk_le : k - ν ≤ smoothMinEntropyReal ε ρ σ :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε ρ σ (k - ν) ρ' hbdd hpd hfloor'
  linarith

/-- A signed floor at a nearby center transfers to the original center after adding their
distance bound to the smoothing radius. -/
theorem smoothMinEntropyReal_ge_of_smoothFloor_of_purifiedDistance
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (εBar s : ℝ) (hεBar : 0 ≤ εBar) (_hs : 0 ≤ s)
    (ρ ρ' : CQState X n) (σ : SubDensityOp n) (k : ℝ)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal (εBar + s) ρ σ)))
    (hd : CQState.purifiedDistance ρ ρ' ≤ s)
    (hk : k ≤ smoothMinEntropyReal εBar ρ' σ) :
    k ≤ smoothMinEntropyReal (εBar + s) ρ σ := by
  refine le_of_forall_pos_le_add (fun ν hν => ?_)
  have hlt : k - ν < smoothMinEntropyReal εBar ρ' σ := by linarith
  obtain ⟨ρ'', hd'', hfloor''⟩ := smoothMinEntropyReal_exists_approx εBar hεBar ρ' σ (k - ν) hlt
  have htri : CQState.purifiedDistance ρ ρ'' ≤ εBar + s := by
    calc CQState.purifiedDistance ρ ρ''
        ≤ CQState.purifiedDistance ρ ρ' + CQState.purifiedDistance ρ' ρ'' :=
          CQState.purifiedDistance_triangle ρ ρ' ρ''
      _ ≤ s + εBar := add_le_add hd hd''
      _ = εBar + s := by ring
  have hge := smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove (εBar + s) ρ σ (k - ν) ρ''
    hbdd htri hfloor''
  linarith

/-- A signed smooth floor on the accepting components transfers to the subnormalized mixture at
radius `εBar + sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
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
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (hsum_lt_one : εBar + Real.sqrt (2 * ε) < 1)
    (h_subNorm : 2 * (εBar + Real.sqrt (2 * ε)) < ∑ x : X, (ρ_mix.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P → k ≤ smoothMinEntropyReal εBar (f τ) σ_ref) :
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
  have h2εBar_lt : 2 * εBar < ∑ x : X, (ρ_good.stateMap x).trace := by
    nlinarith [htrace_gap, h_subNorm, hε_le_two_sqrt, Real.sqrt_nonneg (2 * ε)]
  have hweight_pos_good : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by
    nlinarith [h2εBar_lt, hεBar_nonneg]
  have hcenter : CQState.purifiedDistance ρ_mix ρ_good ≤ Real.sqrt (2 * ε) :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ f goodSet hMeas hClosed hcont P hP_closed
        hP_ae
  have hmix : ∀ x : X, (ρ_good.stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp := by
    intro x
    ext i j
    rw [hρ_good_eq x]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp x i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hfloor_z : ∀ z, k ≤ smoothMinEntropyReal εBar (f (ψ z)) σ_ref :=
    fun z => hf_smoothFloor (ψ z) (hψ_mem z) (hψ_memP z)
  have hbdd_good : BddAbove (setOf (isInSmoothedSetReal εBar ρ_good σ_ref)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd)) εBar
      ((∑ x : X, (ρ_good.stateMap x).trace) - 2 * εBar) (by linarith) ρ_good
      (by linarith) σ_ref
  have hfeas_cb : ∀ z, ∀ ρ' : CQState X dE,
      CQState.purifiedDistance (f (ψ z)) ρ' ≤ εBar → hasFeasibleLambda ρ' σ_ref :=
    fun _ ρ' _ => hasFeasibleLambda_of_posDef ρ' σ_ref hσ_ref
  have hgood_floor : k ≤ smoothMinEntropyReal εBar ρ_good σ_ref :=
    smoothMinEntropyReal_subMixture_ge_inf_component εBar hεBar_nonneg p hp_nonneg hp_sum_le
      (fun z => f (ψ z)) ρ_good hmix σ_ref k hweight_pos_good hbdd_good hfeas_cb hfloor_z
  have hbdd_mix : BddAbove (setOf (isInSmoothedSetReal (εBar + Real.sqrt (2 * ε)) ρ_mix σ_ref)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd))
      (εBar + Real.sqrt (2 * ε))
      ((∑ x : X, (ρ_mix.stateMap x).trace) - 2 * (εBar + Real.sqrt (2 * ε)))
      (by linarith) ρ_mix (by linarith) σ_ref
  exact smoothMinEntropyReal_ge_of_smoothFloor_of_purifiedDistance εBar (Real.sqrt (2 * ε))
    hεBar_nonneg (Real.sqrt_nonneg _) ρ_mix ρ_good σ_ref k hbdd_mix hcenter hgood_floor

/-- A signed smooth floor on the accepting components gives a dominated good branch with the
same signed floor and trace gap at most `ε`. -/
theorem
  smoothMinEntropyReal_ge_goodBranch_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized_linear
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
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_subNorm_linear : 2 * εBar + ε < ∑ x : X, (ρ_mix.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P → k ≤ smoothMinEntropyReal εBar (f τ) σ_ref) :
    ∃ ρ_good : CQState X dE,
      (∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      (∑ x : X, (ρ_mix.stateMap x).trace) - (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε ∧
      k ≤ smoothMinEntropyReal εBar ρ_good σ_ref := by
  rcases exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hMeas h_int hf_lin h_badBranch_traceNorm with
    ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩
  have h2εBar_lt : 2 * εBar < ∑ x : X, (ρ_good.stateMap x).trace := by
    nlinarith [htrace_gap, h_subNorm_linear]
  have hweight_pos_good : 0 < ∑ x : X, (ρ_good.stateMap x).trace := by
    nlinarith [h2εBar_lt, hεBar_nonneg]
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ f goodSet hMeas hClosed hcont P hP_closed
        hP_ae
  have hmix : ∀ x : X, (ρ_good.stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((f (ψ z)).stateMap x).toOp := by
    intro x
    ext i j
    rw [hρ_good_eq x]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp x i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hfloor_z : ∀ z, k ≤ smoothMinEntropyReal εBar (f (ψ z)) σ_ref :=
    fun z => hf_smoothFloor (ψ z) (hψ_mem z) (hψ_memP z)
  have hbdd_good : BddAbove (setOf (isInSmoothedSetReal εBar ρ_good σ_ref)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd)) εBar
      ((∑ x : X, (ρ_good.stateMap x).trace) - 2 * εBar) (by linarith) ρ_good
      (by linarith) σ_ref
  have hfeas_cb : ∀ z, ∀ ρ' : CQState X dE,
      CQState.purifiedDistance (f (ψ z)) ρ' ≤ εBar → hasFeasibleLambda ρ' σ_ref :=
    fun _ ρ' _ => hasFeasibleLambda_of_posDef ρ' σ_ref hσ_ref
  have hgood_floor : k ≤ smoothMinEntropyReal εBar ρ_good σ_ref :=
    smoothMinEntropyReal_subMixture_ge_inf_component εBar hεBar_nonneg p hp_nonneg hp_sum_le
      (fun z => f (ψ z)) ρ_good hmix σ_ref k hweight_pos_good hbdd_good hfeas_cb hfloor_z
  exact ⟨ρ_good, hρ_good_le_mix, htrace_gap, hgood_floor⟩

end InfoTheory.SmoothMinEntropy

end
