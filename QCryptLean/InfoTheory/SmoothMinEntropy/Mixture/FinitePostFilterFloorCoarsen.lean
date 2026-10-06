import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloor
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening

/-!
# Coarsened finite post-filter entropy floors

The finite post-filter witness constructions pass through classical coarsening. Good-branch and
heavy-component floors remain valid for zero outputs, with their geometric trace-gap and distance
charges.
-/

open Quantum.Operators Matrix InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

private local instance {n : ℕ} : ESeminormedAddCommMonoid (Op n) :=
  (NormedAddCommGroup.toENormedAddCommMonoid (E := Op n)).toESeminormedAddCommMonoid

/-- **The coarsened analytic data of a de Finetti post-filter family.**

`CQState.coarsen g` acts blockwise as the fibre sum `∑_{g x = y} (·).stateMap x`
(`CQState.coarsen_stateMap_toOp`), so each analytic datum of the coarsened family is the
corresponding uncoarsened datum regrouped over the fibres of `g`: block integrability and block
continuity are finite fibre sums of integrable / continuous blocks, and the Nahar et al. B13
integral
split and the bad-branch trace both commute with the finite fibre sum
(`sum_fiber_indicator_eq_sum`).

These data support the coarsening transfers for both fixed references and own-marginal
heavy-component floors. -/
private lemma coarsen_deFinetti_postFilter_data
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d)) (ε : ℝ)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε) :
    (∀ y : Yc, MeasureTheory.Integrable
        (fun τ : DensityOp d => ((CQState.coarsen g (f τ)).stateMap y).toOp) μ.measure) ∧
    (∀ (y : Yc) (i j : Fin dE),
        ((CQState.coarsen g ρ_mix).stateMap y).toOp i j =
          ∫ τ : DensityOp d, ((CQState.coarsen g (f τ)).stateMap y).toOp i j ∂μ.measure) ∧
    (∀ y : Yc, Continuous
        (fun τ : DensityOp d => ((CQState.coarsen g (f τ)).stateMap y).toOp)) ∧
    (∑ y : Yc, ((Matrix.of fun i j : Fin dE =>
        ∫ τ in goodSetᶜ, ((CQState.coarsen g (f τ)).stateMap y).toOp i j ∂μ.measure :
          Op dE).trace).re ≤ ε) := by
  haveI := μ.isProbability
  -- Entry-eval CLM (reads matrix entry `i j`), used to transport integrability through entries.
  let entryCLM : Fin dE → Fin dE → (Op dE →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hentInt : ∀ (x : Xc) (i j : Fin dE),
      MeasureTheory.Integrable
        (fun τ : DensityOp d => ((f τ).stateMap x).toOp i j) μ.measure :=
    fun x i j => (entryCLM i j).integrable_comp (h_int x)
  -- Each coarsened block entry is the fiber sum of the fine block entries.
  have hcoarsenEntry : ∀ (ρ : CQState Xc dE) (y : Yc) (i j : Fin dE),
      ((CQState.coarsen g ρ).stateMap y).toOp i j =
        ∑ x : Xc, if g x = y then (ρ.stateMap x).toOp i j else 0 := by
    intro ρ y i j
    rw [CQState.coarsen_stateMap_toOp, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : g x = y <;> simp [hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (D1) coarsened block integrability: a finite fiber sum of integrable blocks.
  · intro y
    have hrw : (fun τ : DensityOp d => ((CQState.coarsen g (f τ)).stateMap y).toOp) =
        fun τ : DensityOp d => ∑ x : Xc, if g x = y then ((f τ).stateMap x).toOp else 0 := by
      funext τ; exact CQState.coarsen_stateMap_toOp g (f τ) y
    rw [hrw]
    refine MeasureTheory.integrable_finsetSum (f := fun x (τ : DensityOp d) =>
      if g x = y then ((f τ).stateMap x).toOp else 0) _ (fun x _ => ?_)
    by_cases hx : g x = y
    · simp only [if_pos hx]; exact h_int x
    · simp only [if_neg hx]; exact MeasureTheory.integrable_zero _ _ _
  -- (D2) coarsened B13 integral split, regrouped over the fibers of `g`.
  · intro y i j
    have hintSum : ∀ x ∈ (Finset.univ : Finset Xc), MeasureTheory.Integrable
        (fun τ : DensityOp d => if g x = y then ((f τ).stateMap x).toOp i j else 0) μ.measure := by
      intro x _
      by_cases hx : g x = y
      · simp only [if_pos hx]; exact hentInt x i j
      · simp only [if_neg hx]; exact MeasureTheory.integrable_zero _ _ _
    rw [hcoarsenEntry ρ_mix y i j,
      show (∫ τ : DensityOp d, ((CQState.coarsen g (f τ)).stateMap y).toOp i j ∂μ.measure)
          = ∫ τ : DensityOp d, (∑ x : Xc, if g x = y then ((f τ).stateMap x).toOp i j else 0)
              ∂μ.measure from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun τ => hcoarsenEntry (f τ) y i j)),
      MeasureTheory.integral_finsetSum _ hintSum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : g x = y
    · simp only [if_pos hx]; exact hf_lin x i j
    · simp only [if_neg hx, MeasureTheory.integral_zero]
  -- (D3) coarsened block continuity: a finite fiber sum of continuous blocks.
  · intro y
    have hrw : (fun τ : DensityOp d => ((CQState.coarsen g (f τ)).stateMap y).toOp) =
        fun τ : DensityOp d => ∑ x : Xc, if g x = y then ((f τ).stateMap x).toOp else 0 := by
      funext τ; exact CQState.coarsen_stateMap_toOp g (f τ) y
    rw [hrw]
    refine continuous_finsetSum _ (fun x _ => ?_)
    by_cases hx : g x = y
    · simp only [if_pos hx]; exact hcont x
    · simp only [if_neg hx]; exact continuous_const
  -- (D4) coarsened bad-branch trace: fiber regrouping of the uncoarsened bad-branch traces.
  · have hmat : ∀ y : Yc,
        (Matrix.of fun i j : Fin dE =>
            ∫ τ in goodSetᶜ, ((CQState.coarsen g (f τ)).stateMap y).toOp i j ∂μ.measure : Op dE)
          = ∑ x : Xc, if g x = y then
              (Matrix.of fun i j : Fin dE =>
                ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE) else 0 := by
      intro y
      ext i j
      simp only [Matrix.sum_apply, Matrix.of_apply]
      rw [MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun τ => hcoarsenEntry (f τ) y i j)),
        MeasureTheory.integral_finsetSum _ (fun x _ => by
          by_cases hx : g x = y
          · simp only [if_pos hx]; exact ((entryCLM i j).integrable_comp (h_int x)).integrableOn
          · simp only [if_neg hx]; exact MeasureTheory.integrableOn_zero)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : g x = y
      · simp only [if_pos hx, Matrix.of_apply]
      · simp only [if_neg hx, Matrix.zero_apply, MeasureTheory.integral_zero]
    have hsum : ∑ y : Yc, ((Matrix.of fun i j : Fin dE =>
            ∫ τ in goodSetᶜ, ((CQState.coarsen g (f τ)).stateMap y).toOp i j ∂μ.measure :
              Op dE).trace).re
          = ∑ y : Yc, ∑ x : Xc, if g x = y then
              ((Matrix.of fun i j : Fin dE =>
                ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re else 0 :=
                    by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hmat y, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : g x = y <;> simp [hx]
    rw [hsum, sum_fiber_indicator_eq_sum]
    exact h_badBranch_traceNorm

/-- **The good-branch restriction commutes with classical coarsening (block form).**

The `y`-block of the good branch of the *coarsened* family `fun τ => CQState.coarsen g (f τ)` is the
fibre sum of the good-branch blocks of the *fine* family `f`:

`goodBranchBlockOp μ (coarsen g ∘ f) goodSet y = ∑_{x} [g x = y] · goodBranchBlockOp μ f goodSet x`.

Both sides are `∑_{x ∈ g⁻¹ y} ∫_{goodSet} ((f τ).stateMap x).toOp dμ`; the only thing to check is
that the finite fibre sum passes through the Bochner set integral, which is
`MeasureTheory.integral_finsetSum` on the restricted measure.  `h_int` pays for exactly that: it
supplies the entrywise integrability of each fine block, restricted to `goodSet`.

**Why this is true at all — the good set carries no fine index.**  `goodSet : Set (DensityOp d)`
lives on the de Finetti Carathéodory parameter `τ`, *not* on the classical register `Xc`.  So the
restriction `∫_{goodSet}` is the same on every fibre of `g` and the regrouping is unobstructed.  Had
the good branch been selected by an `x`-dependent set the two operations would not commute and no
fine-register good branch would coarsen onto the coarse one.  This is the same regrouping
`coarsen_deFinetti_postFilter_data` already performs for the *bad* branch (its `goodSetᶜ` step D4),
here run on the good branch instead.

**Why the fine/coarse distinction matters.**  The consumer needs the good branch on the **fine**
register: the downstream agree filter is a `filterKeep` on the fine register (BB84:
`bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep`, keep predicate
`fun ω => !bb84SiftedKeyStringsDiffer peSel ec ω`) and is **not constant on the fibres of** the
coarsening map, so a good branch that only exists on the coarse register cannot be agree-filtered.
This lemma is what lets the floor be produced coarsened while the branch itself stays fine. -/
lemma goodBranchBlockOp_coarsen_eq_sum_fiber
    {d dE : ℕ} {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState Xc dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (y : Yc) :
    goodBranchBlockOp μ (fun τ => CQState.coarsen g (f τ)) goodSet y =
      ∑ x : Xc, if g x = y then goodBranchBlockOp μ f goodSet x else 0 := by
  classical
  -- Entry-eval CLM (reads matrix entry `i j`), used to transport integrability through entries.
  let entryCLM : Fin dE → Fin dE → (Op dE →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  ext i j
  -- Each coarsened block entry is the fibre sum of the fine block entries.
  have hentry : ∀ τ : DensityOp d,
      ((CQState.coarsen g (f τ)).stateMap y).toOp i j =
        ∑ x : Xc, if g x = y then ((f τ).stateMap x).toOp i j else 0 := by
    intro τ
    rw [CQState.coarsen_stateMap_toOp, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : g x = y <;> simp [hx]
  simp only [goodBranchBlockOp, Matrix.of_apply, Matrix.sum_apply]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hentry),
    MeasureTheory.integral_finsetSum _ (fun x _ => by
      by_cases hx : g x = y
      · simp only [if_pos hx]
        exact ((entryCLM i j).integrable_comp (h_int x)).integrableOn
      · simp only [if_neg hx]
        exact MeasureTheory.integrableOn_zero)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · simp only [if_pos hx, Matrix.of_apply]
  · simp only [if_neg hx, Matrix.zero_apply, MeasureTheory.integral_zero]

/-- **The coarsening of a fine good branch IS the good branch of the coarsened family.**

`CQState`-level form of `goodBranchBlockOp_coarsen_eq_sum_fiber`: if `ρ_good` is *the* good-branch
CQ
state of the fine family `f` — i.e. its blocks are `goodBranchBlockOp μ f goodSet x`, which is what
`exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized` hands back — then
`CQState.coarsen g ρ_good` has exactly the blocks of the good branch of the coarsened family
`fun τ => CQState.coarsen g (f τ)`.

`hρ_good_eq` pays for "`ρ_good` is the good branch and not merely some sub-state of the mixture";
`h_int` pays for the fibre-sum/integral exchange inside
`goodBranchBlockOp_coarsen_eq_sum_fiber`.

The per-`σ` smooth floor is available
on the **coarsened** family, so the floor producer must run coarsened; but the agree filter
downstream is a `filterKeep` on the **fine** register and is not constant on the fibres of the
coarsening map, so the branch it filters has to be fine.  This lemma reconciles the two: keep the
branch fine, and let its coarsening carry the floor.

The BB84 bound
bb84SiftedPEAnnounceEveVisible_bellRef_agreeBlock_ckrTensorTraceNorm_le_lhlOutput_radicalFree
(`BellInnerBudget.lean` §10b) uses a radius shrink with the trivial branch `ρ_good := ρ_mix`.
The de Finetti sub-mixture construction here applies to non-pure references; rank-one blocks
at the Bell purification cannot provide a better floor by this construction. -/
lemma coarsen_stateMap_toOp_eq_goodBranchBlockOp_coarsen
    {d dE : ℕ} {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f : DensityOp d → CQState Xc dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (ρ_good : CQState Xc dE)
    (hρ_good_eq : ∀ x : Xc, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (y : Yc) :
    ((CQState.coarsen g ρ_good).stateMap y).toOp =
      goodBranchBlockOp μ (fun τ => CQState.coarsen g (f τ)) goodSet y := by
  classical
  rw [CQState.coarsen_stateMap_toOp, goodBranchBlockOp_coarsen_eq_sum_fiber g μ f goodSet h_int y]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · simp only [if_pos hx, hρ_good_eq x]
  · simp only [if_neg hx]

/-- Coarsened component smooth floors give an extended post-filter floor at radius
`εBar + sqrt (2 * ε)` without a retained-mass hypothesis. -/
theorem smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Nonempty Xc]
    [Fintype Yc] [DecidableEq Yc] [Nonempty Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (σ_ref : SubDensityOp dE)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor_coarsen : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g (f τ)) σ_ref) :
    ENNReal.ofReal k ≤
      smoothMinEntropy (εBar + Real.sqrt (2 * ε)) (CQState.coarsen g ρ_mix) σ_ref := by
  letI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  obtain ⟨_, hF_lin, hF_cont, hF_badBranch⟩ :=
    coarsen_deFinetti_postFilter_data g μ ρ_mix f h_int hf_lin hcont goodSet ε
      h_badBranch_traceNorm
  exact smoothMinEntropy_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
    μ (CQState.coarsen g ρ_mix) (fun τ => CQState.coarsen g (f τ)) σ_ref
    hF_lin hF_cont goodSet hClosed P hP_closed hP_ae
    k εBar ε hεBar_nonneg hF_badBranch hf_smoothFloor_coarsen

/-- The coarsened retained branch carries the component extended smooth floor at radius
`εBar`; the bad-branch mass remains an explicit trace gap. -/
theorem smoothMinEntropy_coarsen_ge_goodBr_of_postFilterFloor_subNorm_lin
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Nonempty Xc]
    [Fintype Yc] [DecidableEq Yc] [Nonempty Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (σ_ref : SubDensityOp dE)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ)
    (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor_coarsen : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g (f τ)) σ_ref) :
    ∃ ρ_good : CQState Yc dE,
      (∀ y : Yc, opLe (ρ_good.stateMap y).toOp ((CQState.coarsen g ρ_mix).stateMap y).toOp) ∧
      (∑ y : Yc, ((CQState.coarsen g ρ_mix).stateMap y).trace) -
          (∑ y : Yc, (ρ_good.stateMap y).trace) ≤ ε ∧
      ENNReal.ofReal k ≤ smoothMinEntropy εBar ρ_good σ_ref := by
  letI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  obtain ⟨_, hF_lin, hF_cont, hF_badBranch⟩ :=
    coarsen_deFinetti_postFilter_data g μ ρ_mix f h_int hf_lin hcont goodSet ε
      h_badBranch_traceNorm
  exact
    smoothMinEntropy_ge_goodBranch_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized_linear
      μ (CQState.coarsen g ρ_mix) (fun τ => CQState.coarsen g (f τ)) σ_ref
      hF_lin hF_cont goodSet hClosed P hP_closed hP_ae
      k εBar ε hεBar_nonneg hF_badBranch hf_smoothFloor_coarsen

/-- A fine retained branch has the component extended smooth floor after coarsening, with
the bad-branch mass charged only to its trace gap and no lower bound on retained mass. -/
theorem smoothMinEntropy_coarsen_ge_fineGoodBr_of_postFilter_subNorm_lin
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Nonempty Xc]
    [Fintype Yc] [DecidableEq Yc] [Nonempty Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (σ_ref : SubDensityOp dE)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ)
    (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor_coarsen : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g (f τ)) σ_ref) :
    ∃ ρ_good : CQState Xc dE,
      (∀ x : Xc, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp) ∧
      (∑ x : Xc, (ρ_mix.stateMap x).trace) - (∑ x : Xc, (ρ_good.stateMap x).trace) ≤ ε ∧
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g ρ_good) σ_ref := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  obtain ⟨_, _, hF_cont, _⟩ :=
    coarsen_deFinetti_postFilter_data g μ ρ_mix f h_int hf_lin hcont goodSet ε
      h_badBranch_traceNorm
  obtain ⟨ρ_good, hρ_good_eq, hρ_good_le_mix, htrace_gap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ ρ_mix f goodSet hClosed.measurableSet h_int hf_lin h_badBranch_traceNorm
  refine ⟨ρ_good, hρ_good_le_mix, htrace_gap, ?_⟩
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ (fun τ => CQState.coarsen g (f τ))
      goodSet hClosed.measurableSet hClosed hF_cont P hP_closed hP_ae
  have hcoarse_eq : ∀ y : Yc, ((CQState.coarsen g ρ_good).stateMap y).toOp =
      goodBranchBlockOp μ (fun τ => CQState.coarsen g (f τ)) goodSet y :=
    coarsen_stateMap_toOp_eq_goodBranchBlockOp_coarsen g μ f goodSet h_int ρ_good hρ_good_eq
  have hmix : ∀ y : Yc, ((CQState.coarsen g ρ_good).stateMap y).toOp =
      ∑ z, (p z : ℂ) • ((CQState.coarsen g (f (ψ z))).stateMap y).toOp := by
    intro y
    ext i j
    rw [hcoarse_eq y]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp y i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  exact smoothMinEntropy_subMixture_ge_inf_component εBar hεBar_nonneg
    p hp_nonneg hp_sum_le (fun z => CQState.coarsen g (f (ψ z)))
    (CQState.coarsen g ρ_good) hmix σ_ref k
    (fun z => hf_smoothFloor_coarsen (ψ z) (hψ_mem z) (hψ_memP z))

/-- Coarsening preserves the extended own-marginal post-filter floor from heavy components.
The heavy-component guard and reference are unchanged by coarsening. -/
theorem smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Nonempty Xc]
    [Fintype Yc] [DecidableEq Yc] [Nonempty Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ)
    (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
        ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re ≤ ε)
    (hf_smoothFloor_coarsen : ∀ τ ∈ goodSet, τ ∈ P →
      εBar ^ 2 < ∑ x : Xc, ((f τ).stateMap x).trace →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g (f τ)) (f τ).quantumMarginal) :
    ENNReal.ofReal k ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε))
      (CQState.coarsen g ρ_mix) ρ_mix.quantumMarginal := by
  letI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure :=
    fun x => (hcont x).integrable_of_compactSpace
  obtain ⟨_, hF_lin, hF_cont, hF_badBranch⟩ :=
    coarsen_deFinetti_postFilter_data g μ ρ_mix f h_int hf_lin hcont goodSet ε
      h_badBranch_traceNorm
  have hF_floor : ∀ τ ∈ goodSet, τ ∈ P →
      εBar ^ 2 < ∑ y : Yc, ((CQState.coarsen g (f τ)).stateMap y).trace →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (CQState.coarsen g (f τ))
        (CQState.coarsen g (f τ)).quantumMarginal := by
    intro τ hgood hP hweight
    rw [CQState.sum_coarsen_stateMap_trace_eq] at hweight
    rw [CQState.coarsen_quantumMarginal]
    exact hf_smoothFloor_coarsen τ hgood hP hweight
  have hfloor := smoothMinEntropy_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor
    μ (CQState.coarsen g ρ_mix) (fun τ => CQState.coarsen g (f τ))
    hF_lin hF_cont goodSet hClosed P hP_closed hP_ae k εBar ε
    hεBar_nonneg hF_badBranch hF_floor
  rwa [CQState.coarsen_quantumMarginal] at hfloor

/-- A signed smooth floor on the coarsened accepting components transfers to the coarsened
mixture at radius `εBar + sqrt (2 * ε)`. -/
lemma smoothMinEntropyReal_coarsen_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
    {d dE : ℕ} [NeZero d] [NeZero dE] {Xc Yc : Type*}
    [Fintype Xc] [Nonempty Xc]
    [Fintype Yc] [DecidableEq Yc] [Nonempty Yc]
    (g : Xc → Yc)
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (ρ_mix : CQState Xc dE)
    (f : DensityOp d → CQState Xc dE)
    (σ_ref : SubDensityOp dE)
    (hσ_ref : σ_ref.toOp.PosDef)
    (h_int : ∀ x : Xc, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : Xc) (i j : Fin dE),
      (ρ_mix.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : Xc, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d))
    (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (hsum_lt_one : εBar + Real.sqrt (2 * ε) < 1)
    (h_subNorm : 2 * (εBar + Real.sqrt (2 * ε)) < ∑ x : Xc, (ρ_mix.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : Xc, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor_coarsen : ∀ τ ∈ goodSet, τ ∈ P →
      k ≤ smoothMinEntropyReal εBar (CQState.coarsen g (f τ)) σ_ref) :
    k ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) (CQState.coarsen g ρ_mix) σ_ref := by
  classical
  obtain ⟨hF_int, hF_lin, hF_cont, hF_badBranch⟩ :=
    coarsen_deFinetti_postFilter_data g μ ρ_mix f h_int hf_lin hcont goodSet ε
      h_badBranch_traceNorm
  have hF_subNorm :
      2 * (εBar + Real.sqrt (2 * ε)) < ∑ y : Yc, ((CQState.coarsen g ρ_mix).stateMap y).trace := by
    rw [CQState.sum_coarsen_stateMap_trace_eq]; exact h_subNorm
  exact smoothMinEntropyReal_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
    (μ := μ) (ρ_mix := CQState.coarsen g ρ_mix) (f := fun τ => CQState.coarsen g (f τ))
    (σ_ref := σ_ref) hσ_ref hF_int hF_lin hF_cont goodSet hMeas hClosed
    P hP_closed hP_ae k εBar ε hεBar_nonneg hε_nonneg hε_lt_half hsum_lt_one
    hF_subNorm hF_badBranch hf_smoothFloor_coarsen

end InfoTheory.SmoothMinEntropy

end
