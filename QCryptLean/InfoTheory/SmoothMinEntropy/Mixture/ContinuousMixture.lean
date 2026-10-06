import QCryptLean.Math.SpectralTheory.RpowContinuity
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.MixtureFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.GoodBranch
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness

/-!
# Continuous mixture smoothing transfer — Bochner integral fidelity super-additivity

This file develops the analytic core needed for the continuous (Bochner-integral)
analogue of `CQState.purifiedDistance_mixture_le_max` (Nahar, Tupkary, Zhao, Lütkenhaus, Tan Lemma
14 / Renner [46]
Eq. 3.59, integral form): the joint super-additivity of the Uhlmann fidelity under a
de Finetti measure,
`∫_{good} F(A_τ, B_τ) dμ ≤ F(∫_{good} A_τ dμ, ∫_{good} B_τ dμ)`,
proved by Jensen's inequality from the joint concavity and continuity of the root
Uhlmann fidelity on the PSD cone.

## Main statements
- `fidOp_eq_fidelity`: the matrix-level fidelity functional agrees with
  `Quantum.Metrics.fidelity` on PSD pairs.
- `fidOp_continuousOn`: the matrix-level fidelity is continuous on the product PSD cone.
- `fidOp_concaveOn`: the matrix-level fidelity is jointly concave on the product PSD cone.
-/

open Quantum.Operators Quantum.Metrics MeasureTheory Matrix
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

private local instance {n : ℕ} : ContinuousENorm (Op n × Op n) :=
  SeminormedAddGroup.toContinuousENorm

private local instance {n : ℕ} : SecondCountableTopology (Op n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

private local instance {n : ℕ} : TopologicalSpace.PseudoMetrizableSpace (Op n) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin n → Fin n → ℂ))

private local instance {n : ℕ} : OpensMeasurableSpace (Op n × Op n) := Prod.opensMeasurableSpace

/-- Package a PSD matrix as a `PosSemidefOp`. -/
def PosSemidefOp.ofMatrix {n : ℕ} (M : Op n) (h : M.PosSemidef) : PosSemidefOp n :=
  ⟨⟨M, h.isHermitian⟩, fun v => posSemidef_re_quadraticForm_nonneg h v⟩

@[simp] lemma PosSemidefOp.ofMatrix_toOp {n : ℕ} (M : Op n) (h : M.PosSemidef) :
    (PosSemidefOp.ofMatrix M h).toOp = M := rfl

/-- Real scalar multiplication on operators is the complex-coerced scalar
multiplication. -/
lemma real_smul_op_eq {n : ℕ} (a : ℝ) (M : Op n) : a • M = (a : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The matrix-level root Uhlmann fidelity functional `F(A,B) = (Tr √(√A·B·√A)).re`,
defined on all of `Op n × Op n` (meaningful on the PSD cone). -/
noncomputable def fidOp {n : ℕ} (p : Op n × Op n) : ℝ :=
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  (Matrix.trace (CFC.sqrt (CFC.sqrt p.1 * p.2 * CFC.sqrt p.1))).re

/-- On PSD pairs, `fidOp` agrees with `Quantum.Metrics.fidelity`. -/
lemma fidOp_eq_fidelity {n : ℕ} [NeZero n] (A B : PosSemidefOp n) :
    fidOp (A.toOp, B.toOp) = fidelity A B := rfl

/-- The product PSD cone in `Op n × Op n`. -/
def psdProd (n : ℕ) : Set (Op n × Op n) := {p | p.1.PosSemidef ∧ p.2.PosSemidef}

lemma mem_psdProd {n : ℕ} {p : Op n × Op n} :
    p ∈ psdProd n ↔ p.1.PosSemidef ∧ p.2.PosSemidef := Iff.rfl

/-- The inner sandwich `√A · B · √A` is PSD when `A`, `B` are PSD. -/
lemma sandwich_posSemidef {n : ℕ} {A B : Op n} (_hA : A.PosSemidef) (hB : B.PosSemidef) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have hsqrtA : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg (a := A)).posSemidef
  have hS : (CFC.sqrt A)† = CFC.sqrt A := hsqrtA.isHermitian
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hB (CFC.sqrt A)
  rwa [hS] at h

/-- `Continuous (fun M => (Matrix.trace M).re)`. -/
lemma continuous_trace_re {n : ℕ} :
    Continuous (fun M : Op n => (Matrix.trace M).re) := by
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).comp (continuous_apply i)

/-- **Continuity of the matrix-level fidelity on the product PSD cone.** -/
lemma fidOp_continuousOn {n : ℕ} : ContinuousOn (fidOp : Op n × Op n → ℝ) (psdProd n) := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  -- continuity of `p ↦ CFC.sqrt p.1` on the cone
  have hmaps1 : Set.MapsTo (fun p : Op n × Op n => p.1) (psdProd n) {M | 0 ≤ M} :=
    fun p hp => (Matrix.nonneg_iff_posSemidef).2 hp.1
  have hsqrtFst : ContinuousOn (fun p : Op n × Op n => CFC.sqrt p.1) (psdProd n) :=
    Math.SpectralTheory.continuousOn_sqrt_nonneg.comp continuous_fst.continuousOn hmaps1
  have hsnd : ContinuousOn (fun p : Op n × Op n => p.2) (psdProd n) :=
    continuous_snd.continuousOn
  -- continuity of the matrix product `√A · B · √A` via `ContinuousOn.mul`
  -- (first-order match; avoids the costly `Continuous.comp_continuousOn` topology defeq)
  have hg1 : ContinuousOn (fun p : Op n × Op n => CFC.sqrt p.1 * p.2 * CFC.sqrt p.1)
      (psdProd n) :=
    (hsqrtFst.mul hsnd).mul hsqrtFst
  -- the inner sandwich lands in the cone
  have hmaps2 : Set.MapsTo (fun p : Op n × Op n => CFC.sqrt p.1 * p.2 * CFC.sqrt p.1)
      (psdProd n) {M | 0 ≤ M} :=
    fun p hp => (Matrix.nonneg_iff_posSemidef).2 (sandwich_posSemidef hp.1 hp.2)
  have hsqrtInner : ContinuousOn
      (fun p : Op n × Op n => CFC.sqrt (CFC.sqrt p.1 * p.2 * CFC.sqrt p.1)) (psdProd n) :=
    Math.SpectralTheory.continuousOn_sqrt_nonneg.comp hg1 hmaps2
  exact continuous_trace_re.comp_continuousOn hsqrtInner

/-- The product PSD cone is closed. -/
lemma isClosed_psdProd {n : ℕ} : IsClosed (psdProd n) := by
  have h1 :
      IsClosed ((fun p : Op n × Op n => p.1) ⁻¹' (Set.ofPred (fun A : Op n => A.PosSemidef))) :=
    (Quantum.Operators.isClosed_setOf_posSemidef).preimage continuous_fst
  have h2 :
      IsClosed ((fun p : Op n × Op n => p.2) ⁻¹' (Set.ofPred (fun A : Op n => A.PosSemidef))) :=
    (Quantum.Operators.isClosed_setOf_posSemidef).preimage continuous_snd
  have hEq : psdProd n =
      ((fun p : Op n × Op n => p.1) ⁻¹' (Set.ofPred (fun A : Op n => A.PosSemidef)))
      ∩ ((fun p : Op n × Op n => p.2) ⁻¹' (Set.ofPred (fun A : Op n => A.PosSemidef))) := rfl
  rw [hEq]; exact h1.inter h2

/-- The product PSD cone is convex. -/
lemma convex_psdProd {n : ℕ} : Convex ℝ (psdProd n) := by
  rintro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · change (a • p.1 + b • q.1).PosSemidef
    rw [real_smul_op_eq, real_smul_op_eq]
    exact (posSemidef_ofReal_smul _ hp.1 a ha).add (posSemidef_ofReal_smul _ hq.1 b hb)
  · change (a • p.2 + b • q.2).PosSemidef
    rw [real_smul_op_eq, real_smul_op_eq]
    exact (posSemidef_ofReal_smul _ hp.2 a ha).add (posSemidef_ofReal_smul _ hq.2 b hb)

/-- Homogeneity of `fidOp`: `fidOp (a•A, a•B) = a · fidOp (A,B)` for `0 ≤ a` and PSD `A,B`. -/
lemma fidOp_smul {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (A B : PosSemidefOp n) :
    fidOp (a • A.toOp, a • B.toOp) = a * fidOp (A.toOp, B.toOp) := by
  rw [real_smul_op_eq a A.toOp, real_smul_op_eq a B.toOp, fidOp_eq_fidelity]
  have h := Quantum.Metrics.fidelity_smul_smul (α := a) (β := a) ha ha A B
  rw [Real.sqrt_mul_self ha] at h
  exact h

/-- **Joint concavity of the matrix-level fidelity on the product PSD cone.**

Follows from the finite super-additivity `fidelity_sum_le_fidelity_sum` (Renner
Eq. 3.59) at `Fin 2` together with the homogeneity `fidelity_smul_block_eq`. -/
lemma fidOp_concaveOn {n : ℕ} [NeZero n] : ConcaveOn ℝ (psdProd n) fidOp := by
  have : NeZero (n * Fintype.card (Fin 2)) :=
    ⟨by rw [Fintype.card_fin]; exact Nat.mul_ne_zero (NeZero.ne n) (by norm_num)⟩
  refine ⟨convex_psdProd, ?_⟩
  rintro p hp q hq a b ha hb hab
  set A₁ := PosSemidefOp.ofMatrix p.1 hp.1 with hA₁
  set B₁ := PosSemidefOp.ofMatrix p.2 hp.2 with hB₁
  set A₂ := PosSemidefOp.ofMatrix q.1 hq.1 with hA₂
  set B₂ := PosSemidefOp.ofMatrix q.2 hq.2 with hB₂
  set PA₁ := PosSemidefOp.ofMatrix ((a : ℂ) • p.1) (posSemidef_ofReal_smul p.1 hp.1 a ha) with hPA₁
  set PB₁ := PosSemidefOp.ofMatrix ((a : ℂ) • p.2) (posSemidef_ofReal_smul p.2 hp.2 a ha) with hPB₁
  set PA₂ := PosSemidefOp.ofMatrix ((b : ℂ) • q.1) (posSemidef_ofReal_smul q.1 hq.1 b hb) with hPA₂
  set PB₂ := PosSemidefOp.ofMatrix ((b : ℂ) • q.2) (posSemidef_ofReal_smul q.2 hq.2 b hb) with hPB₂
  have hsa : fidelity PA₁ PB₁ = a * fidelity A₁ B₁ :=
    InfoTheory.SmoothMinEntropy.fidelity_smul_block_eq ha A₁ B₁ PA₁ PB₁ rfl rfl
  have hsb : fidelity PA₂ PB₂ = b * fidelity A₂ B₂ :=
    InfoTheory.SmoothMinEntropy.fidelity_smul_block_eq hb A₂ B₂ PA₂ PB₂ rfl rfl
  have hsuper := fidelity_sum_le_fidelity_sum ![PA₁, PA₂] ![PB₁, PB₂]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hsuper
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsuper
  have hpfid : fidOp p = fidelity A₁ B₁ := fidOp_eq_fidelity A₁ B₁
  have hqfid : fidOp q = fidelity A₂ B₂ := fidOp_eq_fidelity A₂ B₂
  have hRHSeq : fidOp (a • p + b • q) = fidelity (PA₁ + PA₂) (PB₁ + PB₂) := by
    have e1 : (a • p + b • q).1 = (PA₁ + PA₂).toOp := by
      change a • p.1 + b • q.1 = (a : ℂ) • p.1 + (b : ℂ) • q.1
      rw [real_smul_op_eq, real_smul_op_eq]
    have e2 : (a • p + b • q).2 = (PB₁ + PB₂).toOp := by
      change a • p.2 + b • q.2 = (a : ℂ) • p.2 + (b : ℂ) • q.2
      rw [real_smul_op_eq, real_smul_op_eq]
    rw [show (a • p + b • q) = ((PA₁ + PA₂).toOp, (PB₁ + PB₂).toOp) from Prod.ext e1 e2]
    exact fidOp_eq_fidelity _ _
  rw [hRHSeq, smul_eq_mul, smul_eq_mul, hpfid, hqfid, ← hsa, ← hsb]
  exact hsuper

/-- The matrix-level fidelity of a measurable PSD-valued pair is a.e. strongly
measurable. -/
lemma aestronglyMeasurable_fidOp {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {A B : α → Op n} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hpsd : ∀ᵐ τ ∂μ, (A τ).PosSemidef ∧ (B τ).PosSemidef) :
    AEStronglyMeasurable (fun τ => fidOp (A τ, B τ)) μ := by
  have hpair : AEMeasurable (fun τ => (A τ, B τ)) μ := hA.prodMk hB
  have hmem : ∀ᵐ x ∂(Measure.map (fun τ => (A τ, B τ)) μ), x ∈ psdProd n :=
    (ae_map_iff hpair isClosed_psdProd.measurableSet).mpr
      (by filter_upwards [hpsd] with τ hτ using hτ)
  have hmap : (Measure.map (fun τ => (A τ, B τ)) μ).restrict (psdProd n)
      = Measure.map (fun τ => (A τ, B τ)) μ :=
    Measure.restrict_eq_self_of_ae_mem hmem
  have hfidmeas : AEMeasurable fidOp (Measure.map (fun τ => (A τ, B τ)) μ) := by
    have := fidOp_continuousOn.aemeasurable (μ := Measure.map (fun τ => (A τ, B τ)) μ)
      isClosed_psdProd.measurableSet
    rwa [hmap] at this
  exact (aestronglyMeasurable_iff_aemeasurable).mpr (hfidmeas.comp_aemeasurable hpair)

/-- `fidOp (0, 0) = 0`. -/
lemma fidOp_zero {n : ℕ} [NeZero n] : fidOp ((0 : Op n), (0 : Op n)) = 0 := by
  calc fidOp ((0 : Op n), (0 : Op n))
      = fidelity (0 : PosSemidefOp n) 0 := fidOp_eq_fidelity 0 0
    _ = (Matrix.trace ((0 : PosSemidefOp n).toOp)).re := fidelity_self_posSemidefOp 0
    _ = 0 := by
        rw [show ((0 : PosSemidefOp n).toOp) = (0 : Op n) from rfl, Matrix.trace_zero,
          Complex.zero_re]

/-- **Bochner-integral fidelity super-additivity (Jensen).**

For a probability measure `μ`, a measurable set `s`, and integrable PSD-valued
families `A`, `B`,
`∫_{s} F(A_τ, B_τ) dμ ≤ F(∫_{s} A_τ dμ, ∫_{s} B_τ dμ)`,
the integral analogue of `Quantum.Metrics.fidelity_sum_le_fidelity_sum`. -/
lemma setIntegral_fidOp_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n] {s : Set α}
    {A B : α → Op n}
    (hA_int : IntegrableOn A s μ) (hB_int : IntegrableOn B s μ)
    (hA_psd : ∀ τ, (A τ).PosSemidef) (hB_psd : ∀ τ, (B τ).PosSemidef)
    (hfid_int : IntegrableOn (fun τ => fidOp (A τ, B τ)) s μ) :
    ∫ τ in s, fidOp (A τ, B τ) ∂μ ≤
      fidOp (∫ τ in s, A τ ∂μ, ∫ τ in s, B τ ∂μ) := by
  set IA := ∫ τ in s, A τ ∂μ with hIA
  set IB := ∫ τ in s, B τ ∂μ with hIB
  have hIA_psd : IA.PosSemidef := matrix_setIntegral_posSemidef s A hA_int hA_psd
  have hIB_psd : IB.PosSemidef := matrix_setIntegral_posSemidef s B hB_int hB_psd
  by_cases hμs : μ s = 0
  · have hIA0 : IA = 0 := by rw [hIA, setIntegral_measure_zero _ hμs]
    have hIB0 : IB = 0 := by rw [hIB, setIntegral_measure_zero _ hμs]
    have hint0 : ∫ τ in s, fidOp (A τ, B τ) ∂μ = 0 := setIntegral_measure_zero _ hμs
    rw [hint0, hIA0, hIB0, fidOp_zero]
  · -- Jensen via the renormalized set average
    set c : ℝ := (μ.real s)⁻¹ with hc
    have hμs_top : μ s ≠ ⊤ := measure_ne_top μ s
    have hμreal_pos : 0 < μ.real s := by
      rw [Measure.real]; exact ENNReal.toReal_pos hμs hμs_top
    have hcpos : 0 < c := by rw [hc]; exact inv_pos.mpr hμreal_pos
    have hc_nonneg : 0 ≤ c := le_of_lt hcpos
    -- Jensen
    have hfi : IntegrableOn (fun τ => (A τ, B τ)) s μ := hA_int.prodMk hB_int
    have hfs : ∀ᵐ x ∂μ.restrict s, (A x, B x) ∈ psdProd n :=
      ae_of_all _ (fun x => ⟨hA_psd x, hB_psd x⟩)
    have key := ConcaveOn.le_map_set_average (μ := μ) (s := psdProd n)
      (f := fun τ => (A τ, B τ)) (t := s) (g := fidOp)
      fidOp_concaveOn fidOp_continuousOn isClosed_psdProd hμs hμs_top hfs hfi hfid_int
    -- rewrite the averages
    have hpair_avg : (⨍ τ in s, (A τ, B τ) ∂μ) = (c • IA, c • IB) := by
      rw [setAverage_eq, integral_pair hA_int hB_int]; rfl
    have hsmul : fidOp (c • IA, c • IB) = c * fidOp (IA, IB) := by
      have h := fidOp_smul (a := c) hc_nonneg
        (PosSemidefOp.ofMatrix IA hIA_psd) (PosSemidefOp.ofMatrix IB hIB_psd)
      simpa using h
    rw [hpair_avg, hsmul, setAverage_eq, smul_eq_mul] at key
    exact le_of_mul_le_mul_left key hcpos

/-- The real-trace continuous linear functional on operators. -/
def traceReCLM (N : ℕ) : Op N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun M => (Matrix.trace M).re
    map_add' := fun A B => by rw [Matrix.trace_add, Complex.add_re]
    map_smul' := fun r A => by
      change (Matrix.trace (r • A)).re = r • (Matrix.trace A).re
      rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul] }

@[simp] lemma traceReCLM_apply {N : ℕ} (M : Op N) : traceReCLM N M = (Matrix.trace M).re := rfl

/-- The real trace of a Bochner set integral is the set integral of the real traces. -/
lemma setIntegral_trace_re {α : Type*} [MeasurableSpace α] {μ : Measure α} {N : ℕ}
    (s : Set α) (F : α → Op N) (h_int : IntegrableOn F s μ) :
    (∫ τ in s, F τ ∂μ).trace.re = ∫ τ in s, (F τ).trace.re ∂μ :=
  ((traceReCLM N).integral_comp_comm h_int).symm

/-- The block trace function is integrable on the good branch. -/
lemma integrableOn_blockTrace {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    IntegrableOn (fun τ : DensityOp d => ((g τ).stateMap x).trace) goodSet μ.measure :=
  (traceReCLM dE).integrable_comp h_int.restrict

/-- The real trace of a good-branch block is the set integral of the block traces. -/
lemma goodBranchBlockOp_trace_re_eq_setIntegral {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    (goodBranchBlockOp μ g goodSet x).trace.re
      = ∫ τ in goodSet, ((g τ).stateMap x).trace ∂μ.measure := by
  rw [goodBranchBlockOp_eq_setIntegral μ g goodSet x h_int.restrict,
    setIntegral_trace_re goodSet (fun τ => ((g τ).stateMap x).toOp) h_int.restrict]
  rfl

/-- The total block weight of a restricted mixture is the integral of its component weights. -/
lemma sum_goodBranchBlockOp_trace_re_eq_setIntegral {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    ∑ x, (goodBranchBlockOp μ g goodSet x).trace.re =
      ∫ τ in goodSet, ∑ x, ((g τ).stateMap x).trace ∂μ.measure := by
  rw [MeasureTheory.integral_finsetSum _
    (fun x _ => integrableOn_blockTrace μ g goodSet x (h_int x))]
  exact Finset.sum_congr rfl
    (fun x _ => goodBranchBlockOp_trace_re_eq_setIntegral μ g goodSet x (h_int x))

/-- Each good-branch block of `g` has real trace at most one. -/
lemma goodBranchBlockOp_g_trace_le_one {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (h_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    (goodBranchBlockOp μ g goodSet x).trace.re ≤ 1 := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  rw [goodBranchBlockOp_trace_re_eq_setIntegral μ g goodSet x h_int]
  calc ∫ τ in goodSet, ((g τ).stateMap x).trace ∂μ.measure
      ≤ ∫ _τ in goodSet, (1 : ℝ) ∂μ.measure :=
        MeasureTheory.integral_mono_of_nonneg
          (ae_of_all _ fun τ => ((g τ).stateMap x).trace_nonneg)
          integrableOn_const
          (ae_of_all _ fun τ => ((g τ).stateMap x).trace_le_one)
    _ = μ.measure.real goodSet := by rw [setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ 1 := measureReal_le_one

/-- The total good-branch weight of `g` is at most one. -/
lemma goodBranchBlockOp_g_weight_le_one {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    ∑ x : X, (goodBranchBlockOp μ g goodSet x).trace.re ≤ 1 := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  rw [sum_goodBranchBlockOp_trace_re_eq_setIntegral μ g goodSet h_int]
  calc ∫ τ in goodSet, ∑ x : X, ((g τ).stateMap x).trace ∂μ.measure
      ≤ ∫ _τ in goodSet, (1 : ℝ) ∂μ.measure :=
        MeasureTheory.integral_mono_of_nonneg
          (ae_of_all _ fun τ =>
            Finset.sum_nonneg fun x _ => ((g τ).stateMap x).trace_nonneg)
          integrableOn_const
          (ae_of_all _ fun τ => (g τ).weight_le_one)
    _ = μ.measure.real goodSet := by rw [setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ 1 := measureReal_le_one

/-- Construct the good-branch CQ state of `g` from block integrability alone. -/
lemma exists_goodBranchCQState_g {d dE : ℕ} {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    ∃ ρ_good' : CQState X dE,
      ∀ x : X, (ρ_good'.stateMap x).toOp = goodBranchBlockOp μ g goodSet x :=
  exists_goodBranchCQState_of_block_conditions μ g goodSet
    (fun x => goodBranchBlockOp_isHermitian_of_integrable μ g goodSet x (h_int x).restrict)
    (fun x => goodBranchBlockOp_quadraticForm_re_nonneg_of_integrable μ g goodSet x (h_int
        x).restrict)
    (fun x => goodBranchBlockOp_g_trace_le_one μ g goodSet x (h_int x))
    (goodBranchBlockOp_g_weight_le_one μ g goodSet h_int)

/-- **Integral Cauchy–Schwarz** (discriminant form):
`(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. -/
lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ with hA
  set B := ∫ x, f x * g x ∂μ with hB
  set C := ∫ x, g x ^ 2 ∂μ with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hC0 : 0 ≤ C := integral_nonneg fun x => sq_nonneg _
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hnn : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hi1 : Integrable (fun x => f x ^ 2 + (-(2 * t)) * (f x * g x)) μ :=
      hf2.add (hfg.const_mul _)
    have hi2 : Integrable (fun x => t ^ 2 * (g x ^ 2)) μ := hg2.const_mul _
    have hexp : ∫ x, (f x - t * g x) ^ 2 ∂μ = A - 2 * t * B + t ^ 2 * C := by
      have h1 : ∫ x, (f x - t * g x) ^ 2 ∂μ
          = ∫ x, (f x ^ 2 + (-(2 * t)) * (f x * g x) + t ^ 2 * (g x ^ 2)) ∂μ := by
        congr 1; funext x; ring
      rw [h1, integral_add hi1 hi2,
        integral_add hf2 (hfg.const_mul (-(2 * t))), integral_const_mul, integral_const_mul,
        ← hA, ← hB, ← hC]
      ring
    rw [hexp] at hnn; exact hnn
  rcases eq_or_lt_of_le hC0 with hCz | hCpos
  · -- C = 0 forces B = 0
    have hCeq : C = 0 := hCz.symm
    have hB0 : B = 0 := by
      by_contra hBne
      have h1 := key ((A + 1) / (2 * B))
      rw [hCeq] at h1
      have hcancel : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by
        field_simp
      rw [hcancel] at h1
      simp only [mul_zero, add_zero] at h1
      linarith
    rw [hB0, hCeq, mul_zero]; norm_num
  · -- C > 0, evaluate the discriminant at `t = B / C`
    have h1 := key (B / C)
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have heq : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    rw [heq] at h1
    have : B ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hCpos] at this
    linarith [this]

/-- **Integral sub-normalization correction** — the Bochner analogue of
`InfoTheory.SmoothMinEntropy.weighted_mixture_fidelityGen_ge`.

From a per-component generalized-fidelity floor `c ≤ fF τ + √((1-wf τ)(1-wg τ))`
(a.e. on `s`), with the missing-mass slack `1 - μ.real s` absorbed exactly as the
finite `w₀` term, the integrated quantities satisfy
`c ≤ ∫_s fF + √((1 - ∫_s wf)(1 - ∫_s wg))`. -/
lemma integral_fidelityGen_correction {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (s : Set α) {fF wf wg : α → ℝ} {c : ℝ}
    (hc1 : c ≤ 1)
    (hwf01 : ∀ᵐ τ ∂μ.restrict s, 0 ≤ wf τ ∧ wf τ ≤ 1)
    (hwg01 : ∀ᵐ τ ∂μ.restrict s, 0 ≤ wg τ ∧ wg τ ≤ 1)
    (hwf_int : IntegrableOn wf s μ) (hwg_int : IntegrableOn wg s μ)
    (hfF_int : IntegrableOn fF s μ)
    (hcomp : ∀ᵐ τ ∂μ.restrict s, c ≤ fF τ + Real.sqrt ((1 - wf τ) * (1 - wg τ))) :
    c ≤ (∫ τ in s, fF τ ∂μ) +
        Real.sqrt ((1 - ∫ τ in s, wf τ ∂μ) * (1 - ∫ τ in s, wg τ ∂μ)) := by
  classical
  set p : α → ℝ := fun τ => Real.sqrt (1 - wf τ) with hp
  set q : α → ℝ := fun τ => Real.sqrt (1 - wg τ) with hq
  -- a.e. facts
  have hp_sq : ∀ᵐ τ ∂μ.restrict s, p τ ^ 2 = 1 - wf τ := by
    filter_upwards [hwf01] with τ hτ using Real.sq_sqrt (sub_nonneg.mpr hτ.2)
  have hq_sq : ∀ᵐ τ ∂μ.restrict s, q τ ^ 2 = 1 - wg τ := by
    filter_upwards [hwg01] with τ hτ using Real.sq_sqrt (sub_nonneg.mpr hτ.2)
  have hpq_eq : ∀ᵐ τ ∂μ.restrict s, p τ * q τ = Real.sqrt ((1 - wf τ) * (1 - wg τ)) := by
    filter_upwards [hwf01] with τ hτ using (Real.sqrt_mul (sub_nonneg.mpr hτ.2) _).symm
  have hp_bound : ∀ᵐ τ ∂μ.restrict s, ‖p τ‖ ≤ 1 := by
    filter_upwards [hwf01] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (sub_le_self 1 hτ.1)
  have hq_bound : ∀ᵐ τ ∂μ.restrict s, ‖q τ‖ ≤ 1 := by
    filter_upwards [hwg01] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (sub_le_self 1 hτ.1)
  -- measurability/integrability
  have hp_aem : AEMeasurable p (μ.restrict s) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (aemeasurable_const.sub hwf_int.aemeasurable)
  have hq_aem : AEMeasurable q (μ.restrict s) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (aemeasurable_const.sub hwg_int.aemeasurable)
  have hp_int : IntegrableOn p s μ :=
    Integrable.of_bound hp_aem.aestronglyMeasurable 1 hp_bound
  have hq_int : IntegrableOn q s μ :=
    Integrable.of_bound hq_aem.aestronglyMeasurable 1 hq_bound
  have hpq_int : IntegrableOn (fun τ => p τ * q τ) s μ :=
    Integrable.of_bound (hp_aem.mul hq_aem).aestronglyMeasurable 1
      (by filter_upwards [hp_bound, hq_bound] with τ h1 h2
          rw [Real.norm_eq_abs, abs_mul]
          calc |p τ| * |q τ| ≤ 1 * 1 :=
                mul_le_mul (by rwa [← Real.norm_eq_abs]) (by rwa [← Real.norm_eq_abs])
                  (abs_nonneg _) (by norm_num)
            _ = 1 := by norm_num)
  have hp2_int : IntegrableOn (fun τ => p τ ^ 2) s μ :=
    ((integrable_const (1 : ℝ)).sub hwf_int).congr
      (by filter_upwards [hp_sq] with τ hτ using hτ.symm)
  have hq2_int : IntegrableOn (fun τ => q τ ^ 2) s μ :=
    ((integrable_const (1 : ℝ)).sub hwg_int).congr
      (by filter_upwards [hq_sq] with τ hτ using hτ.symm)
  -- key quantities
  set m : ℝ := μ.real s with hm
  have hm_le : m ≤ 1 := measureReal_le_one
  have hm_nonneg : 0 ≤ m := measureReal_nonneg
  set Tu : ℝ := ∫ τ in s, wf τ ∂μ with hTu
  set Tv : ℝ := ∫ τ in s, wg τ ∂μ with hTv
  set FF : ℝ := ∫ τ in s, fF τ ∂μ with hFF
  set Wsq : ℝ := ∫ τ in s, p τ * q τ ∂μ with hWsq
  -- ∫ p² = ∫(1-wf) = m - Tu
  have hWu : (∫ τ in s, p τ ^ 2 ∂μ) = m - Tu := by
    rw [MeasureTheory.integral_congr_ae hp_sq,
      integral_sub (integrable_const (1 : ℝ)) hwf_int, setIntegral_const, smul_eq_mul, mul_one]
  have hWv : (∫ τ in s, q τ ^ 2 ∂μ) = m - Tv := by
    rw [MeasureTheory.integral_congr_ae hq_sq,
      integral_sub (integrable_const (1 : ℝ)) hwg_int, setIntegral_const, smul_eq_mul, mul_one]
  -- Cauchy–Schwarz: Wsq² ≤ (m-Tu)(m-Tv)
  have hCS : Wsq ^ 2 ≤ (m - Tu) * (m - Tv) := by
    have h := integral_mul_sq_le (μ := μ.restrict s) hp2_int hq2_int hpq_int
    rw [← hWu, ← hWv]; exact h
  -- AM–GM: 2 Wsq ≤ (m-Tu) + (m-Tv)
  have hAMGM : 2 * Wsq ≤ (m - Tu) + (m - Tv) := by
    rw [← hWu, ← hWv, hWsq, ← integral_const_mul, ← integral_add hp2_int hq2_int]
    refine integral_mono_ae (hpq_int.const_mul 2) (hp2_int.add hq2_int) ?_
    -- pointwise `2 p q ≤ p² + q²`
    filter_upwards with τ
    rw [← mul_assoc]
    exact two_mul_le_add_sq _ _
  -- missing-mass slack
  set w0 : ℝ := 1 - m with hw0
  have hw0_nonneg : 0 ≤ w0 := by rw [hw0]; linarith
  have hstep : w0 + Wsq ≤ Real.sqrt ((w0 + (m - Tu)) * (w0 + (m - Tv))) := by
    apply Real.le_sqrt_of_sq_le
    -- `(w₀ + W)² = w₀² + w₀·2W + W²`, bounded termwise by AM–GM and Cauchy–Schwarz
    linarith [hCS, mul_le_mul_of_nonneg_left hAMGM hw0_nonneg]
  -- integrate the per-component floor
  have hcm : c * m ≤ FF + Wsq := by
    have hmono : (∫ _τ in s, c ∂μ) ≤ ∫ τ in s, (fF τ + p τ * q τ) ∂μ := by
      refine integral_mono_ae (integrable_const c) (hfF_int.add hpq_int) ?_
      filter_upwards [hcomp, hpq_eq] with τ h1 h2
      rw [h2]; exact h1
    rw [setIntegral_const, smul_eq_mul, integral_add hfF_int hpq_int] at hmono
    rw [← hFF, ← hWsq] at hmono
    exact (mul_comm c m).trans_le hmono
  -- assemble
  have hcw0 : c * w0 ≤ w0 := mul_le_of_le_one_left hw0_nonneg hc1
  calc c = c * m + c * w0 := by rw [hw0]; ring
    _ ≤ (FF + Wsq) + w0 := add_le_add hcm hcw0
    _ = FF + (w0 + Wsq) := by ring
    _ ≤ FF + Real.sqrt ((w0 + (m - Tu)) * (w0 + (m - Tv))) :=
        add_le_add le_rfl hstep
    _ = FF + Real.sqrt ((1 - Tu) * (1 - Tv)) := by
        rw [show w0 + (m - Tu) = 1 - Tu by rw [hw0]; ring,
          show w0 + (m - Tv) = 1 - Tv by rw [hw0]; ring]

/-- The per-block matrix fidelity is integrable on the good branch. -/
lemma integrableOn_fidOp_blocks {d dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (f g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (hf_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hg_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure) :
    IntegrableOn
      (fun τ => fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp)) goodSet μ.measure := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  refine Integrable.of_bound
    (aestronglyMeasurable_fidOp hf_int.restrict.aestronglyMeasurable.aemeasurable
      hg_int.restrict.aestronglyMeasurable.aemeasurable
      (ae_of_all _ fun τ => ⟨posSemidefOp_implies_mathlib _, posSemidefOp_implies_mathlib _⟩))
    1 (ae_of_all _ fun τ => ?_)
  have hfe : fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp)
      = fidelity ((f τ).stateMap x).toPosSemidefOp ((g τ).stateMap x).toPosSemidefOp :=
    fidOp_eq_fidelity _ _
  rw [Real.norm_eq_abs, hfe,
    abs_of_nonneg (fidelity_nonneg_posSemidefOp ((f τ).stateMap x).toPosSemidefOp
      ((g τ).stateMap x).toPosSemidefOp)]
  have hle := fidelity_le_sqrt_trace_mul_trace ((f τ).stateMap x).toPosSemidefOp
    ((g τ).stateMap x).toPosSemidefOp
  refine le_trans hle ?_
  rw [show ((1 : ℝ)) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_le_sqrt
  have ht1 : (Matrix.trace ((f τ).stateMap x).toOp).re ≤ 1 := ((f τ).stateMap x).trace_le_one
  have ht2 : (Matrix.trace ((g τ).stateMap x).toOp).re ≤ 1 := ((g τ).stateMap x).trace_le_one
  have hn1 : 0 ≤ (Matrix.trace ((f τ).stateMap x).toOp).re := ((f τ).stateMap x).trace_nonneg
  have hn2 : 0 ≤ (Matrix.trace ((g τ).stateMap x).toOp).re := ((g τ).stateMap x).trace_nonneg
  nlinarith

/-- Per-block Bochner fidelity super-additivity, with the good-branch blocks as centres. -/
lemma setIntegral_blockFidelity_le {d dE : ℕ} [NeZero dE] {X : Type*} [Fintype X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d) (f g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d)) (x : X)
    (hf_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hg_int : MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure)
    (ρ_good ρ_good' : CQState X dE)
    (hρ : (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    (hρ' : (ρ_good'.stateMap x).toOp = goodBranchBlockOp μ g goodSet x) :
    ∫ τ in goodSet, fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp) ∂μ.measure
      ≤ fidOp ((ρ_good.stateMap x).toOp, (ρ_good'.stateMap x).toOp) := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  have h := setIntegral_fidOp_le (μ := μ.measure) (s := goodSet)
    (A := fun τ => ((f τ).stateMap x).toOp) (B := fun τ => ((g τ).stateMap x).toOp)
    hf_int.restrict hg_int.restrict
    (fun τ => posSemidefOp_implies_mathlib _) (fun τ => posSemidefOp_implies_mathlib _)
    (integrableOn_fidOp_blocks μ f g goodSet x hf_int hg_int)
  rw [hρ, hρ', goodBranchBlockOp_eq_setIntegral μ f goodSet x hf_int.restrict,
    goodBranchBlockOp_eq_setIntegral μ g goodSet x hg_int.restrict]
  exact h

/-- **Continuous mixture smoothing transfer** — the generic Bochner-integral analogue of
`CQState.purifiedDistance_mixture_le_max` (Nahar et al. Lemma 14 / Renner Eq. 3.59, integral form).

The block integrability of both families is supplied; the good branch `ρ_good'` of `g` is
constructed, and the joint super-additivity (`setIntegral_blockFidelity_le`) plus the
sub-normalization correction (`integral_fidelityGen_correction`) deliver the
purified-distance bound. -/
theorem exists_continuousMixtureGoodBranch_purifiedDistance_le_of_integrable
    {d dE : ℕ} [NeZero dE] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (f g : DensityOp d → CQState X dE)
    (goodSet : Set (DensityOp d))
    (hf_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hg_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((g τ).stateMap x).toOp) μ.measure)
    (ρ_good : CQState X dE)
    (hρ_good : ∀ x : X, (ρ_good.stateMap x).toOp = goodBranchBlockOp μ f goodSet x)
    {εBar : ℝ} (hεBar : 0 ≤ εBar)
    (hg_ball : ∀ᵐ τ ∂μ.measure.restrict goodSet,
      CQState.purifiedDistance (f τ) (g τ) ≤ εBar) :
    ∃ ρ_good' : CQState X dE,
      (∀ x : X, (ρ_good'.stateMap x).toOp = goodBranchBlockOp μ g goodSet x) ∧
      CQState.purifiedDistance ρ_good ρ_good' ≤ εBar := by
  have : IsProbabilityMeasure μ.measure := μ.isProbability
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (dE * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne _)⟩
  obtain ⟨ρ_good', hρ_good'⟩ := exists_goodBranchCQState_g μ g goodSet hg_int
  refine ⟨ρ_good', hρ_good', ?_⟩
  -- abbreviations
  set fF : DensityOp d → ℝ := fun τ =>
    fidelity (f τ).toJointDensity.toPosSemidefOp (g τ).toJointDensity.toPosSemidefOp with hfF
  set wf : DensityOp d → ℝ := fun τ => (f τ).toJointDensity.trace with hwf
  set wg : DensityOp d → ℝ := fun τ => (g τ).toJointDensity.trace with hwg
  -- integrability of the joint trace / fidelity (via the block sums)
  have hwf_int : IntegrableOn wf goodSet μ.measure :=
    (MeasureTheory.integrable_finsetSum Finset.univ
      (fun x _ => integrableOn_blockTrace μ f goodSet x (hf_int x))).congr
      (by filter_upwards with τ using (CQState.toJointDensity_trace_eq_sum (f τ)).symm)
  have hwg_int : IntegrableOn wg goodSet μ.measure :=
    (MeasureTheory.integrable_finsetSum Finset.univ
      (fun x _ => integrableOn_blockTrace μ g goodSet x (hg_int x))).congr
      (by filter_upwards with τ using (CQState.toJointDensity_trace_eq_sum (g τ)).symm)
  have hfF_int : IntegrableOn fF goodSet μ.measure :=
    (MeasureTheory.integrable_finsetSum Finset.univ
      (fun x _ => integrableOn_fidOp_blocks μ f g goodSet x (hf_int x) (hg_int x))).congr
      (by filter_upwards with τ
          change ∑ x, fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp)
            = fidelity (f τ).toJointDensity.toPosSemidefOp (g τ).toJointDensity.toPosSemidefOp
          rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (f τ) (g τ)]
          exact Finset.sum_congr rfl (fun x _ => (fidOp_eq_fidelity _ _)))
  -- bounds on the joint traces
  have hwf01 : ∀ᵐ τ ∂μ.measure.restrict goodSet, 0 ≤ wf τ ∧ wf τ ≤ 1 :=
    ae_of_all _ (fun τ => ⟨(f τ).toJointDensity.trace_nonneg, (f τ).toJointDensity.trace_le_one⟩)
  have hwg01 : ∀ᵐ τ ∂μ.measure.restrict goodSet, 0 ≤ wg τ ∧ wg τ ≤ 1 :=
    ae_of_all _ (fun τ => ⟨(g τ).toJointDensity.trace_nonneg, (g τ).toJointDensity.trace_le_one⟩)
  -- per-component generalized-fidelity floor
  have hc1 : Real.sqrt (1 - εBar ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg εBar])
  have hcomp : ∀ᵐ τ ∂μ.measure.restrict goodSet,
      Real.sqrt (1 - εBar ^ 2) ≤ fF τ + Real.sqrt ((1 - wf τ) * (1 - wg τ)) := by
    filter_upwards [hg_ball] with τ hτ
    have h := InfoTheory.SmoothMinEntropy.fidelityGen_ge_sqrt_one_sub_sq_of_purifiedDistance_le
      (f τ).toJointDensity (g τ).toJointDensity hεBar hτ
    unfold fidelityGen at h
    exact h
  -- the correction lemma
  have hcorr := integral_fidelityGen_correction (μ := μ.measure) goodSet
    hc1 hwf01 hwg01 hwf_int hwg_int hfF_int hcomp
  -- joint super-additivity: ∫ fF ≤ F(ρ_good, ρ_good')
  have hsuper : (∫ τ in goodSet, fF τ ∂μ.measure)
      ≤ fidelity ρ_good.toJointDensity.toPosSemidefOp ρ_good'.toJointDensity.toPosSemidefOp := by
    have hL : (∫ τ in goodSet, fF τ ∂μ.measure)
        = ∑ x : X, ∫ τ in goodSet,
            fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp) ∂μ.measure := by
      rw [← MeasureTheory.integral_finsetSum _
        (fun x _ => integrableOn_fidOp_blocks μ f g goodSet x (hf_int x) (hg_int x))]
      refine MeasureTheory.integral_congr_ae (ae_of_all _ fun τ => ?_)
      change fidelity (f τ).toJointDensity.toPosSemidefOp (g τ).toJointDensity.toPosSemidefOp
        = ∑ x, fidOp (((f τ).stateMap x).toOp, ((g τ).stateMap x).toOp)
      rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (f τ) (g τ)]
      exact Finset.sum_congr rfl (fun x _ => (fidOp_eq_fidelity _ _).symm)
    rw [hL, CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity ρ_good ρ_good']
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hb := setIntegral_blockFidelity_le μ f g goodSet x (hf_int x) (hg_int x)
      ρ_good ρ_good' (hρ_good x) (hρ_good' x)
    rwa [fidOp_eq_fidelity (ρ_good.stateMap x).toPosSemidefOp
      (ρ_good'.stateMap x).toPosSemidefOp] at hb
  -- trace identities: ∫ wf = tr ρ_good.toJD, ∫ wg = tr ρ_good'.toJD
  have htrace : ∀ (h : DensityOp d → CQState X dE) (ρ : CQState X dE),
      (∀ x : X, MeasureTheory.Integrable
        (fun τ : DensityOp d => ((h τ).stateMap x).toOp) μ.measure) →
      (∀ x : X, (ρ.stateMap x).toOp = goodBranchBlockOp μ h goodSet x) →
      (∫ τ in goodSet, (h τ).toJointDensity.trace ∂μ.measure) = ρ.toJointDensity.trace := by
    intro h ρ hh_int hρ_eq
    rw [CQState.toJointDensity_trace_eq_sum ρ,
      MeasureTheory.integral_congr_ae
        (ae_of_all _ fun τ => CQState.toJointDensity_trace_eq_sum (h τ)),
      MeasureTheory.integral_finsetSum _
        (fun x _ => integrableOn_blockTrace μ h goodSet x (hh_int x))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← goodBranchBlockOp_trace_re_eq_setIntegral μ h goodSet x (hh_int x), ← hρ_eq x]
    rfl
  have hwf_trace : (∫ τ in goodSet, wf τ ∂μ.measure) = ρ_good.toJointDensity.trace :=
    htrace f ρ_good hf_int hρ_good
  have hwg_trace : (∫ τ in goodSet, wg τ ∂μ.measure) = ρ_good'.toJointDensity.trace :=
    htrace g ρ_good' hg_int hρ_good'
  -- assemble the generalized-fidelity floor
  have hfg_ge : Real.sqrt (1 - εBar ^ 2)
      ≤ fidelityGen ρ_good.toJointDensity ρ_good'.toJointDensity := by
    calc Real.sqrt (1 - εBar ^ 2)
        ≤ (∫ τ in goodSet, fF τ ∂μ.measure)
            + Real.sqrt ((1 - ∫ τ in goodSet, wf τ ∂μ.measure)
              * (1 - ∫ τ in goodSet, wg τ ∂μ.measure)) := hcorr
      _ = (∫ τ in goodSet, fF τ ∂μ.measure)
            + Real.sqrt ((1 - ρ_good.toJointDensity.trace)
              * (1 - ρ_good'.toJointDensity.trace)) := by rw [hwf_trace, hwg_trace]
      _ ≤ fidelity ρ_good.toJointDensity.toPosSemidefOp ρ_good'.toJointDensity.toPosSemidefOp
            + Real.sqrt ((1 - ρ_good.toJointDensity.trace)
              * (1 - ρ_good'.toJointDensity.trace)) := by linarith [hsuper]
      _ = fidelityGen ρ_good.toJointDensity ρ_good'.toJointDensity := rfl
  -- convert to the purified-distance bound
  have hfgsq : 1 - εBar ^ 2
      ≤ fidelityGen ρ_good.toJointDensity ρ_good'.toJointDensity ^ 2 := by
    have hc_nn := Real.sqrt_nonneg (1 - εBar ^ 2)
    have hfgnn := fidelityGen_nonneg ρ_good.toJointDensity ρ_good'.toJointDensity
    have hle : 1 - εBar ^ 2 ≤ Real.sqrt (1 - εBar ^ 2) ^ 2 := by
      by_cases h : 0 ≤ 1 - εBar ^ 2
      · rw [Real.sq_sqrt h]
      · push Not at h; nlinarith [sq_nonneg (Real.sqrt (1 - εBar ^ 2))]
    nlinarith [hfg_ge, hc_nn, hfgnn, hle]
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  calc Real.sqrt (1 - fidelityGen ρ_good.toJointDensity ρ_good'.toJointDensity ^ 2)
      ≤ Real.sqrt (εBar ^ 2) := Real.sqrt_le_sqrt (by linarith [hfgsq])
    _ = εBar := Real.sqrt_sq hεBar

end InfoTheory.SmoothMinEntropy

end
