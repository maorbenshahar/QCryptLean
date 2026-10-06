import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mixture entropy and register extension

Finite post-filter entropy floors pass to the mixture and its register extension. Dimension
penalties are finite additive charges in `ENNReal`, avoiding subtraction from an infinite entropy.
-/

open Quantum.Operators Quantum.TensorProducts MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

variable {d dE : ℕ} [NeZero d] [NeZero dE] {X : Type*}
  [Fintype X] [DecidableEq X] [Nonempty X]

/-- An extended component floor survives the post-filter mixture over a closed accepting set
and register extension with an additive dimension penalty. Continuity supplies integrability,
and the bad-branch trace bound supplies `0 ≤ ε`. Infinite floors remain infinite. -/
theorem smoothMinEntropy_registerExtended_le_add_of_deFinetti_postFilter_floor
    (dV : ℕ) [NeZero dV]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (mixCQ_En : CQState X dE) (mixCQ : CQState X (dE * dV))
    (f : DensityOp d → CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (mixCQ.stateMap x).toOp = (mixCQ_En.stateMap x).toOp)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (mixCQ_En.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d)) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (K : ENNReal) (εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P → K ≤ smoothMinEntropy εBar (f τ) σE) :
    K ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε)) mixCQ (σE.tensorMaxMixed dV) +
      ENNReal.ofReal (2 * Real.logb 2 (dV : ℝ)) := by
  have hEn : K ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε)) mixCQ_En σE := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hf : ∀ τ ∈ goodSet, τ ∈ P →
        ENNReal.ofReal (r : ℝ) ≤ smoothMinEntropy εBar (f τ) σE := by
      intro τ hτ hP
      simpa only [ENNReal.ofReal_coe_nnreal] using hr.le.trans (hf_smoothFloor τ hτ hP)
    simpa only [ENNReal.ofReal_coe_nnreal] using
      smoothMinEntropy_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
        μ mixCQ_En f σE hf_lin hcont goodSet hClosed P hP_closed hP_ae
        r εBar ε hεBar_nonneg h_badBranch_traceNorm hf
  have hext := smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    mixCQ mixCQ_En σE hblocks (εBar + Real.sqrt (2 * ε))
  simpa only [Real.logb, mul_div_assoc] using hEn.trans hext

/-- Finite signed component floors yield a completed extended floor after the post-filter
mixture over a closed accepting set and register penalty. Continuity supplies integrability,
and the bad-branch trace bound supplies `0 ≤ ε`. No retained-mass or boundedness premise is
needed. -/
theorem smoothMinEntropy_registerExtended_ge_of_deFinetti_postFilter_finiteSmoothFloor
    (dV : ℕ) [NeZero dV]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (mixCQ_En : CQState X dE) (mixCQ : CQState X (dE * dV))
    (f : DensityOp d → CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (mixCQ.stateMap x).toOp = (mixCQ_En.stateMap x).toOp)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (mixCQ_En.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d)) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (f τ) σE) :
    ENNReal.ofReal (k - 2 * Real.logb 2 (dV : ℝ)) ≤
      smoothMinEntropy (εBar + Real.sqrt (2 * ε)) mixCQ (σE.tensorMaxMixed dV) := by
  have h := smoothMinEntropy_registerExtended_le_add_of_deFinetti_postFilter_floor
    dV μ mixCQ_En mixCQ f σE hblocks hf_lin hcont goodSet hClosed P hP_closed hP_ae
    (ENNReal.ofReal k) εBar ε hεBar_nonneg h_badBranch_traceNorm hf_smoothFloor
  have hp : 0 ≤ 2 * Real.logb 2 (dV : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast NeZero.pos dV)
  rw [ENNReal.ofReal_sub k hp]
  exact tsub_le_iff_right.mpr h


/-- A signed floor on the accepting components transfers to the register-extended mixture with
radius `εBar + sqrt (2 * ε)` and floor `k - 2 * logb 2 dV`. -/
theorem smoothMinEntropyReal_registerExtended_ge_of_deFinetti_postFilter_finiteSmoothFloor
    (dV : ℕ) [NeZero dV]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (mixCQ_En : CQState X dE) (mixCQ : CQState X (dE * dV))
    (f : DensityOp d → CQState X dE)
    (σE : SubDensityOp dE) (hσE : σE.toOp.PosDef)
    (hblocks : ∀ x : X,
      partialTraceB (mixCQ.stateMap x).toOp = (mixCQ_En.stateMap x).toOp)
    (h_int : ∀ x : X, MeasureTheory.Integrable
      (fun τ : DensityOp d => ((f τ).stateMap x).toOp) μ.measure)
    (hf_lin : ∀ (x : X) (i j : Fin dE),
      (mixCQ_En.stateMap x).toOp i j =
        ∫ τ : DensityOp d, ((f τ).stateMap x).toOp i j ∂μ.measure)
    (hcont : ∀ x : X, Continuous (fun τ : DensityOp d => ((f τ).stateMap x).toOp))
    (goodSet : Set (DensityOp d)) (hMeas : MeasurableSet goodSet) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp d)) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ τ ∂μ.measure, τ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (hsum_lt_one : εBar + Real.sqrt (2 * ε) < 1)
    (h_subNorm : 2 * (εBar + Real.sqrt (2 * ε)) < ∑ x : X, (mixCQ_En.stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : X, ((Matrix.of fun i j : Fin dE =>
          ∫ τ in goodSetᶜ, ((f τ).stateMap x).toOp i j ∂μ.measure : Op dE).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ τ ∈ goodSet, τ ∈ P → k ≤ smoothMinEntropyReal εBar (f τ) σE) :
    k - 2 * Real.logb 2 (dV : ℝ)
      ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) mixCQ (σE.tensorMaxMixed dV) := by
  have hEn : k ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) mixCQ_En σE :=
    smoothMinEntropyReal_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized
      μ mixCQ_En f σE hσE h_int hf_lin hcont goodSet hMeas hClosed P hP_closed hP_ae
      k εBar ε hεBar_nonneg hε_nonneg hε_lt_half hsum_lt_one h_subNorm
      h_badBranch_traceNorm hf_smoothFloor
  have hrad_nn : 0 ≤ εBar + Real.sqrt (2 * ε) :=
    add_nonneg hεBar_nonneg (Real.sqrt_nonneg _)
  have hB17 :
      smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) mixCQ_En σE
          - 2 * Real.log (dV : ℝ) / Real.log 2
        ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) mixCQ (σE.tensorMaxMixed dV) :=
    smoothMinEntropyReal_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
      mixCQ mixCQ_En σE hblocks (εBar + Real.sqrt (2 * ε)) hrad_nn
  have hlogb : Real.logb 2 (dV : ℝ) = Real.log (dV : ℝ) / Real.log 2 := rfl
  rw [mul_div_assoc] at hB17
  rw [hlogb]
  linarith [hEn, hB17]

end InfoTheory.SmoothMinEntropy

end
