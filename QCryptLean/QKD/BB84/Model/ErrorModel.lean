import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.BellStates
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.CastDim
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Math.CodingTheory.CSS.Codes
import QCryptLean.InfoTheory.Measurement.POVM
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.Main
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Additivity
import QCryptLean.Math.Concentration.SamplingBounds
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.InfoTheory.DeFinetti.Theorem.Main
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# BB84 error model — error projectors, error rates and Bell dephasing

Core definitions and infrastructure for BB84 quantum key distribution security analysis.
Defines the bit/phase flip error projectors, the single-round error-rate observables and the
Bell dephasing channel.

## Main definitions

* `bitFlipProjector`, `phaseFlipProjector` — error measurement projectors.
* `bitFlipErrorRate_single`, `phaseFlipErrorRate_single` — single-round error rates.
* `bellDephasing` — the Bell-basis dephasing channel.

## Main results

* `phaseFlipProjector_is_projector` — `phaseFlipProjector` is idempotent and Hermitian.
* `phaseFlipErrorRate_single_continuous`, `_measurable` — regularity of the phase-flip rate.
* `phaseFlipErrorRate_single_bounds` — the phase-flip rate lies in `[0, 1]`.
-/

open Quantum.Operators Quantum.TensorProducts Math.RepresentationTheory
open scoped ComplexOrder BigOperators

noncomputable section

namespace QKD.BB84.Model

open Quantum.Basis.BellStates Math.CodingTheory.CSS InfoTheory.Measurement
open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy Quantum.Metrics InfoTheory.RelativeEntropy
open MeasureTheory ProbabilityTheory

/-- For a projector Π and PSD operator ρ, Tr(Πρ) ≥ 0. -/
lemma trace_projector_psd_nonneg (P : Op 4) (ρ : PosSemidefOp 4)
    (h_proj : P * P = P) (h_herm : P† = P) :
    0 ≤ (P * ρ.toOp).trace.re := by
  have hρpsd := posSemidefOp_implies_mathlib ρ
  have hconj := Matrix.PosSemidef.conjTranspose_mul_mul_same hρpsd P
  rw [h_herm] at hconj
  have heq : (P * ρ.toOp).trace.re = (P * ρ.toOp * P).trace.re := by
    congr 1
    calc (P * ρ.toOp).trace
        = ((P * P) * ρ.toOp).trace := by rw [h_proj]
      _ = (ρ.toOp * P * P).trace := Matrix.trace_mul_cycle P P ρ.toOp
      _ = (P * ρ.toOp * P).trace := Matrix.trace_mul_cycle ρ.toOp P P
  rw [heq]
  have htrace_nonneg := Matrix.PosSemidef.trace_nonneg hconj
  exact (RCLike.nonneg_iff.mp htrace_nonneg).1

/-!
## Error Projectors

Projectors for detecting bit flip and phase flip errors on Bell states.
-/

/-- Bit flip projector onto |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁| -/
def bitFlipProjector : Op 4 :=
  (bellState01 * bellState01.dag) + (bellState11 * bellState11.dag)

/-- Phase flip projector onto |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁| -/
def phaseFlipProjector : Op 4 :=
  (bellState10 * bellState10.dag) + (bellState11 * bellState11.dag)

/-- Phase flip projector is a projector: `Π * Π = Π` and `Π† = Π`. -/
theorem phaseFlipProjector_is_projector :
    phaseFlipProjector * phaseFlipProjector = phaseFlipProjector ∧
    phaseFlipProjector† = phaseFlipProjector := by
  refine ⟨?_, ?_⟩
  · unfold phaseFlipProjector
    rw [add_mul, mul_add, mul_add,
        ketbra_idempotent bellState10 bellState10_normalized,
        ketbra_orthogonal_mul_zero bellState10 bellState11 bell10_11_orthogonal,
        ketbra_orthogonal_mul_zero bellState11 bellState10 bell11_10_orthogonal,
        ketbra_idempotent bellState11 bellState11_normalized]
    simp only [add_zero, zero_add]
  · unfold phaseFlipProjector
    rw [Matrix.conjTranspose_add, ketbra_hermitian bellState10,
        ketbra_hermitian bellState11]

/-!
## Error Rates and Random Sampling

The error rate determines the fidelity with the ideal Bell state.
Random sampling allows estimation of the error rate.
-/

/-- Bit flip error rate for a single Bell pair: Tr(Π_bf · ρ)

    For a density operator on dimension 4 (single Bell pair),
    this is the probability of detecting a bit flip error.

    For n Bell pairs (dimension 4^n), we define the average per-pair error rate
    using partial traces. In the i.i.d. error model, this equals the per-pair rate. -/
def bitFlipErrorRate_single (ρ : DensityOp 4) : ℝ :=
  (bitFlipProjector * ρ.toOp).trace.re

/-- Phase flip error rate for a single Bell pair: Tr(Π_pf · ρ) -/
def phaseFlipErrorRate_single (ρ : DensityOp 4) : ℝ :=
  (phaseFlipProjector * ρ.toOp).trace.re

/-- Pairing a density operator with a fixed matrix via `Tr(Aρ)` is continuous. -/
lemma continuous_trace_mul_densityOp_toOp {d : ℕ} (A : Op d) :
    Continuous (fun ρ : DensityOp d => (A * ρ.toOp).trace) := by
  unfold Matrix.trace Matrix.diag
  apply continuous_finsetSum
  intro i _
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (((continuous_apply i).comp
    ((continuous_apply k).comp continuous_induced_dom)))

/-- The single-round phase-flip error rate is continuous. -/
lemma phaseFlipErrorRate_single_continuous :
    Continuous phaseFlipErrorRate_single := by
  simpa [phaseFlipErrorRate_single] using
    (Complex.continuous_re.comp (continuous_trace_mul_densityOp_toOp phaseFlipProjector))

/-- The single-round phase-flip error rate is measurable. -/
lemma phaseFlipErrorRate_single_measurable :
    Measurable phaseFlipErrorRate_single :=
  phaseFlipErrorRate_single_continuous.measurable

/-- Helper: for any projector P and density operator ρ (any dimension), Tr(P * ρ) ∈ [0, 1]. -/
private lemma trace_projector_density_bounds {N : ℕ} (P : Op N) (ρ : DensityOp N)
    (h_proj : P * P = P) (h_herm : P† = P) :
    0 ≤ (P * ρ.toOp).trace.re ∧ (P * ρ.toOp).trace.re ≤ 1 := by
  have hρpsd := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have hP_psd : P.PosSemidef := by
    rw [show P = P† * P from by rw [h_herm, h_proj]]
    exact Matrix.posSemidef_conjTranspose_mul_self P
  have h_lower : 0 ≤ (P * ρ.toOp).trace.re := by
    rw [Matrix.trace_mul_comm]
    exact Quantum.Operators.trace_mul_psd_nonneg ρ.toOp P hρpsd hP_psd
  have h_upper : (P * ρ.toOp).trace.re ≤ 1 := by
    rw [Matrix.trace_mul_comm]
    have h1mP_nonneg : 0 ≤ (ρ.toOp * (1 - P)).trace.re :=
      Quantum.Operators.trace_mul_psd_nonneg ρ.toOp (1 - P) hρpsd
        (projector_complement_posSemidef (P := P) h_proj h_herm)
    have h_split : (ρ.toOp * (1 - P)).trace.re = 1 - (ρ.toOp * P).trace.re := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
          ρ.trace_one, Complex.one_re]
    linarith [h_split ▸ h1mP_nonneg]
  exact ⟨h_lower, h_upper⟩

/-- Phase flip error rate for a single Bell pair is bounded in `[0, 1]`. -/
theorem phaseFlipErrorRate_single_bounds (ρ : DensityOp 4) :
    0 ≤ phaseFlipErrorRate_single ρ ∧ phaseFlipErrorRate_single ρ ≤ 1 :=
  trace_projector_density_bounds phaseFlipProjector ρ
    phaseFlipProjector_is_projector.1 phaseFlipProjector_is_projector.2

/-- Bell dephasing map: projects ρ onto the Bell-diagonal subspace.

    Δ(ρ) = Σᵢ pᵢ |βᵢ⟩⟨βᵢ| where pᵢ = F²(ρ, |βᵢ⟩⟨βᵢ|) = DensityOp.fidelitySq ρ (fromPure βᵢ)

    This removes all off-diagonal coherences in the Bell basis while preserving
    the diagonal elements (Bell fidelities). -/
def bellDephasing (ρ : DensityOp 4) : Op 4 :=
  DensityOp.fidelitySq ρ
      (DensityOp.fromPure bellState00 bellState00_normalized) •
    (bellState00 * bellState00.dag) +
    DensityOp.fidelitySq ρ
        (DensityOp.fromPure bellState01 bellState01_normalized) •
      (bellState01 * bellState01.dag) +
    DensityOp.fidelitySq ρ
        (DensityOp.fromPure bellState10 bellState10_normalized) •
      (bellState10 * bellState10.dag) +
    DensityOp.fidelitySq ρ
        (DensityOp.fromPure bellState11 bellState11_normalized) •
      (bellState11 * bellState11.dag)

end QKD.BB84.Model
