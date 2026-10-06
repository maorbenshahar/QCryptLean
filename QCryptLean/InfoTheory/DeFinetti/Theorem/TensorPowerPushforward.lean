import QCryptLean.InfoTheory.DeFinetti.Theorem.Interleaving

/-!
# Tensor-power pushforward identities

This file records the measure-pushforward step used in the CKMR de Finetti
proof: pushing a measure on bipartite density operators through `Tr_B` commutes
with taking the de Finetti tensor-power mixture, after deinterleaving the paired
tensor powers.
-/

open Quantum.Operators Quantum.TensorProducts Matrix MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-- Push forward a density-operator measure along the second-factor partial trace. -/
noncomputable def partialTraceBDensityMeasure {d : ℕ} [NeZero d]
    (ν : DensityMeasure (d * d)) : DensityMeasure d :=
  let f := (DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d)
  have hf : Measurable f := partialTraceB_measurable
  haveI := ν.isProbability
  { measure := Measure.map f ν.measure
    isProbability := by
      constructor
      rw [Measure.map_apply hf MeasurableSet.univ]
      simp only [Set.preimage_univ]
      exact IsProbabilityMeasure.measure_univ }

@[simp] theorem partialTraceBDensityMeasure_measure {d : ℕ} [NeZero d]
    (ν : DensityMeasure (d * d)) :
    (partialTraceBDensityMeasure ν).measure =
      Measure.map (DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d) ν.measure := rfl

/-- Tensor-power mixtures commute with the `Tr_B` pushforward measure.

Equivalently, if `μ` is the pushforward of `ν` by `Tr_B`, then
`∫ (Tr_B τ)^⊗k dν(τ)` is the partial trace of the deinterleaved mixture
`∫ τ^⊗k dν(τ)`. -/
theorem integralTensorPower_partialTraceBDensityMeasure
    {d k : ℕ} [NeZero d] [NeZero k]
    [NeZero (d * d)] [NeZero (d ^ k)] [NeZero ((d * d) ^ k)]
    (ν : DensityMeasure (d * d)) :
    integralTensorPower k (partialTraceBDensityMeasure ν) =
      DensityOp.partialTraceB
        (densityOp_reindex (interleavingEquiv d k).symm
          (integralTensorPower k ν)) := by
  let f := (DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d)
  have hf_meas : Measurable f := partialTraceB_measurable
  let μ : DensityMeasure d := partialTraceBDensityMeasure ν
  have hμ_measure : μ.measure = Measure.map f ν.measure := rfl
  let deintK := densityOp_reindex (interleavingEquiv d k).symm
  change integralTensorPower k μ =
    DensityOp.partialTraceB (deintK (integralTensorPower k ν))
  have h_pointwise : ∀ (τ : DensityOp (d * d)),
      (f τ).tensorPowGen k =
        DensityOp.partialTraceB (deintK (τ.tensorPowGen k)) :=
    fun τ => partialTraceB_tensorPow_eq τ
  apply DensityOp.ext
  ext i j
  have h_lhs : (integralTensorPower k μ).toOp i j =
      ∫ τ, ((f τ).tensorPowGen k).toOp i j ∂ν.measure := by
    change (Matrix.of fun a b =>
        ∫ σ, (σ.tensorPowGen k).toOp a b ∂μ.measure) i j = _
    simp only [Matrix.of_apply, hμ_measure]
    exact MeasureTheory.integral_map hf_meas.aemeasurable
      (by
        simpa [hμ_measure] using
          (integrable_tensorPow_entry (d := d) k i j μ).aestronglyMeasurable)
  have h_rhs : ((deintK (integralTensorPower k ν)).partialTraceB).toOp i j =
      ∫ τ, ((f τ).tensorPowGen k).toOp i j ∂ν.measure := by
    simp_rw [show ∀ τ : DensityOp (d * d), ((f τ).tensorPowGen k).toOp i j =
      ((deintK (τ.tensorPowGen k)).partialTraceB).toOp i j from
      fun τ => by rw [h_pointwise]]
    simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
      partialTraceB, Matrix.of_apply]
    have hdeintK : ∀ (σ : DensityOp ((d * d) ^ k)) (a b : Fin (d ^ k * d ^ k)),
        (deintK σ).toOp a b =
          σ.toOp ((interleavingEquiv d k) a) ((interleavingEquiv d k) b) := by
      intro σ a b
      simp [deintK, densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp_rw [hdeintK]
    simp only [integralTensorPower, Matrix.of_apply]
    rw [integral_finsetSum Finset.univ]
    intro x _
    set a := (interleavingEquiv d k) (finProdFinEquiv (i, x))
    set b := (interleavingEquiv d k) (finProdFinEquiv (j, x))
    simpa [a, b] using
      (integrable_tensorPow_entry (d := d * d) k a b ν)
  rw [h_lhs, h_rhs]

end InfoTheory.DeFinetti

end
