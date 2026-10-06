import QCryptLean.InfoTheory.DeFinetti.Theorem.TensorPowerPushforward
import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Support facts for de Finetti Haar measures

This module records the topological support facts for Haar-pushforward de Finetti
measures.  In particular, partial tracing the bipartite pure-state Haar measure
has full open-positive support on one-system density operators, because every
density operator has a same-ancilla purification.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics MeasureTheory
open Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

private lemma exists_unitaryGroup_first_column
    {d : ℕ} [NeZero d] (ψ : Ket d) (hψ : ψ.dag * ψ = 1) :
    ∃ U : unitaryGroup (Fin d) ℂ,
      ∀ i : Fin d, (U : Matrix (Fin d) (Fin d) ℂ) i 0 = ψ.vec i := by
  let A : Matrix (Fin d) (Fin d) ℂ := Matrix.single 0 0 1
  let B : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j =>
    if j = 0 then ψ.vec i else 0
  have hgram : A.conjTranspose * A = B.conjTranspose * B := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · have hψ_sum : (∑ x : Fin d, star (ψ.vec x) * ψ.vec x) = 1 := by
        simpa [Ket.dag, bra_mul_ket_eq] using hψ
      simpa [A, B, Matrix.mul_apply, Matrix.single, hi, hj] using hψ_sum.symm
    · have h0j : ¬ 0 = j := fun h => hj h.symm
      simp [A, B, Matrix.mul_apply, Matrix.single, hi, hj, h0j]
    · have h0i : ¬ 0 = i := fun h => hi h.symm
      simp [A, B, Matrix.mul_apply, Matrix.single, hi, hj, h0i]
    · have h0i : ¬ 0 = i := fun h => hi h.symm
      have h0j : ¬ 0 = j := fun h => hj h.symm
      simp [A, B, Matrix.mul_apply, Matrix.single, hi, hj, h0i, h0j]
  obtain ⟨U, hU_left, hU_right, hUA⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      A B hgram
  refine ⟨⟨U, hU_left, hU_right⟩, ?_⟩
  intro i
  have hentry := congrFun (congrFun hUA i) 0
  simpa [A, B, Matrix.mul_apply, Matrix.single] using hentry

/-- Every pure density operator lies in the range of `pureStateMap`. -/
theorem exists_pureStateMap_eq_of_isPure
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (hρ : ρ.IsPure) :
    ∃ U : unitaryGroup (Fin d) ℂ, pureStateMap U = ρ := by
  let ψ := ρ.pureKetOf hρ
  have hψ : ψ.dag * ψ = 1 := ρ.pureKetOf_normalized hρ
  obtain ⟨U, hU0⟩ := exists_unitaryGroup_first_column ψ hψ
  refine ⟨U, ?_⟩
  apply DensityOp.ext
  ext i j
  calc
    (pureStateMap U).toOp i j
        = ψ.vec i * star (ψ.vec j) := by
          simp [pureStateMap, DensityOp.fromPure, hU0]
    _ = ρ.toOp i j := by
          rw [ρ.pureKetOf_entry hρ i j]

/-- The map from bipartite pure states sampled by Haar to one-system marginals is surjective. -/
theorem partialTraceB_pureStateMap_surjective
    {d : ℕ} [NeZero d] [NeZero (d * d)] :
    Function.Surjective
      (fun U : unitaryGroup (Fin (d * d)) ℂ =>
        (DensityOp.partialTraceB (pureStateMap U) : DensityOp d)) := by
  intro σ
  let τ : DensityOp (d * d) :=
    Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ
  have hτpure : τ.IsPure :=
    Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure σ
  obtain ⟨U, hU⟩ := exists_pureStateMap_eq_of_isPure τ hτpure
  refine ⟨U, ?_⟩
  apply DensityOp.ext
  change (DensityOp.partialTraceB (pureStateMap U)).toOp = σ.toOp
  rw [hU]
  exact Quantum.Metrics.KitaevWatrousPurification.partialTraceB_sameAncillaPurificationDensity σ

/-- Normalized Haar measure on the finite-dimensional unitary group is open-positive. -/
theorem haarProbUnitary_isOpenPosMeasure (d : ℕ) [NeZero d] :
    (haarProbUnitary d).IsOpenPosMeasure := by
  unfold haarProbUnitary
  have : (haarOnUnitary d).IsOpenPosMeasure := by
    unfold haarOnUnitary
    infer_instance
  exact Measure.isOpenPosMeasure_smul (μ := haarOnUnitary d)
    ((ENNReal.inv_ne_zero).2 (ne_of_lt (haarOnUnitary_finite d)))

/-- The partial-trace pushforward of bipartite Haar has full open-positive support. -/
theorem partialTraceBDensityMeasure_deFinetti_haarMeasure_isOpenPos
    (d : ℕ) [NeZero d] [NeZero (d * d)] :
    ((partialTraceBDensityMeasure (deFinetti_haarMeasure (d * d))).measure).IsOpenPosMeasure := by
  have : (haarProbUnitary (d * d)).IsOpenPosMeasure :=
    haarProbUnitary_isOpenPosMeasure (d * d)
  have hcont :
      Continuous
        ((DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d) ∘
          (@pureStateMap (d * d) _)) :=
    partialTraceB_continuous_general.comp pureStateMap_continuous
  have hsurj :
      Function.Surjective
        ((DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d) ∘
          (@pureStateMap (d * d) _)) := by
    simpa [Function.comp_def] using
      (partialTraceB_pureStateMap_surjective (d := d))
  rw [partialTraceBDensityMeasure_measure, deFinetti_haarMeasure_measure_eq_map]
  rw [Measure.map_map partialTraceB_measurable_general pureStateMap_measurable]
  exact Continuous.isOpenPosMeasure_map
    (μ := haarProbUnitary (d * d)) hcont hsurj

end InfoTheory.DeFinetti

end
