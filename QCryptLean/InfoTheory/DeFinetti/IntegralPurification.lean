import QCryptLean.InfoTheory.DeFinetti.PurificationAncillaEmbed
import QCryptLean.InfoTheory.DeFinetti.DeFinettiPrefactor
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Operators.MatrixIntegral

/-!
# Integrating and purifying the paired IID extension

`integrable_purificationDensityOp_tensorPowGen` and
`partialTraceB_integral_purificationDensityOp_tensorPowGen` describe the integral of canonical
IID purifications. Its paired-symmetric support gives a rank bound, and
`exists_isPure_partialTraceB_eq_integral_purificationDensityOp_tensorPowGen` purifies it with an
ancilla whose dimension is the de Finetti prefactor.

References: Nahar et al., arXiv:2403.11851, Appendix B's proof of Theorem 3,
`eq:splittingoffV` (main.tex:1391–1395) and the reference identification at main.tex:1418.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Quantum.Symmetry
open InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- The canonical IID purification is integrable against every density measure. -/
lemma integrable_purificationDensityOp_tensorPowGen {d n : ℕ} [NeZero d] [NeZero n]
    (μ : DensityMeasure d) :
    Integrable (fun σ : DensityOp d => (purificationDensityOp (σ.tensorPowGen n)).toOp)
      μ.measure := by
  have := μ.isProbability
  exact continuous_purificationDensityOp_tensorPowGen_toOp.integrable_of_compactSpace

/-- Integrating the canonical IID purifications recovers the de Finetti mixture
on the system register. -/
lemma partialTraceB_integral_purificationDensityOp_tensorPowGen {d n : ℕ} [NeZero d] [NeZero n]
    (μ : DensityMeasure d) :
    partialTraceB (∫ σ : DensityOp d,
      (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) =
        (integralTensorPower n μ).toOp := by
  rw [partialTraceB_integral _ (integrable_purificationDensityOp_tensorPowGen μ)]
  have hmarg (σ : DensityOp d) :
      partialTraceB (purificationDensityOp (σ.tensorPowGen n)).toOp =
        (σ.tensorPowGen n).toOp :=
    congrArg (fun ρ => ρ.toOp) (purificationDensityOp_partialTraceB (σ.tensorPowGen n))
  simp_rw [hmarg]
  exact (integralTensorPower_toOp_eq_integral n μ).symm

/-- The paired-symmetric projector supports the integral of canonical IID
purifications, since it supports each integrand. -/
lemma integral_purificationDensityOp_tensorPowGen_supported {d n : ℕ} [NeZero d] [NeZero n]
    (μ : DensityMeasure d) :
    symmetricProjectorPaired d n *
        (∫ σ : DensityOp d, (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
          symmetricProjectorPaired d n =
      ∫ σ : DensityOp d, (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := by
  let L := (LinearMap.mulRight ℂ (symmetricProjectorPaired d n)).comp
    (LinearMap.mulLeft ℂ (symmetricProjectorPaired d n))
  calc
    _ = ∫ σ : DensityOp d, L (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure :=
      (L.toContinuousLinearMap.integral_comp_comm
        (integrable_purificationDensityOp_tensorPowGen μ)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun σ =>
      purificationDensityOp_in_paired_symmetric_subspace _ (tensorPow_isPermutationInvariant σ))

/-- The integral of canonical IID purifications has rank at most the paired
symmetric-subspace dimension. -/
lemma rank_integral_purificationDensityOp_tensorPowGen_le {d n : ℕ} [NeZero d] [NeZero n]
    (μ : DensityMeasure d) :
    Matrix.rank (∫ σ : DensityOp d,
      (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) ≤
        deFinettiPrefactor (d ^ 2) n := by
  calc
    _ = Matrix.rank (symmetricProjectorPaired d n *
        (∫ σ : DensityOp d, (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
          symmetricProjectorPaired d n) :=
      congrArg Matrix.rank (integral_purificationDensityOp_tensorPowGen_supported μ).symm
    _ ≤ Matrix.rank (symmetricProjectorPaired d n) := Matrix.rank_mul_le_right _ _
    _ = _ := symmetricProjectorPaired_rank_eq_polyDim d n

/-- Appendix B's symmetric extension: a pure state on `(AⁿBⁿEⁿ) ⊗ V`,
with `dim V = g`, whose partial trace over `V` is the integrated IID purification. -/
lemma exists_isPure_partialTraceB_eq_integral_purificationDensityOp_tensorPowGen
    {d n : ℕ} [NeZero d] [NeZero n]
    (μ : DensityMeasure d) :
    ∃ ψ : DensityOp ((d ^ n * d ^ n) * deFinettiPrefactor (d ^ 2) n),
      ψ.IsPure ∧ partialTraceB ψ.toOp =
        ∫ σ : DensityOp d, (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := by
  have : NeZero (deFinettiPrefactor (d ^ 2) n) :=
    ⟨(deFinettiPrefactor_pos (d ^ 2) n).ne'⟩
  have := μ.isProbability
  let ρ := DensityOp.integral μ.measure
    (fun σ : DensityOp d => purificationDensityOp (σ.tensorPowGen n))
    (integrable_purificationDensityOp_tensorPowGen μ)
  exact densityOp_purification_exists_of_rank_le
    (r := deFinettiPrefactor (d ^ 2) n) ρ (rank_integral_purificationDensityOp_tensorPowGen_le μ)

end InfoTheory.DeFinetti
