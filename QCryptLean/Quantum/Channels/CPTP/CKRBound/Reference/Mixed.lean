import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Operators.MatrixIntegral
import QCryptLean.Quantum.Metrics.TraceNormIntegral
import Mathlib.Analysis.Matrix.Normed

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-!
# CKR Mixed Paired References — reindexed Haar integrals and tensor-power transport

Bochner-integral infrastructure identifying the paired CKR reference state with
an interleaved Haar tensor-power integral. This is the mixed-extension step used
to transfer pure paired collective bounds to `pairedDeFinettiState`.

## Main definitions
- This file defines no new data structures.

## Main statements
- `continuous_reindexed_tensorPowGen_toOp`: continuity of the reindexed paired tensor-power map
- `pairedDeFinettiState_eq_reindex_deFinettiState`: paired reference as an
  interleaved ordinary de Finetti state
- `pairedDeFinettiState_eq_haar_integral_paired`: paired reference as a reindexed Haar integral
- `integrable_reindexed_tensorPowGen_toOp`: Bochner integrability of reindexed tensor powers
- `densityOp_reindex_integralTensorPower_toOp`: reindexing commutes with tensor-power integration
- `mapTensorId_reindex_integral_commute`: `mapTensorId` commutes with the reindexed integral
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Reindexing the paired tensor power along the interleaving equivalence depends
    continuously on the underlying pure state. -/
lemma continuous_reindexed_tensorPowGen_toOp
    {d n : ℕ} [NeZero d] [NeZero n] :
    Continuous fun σ : DensityOp (d * d) =>
      (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp := by
  refine continuous_matrix ?_
  intro a b
  simpa [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply] using
    (InfoTheory.DeFinetti.PureState.continuous_tensorPowGen_entry
      (d := d * d) (n := n)
      ((interleavingEquiv d n) a) ((interleavingEquiv d n) b))

/-- The paired symmetric projector has the same trace as the ordinary symmetric
projector after interleaving the two tensor registers. -/
lemma symmetricProjectorPaired_trace_eq_interleaved
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d * d)] [NeZero ((d * d) ^ n)] :
    Matrix.trace (symmetricProjectorPaired d n) =
      Matrix.trace (symmetricProjector (d * d) n) := by
  rw [symmetricProjectorPaired_trace_eq, symmetricProjector_trace]
  have hd : 1 ≤ d * d := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (NeZero.pos d) (NeZero.pos d))
  rw [Nat.add_sub_assoc hd]
  simp [pow_two]

/-- Entrywise form of the interleaving equivalence between the paired and
ordinary symmetric projectors. -/
lemma symmetricProjectorPaired_apply_eq_interleaved
    (d n : ℕ) [NeZero d] [NeZero n]
    (i j : Fin (d ^ n * d ^ n)) :
    symmetricProjectorPaired d n i j =
      symmetricProjector (d * d) n ((interleavingEquiv d n) i) ((interleavingEquiv d n) j) := by
  have h :=
    congrArg
      (fun M => M ((interleavingEquiv d n) i) ((interleavingEquiv d n) j))
      (InfoTheory.DeFinetti.interleavingEquiv_conjugates_projector (d := d) (n := n))
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h

/-- Reindexing the paired symmetric reference state identifies it with the
ordinary de Finetti state on the local dimension `d * d`. -/
theorem pairedDeFinettiState_eq_reindex_deFinettiState (d n : ℕ) [NeZero d] [NeZero n]
    [NeZero (d * d)] [NeZero ((d * d) ^ n)] :
    pairedDeFinettiState d n =
      densityOp_reindex (interleavingEquiv d n).symm
        (InfoTheory.DeFinetti.deFinettiState (d * d) n) := by
  apply DensityOp.ext
  rw [pairedDeFinettiState_eq_of_neZero (d := d) (n := n)]
  ext i j
  have h_trace :
      Matrix.trace (symmetricProjectorPaired d n) =
        Matrix.trace (symmetricProjector (d * d) n) := by
    exact symmetricProjectorPaired_trace_eq_interleaved d n
  simp [pairedDeFinettiStateOfNeZero, densityOp_reindex,
    InfoTheory.DeFinetti.deFinettiState, Matrix.reindex_apply,
    Matrix.submatrix_apply, symmetricProjectorPaired_apply_eq_interleaved, h_trace]

/-- The paired de Finetti state is the Haar integral of pure tensor powers on
`H ⊗ K`, reindexed from the interleaved encoding to the paired registers. -/
theorem pairedDeFinettiState_eq_haar_integral_paired (d n : ℕ) [NeZero d] [NeZero n]
    [NeZero (d * d)] [NeZero ((d * d) ^ n)] :
    pairedDeFinettiState d n =
      densityOp_reindex (interleavingEquiv d n).symm
        (InfoTheory.DeFinetti.integralTensorPower n
          (InfoTheory.DeFinetti.deFinetti_haarMeasure (d * d))) := by
  rw [pairedDeFinettiState_eq_reindex_deFinettiState d n,
    InfoTheory.DeFinetti.deFinettiState_eq_haar_integral (d * d) n]

/-- A square matrix whose entries all have norm at most one has Frobenius norm
at most its dimension. -/
lemma frobenius_norm_op_le_dim_of_entry_norm_le_one {m : ℕ} (A : Op m)
    (h_entry : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A‖ ≤ (m : ℝ) := by
  have h_sq_le : ∀ i j, ‖A i j‖ ^ 2 ≤ 1 := by
    intro i j
    nlinarith [h_entry i j, norm_nonneg (A i j)]
  have h_sum_le_nat : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (m : ℝ) ^ 2 := by
    calc
      ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ i, ∑ j, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i _
        refine Finset.sum_le_sum ?_
        intro j _
        exact h_sq_le i j
      _ = (m : ℝ) ^ 2 := by
        simp [pow_two]
  have h_sum_le :
      ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using h_sum_le_nat
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  exact (Real.sqrt_le_iff).2 ⟨Nat.cast_nonneg _, h_sum_le⟩

/-- Every matrix entry of a paired reindexed tensor-power density operator has
norm at most one. -/
lemma reindexed_tensorPowGen_entry_norm_le_one
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d * d)] [NeZero ((d * d) ^ n)]
    (σ : DensityOp (d * d)) (i j : Fin (d ^ n * d ^ n)) :
    ‖(densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp i j‖ ≤ 1 := by
  simpa [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply] using
    (DensityOp.entry_norm_le_one (σ.tensorPowGen n)
      ((interleavingEquiv d n) i) ((interleavingEquiv d n) j))

/-- The reindexed tensor-power map is Bochner integrable against any density
measure on `DensityOp (d * d)`: it is continuous on the compact state space. -/
theorem integrable_reindexed_tensorPowGen_toOp
    {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d * d)] [NeZero ((d * d) ^ n)] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (ν : InfoTheory.DeFinetti.DensityMeasure (d * d)) :
    MeasureTheory.Integrable
      (fun σ : DensityOp (d * d) =>
        (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp)
      ν.measure := by
  have hF_cont : Continuous fun σ : DensityOp (d * d) =>
      (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp := by
    simpa using continuous_reindexed_tensorPowGen_toOp (d := d) (n := n)
  haveI : MeasureTheory.IsProbabilityMeasure ν.measure := ν.isProbability
  exact hF_cont.integrable_of_compactSpace

/-- Reindexing the integral tensor power commutes with Bochner integration at
the matrix level. -/
theorem densityOp_reindex_integralTensorPower_toOp
    {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d * d)] [NeZero ((d * d) ^ n)] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (ν : InfoTheory.DeFinetti.DensityMeasure (d * d)) :
    (densityOp_reindex (interleavingEquiv d n).symm
      (InfoTheory.DeFinetti.integralTensorPower n ν)).toOp =
    ∫ σ : DensityOp (d * d),
      (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp
      ∂ν.measure := by
  change Matrix.reindex (interleavingEquiv d n).symm (interleavingEquiv d n).symm
    (InfoTheory.DeFinetti.integralTensorPower n ν).toOp = _
  rw [InfoTheory.DeFinetti.integralTensorPower_toOp_eq_integral]
  exact ((Matrix.reindexLinearEquiv ℂ ℂ (interleavingEquiv d n).symm
    (interleavingEquiv d n).symm).toLinearMap.toContinuousLinearMap.integral_comp_comm
      (by
        haveI := ν.isProbability
        exact InfoTheory.DeFinetti.continuous_tensorPowGen_toOp.integrable_of_compactSpace)).symm

/-- `mapTensorId` commutes with Bochner integration after reindexing by the
interleaving equivalence. -/
theorem mapTensorId_reindex_integral_commute
    {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    [NeZero (d * d)] [NeZero ((d * d) ^ n)] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (ν : InfoTheory.DeFinetti.DensityMeasure (d * d)) :
    Quantum.Channels.mapTensorId Δ
      (densityOp_reindex (interleavingEquiv d n).symm
        (InfoTheory.DeFinetti.integralTensorPower n ν)).toOp =
    ∫ σ : DensityOp (d * d),
      Quantum.Channels.mapTensorId Δ
        (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp
      ∂ν.measure := by
  let F : DensityOp (d * d) → Op (d ^ n * d ^ n) := fun σ =>
    (densityOp_reindex (interleavingEquiv d n).symm (σ.tensorPowGen n)).toOp
  have hF_int : MeasureTheory.Integrable F ν.measure := by
    simpa [F] using integrable_reindexed_tensorPowGen_toOp (d := d) (n := n) ν
  rw [densityOp_reindex_integralTensorPower_toOp (d := d) (n := n) ν]
  simpa [F] using Quantum.Channels.mapTensorId_integral_commute ν.measure Δ F hF_int

end Quantum.Channels

end
