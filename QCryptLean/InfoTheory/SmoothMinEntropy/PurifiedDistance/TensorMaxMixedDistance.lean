import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.Metrics.BlockDiagonalTensorMaxMixed
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# Purified distance under tensoring with a common maximally mixed register

This module isolates the geometric contraction needed by the smoothed extension
penalty: tensoring every CQ block with the same normalized maximally mixed
register does not increase CQ purified distance.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The trace-norm form of the CQ joint-density fidelity is preserved by appending
the same normalized maximally mixed register to every block.

This is the remaining metric/tensor fact behind
`CQState.purifiedDistance_tensorMaxMixed_contract`: it should follow from the
block-diagonal trace-norm fidelity formula together with preservation of
fidelity under tensoring both arguments with `I / dR`. -/
theorem CQState.traceNorm_sqrtProduct_tensorMaxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρEtensor σEtensor : CQState X (dE * dR))
    (ρE σE : CQState X dE)
    (hρ : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    (hσ : ∀ x : X,
      (σEtensor.stateMap x).toOp =
        (σE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    Quantum.Metrics.traceNorm
        (Quantum.Metrics.sqrtPosSemidefOp ρEtensor.toJointDensity.toPosSemidefOp *
          Quantum.Metrics.sqrtPosSemidefOp σEtensor.toJointDensity.toPosSemidefOp) =
      Quantum.Metrics.traceNorm
        (Quantum.Metrics.sqrtPosSemidefOp ρE.toJointDensity.toPosSemidefOp *
          Quantum.Metrics.sqrtPosSemidefOp σE.toJointDensity.toPosSemidefOp) := by
  let A : X → PosSemidefOp dE := fun x => (ρE.stateMap x).toPosSemidefOp
  let B : X → PosSemidefOp dE := fun x => (σE.stateMap x).toPosSemidefOp
  have hρjoint :
      ρEtensor.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.cqBlockPosSemidefOp
          (fun x => (A x).tensorMaxMixed dR) := by
    ext i j
    simp [A, Quantum.Metrics.cqBlockPosSemidefOp,
      CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
      Quantum.Operators.PosSemidefOp.tensorMaxMixed, hρ]
  have hσjoint :
      σEtensor.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.cqBlockPosSemidefOp
          (fun x => (B x).tensorMaxMixed dR) := by
    ext i j
    simp [B, Quantum.Metrics.cqBlockPosSemidefOp,
      CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
      Quantum.Operators.PosSemidefOp.tensorMaxMixed, hσ]
  have hρEjoint :
      ρE.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.cqBlockPosSemidefOp A := by
    ext i j
    simp [A, Quantum.Metrics.cqBlockPosSemidefOp,
      CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  have hσEjoint :
      σE.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.cqBlockPosSemidefOp B := by
    ext i j
    simp [B, Quantum.Metrics.cqBlockPosSemidefOp,
      CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rw [hρjoint, hσjoint, hρEjoint, hσEjoint]
  exact Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_tensorMaxMixed_eq A B

/-- The standard fidelity of the CQ joint density is preserved by appending the
same normalized maximally mixed register to every block. -/
theorem CQState.fidelity_tensorMaxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρEtensor σEtensor : CQState X (dE * dR))
    (ρE σE : CQState X dE)
    (hρ : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    (hσ : ∀ x : X,
      (σEtensor.stateMap x).toOp =
        (σE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    Quantum.Metrics.fidelity
        ρEtensor.toJointDensity.toPosSemidefOp
        σEtensor.toJointDensity.toPosSemidefOp =
      Quantum.Metrics.fidelity
        ρE.toJointDensity.toPosSemidefOp
        σE.toJointDensity.toPosSemidefOp := by
  rw [Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
    Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]
  exact CQState.traceNorm_sqrtProduct_tensorMaxMixed_eq
    ρEtensor σEtensor ρE σE hρ hσ

/-- Generalized fidelity of the CQ joint density is preserved by appending the
same normalized maximally mixed register to every block. -/
theorem CQState.fidelityGen_tensorMaxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρEtensor σEtensor : CQState X (dE * dR))
    (ρE σE : CQState X dE)
    (hρ : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    (hσ : ∀ x : X,
      (σEtensor.stateMap x).toOp =
        (σE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    fidelityGen ρEtensor.toJointDensity σEtensor.toJointDensity =
      fidelityGen ρE.toJointDensity σE.toJointDensity := by
  have hF := CQState.fidelity_tensorMaxMixed_eq
    ρEtensor σEtensor ρE σE hρ hσ
  have hρtrace :
      ρEtensor.toJointDensity.trace = ρE.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      CQState.toJointDensity_trace_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [hρ x, Op.trace_tensor]
    have hmax_trace :
        (((1 / (dR : ℂ)) • (1 : Op dR)).trace) = 1 := by
      exact (DensityOp.maxMixed dR).trace_one
    rw [hmax_trace, mul_one]
  have hσtrace :
      σEtensor.toJointDensity.trace = σE.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      CQState.toJointDensity_trace_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [hσ x, Op.trace_tensor]
    have hmax_trace :
        (((1 / (dR : ℂ)) • (1 : Op dR)).trace) = 1 := by
      exact (DensityOp.maxMixed dR).trace_one
    rw [hmax_trace, mul_one]
  simp [fidelityGen, hF, hρtrace, hσtrace]

/-- Tensoring both CQ states blockwise with the same normalized maximally mixed
register does not increase CQ purified distance. -/
theorem CQState.purifiedDistance_tensorMaxMixed_contract
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor σEtensor : CQState X (dE * dR))
    (ρE σE : CQState X dE)
    (hρ : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    (hσ : ∀ x : X,
      (σEtensor.stateMap x).toOp =
        (σE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    CQState.purifiedDistance ρEtensor σEtensor ≤
      CQState.purifiedDistance ρE σE := by
  unfold CQState.purifiedDistance
  have : NeZero ((dE * dR) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR))
      Fintype.card_ne_zero⟩
  have : NeZero (dE * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) Fintype.card_ne_zero⟩
  apply purifiedDistance_le_of_fidelityGen_ge
  exact le_of_eq (CQState.fidelityGen_tensorMaxMixed_eq
    ρEtensor σEtensor ρE σE hρ hσ).symm

end InfoTheory.SmoothMinEntropy

end
