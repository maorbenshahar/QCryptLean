import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.Metrics.BlockDiagonalTensorMaxMixed
import QCryptLean.Quantum.Metrics.TraceNorm.FidelityPositivity

/-!
# Fidelity-Based Conditional Max-Entropy for CQ States — reference operators and marginal bounds

This module contains the fidelity-optimized real-valued CQ conditional
max-entropy interface intended for Berta-style uncertainty relations.

## Main definitions

- `conditionalMaxEntropyFidelityReferenceOp`: the positive operator
  `I_X ⊗ σ_A` in the same quantum-first block layout as `CQState.toJointDensity`.
- `conditionalMaxEntropyFidelityReal`: `log₂ F(ρ_XA, I_X ⊗ σ_A)^2` for positive fidelity.
- `conditionalMaxEntropyFidelityOptReal`: the supremum over normalized reference
  states `σ_A` with positive fidelity, for CQ states of positive weight.

## Main statements

- `conditionalMaxEntropyFidelity_reference_fidelity_le_sum_sqrt_marginal`: the
  fixed-reference fidelity is bounded by the Bhattacharyya weight of the
  classical marginal.
-/

open Quantum.Operators Quantum.Metrics

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The block-diagonal positive operator `I_X ⊗ σ_A`, represented in the same
quantum-first layout as `CQState.toJointDensity`.

The operator is positive semidefinite but not generally sub-normalized:
`Tr(I_X ⊗ σ_A) = |X|`. This is the reference object used in the fidelity formula
for conditional max-entropy. -/
noncomputable def conditionalMaxEntropyFidelityReferenceOp
    {X : Type*} [Fintype X] {n : ℕ} (σ : DensityOp n) :
    PosSemidefOp (n * Fintype.card X) := by
  classical
  exact cqBlockPosSemidefOp (fun _ : X => σ.toPosSemidefOp)

/-- Conditional max-entropy relative to a normalized reference with positive fidelity:
`H_max(X|A)_{ρ|σ} = log₂ F(ρ_XA, I_X ⊗ σ_A)^2`.

Zero fidelity has extended entropy `−∞` and is excluded from this real-valued domain. -/
noncomputable def conditionalMaxEntropyFidelityReal
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (_hF : 0 < fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) : ℝ :=
  Real.log ((fidelity
    (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
    (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) ^ 2) / Real.log 2

/-- Conditional max-entropy of a CQ state of positive weight, optimized over normalized
references with positive fidelity:
`H_max(X|A)_ρ = sup_{σ_A ∈ S_=(A), F(ρ, I_X ⊗ σ_A) > 0} log₂ F(ρ, I_X ⊗ σ_A)^2`.

Tomamichel (2016), Definition 6.3. References of zero fidelity have extended entropy `−∞`
and do not affect this supremum. Positive state weight excludes the zero-state value `−∞`. -/
noncomputable def conditionalMaxEntropyFidelityOptReal
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ : 0 < ∑ x, ρ.classicalMarginal x) : ℝ :=
  sSup {h | ∃ (σ : DensityOp n) (hF : 0 < fidelity
    (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
    (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)),
    h = conditionalMaxEntropyFidelityReal ρ σ hF}

/-- The fidelity max-entropy reference operator is the constant CQ block
diagonal with normalized block `σ`. -/
lemma conditional_max_entropy_fidelity_reference_op_eq_cq_block
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (σ : DensityOp n) :
    conditionalMaxEntropyFidelityReferenceOp (X := X) σ =
      Quantum.Metrics.cqBlockPosSemidefOp
        (fun _ : X => σ.toPosSemidefOp) := by
  classical
  unfold conditionalMaxEntropyFidelityReferenceOp
  have hdec : (Classical.decEq X) = (inferInstance : DecidableEq X) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  rfl

/-- The fidelity between one CQ block and a normalized reference is bounded by
the square root of the block's classical marginal weight. -/
lemma cq_state_block_fidelity_le_sqrt_classical_marginal
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) :
    Quantum.Metrics.fidelity ((ρ.stateMap x).toPosSemidefOp) σ.toPosSemidefOp ≤
      Real.sqrt (ρ.classicalMarginal x) := by
  calc
    Quantum.Metrics.fidelity ((ρ.stateMap x).toPosSemidefOp) σ.toPosSemidefOp
        ≤ Real.sqrt
          ((Matrix.trace ((ρ.stateMap x).toPosSemidefOp).toOp).re *
            (Matrix.trace σ.toPosSemidefOp.toOp).re) := by
      exact Quantum.Metrics.fidelity_le_sqrt_trace_mul_trace
        ((ρ.stateMap x).toPosSemidefOp) σ.toPosSemidefOp
    _ = Real.sqrt (ρ.classicalMarginal x) := by
      rw [σ.trace_one]
      simp [CQState.classicalMarginal, SubDensityOp.trace]

/-- The fidelity against a normalized reference state is bounded by the
Bhattacharyya weight of the classical marginal.

This is the block-level estimate used by the normalized max-entropy bound:
rewrite both joint operators as CQ block diagonals, decompose the trace-norm
fidelity blockwise, and bound each block by the geometric mean of traces. -/
lemma conditionalMaxEntropyFidelity_reference_fidelity_le_sum_sqrt_marginal
    {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} [NeZero n] [NeZero (n * Fintype.card X)]
    (ρ : CQState X n) (σ : DensityOp n) :
    Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        (conditionalMaxEntropyFidelityReferenceOp (X := X) σ) ≤
      ∑ x : X, Real.sqrt (ρ.classicalMarginal x) := by
  classical
  rw [InfoTheory.SmoothMinEntropy.CQState.toJointDensity_toPosSemidefOp_eq_cqBlock ρ,
    conditional_max_entropy_fidelity_reference_op_eq_cq_block (X := X) σ,
    Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]
  rw [Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  calc
    Quantum.Metrics.traceNorm
        (Quantum.Metrics.sqrtPosSemidefOp ((ρ.stateMap x).toPosSemidefOp) *
          Quantum.Metrics.sqrtPosSemidefOp σ.toPosSemidefOp)
        = Quantum.Metrics.fidelity ((ρ.stateMap x).toPosSemidefOp) σ.toPosSemidefOp := by
      rw [← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]
    _ ≤ Real.sqrt (ρ.classicalMarginal x) := by
      exact cq_state_block_fidelity_le_sqrt_classical_marginal ρ σ x

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
