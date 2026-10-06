import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.InfoTheory.QuantumLHL.UniformOutputBlock

/-!
# Classical Coarsening Trace Distance — trace-norm and generalized-distance contraction

This file packages the metric part of finite classical coarsening for CQ states.
The underlying coarsening operation and trace-preservation identities are defined
in `ClassicalCoarsening.lean`; here we combine them with block-diagonal trace-norm
infrastructure to prove contraction of generalized trace distance.

## Main statements
- `CQState.traceNorm_coarsen_stateMap_diff_le_sum_fiber`: a coarsened block's
  trace norm is bounded by the sum over its input fiber.
- `CQState.traceNorm_coarsen_joint_diff_le`: coarsening contracts joint-density
  trace norm.
- `CQState.traceDistanceGen_coarsen_le`: coarsening contracts generalized trace
  distance.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- The trace norm of one coarsened block difference is bounded by the
sum of trace norms over its fiber. -/
lemma CQState.traceNorm_coarsen_stateMap_diff_le_sum_fiber
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} [NeZero n] (g : X → Y) (ρ ρ' : CQState X n) (y : Y) :
    traceNorm
        (((CQState.coarsen g ρ).stateMap y).toOp -
          ((CQState.coarsen g ρ').stateMap y).toOp) ≤
      ∑ x : X, if g x = y then
        traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
  rw [CQState.coarsen_stateMap_toOp_sub_eq_sum g ρ ρ' y]
  calc
    traceNorm (∑ x : X, if g x = y then
        (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0)
        ≤ ∑ x : X, traceNorm
            (if g x = y then
              (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0) :=
      traceNorm_sum_le _ _
    _ = ∑ x : X, if g x = y then
        traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : g x = y <;> simp [hx, Quantum.Channels.traceNorm_zero]

/-- The sum of block trace norms contracts when finite classical labels are coarsened. -/
lemma CQState.sum_traceNorm_coarsen_stateMap_diff_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} [NeZero n] (g : X → Y) (ρ ρ' : CQState X n) :
    ∑ y : Y, traceNorm
        (((CQState.coarsen g ρ).stateMap y).toOp -
          ((CQState.coarsen g ρ').stateMap y).toOp) ≤
      ∑ x : X, traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
  calc
    ∑ y : Y, traceNorm
        (((CQState.coarsen g ρ).stateMap y).toOp -
          ((CQState.coarsen g ρ').stateMap y).toOp)
        ≤ ∑ y : Y, ∑ x : X, if g x = y then
            traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      exact CQState.traceNorm_coarsen_stateMap_diff_le_sum_fiber g ρ ρ' y
    _ = ∑ x : X, traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
      exact sum_fiber_indicator_eq_sum g
        (fun x : X => traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp))

/-- The trace norm of a coarsened CQ joint-density difference is bounded by the
trace norm of the original CQ joint-density difference. -/
lemma CQState.traceNorm_coarsen_joint_diff_le
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} [NeZero n]
    (g : X → Y) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Y) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceNorm
        ((CQState.coarsen g ρ).toJointDensity.toOp -
          (CQState.coarsen g ρ').toJointDensity.toOp) ≤
      traceNorm (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Y) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [traceNorm_joint_diff_eq_sum (CQState.coarsen g ρ) (CQState.coarsen g ρ'),
    traceNorm_joint_diff_eq_sum ρ ρ']
  exact CQState.sum_traceNorm_coarsen_stateMap_diff_le g ρ ρ'

/-- Generalized trace distance contracts under finite classical coarsening. -/
lemma CQState.traceDistanceGen_coarsen_le
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} [NeZero n]
    (g : X → Y) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Y) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceDistanceGen
        (CQState.coarsen g ρ).toJointDensity.toOp
        (CQState.coarsen g ρ').toJointDensity.toOp ≤
      traceDistanceGen ρ.toJointDensity.toOp ρ'.toJointDensity.toOp := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Y) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have hnorm := CQState.traceNorm_coarsen_joint_diff_le g ρ ρ'
  have htrρ := CQState.coarsen_joint_trace_re_eq g ρ
  have htrρ' := CQState.coarsen_joint_trace_re_eq g ρ'
  have htr :
      (((CQState.coarsen g ρ).toJointDensity.toOp.trace -
          (CQState.coarsen g ρ').toJointDensity.toOp.trace).re) =
        (ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re := by
    rw [Complex.sub_re, Complex.sub_re, htrρ, htrρ']
  exact traceDistanceGen_le_of_traceNorm_sub_le_of_trace_re_sub_eq hnorm htr

end InfoTheory.QuantumLHL

end -- noncomputable section
