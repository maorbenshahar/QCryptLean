import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized

/-!
# Uniform-Output and Joint-Marginal Reductions for the Smoothing Triangle

Helper lemmas powering the (T3) leg of the smooth quantum-leftover-hash-lemma
triangle inequality (`traceDistanceGen_uniformOutput_le_marginal_purifiedDistance`
in `Smoothing.lean`).

The chain is:
```
D_gen(U(ρ_A), U(ρ'_A))            -- (Stage 1)  =  D_gen(ρ_A, ρ'_A)
                                   -- (Stage 2)  ≤  D_gen(ρ_joint, ρ'_joint)
                                   -- (Stage 3)  ≤  P(ρ_joint, ρ'_joint) = ρ.purifiedDistance ρ'
```

Stage 1 (uniform-output reduction): trace-norm and trace of
`(uniformOutputState σ).toJointDensity.toOp` collapse through
`traceNorm_blockDiagonal` + `Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq`, giving the
identity
`D_gen(U(σ₁), U(σ₂)) = D_gen(σ₁.toOp, σ₂.toOp)`.

Stage 2 (marginal ≤ joint): the block-diagonal joint trace-norm identity plus
iterated triangle inequality gives
`‖ρ_A − ρ'_A‖₁ ≤ ∑_x ‖Δ_x‖₁ = ‖ρ_joint − ρ'_joint‖₁`, while the trace halves
are equal.

Stage 3 is then `traceDistanceGen_le_purifiedDistance` applied to the joint
densities.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace Quantum.Metrics

/-- **Iterated triangle inequality for `traceNorm`.**

    `‖∑ i ∈ s, f i‖₁ ≤ ∑ i ∈ s, ‖f i‖₁`. -/
lemma traceNorm_sum_le
    {α : Type*} {n : ℕ} [NeZero n]
    (s : Finset α) (f : α → Op n) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Quantum.Channels.traceNorm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc traceNorm (f a + ∑ i ∈ s, f i)
          ≤ traceNorm (f a) + traceNorm (∑ i ∈ s, f i) :=
            traceNorm_add_le _ _
        _ ≤ traceNorm (f a) + ∑ i ∈ s, traceNorm (f i) := by linarith

end Quantum.Metrics

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-!
## Stage 1: uniform-output reduction

The uniform-output `(uniformOutputState σ).toJointDensity.toOp` is a reindexed
block-diagonal of `|Z|` copies of `(1/|Z|) • σ.toOp`; both trace-norm and
trace-real-part collapse to the underlying `σ.toOp` quantities. -/

section UniformOutput

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {n : ℕ} [NeZero n]

omit [DecidableEq Z] [NeZero n] in
/-- Public access to the per-outcome block of a `uniformOutputState σ`: the
    block at any index is the scaled sub-density `((uniformWeight Z) : ℂ) • σ.toOp`.
    Written in the concrete form `Complex.ofReal (1 / (Fintype.card Z : ℝ))`. -/
lemma uniformOutput_stateMap_toOp
    (σ : SubDensityOp n) (z : Z) :
    ((uniformOutputState (Z := Z) σ : CQState Z n).stateMap z).toOp =
      ((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ) • σ.toOp :=
  rfl

omit [NeZero n] in
/-- The joint-density operator of a `uniformOutputState σ` is a reindexed
    block-diagonal of `|Z|` copies of `(1/|Z| : ℂ) • σ.toOp`. -/
lemma uniformOutput_toJointDensity_toOp_eq
    (σ : SubDensityOp n) :
    (uniformOutputState (Z := Z) σ : CQState Z n).toJointDensity.toOp =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin Z)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin Z)).trans finProdFinEquiv)
        (Matrix.blockDiagonal
          (fun _ : Z => (((1 / (Fintype.card Z : ℝ)) : ℝ) : ℂ) • σ.toOp)) := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rfl

omit [NeZero n] in
/-- The difference of two uniform-output joint densities is a reindexed
    block-diagonal whose block at every index is `(1/|Z| : ℂ) • (σ₁.toOp − σ₂.toOp)`. -/
lemma uniformOutput_toOp_diff_eq
    (σ₁ σ₂ : SubDensityOp n) :
    (uniformOutputState (Z := Z) σ₁ : CQState Z n).toJointDensity.toOp -
        (uniformOutputState (Z := Z) σ₂ : CQState Z n).toJointDensity.toOp =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin Z)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin Z)).trans finProdFinEquiv)
        (Matrix.blockDiagonal
          (fun _ : Z => ((1 / (Fintype.card Z : ℝ) : ℂ)) • (σ₁.toOp - σ₂.toOp))) := by
  rw [uniformOutput_toJointDensity_toOp_eq, uniformOutput_toJointDensity_toOp_eq]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.blockDiagonal_apply, smul_sub]
  split_ifs <;> simp

/-- **Stage 1, trace-norm half.**  Trace norm of the uniform-output difference
    collapses to the trace norm of the underlying sub-density difference. -/
lemma traceNorm_uniformOutput_diff
    (σ₁ σ₂ : SubDensityOp n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceNorm
        ((uniformOutputState (Z := Z) σ₁ : CQState Z n).toJointDensity.toOp -
          (uniformOutputState (Z := Z) σ₂ : CQState Z n).toJointDensity.toOp) =
      traceNorm (σ₁.toOp - σ₂.toOp) := by
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [uniformOutput_toOp_diff_eq, traceNorm_blockDiagonal]
  -- ∑ z : Z, traceNorm ((1/|Z| : ℂ) • (σ₁.toOp − σ₂.toOp)) = traceNorm (σ₁.toOp − σ₂.toOp)
  rw [show (fun z : Z =>
        traceNorm (((1 / (Fintype.card Z : ℝ) : ℂ)) • (σ₁.toOp - σ₂.toOp))) =
        (fun _ : Z => (1 / (Fintype.card Z : ℝ)) * traceNorm (σ₁.toOp - σ₂.toOp))
      from by
        funext _
        rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
        have hnorm : ‖((1 / (Fintype.card Z : ℝ) : ℂ))‖ = 1 / (Fintype.card Z : ℝ) := by
          simp
        rw [hnorm]]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

omit [NeZero n] in
/-- **Stage 1, trace half.**  The real-trace of a `uniformOutputState σ`'s
    joint density equals `σ.trace`. -/
lemma trace_uniformOutput_toJointDensity_re
    (σ : SubDensityOp n) :
    ((uniformOutputState (Z := Z) σ : CQState Z n).toJointDensity.toOp).trace.re =
      σ.toOp.trace.re :=
  uniformCQState_toJointDensity_trace (X := Z) σ

/-- **Stage 1, combined.**  Generalized trace distance between two
    uniform-output joint densities equals that between their underlying
    sub-density operators. -/
lemma traceDistanceGen_uniformOutput_eq
    (σ₁ σ₂ : SubDensityOp n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceDistanceGen
        (uniformOutputState (Z := Z) σ₁ : CQState Z n).toJointDensity.toOp
        (uniformOutputState (Z := Z) σ₂ : CQState Z n).toJointDensity.toOp =
      traceDistanceGen σ₁.toOp σ₂.toOp := by
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  unfold traceDistanceGen
  congr 1
  · -- trace-norm halves
    rw [traceNorm_uniformOutput_diff]
  · -- trace halves: |Re(tr U(σ₁) − tr U(σ₂))| = |Re(tr σ₁ − tr σ₂)|
    congr 1
    rw [Complex.sub_re, Complex.sub_re,
        trace_uniformOutput_toJointDensity_re,
        trace_uniformOutput_toJointDensity_re]

end UniformOutput

/-!
## Stage 2: marginal ≤ joint

Set `Δ_x := (ρ.stateMap x).toOp − (ρ'.stateMap x).toOp`.  Then
`ρ.quantumMarginal.toOp − ρ'.quantumMarginal.toOp = ∑_x Δ_x`, whose trace norm
is bounded by `∑_x ‖Δ_x‖₁`, which equals the trace norm of the joint
difference `‖ρ.toJointDensity.toOp − ρ'.toJointDensity.toOp‖₁`.  The trace
halves are equal. -/

section MarginalJoint

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The difference of two CQ joint densities is a reindexed block-diagonal of
    per-outcome sub-density differences. -/
lemma toJointDensity_toOp_diff_eq
    (ρ ρ' : CQState X n) :
    ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal
          (fun x : X => (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp)) := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
      CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.blockDiagonal_apply]
  split_ifs <;> simp

/-- The trace norm of the joint-density difference equals the sum of per-outcome
    sub-density differences' trace norms. -/
lemma traceNorm_joint_diff_eq_sum
    [Nonempty X]
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceNorm (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) =
      ∑ x : X, traceNorm ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [toJointDensity_toOp_diff_eq]
  exact traceNorm_blockDiagonal _

omit [DecidableEq X] [NeZero n] in
/-- The difference of two quantum marginals of CQ states equals the sum of
    per-outcome sub-density differences. -/
lemma quantumMarginal_diff_eq_sum
    (ρ ρ' : CQState X n) :
    (ρ.quantumMarginal).toOp - (ρ'.quantumMarginal).toOp =
      ∑ x : X, ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
  change ρ.quantumMarginalOp - ρ'.quantumMarginalOp = _
  unfold CQState.quantumMarginalOp
  rw [Finset.sum_sub_distrib]

/-- **Stage 2, trace-norm half.**  Trace norm of the quantum-marginal
    difference is bounded by the trace norm of the joint-density difference. -/
lemma traceNorm_marginal_diff_le_joint
    [Nonempty X]
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceNorm ((ρ.quantumMarginal).toOp - (ρ'.quantumMarginal).toOp) ≤
      traceNorm (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [quantumMarginal_diff_eq_sum, traceNorm_joint_diff_eq_sum]
  exact traceNorm_sum_le _ _

omit [NeZero n] in
/-- **Stage 2, trace half.**  The real trace-difference of the quantum
    marginals equals that of the joint densities. -/
lemma trace_marginal_diff_eq_joint
    (ρ ρ' : CQState X n) :
    ((ρ.quantumMarginal).toOp.trace - (ρ'.quantumMarginal).toOp.trace).re =
      (ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re := by
  -- Both equal ∑ x, ((ρ.stateMap x).toOp.trace - (ρ'.stateMap x).toOp.trace).re
  have hmarg : ∀ (τ : CQState X n),
      (τ.quantumMarginal).toOp.trace.re =
        ∑ x : X, (τ.stateMap x).toOp.trace.re := by
    intro τ
    change (τ.quantumMarginalOp).trace.re = _
    unfold CQState.quantumMarginalOp
    rw [Matrix.trace_sum, Complex.re_sum]
  have hjoint : ∀ (τ : CQState X n),
      τ.toJointDensity.toOp.trace.re =
        ∑ x : X, (τ.stateMap x).toOp.trace.re := by
    intro τ
    have h := τ.toJointDensity_trace_eq_sum
    -- τ.toJointDensity.trace = τ.toJointDensity.toOp.trace.re definitionally
    change τ.toJointDensity.toOp.trace.re = ∑ x : X, (τ.stateMap x).trace at h
    rw [h]
    rfl
  rw [Complex.sub_re, Complex.sub_re, hmarg ρ, hmarg ρ', hjoint ρ, hjoint ρ']

/-- **Stage 2, combined.**  Generalized trace distance between quantum
    marginals is bounded by the generalized trace distance between joint
    densities. -/
lemma traceDistanceGen_marginal_le_joint
    [Nonempty X]
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    traceDistanceGen (ρ.quantumMarginal).toOp (ρ'.quantumMarginal).toOp ≤
      traceDistanceGen ρ.toJointDensity.toOp ρ'.toJointDensity.toOp := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  unfold traceDistanceGen
  have htn := traceNorm_marginal_diff_le_joint ρ ρ'
  have htr := trace_marginal_diff_eq_joint ρ ρ'
  have : (1 : ℝ) / 2 * traceNorm ((ρ.quantumMarginal).toOp -
            (ρ'.quantumMarginal).toOp) ≤
        1 / 2 * traceNorm (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
    have h2 : (0 : ℝ) ≤ 1/2 := by norm_num
    exact mul_le_mul_of_nonneg_left htn h2
  linarith [this, (show |((ρ.quantumMarginal).toOp.trace
      - (ρ'.quantumMarginal).toOp.trace).re|
      = |(ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re| from by
      rw [htr])]

end MarginalJoint

end InfoTheory.QuantumLHL

end -- noncomputable section
