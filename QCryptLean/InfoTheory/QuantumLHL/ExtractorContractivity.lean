import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized

/-!
# Extractor contractivity of the generalized trace distance

This file collects the low-level helper lemmas showing that applying the
extractor channel
`E(·) = (extractorOutputState H ·).toJointDensity.toOp` to a CQ state on the
classical register contracts the generalized trace distance (Tomamichel
§3.2):

  `D_gen(E(ρ), E(ρ')) ≤ D_gen(ρ.joint, ρ'.joint)`.

Combined with `traceDistanceGen_le_purifiedDistance` this yields the DPI
bound used in the triangle argument for the smooth quantum LHL (see
`InfoTheory.QuantumLHL.traceDistanceGen_extractorOutput_le_purifiedDistance`).

The contraction is proved by the classical post-processing argument:
the extractor channel on a CQ state is a classical stochastic kernel on
the classical register times the identity on the quantum register, so
contraction reduces to the triangle inequality and scalar homogeneity of
the matrix trace norm.

## Main lemmas

- `cqState_joint_traceNorm_eq_sum_blocks` — block-diagonal factorization
  of the CQ joint trace-norm difference.
- `extractorConditionedOp_sub_toOp_eq` — linearity of
  `extractorWeightedOp` in `ρ`.
- `traceNorm_real_smul`, `traceNorm_finset_sum_le` — real-scalar
  homogeneity and finite-sum triangle inequality for the trace norm.
- `traceNorm_extractorConditionedOp_sub_le` — per-output-z triangle
  bound.
- `sum_traceNorm_extractorConditionedOp_sub_le` — aggregate bound summed
  over `z`, reducing to `∑ x, ‖(ρ − ρ').stateMap x‖₁`.
- `traceNorm_extractorOutput_sub_joint_le` — the STEP 1 (1a)
  trace-norm contraction on joint densities.
- `trace_extractorOutput_joint_re_eq` — trace preservation under the
  extractor.
- `traceDistanceGen_extractorOutput_le` — the STEP 1 D_gen contraction
  on joint densities.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Block-diagonal factorization of the CQ joint trace-norm difference**
(T1.4 corollary, cf. Tomamichel 2016, Prop 7.1, eq. 7.35).

The joint-state trace norm of the difference of two CQ states on output
register X factors as a sum of per-block trace norms:

  `‖ρ.joint − σ.joint‖₁ = ∑ x, ‖(ρ.stateMap x).toOp − (σ.stateMap x).toOp‖₁`.

This is an application of `Quantum.Metrics.traceNorm_blockDiagonal` to the
block-diagonal difference. -/
lemma cqState_joint_traceNorm_eq_sum_blocks
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ σ : CQState X n) :
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        (ρ.toJointDensity.toOp - σ.toJointDensity.toOp) =
      ∑ x : X, Quantum.Metrics.traceNorm
          ((ρ.stateMap x).toOp - (σ.stateMap x).toOp) := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [ρ.toJointDensity_toOp_eq_reindex_blockDiagonal,
      σ.toJointDensity_toOp_eq_reindex_blockDiagonal]
  set e : Fin n × X ≃ Fin (n * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv
  have hcomb :
      Matrix.reindex e e (Matrix.blockDiagonal (fun x => (ρ.stateMap x).toOp)) -
        Matrix.reindex e e (Matrix.blockDiagonal (fun x => (σ.stateMap x).toOp)) =
      Matrix.reindex e e
        (Matrix.blockDiagonal
          (fun x => (ρ.stateMap x).toOp - (σ.stateMap x).toOp)) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.blockDiagonal_apply]
    split_ifs <;> simp
  rw [hcomb]
  exact Quantum.Metrics.traceNorm_blockDiagonal
    (fun x => (ρ.stateMap x).toOp - (σ.stateMap x).toOp)

/-- **Linearity of `extractorWeightedOp` in the CQ input.**

The difference of the extractor-conditioned operators on two CQ states
`ρ, ρ'` equals the extractor-weighted difference of their `stateMap`s.

This is purely the pointwise bilinearity of the `(1/|S|) • ∑ s, ∑ x, if …`
expression in the input `ρ.stateMap`. -/
lemma extractorConditionedOp_sub_toOp_eq
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) (z : Z) :
    (extractorConditionedOp H ρ z).toOp -
        (extractorConditionedOp H ρ' z).toOp =
      (1 / (Fintype.card S : ℝ)) •
        ∑ s : S, ∑ x : X, if H.hash s x = z then
          (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0 := by
  change extractorWeightedOp H ρ z - extractorWeightedOp H ρ' z = _
  unfold extractorWeightedOp
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · rfl
  · simp

/-- Real-scalar homogeneity of the trace norm. -/
lemma traceNorm_real_smul {n : ℕ} [NeZero n] (r : ℝ) (M : Op n) :
    Quantum.Metrics.traceNorm (r • M) = |r| * Quantum.Metrics.traceNorm M := by
  have h1 : r • M = ((r : ℂ)) • M := by
    funext i j
    change r • M i j = (r : ℂ) • M i j
    rw [Complex.real_smul]
    rfl
  rw [h1, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  simp [Complex.norm_real]

/-- Triangle inequality for finite sums of the trace norm. -/
lemma traceNorm_finset_sum_le {n : ℕ} [NeZero n] {ι : Type*}
    (s : Finset ι) (f : ι → Op n) :
    Quantum.Metrics.traceNorm (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, Quantum.Metrics.traceNorm (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_of_eq (Quantum.Channels.traceNorm_zero (n := n))
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    refine le_trans (Quantum.Metrics.traceNorm_add_le (f a) (∑ i ∈ s, f i)) ?_
    exact add_le_add (le_refl _) ih

/-- **Per-output-z triangle bound for the extractor.**

For each output `z`, the trace norm of the difference of the
extractor-conditioned operators is bounded by the uniform average over
`(s, x)` of the block-wise trace norms, restricted to the pairs hashing
to `z`. -/
lemma traceNorm_extractorConditionedOp_sub_le
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) (z : Z) :
    Quantum.Metrics.traceNorm
        ((extractorConditionedOp H ρ z).toOp -
           (extractorConditionedOp H ρ' z).toOp) ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, if H.hash s x = z then
          Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
  have : Nonempty S := H.seedNonempty
  have hS_nn : (0 : ℝ) ≤ 1 / (Fintype.card S : ℝ) := by positivity
  rw [extractorConditionedOp_sub_toOp_eq H ρ ρ' z, traceNorm_real_smul]
  rw [abs_of_nonneg hS_nn]
  refine mul_le_mul_of_nonneg_left ?_ hS_nn
  -- Sum over s.
  calc Quantum.Metrics.traceNorm
        (∑ s : S, ∑ x : X, if H.hash s x = z then
          (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0)
      ≤ ∑ s : S, Quantum.Metrics.traceNorm
          (∑ x : X, if H.hash s x = z then
            (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0) :=
        traceNorm_finset_sum_le _ _
    _ ≤ ∑ s : S, ∑ x : X, if H.hash s x = z then
          Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        refine (traceNorm_finset_sum_le _ _).trans ?_
        apply le_of_eq
        refine Finset.sum_congr rfl (fun x _ => ?_)
        split_ifs
        · rfl
        · exact Quantum.Channels.traceNorm_zero (n := n)

/-- **Aggregate trace-norm bound after summing over `z`.**

Using `∑_z ∑_s ∑_x = ∑_s ∑_x ∑_z` and `∑_z, if H.hash s x = z then _ else 0
= _` (via `Finset.sum_ite_eq`), together with the uniform seed average
`(1/|S|) · ∑_s = 1`, one obtains

  `∑ z, ‖(E ρ).stateMap z − (E ρ').stateMap z‖₁
    ≤ ∑ x, ‖(ρ.stateMap x).toOp − (ρ'.stateMap x).toOp‖₁`. -/
lemma sum_traceNorm_extractorConditionedOp_sub_le
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) :
    ∑ z : Z, Quantum.Metrics.traceNorm
        ((extractorConditionedOp H ρ z).toOp -
           (extractorConditionedOp H ρ' z).toOp) ≤
      ∑ x : X, Quantum.Metrics.traceNorm
          ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
  have : Nonempty S := H.seedNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  -- Step 1: per-z triangle bound.
  have hperZ := fun z =>
    traceNorm_extractorConditionedOp_sub_le H ρ ρ' z
  calc ∑ z : Z, Quantum.Metrics.traceNorm
          ((extractorConditionedOp H ρ z).toOp -
             (extractorConditionedOp H ρ' z).toOp)
      ≤ ∑ z : Z, (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ x : X, if H.hash s x = z then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 :=
        Finset.sum_le_sum (fun z _ => hperZ z)
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ z : Z, ∑ s : S, ∑ x : X, if H.hash s x = z then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        rw [Finset.mul_sum]
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ x : X, ∑ z : Z, if H.hash s x = z then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_comm]
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ x : X, Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
        congr 1
        refine Finset.sum_congr rfl (fun s _ => ?_)
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have := Finset.sum_ite_eq (Finset.univ : Finset Z) (H.hash s x)
          (fun _ => Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp))
        rw [this]
        simp
    _ = (1 / (Fintype.card S : ℝ)) *
          ((Fintype.card S : ℝ) *
            ∑ x : X, Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp)) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x : X, Quantum.Metrics.traceNorm
          ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hS_ne, one_mul]

/-- **STEP 1a — trace-norm contraction of the extractor channel.**

Combining the block-diagonal factorization
`cqState_joint_traceNorm_eq_sum_blocks` applied to each joint state with
`sum_traceNorm_extractorConditionedOp_sub_le`. -/
lemma traceNorm_extractorOutput_sub_joint_le
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((extractorOutputState H ρ).toJointDensity.toOp -
          (extractorOutputState H ρ').toJointDensity.toOp) ≤
      Quantum.Metrics.traceNorm
        (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [cqState_joint_traceNorm_eq_sum_blocks
        (extractorOutputState H ρ) (extractorOutputState H ρ'),
      cqState_joint_traceNorm_eq_sum_blocks ρ ρ']
  exact sum_traceNorm_extractorConditionedOp_sub_le H ρ ρ'

/-- **STEP 1b — trace preservation under the extractor channel.**

The joint-density trace of the extractor output equals the joint-density
trace of the input, because summing `extractorWeightedOp` over `z` yields
the quantum marginal (`sum_extractorWeightedOp_eq_quantumMarginalOp`),
whose real trace equals `∑ x, (ρ.stateMap x).trace = ρ.joint.trace.re`. -/
lemma trace_extractorOutput_joint_re_eq
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    (extractorOutputState H ρ).toJointDensity.toOp.trace.re =
      ρ.toJointDensity.toOp.trace.re := by
  -- LHS: trace of joint of extractor output.
  have hLHS :
      (extractorOutputState H ρ).toJointDensity.toOp.trace.re =
        ∑ z : Z, (extractorConditionedOp H ρ z).trace := by
    change (extractorOutputState H ρ).toJointDensity.trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
    rfl
  -- RHS: trace of joint of ρ.
  have hRHS : ρ.toJointDensity.toOp.trace.re = ∑ x : X, (ρ.stateMap x).trace := by
    change ρ.toJointDensity.trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
  rw [hLHS, hRHS]
  -- Sum of extractor conditioned traces = ∑ x, (ρ.stateMap x).trace via marginal.
  have hmarg :
      ∑ z : Z, (extractorConditionedOp H ρ z).trace =
        (ρ.quantumMarginalOp).trace.re := by
    change ∑ z : Z, (extractorWeightedOp H ρ z).trace.re = _
    rw [← Complex.re_sum, ← Matrix.trace_sum,
        sum_extractorWeightedOp_eq_quantumMarginalOp]
  rw [hmarg]
  unfold CQState.quantumMarginalOp
  rw [Matrix.trace_sum, Complex.re_sum]
  rfl

/-- **STEP 1 — generalized trace distance contraction of the extractor
channel on joint densities.** -/
lemma traceDistanceGen_extractorOutput_le
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H ρ).toJointDensity.toOp
        (extractorOutputState H ρ').toJointDensity.toOp ≤
      Quantum.Metrics.traceDistanceGen
        ρ.toJointDensity.toOp ρ'.toJointDensity.toOp := by
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  unfold Quantum.Metrics.traceDistanceGen
  have h1 := traceNorm_extractorOutput_sub_joint_le H ρ ρ'
  have h2re := trace_extractorOutput_joint_re_eq H ρ
  have h2re' := trace_extractorOutput_joint_re_eq H ρ'
  have htr :
      ((extractorOutputState H ρ).toJointDensity.toOp.trace -
         (extractorOutputState H ρ').toJointDensity.toOp.trace).re =
        (ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re := by
    rw [Complex.sub_re, Complex.sub_re, h2re, h2re']
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1' : (1 / 2) *
      Quantum.Metrics.traceNorm
        ((extractorOutputState H ρ).toJointDensity.toOp -
          (extractorOutputState H ρ').toJointDensity.toOp) ≤
      (1 / 2) *
      Quantum.Metrics.traceNorm
        (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) :=
    mul_le_mul_of_nonneg_left h1 hhalf
  have h2' : (1 / 2) *
      |((extractorOutputState H ρ).toJointDensity.toOp.trace -
         (extractorOutputState H ρ').toJointDensity.toOp.trace).re| =
      (1 / 2) *
      |(ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re| := by
    rw [htr]
  linarith

end InfoTheory.QuantumLHL

end -- noncomputable section
