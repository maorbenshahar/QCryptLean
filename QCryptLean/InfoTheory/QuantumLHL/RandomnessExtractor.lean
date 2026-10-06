import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Math.Concentration.PrivacyAmplification

/-!
# Quantum Hash Families and Extractor Output State

A quantum hash family is a classical hash family whose domain matches the classical
register of a CQ state. Applying the hash on the classical register X produces a
new CQ state on the compressed register Z and the original quantum side A. The
seed is drawn uniformly and traced out in `extractorOutputState`.

This file defines the quantum hash family structure and the extractor output state,
following Tomamichel 2016, §7.3.

## Main definitions
- `QuantumHashFamily`: 2-universal hash family with classical domain X, output Z, seed S
- `QuantumHashFamily.isUniversal`: 2-universality property matching Tomamichel eq. 7.31
- `extractorOutputState`: the seed-averaged CQ state after hashing the X register
- `uniformOutputState`: uniform distribution on Z tensored with a quantum side state

## Main statements
- `extractorConditionedOp_trace_le_one`: trace bound for the conditioned operator
- `extractorOutputState_weight_le_one`: normalization of the extractor output state
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-!
## Quantum Hash Family

A quantum hash family is a classical hash family (seed-indexed family of functions
from domain X to output Z) satisfying the 2-universality collision bound.
-/

/-- A quantum hash family: seed-indexed classical hash functions from X to Z.

    This is the classical hash family structure adapted for use in the quantum
    leftover hash lemma. The quantum side is handled at the level of the extractor
    output state, not inside this structure.

    Tomamichel 2016, §7.3.1: the seed F is drawn from distribution τ(f);
    here we use the uniform distribution over a finite seed type S. -/
structure QuantumHashFamily (S X Z : Type*) where
  /-- The hash function: seed s and input x give output z -/
  hash : S → X → Z
  /-- Seed type has finitely many elements -/
  [seedFintype : Fintype S]
  /-- Seed type is nonempty -/
  [seedNonempty : Nonempty S]
  /-- Output type has finitely many elements -/
  [outputFintype : Fintype Z]
  /-- Output type is nonempty -/
  [outputNonempty : Nonempty Z]

attribute [instance] QuantumHashFamily.seedFintype QuantumHashFamily.seedNonempty
attribute [instance] QuantumHashFamily.outputFintype QuantumHashFamily.outputNonempty

/-- 2-universality property for a quantum hash family.

    Tomamichel 2016, §7.3.2, eq. 7.31:
    For any two distinct inputs x ≠ x' in domain X,
      Pr_{s ∼ Uniform(S)}[hash(s, x) = hash(s, x')] ≤ 1/|Z|

    The collision probability is |{s : hash(s,x) = hash(s,x')}| / |S| ≤ 1/|Z|,
    which after clearing |S| gives the ℝ-valued inequality below. -/
def QuantumHashFamily.isUniversal {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) : Prop :=
  ∀ x x' : X, x ≠ x' →
    ((Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card : ℝ) ≤
    (Fintype.card S : ℝ) / (Fintype.card Z : ℝ)

/-!
## Extractor Output State

Applying a uniformly sampled hash function to the classical register X of a CQ
state `ρ_{XA}` and tracing out the seed gives the CQ state `ρ_{ZA}` with blocks

`ρ_A(z) = (1/|S|) · ∑_s ∑_{x : hash(s,x)=z} ρ_A(x)`.

The quantum system still has dimension `n`. Closeness of this seed-averaged state
to a uniform key tensored with `ρ_A` is the weak extractor criterion.

Tomamichel's `Δ(S|EF)` (eq. 7.33) retains the seed and averages the distances for
individual seeds. The distance after averaging states can be strictly smaller.
The comparison is `extractorDistance_le_seedKeyExtractorDistance` in
`SeedKeyExtractor.lean`; combined with `quantum_seedKey_LHL_smooth` in
`SeedKeySmoothing.lean`, it yields the weak bound after tracing out the seed.
-/

/-- The unnormalized weight of output `z` in the extractor output state, obtained
    by averaging over the uniform seed distribution (no free seed parameter).

    Concretely, `(1/|S|) · ∑_s ∑_{x : hash(s,x)=z} (ρ.stateMap x).toOp`. -/
noncomputable def extractorWeightedOp {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (z : Z) : Op n :=
  (1 / Fintype.card S : ℝ) •
    ∑ s : S, ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0

/-- Trace-expansion helper for `extractorWeightedOp`. -/
lemma extractorWeightedOp_trace_re_eq {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (z : Z) :
    (extractorWeightedOp H ρ z).trace.re =
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, if H.hash s x = z then (ρ.stateMap x).trace else 0 := by
  unfold extractorWeightedOp
  rw [Matrix.trace_smul, Complex.smul_re, Matrix.trace_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl; intro s _
  rw [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro x _
  split_ifs with h
  · rfl
  · rw [Matrix.trace_zero, Complex.zero_re]

/-- The trace of `extractorWeightedOp H ρ z` is at most 1
    (in fact bounded by the total weight of ρ).

    Tomamichel §7.3: each conditioned block has trace bounded by the input weight. -/
theorem extractorConditionedOp_trace_le_one {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (z : Z) :
    (extractorWeightedOp H ρ z).trace.re ≤ 1 := by
  rw [extractorWeightedOp_trace_re_eq]
  haveI : Nonempty S := H.seedNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hInnerBound :
      ∑ s : S, ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).trace else 0) ≤
        (Fintype.card S : ℝ) * ∑ x : X, (ρ.stateMap x).trace := by
    have hPerX : ∀ s : S, ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).trace else 0) ≤
        ∑ x : X, (ρ.stateMap x).trace := fun s =>
      Finset.sum_le_sum fun x _ => by
        split_ifs
        · exact le_rfl
        · exact (ρ.stateMap x).trace_nonneg
    calc ∑ s : S, ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).trace else 0)
        ≤ ∑ _s : S, ∑ x : X, (ρ.stateMap x).trace := Finset.sum_le_sum fun s _ => hPerX s
      _ = (Fintype.card S : ℝ) * ∑ x : X, (ρ.stateMap x).trace := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hρ : ∑ x : X, (ρ.stateMap x).trace ≤ 1 := ρ.weight_le_one
  have hInv_nn : (0 : ℝ) ≤ 1 / (Fintype.card S : ℝ) := by positivity
  calc (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).trace else 0)
      ≤ (1 / (Fintype.card S : ℝ)) * ((Fintype.card S : ℝ) * ∑ x : X, (ρ.stateMap x).trace) := by
        exact mul_le_mul_of_nonneg_left hInnerBound hInv_nn
    _ = ∑ x : X, (ρ.stateMap x).trace := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hS_ne, one_mul]
    _ ≤ 1 := hρ

/-- The extractor output state conditioned on output z.

    This is the unnormalized quantum state on system A when the hash outputs z,
    averaging over the uniform seed distribution. -/
noncomputable def extractorConditionedOp {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (z : Z) : SubDensityOp n where
  toOp := extractorWeightedOp H ρ z
  isHermitian := by
    unfold extractorWeightedOp Matrix.IsHermitian
    simp only [Matrix.conjTranspose_smul, RCLike.star_def,
               Matrix.conjTranspose_sum]
    congr 1
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro x _
    split_ifs with h
    · exact (ρ.stateMap x).isHermitian
    · simp
  pos_semidef := by
    unfold extractorWeightedOp
    intro v
    unfold quadraticForm
    rw [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re]
    apply mul_nonneg; · positivity
    have hmulVec : (∑ s : S, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp else 0).mulVec v =
        ∑ s : S, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0 := by
      rw [Matrix.sum_mulVec Finset.univ]
      apply Finset.sum_congr rfl; intro s _
      rw [Matrix.sum_mulVec Finset.univ]
      apply Finset.sum_congr rfl; intro x _
      split_ifs
      · rfl
      · exact Matrix.zero_mulVec v
    rw [hmulVec]
    have hdot : star v ⬝ᵥ (∑ s : S, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0) =
        ∑ s : S, ∑ x : X,
          star v ⬝ᵥ if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0 := by
      rw [dotProduct_sum]
      apply Finset.sum_congr rfl; intro s _
      rw [dotProduct_sum]
    rw [hdot, Complex.re_sum]
    apply Finset.sum_nonneg; intro s _
    rw [Complex.re_sum]
    apply Finset.sum_nonneg; intro x _
    split_ifs with h
    · exact (ρ.stateMap x).pos_semidef v
    · simp [dotProduct_zero]
  trace_le_one := extractorConditionedOp_trace_le_one H ρ z

/-- Summing `extractorWeightedOp H ρ z` over all outputs `z` yields the quantum
    marginal of the input CQ state. The uniform seed average cancels the `1/|S|`
    prefactor because the inner indicator picks out exactly one `z` for each
    `(s, x)`. -/
lemma sum_extractorWeightedOp_eq_quantumMarginalOp
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    ∑ z : Z, extractorWeightedOp H ρ z = ρ.quantumMarginalOp := by
  haveI : Nonempty S := H.seedNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  unfold extractorWeightedOp CQState.quantumMarginalOp
  -- pull the scalar out of the outer sum over z
  rw [← Finset.smul_sum]
  -- commute sums: ∑ z ∑ s ∑ x = ∑ s ∑ x ∑ z
  rw [Finset.sum_comm]
  have hInner : ∀ s : S,
      ∑ z : Z, ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).toOp else 0) =
        ∑ x : X, (ρ.stateMap x).toOp := by
    intro s
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    have := Finset.sum_ite_eq (Finset.univ : Finset Z) (H.hash s x)
      (fun _ => (ρ.stateMap x).toOp)
    rw [this]
    simp
  simp_rw [hInner]
  -- ∑ s, ∑ x, (ρ.stateMap x).toOp = |S| • ∑ x, (ρ.stateMap x).toOp
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, one_div, inv_mul_cancel₀ hS_ne, one_smul]

/-- The total weight of `extractorOutputState H ρ` is at most 1.

    This follows because summing over all z partitions the contributions from ρ,
    and ρ's total weight is at most 1. -/
theorem extractorOutputState_weight_le_one {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) :
    ∑ z : Z, (extractorConditionedOp H ρ z).trace ≤ 1 := by
  change ∑ z : Z, (extractorWeightedOp H ρ z).trace.re ≤ 1
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_extractorWeightedOp_eq_quantumMarginalOp]
  exact ρ.quantumMarginalOp_trace_le_one

/-- The seed-averaged extractor output as a CQ state on register Z with quantum system A.

The uniformly sampled seed is traced out. Its distance to a uniform key tensored with
`ρ`'s quantum marginal is bounded by the seed-visible distance and can be strictly smaller
(`extractorDistance_le_seedKeyExtractorDistance`, `SeedKeyExtractor.lean`). Thus it defines
the weak extractor criterion, not Tomamichel's seed-visible `Δ(S|EF)` (eq. 7.33). -/
noncomputable def extractorOutputState {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) : CQState Z n where
  stateMap := extractorConditionedOp H ρ
  weight_le_one := extractorOutputState_weight_le_one H ρ

/-!
## Uniform Output State

The ideal target state for privacy amplification: uniform distribution on Z
paired with the quantum side information.
-/

/-- The uniform classical state on Z, used as the ideal output of the extractor.

    This is the state (1/|Z|) Σ_z |z⟩⟨z|_Z ⊗ σ_A for some reference σ_A. -/
noncomputable def uniformOutputState {Z : Type*} [Fintype Z] [Nonempty Z] {n : ℕ}
    (σ : SubDensityOp n) : CQState Z n :=
  uniformCQState σ

end InfoTheory.QuantumLHL

end -- noncomputable section
