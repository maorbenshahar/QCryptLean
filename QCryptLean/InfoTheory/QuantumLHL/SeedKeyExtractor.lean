import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarseningTraceDistance

/-!
# Seed-Visible Extractor Output State — public seeds, uniform targets, coarsening comparison

When the PA hash seed is part of the public output transcript (not traced out by the
channel), the relevant LHL object is a CQ state on `S × Z` — the joint classical register
carrying both the seed and the hashed key — rather than the seed-averaged `CQState Z n`.

This file defines `seedKeyExtractorOutputState` and the corresponding seed-visible
uniform target state `seedUniformOutputState`.  The seed-visible state keeps the
hash seed in the classical register; forgetting that seed gives the seed-averaged
extractor state.

## Main definitions

- `seedPerSeedWeightedOp H ρ s z`: the unnormalized quantum block at classical output `(s, z)`,
  i.e. `(1/|S|) × ∑_{x : H.hash s x = z} (ρ.stateMap x).toOp`.
- `seedKeyExtractorOutputState H ρ`: CQ state on `S × Z` with quantum system `n`,
  where block `(s, z)` is `seedPerSeedWeightedOp H ρ s z`.
- `seedUniformOutputState σ`: the ideal target state with block `(s, z)` equal to
  `(1/(|S|·|Z|)) × σ.toOp`, representing the uniform-key-times-uniform-seed ideal.

## Main statements

- `seedKeyExtractorOutputState_weight_le_one`: normalization bound.
- `seedKeyExtractorOutputState_coarsen_snd`: forgetting the seed gives the
  seed-averaged extractor output state.
- `seedUniformOutputState_coarsen_snd`: forgetting the seed gives the usual
  uniform-output target.
- `extractorDistance_le_seedKeyExtractorDistance`: forgetting the seed can only
  decrease trace distance.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-!
## Per-seed weighted operator
-/

/-- The unnormalized quantum block at seed `s` and output `z`.

    `(1/|S|) × ∑_{x : H.hash s x = z} (ρ.stateMap x).toOp`.

    Per-seed analogue of `extractorWeightedOp`: retains seed `s` rather than
    summing over all seeds. -/
noncomputable def seedPerSeedWeightedOp {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) : Op n :=
  (1 / Fintype.card S : ℝ) •
    ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0

/-- Trace-expansion helper for `seedPerSeedWeightedOp`. -/
lemma seedPerSeedWeightedOp_trace_re_eq {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) :
    (seedPerSeedWeightedOp H ρ s z).trace.re =
      (1 / (Fintype.card S : ℝ)) *
        ∑ x : X, if H.hash s x = z then (ρ.stateMap x).trace else 0 := by
  unfold seedPerSeedWeightedOp
  rw [Matrix.trace_smul, Complex.smul_re, Matrix.trace_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · rfl
  · rw [Matrix.trace_zero, Complex.zero_re]

/-- The trace of `seedPerSeedWeightedOp H ρ s z` is at most `1/|S|`. -/
theorem seedPerSeedWeightedOp_trace_le {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) :
    (seedPerSeedWeightedOp H ρ s z).trace.re ≤ 1 / Fintype.card S := by
  have : Nonempty S := H.seedNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hCoeff_nonneg : 0 ≤ (1 / (Fintype.card S : ℝ)) :=
    div_nonneg zero_le_one (le_of_lt hS_pos)
  rw [seedPerSeedWeightedOp_trace_re_eq]
  have hInner :
      ∑ x : X, (if H.hash s x = z then (ρ.stateMap x).trace else 0) ≤ 1 := by
    exact le_trans
      (Finset.sum_le_sum fun x _ => by
        split_ifs
        · exact le_rfl
        · exact (ρ.stateMap x).trace_nonneg)
      ρ.weight_le_one
  simpa using mul_le_mul_of_nonneg_left hInner hCoeff_nonneg

/-- Each seed-visible weighted block is Hermitian. -/
lemma seedPerSeedWeightedOp_isHermitian {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) :
    (seedPerSeedWeightedOp H ρ s z).IsHermitian := by
  unfold seedPerSeedWeightedOp Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, RCLike.star_def, Matrix.conjTranspose_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · exact (ρ.stateMap x).isHermitian
  · simp

/-- Each seed-visible weighted block is positive semidefinite. -/
lemma seedPerSeedWeightedOp_pos_semidef {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) :
    ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (seedPerSeedWeightedOp H ρ s z) v).re := by
  intro v
  unfold seedPerSeedWeightedOp quadraticForm
  rw [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re]
  apply mul_nonneg
  · have : Nonempty S := H.seedNonempty
    positivity
  · have hmulVec : (∑ x : X,
        if H.hash s x = z then (ρ.stateMap x).toOp else 0).mulVec v =
      ∑ x : X,
        if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0 := by
      rw [Matrix.sum_mulVec Finset.univ]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · rfl
      · exact Matrix.zero_mulVec v
    rw [hmulVec]
    have hdot : star v ⬝ᵥ (∑ x : X,
        if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0) =
      ∑ x : X,
        star v ⬝ᵥ if H.hash s x = z then (ρ.stateMap x).toOp.mulVec v else 0 := by
      rw [dotProduct_sum]
    rw [hdot, Complex.re_sum]
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact (ρ.stateMap x).pos_semidef v
    · simp [dotProduct_zero]

/-- `seedPerSeedWeightedOp H ρ s z` is a sub-density operator. -/
noncomputable def seedPerSeedConditionedOp {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) (z : Z) : SubDensityOp n where
  toOp := seedPerSeedWeightedOp H ρ s z
  isHermitian := seedPerSeedWeightedOp_isHermitian H ρ s z
  pos_semidef := seedPerSeedWeightedOp_pos_semidef H ρ s z
  trace_le_one := by
    exact le_trans (seedPerSeedWeightedOp_trace_le H ρ s z) (by
      have : Nonempty S := H.seedNonempty
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)

/-!
## Normalization of seed-key extractor output
-/

/-- Summing the seed-visible blocks over seeds gives the seed-averaged extractor block. -/
lemma sum_seedPerSeedWeightedOp_eq_extractorWeightedOp
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) (z : Z) :
    ∑ s : S, seedPerSeedWeightedOp H ρ s z = extractorWeightedOp H ρ z := by
  unfold seedPerSeedWeightedOp extractorWeightedOp
  rw [← Finset.smul_sum]

/-- Summing `seedPerSeedWeightedOp` over all `(s, z)` yields the quantum marginal. -/
lemma sum_seedPerSeedWeightedOp_eq_quantumMarginalOp
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    ∑ sz : S × Z, seedPerSeedWeightedOp H ρ sz.1 sz.2 = ρ.quantumMarginalOp := by
  rw [← sum_extractorWeightedOp_eq_quantumMarginalOp H ρ]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  exact sum_seedPerSeedWeightedOp_eq_extractorWeightedOp H ρ z

/-- The total weight of `seedKeyExtractorOutputState H ρ` is at most 1. -/
theorem seedKeyExtractorOutputState_weight_le_one {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) :
    ∑ sz : S × Z, (seedPerSeedConditionedOp H ρ sz.1 sz.2).trace ≤ 1 := by
  change ∑ sz : S × Z, (seedPerSeedWeightedOp H ρ sz.1 sz.2).trace.re ≤ 1
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_seedPerSeedWeightedOp_eq_quantumMarginalOp]
  exact ρ.quantumMarginalOp_trace_le_one

/-!
## Seed-key extractor output state
-/

/-- The seed-visible extractor output state.

    A `CQState (S × Z) n` where block `(s, z)` is `seedPerSeedConditionedOp H ρ s z` —
    the per-seed unnormalized quantum state conditioned on hash seed `s` and output `z`.

    When the PA seed is part of the public output transcript (not traced out), this is the
    CQ state on the joint `(seed, hashed-key)` classical register with quantum side `A`. -/
noncomputable def seedKeyExtractorOutputState {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) : CQState (S × Z) n where
  stateMap := fun sz => seedPerSeedConditionedOp H ρ sz.1 sz.2
  weight_le_one := seedKeyExtractorOutputState_weight_le_one H ρ

/-- The seed-visible extractor block is the scaled sum over its hash fiber. -/
@[simp] lemma seedKeyExtractorOutputState_stateMap_toOp
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : CQState X n) (sz : S × Z) :
    ((seedKeyExtractorOutputState H ρ).stateMap sz).toOp =
      (1 / (Fintype.card S : ℝ)) •
        ∑ x, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0 := rfl

/-!
## Seed-visible uniform target state
-/

/-- The seed-visible uniform target state.

    The ideal CKR state when the seed `s` is in the transcript: each `(s, z)` block is
    `(1/(|S|·|Z|)) × σ.toOp`, representing the joint state where the seed is uniform
    over `S` and the key is uniform over `Z`, independent of the quantum side `σ`. -/
noncomputable def seedUniformOutputState {S Z : Type*} [Fintype S] [Nonempty S]
    [Fintype Z] [Nonempty Z] {n : ℕ} (σ : SubDensityOp n) : CQState (S × Z) n :=
  uniformCQState σ

/-- Each uniform seed-key block is the marginal scaled by the inverse output cardinality. -/
@[simp] lemma seedUniformOutputState_stateMap_toOp
    {S Z : Type*} [Fintype S] [Nonempty S] [Fintype Z] [Nonempty Z] {n : ℕ}
    (σ : SubDensityOp n) (sz : S × Z) :
    ((seedUniformOutputState σ).stateMap sz).toOp =
      (1 / (Fintype.card (S × Z) : ℝ)) • σ.toOp := rfl

/-- A hash with more possible outputs than inputs cannot produce an exactly
uniform seed-visible key from a nonzero CQ state. An empty hash fiber forces
its ideal block, hence the entire quantum marginal, to vanish. -/
lemma quantumMarginal_eq_zero_of_card_lt_of_seedKeyExtractorOutputState_eq
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {c : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : CQState X c)
    (hcard : Fintype.card X < Fintype.card Z)
    (heq : (seedKeyExtractorOutputState H ρ).toJointDensity.toOp =
      (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) :
    ρ.quantumMarginal.toOp = 0 := by
  classical
  let s : S := Classical.choice inferInstance
  have hnot : ¬ Function.Surjective (H.hash s) := fun hsurj =>
    (not_le_of_gt hcard) (Fintype.card_le_of_surjective _ hsurj)
  obtain ⟨z, hz⟩ : ∃ z, ∀ x, H.hash s x ≠ z := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnot
  have hblocks := CQState.toJointDensity_injective (SubDensityOp.ext heq)
  have hblock := congrArg (fun f => (f (s, z)).toOp) hblocks
  have hzero : ((seedKeyExtractorOutputState H ρ).stateMap (s, z)).toOp = 0 := by
    simp [seedKeyExtractorOutputState_stateMap_toOp, hz]
  change ((seedKeyExtractorOutputState H ρ).stateMap (s, z)).toOp =
    ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap (s, z)).toOp at hblock
  rw [hzero] at hblock
  change (0 : Op c) = (1 / (Fintype.card (S × Z) : ℝ)) • ρ.quantumMarginal.toOp at hblock
  exact (smul_eq_zero.mp hblock.symm).resolve_left (by positivity)

/-!
## Distance coarsening
-/

/-- Forgetting the seed from the seed-visible extractor output gives the
seed-averaged extractor output. -/
lemma seedKeyExtractorOutputState_coarsen_snd
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    CQState.coarsen (fun sz : S × Z => sz.2) (seedKeyExtractorOutputState H ρ) =
      extractorOutputState H ρ := by
  apply CQState.ext_stateMap
  funext z
  apply SubDensityOp.ext
  change ∑ sz : S × Z,
        (if sz.2 = z then seedPerSeedWeightedOp H ρ sz.1 sz.2 else 0) =
      extractorWeightedOp H ρ z
  rw [← sum_seedPerSeedWeightedOp_eq_extractorWeightedOp H ρ z]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single z]
  · rw [ite_eq_left rfl]
  · intro z' _ hz'
    rw [ite_eq_right hz']
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

/-- Summing the uniform product weight over the seed register leaves the
uniform output-register weight. -/
lemma sum_seed_uniform_product_smul
    {S Z : Type*} [Fintype S] [Fintype Z] [Nonempty S] [Nonempty Z]
    {n : ℕ} (A : Op n) :
    ∑ _s : S,
        (((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ) • A) =
      (((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ) • A) := by
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := S)
  have hZ_ne : (Fintype.card Z : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Z)
  have hcardR :
      (Fintype.card (S × Z) : ℝ) =
        (Fintype.card S : ℝ) * (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_prod S Z
  have hscalarR :
      (Fintype.card S : ℝ) * (1 / (Fintype.card (S × Z) : ℝ)) =
        1 / (Fintype.card Z : ℝ) := by
    rw [hcardR]
    field_simp [hS_ne, hZ_ne]
  have hscalarC :
      (Fintype.card S : ℂ) * (((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ)) =
        (((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ)) := by
    exact_mod_cast hscalarR
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, hscalarC]

/-- Forgetting the seed from the seed-visible uniform target gives the usual
uniform-output target. -/
lemma seedUniformOutputState_coarsen_snd
    {S Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    [Nonempty S] [Nonempty Z] {n : ℕ} (σ : SubDensityOp n) :
    CQState.coarsen (fun sz : S × Z => sz.2)
        (seedUniformOutputState (S := S) (Z := Z) σ) =
      uniformOutputState σ := by
  apply CQState.ext_stateMap
  funext z
  apply SubDensityOp.ext
  let cSZ : ℂ := ((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ)
  let cZ : ℂ := ((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ)
  have hseed_block : ∀ sz : S × Z,
      ((seedUniformOutputState (S := S) (Z := Z) σ).stateMap sz).toOp =
        cSZ • σ.toOp := by
    intro sz
    change ((uniformCQState (X := S × Z) σ : CQState (S × Z) n).stateMap sz).toOp =
      cSZ • σ.toOp
    simpa [cSZ, uniformOutputState] using
      (uniformOutput_stateMap_toOp (Z := S × Z) σ sz)
  have hout_block :
      ((uniformOutputState (Z := Z) σ).stateMap z).toOp = cZ • σ.toOp := by
    simpa [cZ] using (uniformOutput_stateMap_toOp (Z := Z) σ z)
  change ∑ sz : S × Z,
        (if sz.2 = z then
          ((seedUniformOutputState (S := S) (Z := Z) σ).stateMap sz).toOp else 0) =
      ((uniformOutputState (Z := Z) σ).stateMap z).toOp
  rw [hout_block]
  simp_rw [hseed_block]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  calc
    ∑ s : S, ∑ z' : Z, (if z' = z then cSZ • σ.toOp else 0) =
        ∑ _s : S, cSZ • σ.toOp := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_eq_single z]
      · rw [ite_eq_left rfl]
      · intro z' _ hz'
        rw [ite_eq_right hz']
      · intro hz
        exact (hz (Finset.mem_univ z)).elim
    _ = cZ • σ.toOp := by
      simpa [cSZ, cZ] using
        (sum_seed_uniform_product_smul (S := S) (Z := Z) σ.toOp)

/-- Forgetting the public seed is a classical coarsening, so the seed-averaged
extractor distance is bounded by the seed-visible distance. -/
theorem extractorDistance_le_seedKeyExtractorDistance
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq S] [DecidableEq Z]
    [Nonempty S] [Nonempty Z] {n : ℕ}
    [NeZero n] [NeZero (n * Fintype.card (S × Z))] [NeZero (n * Fintype.card Z)]
    (H : QuantumHashFamily S X Z) (ρ : CQState X n) (σ : SubDensityOp n) :
    Quantum.Metrics.traceDistanceGen
      (extractorOutputState H ρ).toJointDensity.toOp
      (uniformOutputState σ).toJointDensity.toOp ≤
    Quantum.Metrics.traceDistanceGen
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z) σ).toJointDensity.toOp := by
  have hcoarsen :=
    CQState.traceDistanceGen_coarsen_le
      (g := fun sz : S × Z => sz.2)
      (ρ := seedKeyExtractorOutputState H ρ)
      (ρ' := seedUniformOutputState (S := S) (Z := Z) σ)
  simpa [seedKeyExtractorOutputState_coarsen_snd H ρ,
    seedUniformOutputState_coarsen_snd (S := S) (Z := Z) σ] using hcoarsen

end InfoTheory.QuantumLHL

end -- noncomputable section
