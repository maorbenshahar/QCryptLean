import QCryptLean.InfoTheory.QuantumLHL.SeedKeyReferenceOptimised
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.LambdaBound
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSubNormalized
import QCryptLean.InfoTheory.QuantumLHL.Smoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Quantum leftover hashing

The extractor distance is bounded by a real exponential hashing term plus `2 * ε` from a fixed-
reference or optimized smooth entropy floor. The smooth entropy is extended-valued; its infinite
case has zero hashing error. Unsmooth statements are the radius-zero cases.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-!
## Helpers for `extractorDistance_le_of_minEntropy` (Tomamichel Prop 7.1)

The helpers below follow the proof structure of Tomamichel 2016, Prop 7.1,
eq. 7.32–7.41. The block-diagonal factorization lemma
`cqState_joint_traceNorm_eq_sum_blocks` lives in
`QCryptLean.InfoTheory.QuantumLHL.ExtractorContractivity` and is
available here through the import chain Main → Smoothing → ExtractorContractivity.
-/

/-- **Cauchy–Schwarz–Jensen bound on the joint trace norm** (Tomamichel Prop 7.1,
eq. 7.37–7.41).

For a normalized CQ state ρ with reference σ admitting a feasible λ,

  `‖(extractorOutputState H ρ)_joint − (uniformOutputState ρ_A)_joint‖₁
      ≤ √(|Z| · minFeasibleLambda ρ σ)`

where `ρ_A = ρ.toCQState.quantumMarginal`.

Proof: The σ^{−1/2} sandwich inequality (Renner's operator Cauchy–Schwarz, see
Tomamichel 2016 eq. 7.39) applied block-by-block, followed by the 2-universality
of H (eq. 7.31), yields the per-block bound
`‖M_z − (1/|Z|)·ρ_A‖₁ ≤ (1/|Z|) · (minFeasibleLambda ρ σ)^{1/2} · ...`
and Jensen's inequality assembles these into the stated global bound.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37–7.41. -/
lemma joint_traceNorm_le_sqrt_card_mul_lambda
    {S X Z : Type*} [Fintype S] [Fintype X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : NormalizedCQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda (ρ : CQState X n) σ) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp -
          (uniformOutputState ρ.toCQState.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt (Fintype.card Z * minFeasibleLambda (ρ : CQState X n) σ) := by
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  -- Step 1 (Tomamichel eq. 7.35, T1.4 corollary): block-diagonal factorization.
  rw [cqState_joint_traceNorm_eq_sum_blocks
        (extractorOutputState H (ρ : CQState X n))
        (uniformOutputState ρ.toCQState.quantumMarginal)]
  -- Step 2 (Tomamichel eq. 7.37–7.41): σ⁻¹/² Cauchy–Schwarz + 2-universality + Jensen.
  exact joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda
    H hH ρ σ hσ_pd hfeas

/-- **Normalized CQ joint trace equals 1.**

For a normalized CQ state ρ (weight exactly 1), the joint density operator
has trace equal to 1. This forces the `|tr ρ − tr σ|` term in `traceDistanceGen`
to vanish when both states are normalized, collapsing the generalized trace distance
to the standard trace distance `(1/2) · ‖·‖₁`.

Reference: follows from `CQState.toJointDensity_trace_eq_sum` and the
`NormalizedCQState.weight_eq_one` field. -/
lemma toJointDensity_trace_eq_one_of_normalized
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : NormalizedCQState X n) :
    ρ.toCQState.toJointDensity.trace = 1 := by
  rw [CQState.toJointDensity_trace_eq_sum]
  exact ρ.weight_eq_one

/-- **Uniform-output-state joint trace equals 1.**

The uniform output state `uniformOutputState σ` on register Z (with σ normalized,
i.e. `σ.trace = 1`) has joint trace equal to 1. When σ = ρ.toCQState.quantumMarginal
and ρ is normalized, the quantum marginal has trace 1 (from `weight_eq_one`).

This ensures the `|tr ρ − tr σ|` term in `traceDistanceGen` vanishes for the
uniform output state derived from a normalized CQ state.

Reference: `CQState.toJointDensity_trace_eq_sum` + `uniformCQState` definition. -/
lemma toJointDensity_uniformOutputState_trace_eq_of_normalized
    {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ}
    (σ : SubDensityOp n)
    (hσ : σ.trace = 1) :
    (uniformOutputState σ : CQState Z n).toJointDensity.trace = 1 := by
  change (uniformCQState σ : CQState Z n).toJointDensity.trace = 1
  rw [uniformCQState_toJointDensity_trace]
  exact hσ

/-- **Quantum marginal trace of a normalized CQ state is 1.**

For `ρ : NormalizedCQState X n`, the quantum marginal operator has trace 1.
This is used to apply `toJointDensity_uniformOutputState_trace_eq_of_normalized`
with `σ = ρ.toCQState.quantumMarginal`.

Reference: `NormalizedCQState.weight_eq_one` + `CQState.quantumMarginalOp` definition. -/
lemma quantumMarginal_trace_eq_one_of_normalized
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : NormalizedCQState X n) :
    ρ.toCQState.quantumMarginal.trace = 1 := by
  unfold CQState.quantumMarginal SubDensityOp.trace
  simp only [CQState.quantumMarginalOp, Matrix.trace_sum, Complex.re_sum]
  exact ρ.weight_eq_one

/-- **Extractor output joint trace equals 1 for normalized inputs.**

For a normalized CQ state ρ, the joint density of the extractor output state
has trace 1. The proof mirrors `extractorOutputState_weight_le_one`: reduce
`∑ z, (extractorWeightedOp H ρ z)` to the quantum marginal via
`sum_extractorWeightedOp_eq_quantumMarginalOp`, then conclude with
`weight_eq_one`. -/
lemma extractorOutputState_joint_trace_eq_one_of_normalized
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : NormalizedCQState X n) :
    ((extractorOutputState H (ρ : CQState X n)) : CQState Z n).toJointDensity.trace = 1 := by
  rw [CQState.toJointDensity_trace_eq_sum]
  change ∑ z : Z, (extractorWeightedOp H (ρ : CQState X n) z).trace.re = 1
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_extractorWeightedOp_eq_quantumMarginalOp]
  simp only [CQState.quantumMarginalOp, Matrix.trace_sum, Complex.re_sum]
  exact ρ.weight_eq_one

/-- Seed-averaged hashing from optimized extended smooth entropy. -/
theorem extractorDistance_le_of_smoothMinEntropyOpt
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X] [DecidableEq X]
    [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropyOpt ε ρ) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp
        (uniformOutputState ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) + 2 * ε := by
  classical
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  exact (extractorDistance_le_seedKeyExtractorDistance H ρ ρ.quantumMarginal).trans
    (quantum_seedKey_LHL_smoothOpt H hH ρ ε hε k hk)

/-- Infinite optimized entropy leaves only the seed-averaged smoothing charge. -/
theorem extractorDistance_le_of_smoothMinEntropyOpt_top
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X] [DecidableEq X]
    [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropyOpt ε ρ = ⊤) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp
        (uniformOutputState ρ.quantumMarginal).toJointDensity.toOp ≤
      2 * ε := by
  apply le_two_mul_of_forall_hashing_bound _ ε (Fintype.card Z)
  intro k
  exact extractorDistance_le_of_smoothMinEntropyOpt H hH ρ ε hε k
    (by rw [hk]; exact le_top)

/-- Seed-averaged leftover hashing for a subnormalized centre and an arbitrary reference. -/
theorem extractorDistance_le_of_smoothMinEntropy
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X] [DecidableEq X]
    [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp
        (uniformOutputState ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) + 2 * ε := by
  exact extractorDistance_le_of_smoothMinEntropyOpt H hH ρ ε hε k
    (hk.trans (smoothMinEntropy_le_smoothMinEntropyOpt ε ρ σ))

/-- Infinite smooth entropy against an arbitrary reference leaves only the `2 * ε` charge. -/
theorem extractorDistance_le_of_smoothMinEntropy_top
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X] [DecidableEq X]
    [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropy ε ρ σ = ⊤) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp
        (uniformOutputState ρ.quantumMarginal).toJointDensity.toOp ≤
      2 * ε := by
  apply extractorDistance_le_of_smoothMinEntropyOpt_top H hH ρ ε hε
  exact top_unique (hk ▸ smoothMinEntropy_le_smoothMinEntropyOpt ε ρ σ)

/-- Seed-averaged hashing from extended entropy against an arbitrary reference. -/
theorem extractorDistance_le_of_minEntropy
    {S X Z : Type*} [Fintype S] [Fintype X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy (ρ : CQState X n) σ) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H (ρ : CQState X n)).toJointDensity.toOp
        (uniformOutputState ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt (Fintype.card Z * 2 ^ (-k)) := by
  classical
  have : Nonempty S := H.seedNonempty
  simpa using extractorDistance_le_of_smoothMinEntropy H hH ρ σ 0 (by norm_num) k
    (by simpa using hk)

end InfoTheory.QuantumLHL

end -- noncomputable section
