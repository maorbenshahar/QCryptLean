import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropyFidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.MinEntropyGuess

/-!
# Conditional max-entropy for CQ states of positive weight

The real-valued entropy interfaces have positive-weight domains:

1. `conditionalMaxEntropyOptReal`, the public optimized CQ conditional
   max-entropy in the fidelity formulation.
2. `conditionalMaxEntropyPartialTransposeSurrogateOptReal`, the algebraic
   partial-transpose min-entropy surrogate.

## Main definitions
- `conditionalMaxEntropyFidelityReal`: real-valued conditional max-entropy
  relative to a reference density operator with positive fidelity.
- `conditionalMaxEntropyFidelityOptReal`: optimized real-valued conditional
  max-entropy of a CQ state of positive weight, optimized over positive-fidelity references.
- `conditionalMaxEntropyPartialTransposeSurrogateOptReal`: the partial-transpose
  min-entropy surrogate.
- `conditionalMaxEntropyOptReal`: public alias for the fidelity-optimized
  max-entropy.
- `classicalMarginalMaxEntropyReal`: classical max-entropy of the marginal
  distribution, an upper bound for CQ states of positive weight.

## Main statements
- `conditionalMaxEntropyPartialTransposeSurrogateOptReal_nonpos`: the legacy
  surrogate is nonpositive on its positive-weight domain.
- `conditionalMaxEntropyOptReal_le_classicalMarginalMaxEntropy`: CQ
  max-entropy is bounded by the classical max-entropy of the marginal
  distribution.
-/

open Quantum.Operators
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Partial-transpose surrogate on CQ states of positive weight.

For a CQ state `ρ_{CA}` with blocks `ρ_c : SubDensityOp n`:

  `H_sur(C|A)_ρ = −H_min(C|Ā)_{ρ̄}`

where `ρ̄ = CQState.partialTransposeQ ρ` is the partial transpose on A.

This is not the standard CQ conditional max-entropy used in Berta's uncertainty
relation: over the current CQ-only min-entropy interface it is always nonpositive
for nonempty classical registers. -/
noncomputable def conditionalMaxEntropyPartialTransposeSurrogateOptReal
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (_hρ : 0 < ∑ x, ρ.classicalMarginal x) : ℝ :=
  -conditionalMinEntropyOptReal ρ.partialTransposeQ

/-- Public optimized CQ conditional max-entropy for states of positive weight.

The supremum ranges over normalized references with positive fidelity.

This name is the stable downstream interface. The partial-transpose surrogate
is available as `conditionalMaxEntropyPartialTransposeSurrogateOptReal`. -/
noncomputable def conditionalMaxEntropyOptReal
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) : ℝ :=
  conditionalMaxEntropyFidelityOptReal ρ hρ

/-- Classical Rényi-1/2 max-entropy of a CQ marginal of positive total weight.

For a marginal `p_x = ρ.classicalMarginal x`, this is
`log₂ ((∑ x, √p_x)^2)`. It bounds the fidelity-based CQ max-entropy above
for all CQ states of positive weight. -/
noncomputable def classicalMarginalMaxEntropyReal
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n)
    (_hρ : 0 < ∑ x, ρ.classicalMarginal x) : ℝ :=
  Real.log ((∑ x : X, Real.sqrt (ρ.classicalMarginal x)) ^ 2) / Real.log 2

/-- The maximally mixed reference has positive fidelity with every CQ state of positive weight. -/
lemma conditionalMaxEntropyFidelity_maxMixed_pos
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) :
    0 < Quantum.Metrics.fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) (DensityOp.maxMixed n)) := by
  classical
  apply Quantum.Metrics.fidelity_pos_of_posDef
  · intro hz
    have ht := CQState.toJointDensity_trace_eq_sum ρ
    have ht0 : ρ.toJointDensity.trace = 0 := by
      simp [SubDensityOp.trace, hz]
    have : ∑ x, ρ.classicalMarginal x = 0 := ht.symm.trans ht0
    linarith
  · have href :
        (conditionalMaxEntropyFidelityReferenceOp (X := X) (DensityOp.maxMixed n)).toOp =
          (1 / (n : ℂ)) • 1 := by
      rw [conditional_max_entropy_fidelity_reference_op_eq_cq_block]
      simp only [Quantum.Metrics.cqBlockPosSemidefOp_toOp, DensityOp.maxMixed]
      rw [show (fun _ : X => (1 / (n : ℂ)) • (1 : Op n)) =
        (1 / (n : ℂ)) • (1 : X → Op n) from rfl]
      rw [Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one, Matrix.reindex_apply,
        Matrix.submatrix_smul]
      simp only [Pi.smul_apply, Matrix.submatrix_one_equiv]
    rw [href]
    apply Matrix.PosDef.one.smul
    have hpos : (0 : ℝ) < 1 / (n : ℝ) :=
      one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero n))
    simpa using Complex.zero_lt_real.mpr hpos

/-- Fixed-reference max-entropy is bounded by the classical marginal max-entropy
for every CQ state of positive weight and every reference with positive fidelity. -/
lemma conditionalMaxEntropyFidelityReal_le_classicalMarginalMaxEntropy_of_normalized
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x)
    (σ : DensityOp n)
    (hF : 0 < Quantum.Metrics.fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) :
    conditionalMaxEntropyFidelityReal ρ σ hF ≤ classicalMarginalMaxEntropyReal ρ hρ := by
  classical
  have hF_le := conditionalMaxEntropyFidelity_reference_fidelity_le_sum_sqrt_marginal ρ σ
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (sq_pos_of_pos hF) (pow_le_pow_left₀ hF.le hF_le 2))
    (Real.log_pos one_lt_two).le

/-- Optimized fidelity max-entropy is bounded by the classical marginal max-entropy
for every CQ state of positive weight. -/
lemma conditionalMaxEntropyFidelityOptReal_le_classicalMarginalMaxEntropy_of_normalized
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) :
    conditionalMaxEntropyFidelityOptReal ρ hρ ≤ classicalMarginalMaxEntropyReal ρ hρ := by
  unfold conditionalMaxEntropyFidelityOptReal
  apply csSup_le
  · exact ⟨_, DensityOp.maxMixed n, conditionalMaxEntropyFidelity_maxMixed_pos ρ hρ, rfl⟩
  · rintro b ⟨σ, hF, rfl⟩
    exact conditionalMaxEntropyFidelityReal_le_classicalMarginalMaxEntropy_of_normalized
      ρ hρ σ hF

/-- The partial-transpose surrogate is nonpositive for CQ states of positive weight.

This follows from the CQ guessing-probability identity for the min-entropy and
the bound `povmGuessingProb ρ ≤ 1`. -/
lemma conditionalMaxEntropyPartialTransposeSurrogateOptReal_nonpos
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) :
    conditionalMaxEntropyPartialTransposeSurrogateOptReal ρ hρ ≤ 0 := by
  unfold conditionalMaxEntropyPartialTransposeSurrogateOptReal
  rw [conditionalMinEntropyReal_cq_guess_eq ρ.partialTransposeQ]
  have hlog_nonpos :
      Real.log (povmGuessingProb ρ.partialTransposeQ) ≤ 0 :=
    Real.log_nonpos (povmGuessingProb_nonneg ρ.partialTransposeQ)
      (povmGuessingProb_le_one ρ.partialTransposeQ)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hquot :
      Real.log (povmGuessingProb ρ.partialTransposeQ) / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog_nonpos hlog2_pos.le
  simpa [neg_div] using hquot

/-- Fidelity-based CQ max-entropy is bounded by the classical max-entropy of
the classical marginal for CQ states of positive weight.

The proof follows the block/fidelity route:
decompose the CQ fidelity blockwise, bound each block by the square root of the
product of traces, then lift the pointwise reference-state bound through the
`sSup` optimization. -/
lemma conditionalMaxEntropyOptReal_le_classicalMarginalMaxEntropy
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) :
    conditionalMaxEntropyOptReal ρ hρ ≤ classicalMarginalMaxEntropyReal ρ hρ := by
  simpa [conditionalMaxEntropyOptReal] using
    conditionalMaxEntropyFidelityOptReal_le_classicalMarginalMaxEntropy_of_normalized
      ρ hρ

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
