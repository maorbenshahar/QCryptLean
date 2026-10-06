import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.DistanceBounds.AcceptSplit
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothCompactness

/-!
# Operator-block leftover hashing

The smooth entropy bound gives an accept-block trace-distance estimate and a residual trace-norm
bound from an exact hashing witness. The entropy hypothesis is `ENNReal.ofReal k ≤
smoothMinEntropy ε ρ σ`; no positive witness-weight or real-supremum boundedness assumption is
needed.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Extended-entropy smoothing with exact hashing accept blocks and residual charge `2 * ε`. -/
theorem quantum_seedKey_LHL_smooth_operatorBlock
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    ∃ ρReal_acc ρReal_resid ρIdeal_acc ρIdeal_resid : Op (n * Fintype.card (S × Z)),
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp = ρReal_acc + ρReal_resid ∧
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp =
            ρIdeal_acc + ρIdeal_resid ∧
          ((1 / 2) * traceNorm ρReal_resid + (1 / 2) * traceNorm ρIdeal_resid ≤ 2 * ε) ∧
            traceDistanceGen ρReal_acc ρIdeal_acc ≤
              (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  obtain ⟨ρ', hρ'_dist, hρ'_k⟩ :=
    quantum_seedKey_LHL_smooth_hashing_witness H hH ρ σ hσ_pd ε hε k hk
  refine ⟨(seedKeyExtractorOutputState H ρ').toJointDensity.toOp,
    (seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
      (seedKeyExtractorOutputState H ρ').toJointDensity.toOp,
    (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp,
    (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp -
      (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp,
    ?_, ?_, ?_, ?_⟩
  · -- `E ρ = E ρ' + (E ρ − E ρ')`
    abel
  · -- `U ρ_X = U ρ'_X + (U ρ_X − U ρ'_X)`
    abel
  · -- Each residual half-trace-norm is bounded by the purified distance.
    have hT1 :
        traceDistanceGen
            (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
            (seedKeyExtractorOutputState H ρ').toJointDensity.toOp ≤ ε :=
      (traceDistanceGen_seedKeyExtractorOutput_le_purifiedDistance H ρ ρ').trans hρ'_dist
    have hT3 :
        traceDistanceGen
            (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp
            (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp ≤
          ε := by
      rw [traceDistanceGen_symm]
      refine (traceDistanceGen_uniformOutput_le_marginal_purifiedDistance (Z := S × Z) ρ' ρ).trans
        ?_
      rw [CQState.purifiedDistance_symm]
      exact hρ'_dist
    have hR := traceNorm_sub_le_two_traceDistanceGen
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedKeyExtractorOutputState H ρ').toJointDensity.toOp
    have hI := traceNorm_sub_le_two_traceDistanceGen
      (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp
    linarith
  · -- Accept bound: direct (sharp, non-smooth) leftover hashing on the witness `ρ'`.
    exact hρ'_k

/-- Extended-entropy smoothing with exact hashing accept blocks and residual charge `2 * ε`. -/
theorem quantum_seedKey_LHL_smooth_operatorBlock_witness
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    ∃ ρ' : CQState X n,
      ((1 / 2) * traceNorm
            ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp
              - (seedKeyExtractorOutputState H ρ').toJointDensity.toOp)
          ≤ ε) ∧
        ((1 / 2) * traceNorm
            ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp
              - (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp)
          ≤ ε) ∧
        traceDistanceGen
            ((seedKeyExtractorOutputState H ρ').toJointDensity.toOp)
            ((seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp) ≤
          (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  obtain ⟨ρ', hρ'_dist, hρ'_k⟩ :=
    quantum_seedKey_LHL_smooth_hashing_witness H hH ρ σ hσ_pd ε hε k hk
  refine ⟨ρ', ?_, ?_, ?_⟩
  · -- Real smoothing remainder half-trace-norm ≤ ε.
    have hT1 :
        traceDistanceGen
            (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
            (seedKeyExtractorOutputState H ρ').toJointDensity.toOp ≤ ε :=
      (traceDistanceGen_seedKeyExtractorOutput_le_purifiedDistance H ρ ρ').trans hρ'_dist
    have hR := traceNorm_sub_le_two_traceDistanceGen
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedKeyExtractorOutputState H ρ').toJointDensity.toOp
    linarith
  · -- Ideal smoothing remainder half-trace-norm ≤ ε.
    have hT3 :
        traceDistanceGen
            (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp
            (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp ≤
          ε := by
      rw [traceDistanceGen_symm]
      refine (traceDistanceGen_uniformOutput_le_marginal_purifiedDistance (Z := S × Z) ρ' ρ).trans
        ?_
      rw [CQState.purifiedDistance_symm]
      exact hρ'_dist
    have hI := traceNorm_sub_le_two_traceDistanceGen
      (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal).toJointDensity.toOp
    linarith
  · -- Accept bound: direct (sharp, non-smooth) leftover hashing on the witness `ρ'`.
    exact hρ'_k


/-- For a positive-definite reference, every floor at most the signed smooth min-entropy is
attained by a state in the smoothing ball. -/
theorem smoothMinEntropyReal_exists_approx_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε)
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef)
    (k : ℝ) (hk : k ≤ smoothMinEntropyReal ε ρ σ) :
    ∃ ρ' : CQState X n,
      CQState.purifiedDistance ρ ρ' ≤ ε ∧ k ≤ conditionalMinEntropyReal ρ' σ := by
  by_cases hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ))
  · -- The defining supremum is a genuine finite maximum.
    rcases eq_or_lt_of_le hk with heq | hlt
    · -- Boundary `k = H_min^ε`: the supremum is attained (compactness + continuity).
      obtain ⟨ρ', hd, hval⟩ :=
        smoothMinEntropyReal_sSup_attained_of_bddAbove ε hε ρ σ hσ_pd hbdd
      exact ⟨ρ', hd, le_of_eq (heq.trans hval.symm)⟩
    · -- Strict interior `k < H_min^ε`: the existing strict extractor suffices.
      exact smoothMinEntropyReal_exists_approx ε hε ρ σ k hlt
  · -- The optimization set is unbounded above (the `sSup = 0` sentinel): some candidate already
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨y, hy_mem, hky⟩ := hbdd k
    obtain ⟨ρ', hval, hd⟩ := hy_mem
    exact ⟨ρ', hd, hval ▸ hky.le⟩

end InfoTheory.QuantumLHL

end -- noncomputable section
