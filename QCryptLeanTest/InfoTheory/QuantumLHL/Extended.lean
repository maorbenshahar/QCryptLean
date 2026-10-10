import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLeanTest.InfoTheory.SmoothMinEntropy.Extended

/-! # Extended entropy and arbitrary-reference hashing regressions -/
open Quantum.Operators Quantum.Metrics InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
noncomputable section
namespace QCryptLeanTest.QuantumLHL

private def oneInputHash : HashFamily Unit Unit Bool where
  hash _ _ := false

private lemma oneInputHash_universal : oneInputHash.IsTwoUniversal := by
  intro x y hxy
  exact (hxy (Subsingleton.elim _ _)).elim

/-- A zero floor gives a hashing estimate without a positive-definite reference premise. -/
theorem zero_floor_hashing (ρ : CQState Unit Unit) :
    traceDistanceGen (SeedKey.output oneInputHash ρ).toJointDensity.toOp
      (uniformCQState (C := Unit × Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt 2 := by
  simpa using SeedKey.traceDistanceGen_output_le_of_le_smoothMinEntropyOpt
    oneInputHash oneInputHash_universal ρ 0 (by norm_num) 0 (by simp)

/-- The zero state has exactly zero public-seed hashing error. -/
theorem zero_state_optimized_hashing :
    traceDistanceGen
      (SeedKey.output oneInputHash (CQState.zero : CQState Unit (Fin 2))).toJointDensity.toOp
      (uniformCQState (C := Unit × Bool)
        (CQState.zero : CQState Unit (Fin 2)).quantumMarginal).toJointDensity.toOp ≤ 0 := by
  simpa using SeedKey.traceDistanceGen_output_le_of_smoothMinEntropyOpt_eq_top oneInputHash
    oneInputHash_universal CQState.zero 0 (by norm_num)
    QCryptLeanTest.SmoothMinEntropy.zero_state_entropy.2.2

/-- A singular or non-normalized reference is accepted by the smooth hashing bound. -/
theorem arbitrary_reference_smooth_hashing (ρ : CQState Unit Unit) (σ : SubDensityOp Unit)
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    traceDistanceGen (extractorOutputState oneInputHash ρ).toJointDensity.toOp
      (uniformCQState (C := Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
        (1 / 2) * Real.sqrt (2 * 2 ^ (-k)) + 2 * ε := by
  simpa using extractorDistance_le_of_smoothMinEntropy oneInputHash oneInputHash_universal
    ρ σ ε hε k hk

end QCryptLeanTest.QuantumLHL
