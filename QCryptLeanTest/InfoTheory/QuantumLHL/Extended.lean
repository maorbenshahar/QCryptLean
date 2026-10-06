import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyPosDefBridge
import QCryptLean.InfoTheory.QuantumLHL.FlagPackEntropy
import QCryptLeanTest.InfoTheory.SmoothMinEntropy.Extended

/-!
# Extended-entropy leftover hashing regressions

These checks cover the zero floor, infinite floor, exact zero-state threshold, and packed zero
witnesses. Nonuniversal constant hashes exercise both zero-floor bounds, and arbitrary or singular
references exercise the scalar extended-entropy bounds. The negative fixed-reference regression
confirms why zero floors need a separate proof.
-/

open Quantum.Operators Quantum.Metrics InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace QCryptLeanTest.QuantumLHL

/-- A one-input hash family with a nontrivial two-element output alphabet. -/
private def oneInputHash : QuantumHashFamily Unit Unit Bool where
  hash _ _ := false

private lemma oneInputHash_universal : oneInputHash.isUniversal := by
  intro x y hxy
  exact (hxy (Subsingleton.elim _ _)).elim

/-- Zero floors give a nontrivial hashing estimate without coefficient-one domination. -/
theorem zero_floor_hashing (ρ : CQState Unit 1) (σ : SubDensityOp 1)
    (hσ : σ.toOp.PosDef) :
    traceDistanceGen (seedKeyExtractorOutputState oneInputHash ρ).toJointDensity.toOp
      (seedUniformOutputState (S := Unit) (Z := Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt 2 := by
  simpa using quantum_seedKey_LHL_smooth oneInputHash oneInputHash_universal ρ σ hσ
    0 (by norm_num) 0 (by simp)

/-- At zero radius, the zero state has infinite entropy and exactly zero hashing error. -/
theorem zero_state_hashing (σ : SubDensityOp 1) (hσ : σ.toOp.PosDef) :
    traceDistanceGen
      (seedKeyExtractorOutputState oneInputHash (zeroCQ (X := Unit) (n := 1))).toJointDensity.toOp
      (seedUniformOutputState (S := Unit) (Z := Bool)
        (zeroCQ (X := Unit) (n := 1)).quantumMarginal).toJointDensity.toOp ≤ 0 := by
  simpa using quantum_seedKey_LHL_smooth_of_top oneInputHash oneInputHash_universal
    zeroCQ σ hσ 0 (by norm_num) (by simp)

/-- The exact weight threshold is admitted, including its infinite-entropy endpoint. -/
theorem threshold_hashing (ρ : CQState Unit 1) (σ : SubDensityOp 1)
    (hσ : σ.toOp.PosDef) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∑ x, (ρ.stateMap x).trace = ε ^ 2) :
    traceDistanceGen (seedKeyExtractorOutputState oneInputHash ρ).toJointDensity.toOp
      (seedUniformOutputState (S := Unit) (Z := Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
      2 * ε := by
  exact quantum_seedKey_LHL_smooth_of_top oneInputHash oneInputHash_universal ρ σ hσ ε hε
    (smoothMinEntropy_eq_top_of_weight_le_eps_sq hε ρ σ hw.le)

/-- Reference optimization accepts the zero state without a positive-definite reference input. -/
theorem zero_state_optimized_hashing :
    traceDistanceGen
      (seedKeyExtractorOutputState oneInputHash (zeroCQ (X := Unit) (n := 1))).toJointDensity.toOp
      (seedUniformOutputState (S := Unit) (Z := Bool)
        (zeroCQ (X := Unit) (n := 1)).quantumMarginal).toJointDensity.toOp ≤ 0 := by
  apply le_trans (quantum_seedKey_LHL_smoothOpt_of_top oneInputHash oneInputHash_universal
    zeroCQ 0 (by norm_num) ?_) (by norm_num)
  apply smoothMinEntropyOpt_eq_top_of_weight_le_eps_sq (by norm_num)
  have hzero : (0 : SubDensityOp 1).trace = 0 := by
    change (0 : Op 1).trace.re = 0
    simp
  simp [zeroCQ, hzero]

/-- Zero packed witnesses require no positive weight and carry every per-block finite floor. -/
theorem packed_zero_witnesses (σ : Unit → SubDensityOp 1) (k : Unit → ℝ) :
    let blocks : Unit → CQState Unit 1 := fun _ => zeroCQ
    let hjoint : ∑ c : Unit, ∑ x : Unit, ((blocks c).stateMap x).trace ≤ 1 := by
      simpa [blocks, zeroCQ] using (show (0 : SubDensityOp 1).trace ≤ 1 from
        (0 : SubDensityOp 1).trace_le_one)
    ENNReal.ofReal (-Real.logb 2 (packExpSum k)) ≤
      smoothMinEntropy 0 (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity := by
  dsimp only
  apply flagPack_smoothMinEntropy_ge_of_blocks
  · intro c
    simp
  · norm_num

/-- A constant hash on two distinct inputs is not universal. -/
private def constantHash : QuantumHashFamily Unit Bool Bool where
  hash _ _ := false

private lemma constantHash_not_universal : ¬ constantHash.isUniversal := by
  intro h
  have hcollision := h false true (by decide)
  norm_num [constantHash] at hcollision

/-- The seed-averaged zero floor does not require a universal hash family. -/
theorem nonuniversal_zero_floor (ρ : CQState Bool 1) :
    traceNorm ((extractorOutputState constantHash ρ).toJointDensity.toOp -
      (uniformOutputState (Z := Bool) ρ.quantumMarginal).toJointDensity.toOp) ≤
        Real.sqrt 2 := by
  simpa using quantum_LHL_zero_floor constantHash ρ

/-- Keeping the seed also needs no universality at the zero floor. -/
theorem nonuniversal_seed_zero_floor (ρ : CQState Bool 1) :
    traceNorm ((seedKeyExtractorOutputState constantHash ρ).toJointDensity.toOp -
      (seedUniformOutputState (S := Unit) (Z := Bool)
        ρ.quantumMarginal).toJointDensity.toOp) ≤ Real.sqrt 2 := by
  simpa using quantum_seedKey_LHL_zero_floor constantHash ρ

/-- The smooth scalar bound accepts an arbitrary reference, including singular ones. -/
theorem arbitrary_reference_smooth_hashing (ρ : CQState Unit 1) (σ : SubDensityOp 1)
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    traceDistanceGen (extractorOutputState oneInputHash ρ).toJointDensity.toOp
      (uniformOutputState (Z := Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
        (1 / 2) * Real.sqrt (2 * 2 ^ (-k)) + 2 * ε := by
  simpa using extractorDistance_le_of_smoothMinEntropy oneInputHash oneInputHash_universal
    ρ σ ε hε k hk

/-- The unsmoothed scalar bound accepts an arbitrary reference. -/
theorem arbitrary_reference_hashing (ρ : CQState Unit 1) (σ : SubDensityOp 1)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    traceDistanceGen (extractorOutputState oneInputHash ρ).toJointDensity.toOp
      (uniformOutputState (Z := Bool) ρ.quantumMarginal).toJointDensity.toOp ≤
        (1 / 2) * Real.sqrt (2 * 2 ^ (-k)) := by
  simpa using extractorDistance_le_of_minEntropy oneInputHash oneInputHash_universal ρ σ k hk

/-- The top scalar bound applies to the zero state against the singular zero reference. -/
theorem singular_reference_top_hashing :
    traceDistanceGen
      (extractorOutputState oneInputHash (zeroCQ (X := Unit) (n := 1))).toJointDensity.toOp
      (uniformOutputState (Z := Bool)
        (zeroCQ (X := Unit) (n := 1)).quantumMarginal).toJointDensity.toOp ≤ 0 := by
  simpa using extractorDistance_le_of_smoothMinEntropy_top oneInputHash oneInputHash_universal
    zeroCQ 0 0 (by norm_num) (by simp)

#check QCryptLeanTest.SmoothMinEntropy.negative_fixed_reference_entropy
#check quantum_LHL_subNormalized
#check extractorDistance_le_of_minEntropy
#check extractorDistance_le_of_smoothMinEntropy
#check extractorDistance_le_of_smoothMinEntropy_top
#check extractorDistance_le_of_smoothMinEntropyOpt
#check extractorDistance_le_of_smoothMinEntropyOpt_top
#check quantum_seedKey_LHL_smooth_operatorBlock
#check quantum_seedKey_LHL_smooth_operatorBlock_witness
#check quantum_seedKey_LHL_smooth_operatorBlock_of_posDef_dominating
#check quantum_seedKey_LHL_smooth_operatorBlock_of_smul_opLe
#check quantum_seedKey_LHL_smooth_of_refOptimisedFloor
#check flagPack_smoothMinEntropy_ge_of_block_witnesses

#print axioms sum_traceNorm_sub_uniform_le
#print axioms quantum_LHL_zero_floor
#print axioms quantum_seedKey_LHL_zero_floor
#print axioms extractorDistance_le_of_smoothMinEntropy
#print axioms quantum_seedKey_LHL_smooth
#print axioms quantum_seedKey_LHL_smooth_of_top
#print axioms quantum_seedKey_LHL_smoothOpt
#print axioms quantum_seedKey_LHL_smooth_operatorBlock_witness
#print axioms flagPack_conditionalMinEntropy_ge_of_blocks

end QCryptLeanTest.QuantumLHL

end
