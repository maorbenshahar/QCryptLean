import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.LambdaBound
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSubNormalized
import QCryptLean.InfoTheory.QuantumLHL.ExtractorContractivity
import QCryptLean.InfoTheory.QuantumLHL.UniformOutputBlock
import QCryptLean.InfoTheory.QuantumLHL.SmoothingSideConditions
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Metrics.TraceNormDilation

/-!
# Contractivity for extractor smoothing

Purified distance bounds the change in both the seed-averaged extractor output and its uniform
comparison state. The two estimates supply the smoothing charge in leftover hashing.
-/

open Quantum.Operators Quantum.Metrics Matrix Real

open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **DPI step (T1) for the smooth LHL.**

The extractor channel `E(·) = (extractorOutputState H ·).toJointDensity.toOp` is
CPTP on the joint space, so the generalized trace distance contracts under it.
Combined with `traceDistanceGen_le_purifiedDistance` on the joint, we get:

  `D_gen(E(ρ), E(ρ')) ≤ CQState.purifiedDistance ρ ρ'`.

This is the bound used to control the (T1) leg of the triangle in
`quantum_seedKey_LHL_smooth`. -/
lemma traceDistanceGen_extractorOutput_le_purifiedDistance
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (extractorOutputState H ρ).toJointDensity.toOp
        (extractorOutputState H ρ').toJointDensity.toOp ≤
      CQState.purifiedDistance ρ ρ' := by
  haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  -- STEP 1: extractor contracts the generalized trace distance on joint densities.
  have hStep1 := traceDistanceGen_extractorOutput_le H ρ ρ'
  -- STEP 2: D_gen(ρ.joint, ρ'.joint) ≤ purifiedDistance ρ.joint ρ'.joint.
  have hStep2 :=
    InfoTheory.SmoothMinEntropy.traceDistanceGen_le_purifiedDistance
      ρ.toJointDensity ρ'.toJointDensity
  -- Compose; CQState.purifiedDistance unfolds to the joint purifiedDistance.
  exact hStep1.trans hStep2

/-- **DPI step (T3) for the smooth LHL.**

The uniform output channel `U(σ) = (uniformOutputState σ).toJointDensity.toOp`
applied to the quantum marginal `ρ.quantumMarginal` of a CQ state contracts
the generalized trace distance compared to the input CQ states' purified
distance:

  `D_gen(U(ρ.quantumMarginal), U(ρ'.quantumMarginal)) ≤ CQState.purifiedDistance ρ ρ'`.

This is the bound used to control the (T3) leg of the triangle in
`quantum_seedKey_LHL_smooth`. -/
lemma traceDistanceGen_uniformOutput_le_marginal_purifiedDistance
    {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) := ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (uniformOutputState ρ.quantumMarginal : CQState Z n).toJointDensity.toOp
        (uniformOutputState ρ'.quantumMarginal : CQState Z n).toJointDensity.toOp ≤
      CQState.purifiedDistance ρ ρ' := by
  haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  -- Stage 1: collapse uniform-output to the quantum marginals.
  rw [traceDistanceGen_uniformOutput_eq]
  -- Stage 2: marginal ≤ joint.
  -- Stage 3: traceDistanceGen_le_purifiedDistance on the joint.
  exact (traceDistanceGen_marginal_le_joint ρ ρ').trans
    (InfoTheory.SmoothMinEntropy.traceDistanceGen_le_purifiedDistance
      ρ.toJointDensity ρ'.toJointDensity)

end InfoTheory.QuantumLHL

end -- noncomputable section
