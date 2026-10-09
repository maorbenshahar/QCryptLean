import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.QuantumLHL.SeedContractivity

/-! # Measure-then-hash consistency and nonuniform output regressions -/
open Quantum.Operators Quantum.Channels Quantum.Metrics Matrix
open InfoTheory.Postselection InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open scoped ComplexOrder
noncomputable section
namespace QCryptLeanTest.MeasureThenHash

variable {A B K C CE CP Raw E Public Seed Key : Type*}
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] [Fintype Public] [Fintype Seed] [Nonempty Seed]
  [Fintype Key] [Nonempty Key] [DecidableEq Seed] [DecidableEq Key] [DecidableEq Public]
  {k l : ℕ} {M : RawKeyMeasurement A B K C CE CP Raw E k}

/-- Equal protocol variants force uniformity of the same instrument's accepted hash output. -/
theorem extractor_eq_uniform_of_variants_eq (H : MeasureThenHash M Public Seed Key l)
    (h : M.toProtocol.variantReal l = M.toProtocol.variantIdeal l)
    (ρ : DensityOp (Fin k → A × B)) :
    let τ := CQState.ofInstrument H.instrument H.instrument_isCompletelyPositive
      H.instrument_weight_le_one ρ
    (SeedKey.output H.hash τ).toJointDensity.toOp =
      (uniformCQState (C := Seed × Key) τ.quantumMarginal).toJointDensity.toOp := by
  have heq := congrArg (fun f => M.toProtocol.acceptProj
    (f (Matrix.reindex (Quantum.Symmetry.pairFunctions A B k)
      (Quantum.Symmetry.pairFunctions A B k) ρ.toOp))) h
  rw [H.acceptProj_variantReal ρ, H.acceptProj_variantIdeal ρ] at heq
  have hinj : Function.Injective (fun T : Op (Public × (Seed × Key)) =>
      H.encode * T * H.encodeᴴ) := by
    apply Function.LeftInverse.injective (g := fun T => H.encodeᴴ * T * H.encode)
    intro T
    simp only [← Matrix.mul_assoc, H.encode_isometry, Matrix.one_mul]
    rw [Matrix.mul_assoc, H.encode_isometry, Matrix.mul_one]
  exact hinj heq

private def raw : CQState Unit Unit where
  stateMap _ := ⟨1, Matrix.PosSemidef.one, by norm_num [Matrix.trace]⟩
  weight_le_one := by norm_num [SubDensityOp.trace, Matrix.trace]

private def hash : HashFamily Unit Unit Bool where
  hash _ _ := false

/-- Two-universality does not force a deterministic input to produce a uniform key. -/
example : hash.IsTwoUniversal := by
  intro x y hxy
  exact (hxy (Subsingleton.elim _ _)).elim

/-- A one-element raw alphabet yields unequal real and ideal output matrices. -/
theorem deterministic_hash_ne_uniform :
    (SeedKey.output hash raw).toJointDensity.toOp ≠
      (uniformCQState (C := Unit × Bool) raw.quantumMarginal).toJointDensity.toOp := by
  intro h
  have he := congrArg (fun T : Op (Unit × (Unit × Bool)) => T ((), (), true) ((), (), true)) h
  norm_num [SeedKey.output, SeedKey.weightedOp, uniformCQState, CQState.toJointDensity,
    CQState.toJointOp, CQState.ofBlocks, CQState.quantumMarginal, Matrix.blockDiagonal, raw, hash,
    DensityOp.toSubDensityOp, NormKet.toDensityOp, Ket.projector, stdNormKet, stdKet] at he

end QCryptLeanTest.MeasureThenHash
