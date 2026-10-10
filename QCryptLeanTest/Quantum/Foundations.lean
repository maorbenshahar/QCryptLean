import QCryptLean.Math.LinearAlgebra.Matrix.Blocks
import QCryptLean.Quantum.Operators.TensorAlgebra
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Spectral
import QCryptLean.Quantum.Operators.Purification

/-! # Register, normalization, and universe regression probes -/

open Quantum.Operators Matrix
open scoped Kronecker ComplexOrder

universe u v

noncomputable section

-- The carrier, rectangular tensor, and self-adjoint space require no finiteness.
example (X : Type u) : Type u := Op X
example {X : Type u} {Y : Type v} (A : Op X) (B : Op Y) : Op (X × Y) := A ⊗ₖ B
example (X : Type u) : Module ℝ (HermitianOp X) := inferInstance
example (X : Type u) [Fintype X] [DecidableEq X] : Group (UnitaryOp X) := inferInstance

-- Empty registers admit sub-states, but no density states.
example : (SubDensityOp.zero (X := Empty)).toOp = 0 := rfl
example (ρ : DensityOp Empty) : False := by
  obtain ⟨x⟩ := ρ.nonempty
  exact Empty.elim x

-- The empty tensor family is the scalar unit even if its local register is empty.
example : Op.tensorPow (0 : Op Empty) 0 = 1 := by
  ext x y
  simp [Op.tensorPow, Matrix.one_apply, Subsingleton.elim x y]

-- A zero-site power of a zero sub-state is normalized; no `NeZero` premise appears.
example : ((SubDensityOp.zero (X := Empty)).tensorPow 0).toOp.trace = 1 := by
  simp [SubDensityOp.tensorPow, SubDensityOp.tensorFamily, Matrix.trace_piTensorProduct]

-- Canonical purification works on a named singleton register.
example : (stdNormKet ()).toDensityOp.purification.partialTraceRight =
    (stdNormKet ()).toDensityOp := DensityOp.partialTraceRight_purification _

example : ((stdNormKet ()).toDensityOp.tensorPow 3).IsPure :=
  DensityOp.isPure_tensorPow (NormKet.isPure_toDensityOp _) _

-- The same proofs accept registers in different universes.
example {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (ρ : DensityOp X) (σ : DensityOp Y) :
    (ρ.kronecker σ).partialTraceLeft = σ := DensityOp.partialTraceLeft_kronecker _ _

example : OpLe (0 : Op Unit) (Complex.I • 1) ∧ OpLe (Complex.I • 1) (0 : Op Unit) := by
  constructor <;> intro x <;>
    simp [quadraticForm, Matrix.mulVec, dotProduct, Complex.mul_re, Complex.mul_im] <;>
      ring_nf <;> exact le_rfl

example : ¬(Complex.I • (1 : Op Unit)).PosSemidef := by
  intro h
  have he := congrFun (congrFun h.isHermitian () ) ()
  have hi := congrArg Complex.im he
  norm_num [Matrix.conjTranspose_apply] at hi
