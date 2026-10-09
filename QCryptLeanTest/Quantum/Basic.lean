import QCryptLean.Quantum.Operators.Basic

/-! # Register, normalization, and universe regression probes -/

open Quantum.Operators
open scoped ComplexOrder

universe u v

example (X : Type u) : Type u := Op X

example {X : Type u} [Fintype X] (ρ : DensityOp X) : ρ.toOp.IsHermitian := ρ.isHermitian

example (ρ : DensityOp Empty) : False := by
  obtain ⟨x⟩ := ρ.nonempty
  exact Empty.elim x

example : (SubDensityOp.zero (X := Empty)).toOp.trace = 0 := by
  simp [SubDensityOp.zero]

example (k l : ℕ) (ρ : DensityOp ((Fin k → Bool) × (Fin l → Bool))) :
    DensityOp (Fin k → Bool) := ρ.partialTraceRight

