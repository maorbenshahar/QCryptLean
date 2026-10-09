import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import Mathlib.Analysis.Complex.Basic

/-!
# Typed partial-trace boundary probes

Check independent universes, infinite retained indices, degenerate discarded
registers, noncommutative coefficients, and symbolic function registers.
-/

open Matrix
open scoped ComplexOrder Kronecker

universe u v w

section Universes

variable {X : Type u} {Y : Type v} {Z : Type w} [Fintype Z]

example (M : Matrix (X × Z) (Y × Z) ℤ) : Matrix X Y ℤ := partialTraceRight M

example (M : Matrix (Z × X) (Z × Y) ℤ) : Matrix X Y ℤ := partialTraceLeft M

example {M : Matrix (X × Z) (X × Z) ℂ} (h : M.PosSemidef) :
    (partialTraceRight M).PosSemidef := h.partialTraceRight

example (M N : Matrix (X × Z) (Y × Z) ℂ) :
    partialTraceRightLinearMap (S := ℝ) (M + N) =
      partialTraceRightLinearMap (S := ℝ) M + partialTraceRightLinearMap (S := ℝ) N :=
  map_add _ _ _

end Universes

example (M : Matrix (ℕ × Empty) (ℤ × Empty) ℤ) : partialTraceRight M = 0 := by
  simp

example (M : Matrix (Empty × ℕ) (Empty × ℤ) ℤ) : partialTraceLeft M = 0 := by
  simp

example (M : Matrix (ℕ × Unit) (ℤ × Unit) ℤ) (i : ℕ) (j : ℤ) :
    partialTraceRight M i j = M (i, ()) (j, ()) := by simp

example (M : Matrix (Unit × ℕ) (Unit × ℤ) ℤ) (i : ℕ) (j : ℤ) :
    partialTraceLeft M i j = M ((), i) ((), j) := by simp

-- Nonemptiness in strict positivity is necessary even though PSD needs no such assumption.
example : ¬ (partialTraceRight (1 : Matrix (Unit × Empty) (Unit × Empty) ℂ)).PosDef := by
  rw [partialTraceRight_of_isEmpty]
  intro h
  have hpos := h.diag_pos (i := ())
  simp at hpos

-- Matrix coefficients exercise the noncommutative sandwich statements.
example (A B : Matrix Bool Bool (Matrix Bool Bool ℤ))
    (M : Matrix (Bool × Unit) (Bool × Unit) (Matrix Bool Bool ℤ)) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix Unit Unit (Matrix Bool Bool ℤ))) * M *
      (B ⊗ₖ (1 : Matrix Unit Unit (Matrix Bool Bool ℤ)))) =
        A * partialTraceRight M * B :=
  partialTraceRight_kronecker_one_sandwich A M B

section FunctionRegisters

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {D : I → Type v} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

example : DecidableEq ((i : I) → D i) := inferInstance

example : Fintype ((i : I) → D i) := inferInstance

example : Fintype (Σ i, D i) := inferInstance

example (M : Matrix ((Σ i, D i) × ((i : I) → D i))
    ((Σ i, D i) × ((i : I) → D i)) ℂ) :
    (partialTraceRight M).trace = M.trace := trace_partialTraceRight M

example (k l : ℕ)
    (M : Matrix ((Fin k → Bool) × (Fin l → Bool)) ((Fin k → Bool) × (Fin l → Bool)) ℂ)
    (h : M.PosDef) : (partialTraceRight M).PosDef := h.partialTraceRight

example (M : Matrix (Bool × (Fin 0 → Empty)) (Bool × (Fin 0 → Empty)) ℤ) :
    partialTraceRight M =
      M.submatrix (fun x => (x, default)) (fun y => (y, default)) :=
  partialTraceRight_of_unique M

end FunctionRegisters
