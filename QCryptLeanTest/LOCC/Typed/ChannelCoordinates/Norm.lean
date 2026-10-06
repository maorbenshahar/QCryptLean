import QCryptLean.LOCC.Typed.ChannelCoordinates.Norm

/-!
# Diamond norm API regression tests

The norm laws bound sums of arbitrary blocks without positivity assumptions. The channel bound
discharges the large-budget branch, so only budgets below two need a separate security argument.
-/

namespace QCryptLeanTest.DiamondNorm

open Quantum.Operators Quantum.Channels

/-- A weighted three-block decomposition is bounded by the sum of its block budgets. -/
example {n m : ℕ} [NeZero n] [NeZero m]
    (A B C : Op n →ₗ[ℂ] Op m) (c : ℂ) :
    diamondNorm (c • A + B - C) ≤
      ‖c‖ * diamondNorm A + diamondNorm B + diamondNorm C := by
  calc
    diamondNorm (c • A + B - C) ≤ diamondNorm (c • A + B) + diamondNorm C :=
      diamondNorm_sub_le (c • A + B) C
    _ ≤ (diamondNorm (c • A) + diamondNorm B) + diamondNorm C := by
      have h := diamondNorm_add_le (c • A) B
      linarith only [h]
    _ = ‖c‖ * diamondNorm A + diamondNorm B + diamondNorm C := by
      rw [diamondNorm_smul]

/-- The universal channel bound removes the large-budget branch from a numeral estimate. -/
example {n m : ℕ} [NeZero n] [NeZero m]
    {real ideal : Op n →ₗ[ℂ] Op m} (hreal : IsCPTP ⇑real) (hideal : IsCPTP ⇑ideal)
    (ε : ℝ) (hsmall : ε < 1 → (1 / 2) * diamondNorm (real - ideal) ≤ ε) :
    (1 / 2) * diamondNorm (real - ideal) ≤ ε := by
  by_cases hε : ε < 1
  · exact hsmall hε
  · have h := diamondNorm_sub_le_two hreal hideal
    linarith

section Typed

open TypedLOCC

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β] [Nonempty β]

/-- Three successive replacements contribute additively to the diamond distance. -/
example (Φ₀ Φ₁ Φ₂ Φ₃ : TypedLOCC.Op α →ₗ[ℂ] TypedLOCC.Op β) :
    diamondDist Φ₀ Φ₃ ≤ diamondDist Φ₀ Φ₁ + diamondDist Φ₁ Φ₂ + diamondDist Φ₂ Φ₃ := by
  have h₀₂ := diamondDist_triangle Φ₀ Φ₁ Φ₂
  have h₀₃ := diamondDist_triangle Φ₀ Φ₂ Φ₃
  linarith only [h₀₂, h₀₃]

/-- The universal channel bound removes the large-budget branch from a typed estimate. -/
example {real ideal : TypedLOCC.Op α →ₗ[ℂ] TypedLOCC.Op β}
    (hreal : IsChannel real) (hideal : IsChannel ideal)
    (ε : ℝ) (hsmall : ε < 1 → diamondDist real ideal ≤ ε) :
    diamondDist real ideal ≤ ε := by
  by_cases hε : ε < 1
  · exact hsmall hε
  · exact (hreal.diamondDist_le_one hideal).trans (le_of_not_gt hε)

end Typed

end QCryptLeanTest.DiamondNorm
