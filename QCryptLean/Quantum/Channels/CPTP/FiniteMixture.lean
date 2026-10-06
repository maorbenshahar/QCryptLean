import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Finite Mixtures of CPTP Maps — uniform averages, Choi matrices, CPTP closure

This module packages finite uniform averages of linear quantum maps, including
Choi-matrix, complete-positivity, trace-preservation, and CPTP closure lemmas.

## Main statements
- `isCompletelyPositive_zero_map`: the zero operator map is completely positive.
- `choiMatrix_smul_sum`: Choi matrices commute with scalar multiples of finite sums.
- `isCompletelyPositive_smul_sum`: nonnegative finite sums of CP maps are CP.
- `isCompletelyPositive_uniformAverage`: a uniform average of CP maps is CP.
- `isTracePreserving_uniformAverage`: a uniform average of trace-preserving maps is
  trace-preserving.
- `cptp_uniformAverage`: a uniform average of CPTP maps is CPTP.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The zero operator map is completely positive. -/
lemma isCompletelyPositive_zero_map {n m : ℕ} [NeZero n] [NeZero m] :
    IsCompletelyPositive (0 : Op n → Op m) := by
  simpa [IsCompletelyPositive, ChoiMatrix] using
    (Matrix.PosSemidef.zero :
      (0 : Op (n * m)).PosSemidef)

/-- The Choi matrix is linear on scalar multiples of finite sums of linear maps. -/
lemma choiMatrix_smul_sum {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] (c : ℂ) (Φ : κ → Op n →ₗ[ℂ] Op m) :
    ChoiMatrix n m (⇑(c • ∑ i, Φ i)) =
      c • ∑ i, ChoiMatrix n m (⇑(Φ i)) := by
  ext α β
  simp only [ChoiMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]

/-- The Choi matrix is linear on scalar multiples of a linear map. -/
lemma choiMatrix_smul {n m : ℕ} [NeZero n] [NeZero m]
    (c : ℂ) (Φ : Op n →ₗ[ℂ] Op m) :
    ChoiMatrix n m (⇑(c • Φ)) =
      c • ChoiMatrix n m (⇑Φ) := by
  ext α β
  simp only [ChoiMatrix, Matrix.of_apply, Matrix.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]

/-- A nonnegative scalar multiple of a completely positive linear map is
completely positive. -/
lemma isCompletelyPositive_smul {n m : ℕ} [NeZero n] [NeZero m]
    (c : ℂ) (Φ : Op n →ₗ[ℂ] Op m)
    (hc : 0 ≤ c) (hΦ : IsCompletelyPositive (⇑Φ)) :
    IsCompletelyPositive (⇑(c • Φ)) := by
  unfold IsCompletelyPositive at *
  rw [choiMatrix_smul c Φ]
  exact Matrix.PosSemidef.smul hΦ hc

/-- A nonnegative scalar multiple of a finite sum of completely positive maps is
completely positive. -/
lemma isCompletelyPositive_smul_sum {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] (c : ℂ) (Φ : κ → Op n →ₗ[ℂ] Op m)
    (hc : 0 ≤ c) (hΦ : ∀ i, IsCompletelyPositive (⇑(Φ i))) :
    IsCompletelyPositive (⇑(c • ∑ i, Φ i)) := by
  unfold IsCompletelyPositive
  rw [choiMatrix_smul_sum c Φ]
  apply Matrix.PosSemidef.smul
  · apply Matrix.posSemidef_sum
    intro i _
    exact hΦ i
  · exact hc

/-- A finite uniform average of completely positive linear maps is completely
positive. -/
lemma isCompletelyPositive_uniformAverage {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] (Φ : κ → Op n →ₗ[ℂ] Op m)
    (hΦ : ∀ i, IsCompletelyPositive (⇑(Φ i))) :
    IsCompletelyPositive (⇑((((Fintype.card κ : ℝ)⁻¹ : ℂ)) • ∑ i, Φ i)) := by
  exact isCompletelyPositive_smul_sum _ Φ (by
    rw [Complex.le_def]
    constructor
    · have hnonneg : (0 : ℝ) ≤ (Fintype.card κ : ℝ)⁻¹ := by
        exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (Fintype.card κ))
      simp [hnonneg]
    · simp) hΦ

/-- A finite uniform average of trace-preserving linear maps is trace preserving. -/
lemma isTracePreserving_uniformAverage {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (Φ : κ → Op n →ₗ[ℂ] Op m)
    (hΦ : ∀ i, IsTracePreserving (⇑(Φ i))) :
    IsTracePreserving (⇑((((Fintype.card κ : ℝ)⁻¹ : ℂ)) • ∑ i, Φ i)) := by
  intro A
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul]
  simp_rw [fun i => hΦ i A]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_ne : (Fintype.card κ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcoeff : (((Fintype.card κ : ℝ)⁻¹ : ℂ) * (Fintype.card κ : ℂ)) = 1 := by
    exact inv_mul_cancel₀ hcard_ne
  rw [← mul_assoc, hcoeff, one_mul]

/-- A finite uniform average of CPTP linear maps is CPTP. -/
theorem cptp_uniformAverage {n m : ℕ} [NeZero n] [NeZero m]
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (Φ : κ → Op n →ₗ[ℂ] Op m)
    (hΦ : ∀ i, IsCPTP (⇑(Φ i))) :
    IsCPTP (⇑((((Fintype.card κ : ℝ)⁻¹ : ℂ)) • ∑ i, Φ i)) := by
  refine ⟨((((Fintype.card κ : ℝ)⁻¹ : ℂ)) • ∑ i, Φ i).isLinear, ?_, ?_⟩
  · exact isCompletelyPositive_uniformAverage Φ fun i => (hΦ i).2.1
  · exact isTracePreserving_uniformAverage Φ fun i => (hΦ i).2.2

end Quantum.Channels

end
