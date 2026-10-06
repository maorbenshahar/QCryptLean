import QCryptLean.Quantum.Metrics.TraceNorm.Jordan
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.SpectralTheory.Weyl

/-!
# Trace Distance Metric Properties — boundedness, symmetry, triangle inequality, separability

Basic metric-space properties of trace distance on density operators: D(ρ,σ) ≤ 1,
symmetry, triangle inequality, and D(ρ,σ) = 0 ↔ ρ = σ.

## Main statements
- `traceDistance_le_one`: D(ρ,σ) ≤ 1
- `traceDistance_symm`: D(ρ,σ) = D(σ,ρ)
- `traceDistance_triangle`: D(ρ,τ) ≤ D(ρ,σ) + D(σ,τ)
- `traceDistance_eq_zero_iff`: D(ρ,σ) = 0 ↔ ρ = σ
-/

open Quantum.Operators Quantum.TensorProducts Matrix InfoTheory.VonNeumannEntropy Quantum.Metrics
open Math.SpectralTheory
open scoped ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Advanced Trace Distance Theorems

Eigenvalue bounds, distance properties, and spectral helpers.
Core trace-distance definitions are in the Quantum.Metrics.TraceNorm.Basic module;
fidelity and pure-state formulas are in the Quantum.Metrics.TraceNorm.Fidelity module.
-/

/-- Sum of positive eigenvalues of ρ - σ is at most 1.

    Key insight: For eigenvalue λᵢ with eigenvector vᵢ:
      λᵢ = ⟨vᵢ|(ρ-σ)|vᵢ⟩ = ⟨vᵢ|ρ|vᵢ⟩ - ⟨vᵢ|σ|vᵢ⟩
    Sum of positive eigenvalues:
      Σ_{λᵢ>0} λᵢ ≤ Σ_{λᵢ>0} ⟨vᵢ|ρ|vᵢ⟩  (dropping non-negative σ terms)
                 ≤ Σᵢ ⟨vᵢ|ρ|vᵢ⟩         (adding non-negative ρ terms)
                 = Tr(ρ) = 1 -/
lemma sum_positive_eigenvalues_le_one {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_herm : (ρ.toOp - σ.toOp).IsHermitian) :
    ∑ i, max 0 (h_herm.eigenvalues i) ≤ 1 := by
  let v := fun i => (h_herm.eigenvectorUnitary.val · i : Fin n → ℂ)
  -- Step 1: Eigenvalue λᵢ = ⟨vᵢ|(ρ-σ)|vᵢ⟩
  have h_ev_eq_qf : ∀ i, h_herm.eigenvalues i =
      (star (v i) ⬝ᵥ ((ρ.toOp - σ.toOp).mulVec (v i))).re := by
    intro i; exact (eigenvector_quadraticForm_eq_eigenvalue h_herm i).symm
  -- Step 2: Quadratic form splits as ⟨v|ρ|v⟩ - ⟨v|σ|v⟩
  have h_qf_split : ∀ i, (star (v i) ⬝ᵥ ((ρ.toOp - σ.toOp).mulVec (v i))).re =
      (star (v i) ⬝ᵥ (ρ.toOp.mulVec (v i))).re -
      (star (v i) ⬝ᵥ (σ.toOp.mulVec (v i))).re := by
    intro i; simp only [sub_mulVec, dotProduct_sub, Complex.sub_re]
  -- Define qρᵢ = ⟨vᵢ|ρ|vᵢ⟩ and qσᵢ = ⟨vᵢ|σ|vᵢ⟩
  let qρ := fun i => (star (v i) ⬝ᵥ (ρ.toOp.mulVec (v i))).re
  let qσ := fun i => (star (v i) ⬝ᵥ (σ.toOp.mulVec (v i))).re
  -- Step 3: qρ, qσ are non-negative (ρ, σ are PSD)
  have hqρ_nonneg : ∀ i, 0 ≤ qρ i := fun i => density_quadraticForm_nonneg ρ (v i)
  have hqσ_nonneg : ∀ i, 0 ≤ qσ i := fun i => density_quadraticForm_nonneg σ (v i)
  -- Step 4: λᵢ = qρᵢ - qσᵢ
  have h_ev_diff : ∀ i, h_herm.eigenvalues i = qρ i - qσ i := by
    intro i; rw [h_ev_eq_qf i, h_qf_split i]
  -- Step 5: max(0, λᵢ) ≤ qρᵢ (since qσᵢ ≥ 0)
  have h_max_le : ∀ i, max 0 (h_herm.eigenvalues i) ≤ qρ i := by
    intro i
    rw [h_ev_diff i]
    calc max 0 (qρ i - qσ i)
        ≤ max 0 (qρ i) := max_le_max_left 0 (by linarith [hqσ_nonneg i])
      _ = qρ i := max_eq_right (hqρ_nonneg i)
  -- Step 6: Sum ≤ Σᵢ qρᵢ = Tr(ρ) = 1
  calc ∑ i, max 0 (h_herm.eigenvalues i)
      ≤ ∑ i, qρ i := Finset.sum_le_sum (fun i _ => h_max_le i)
    _ = ∑ i, (star (v i) ⬝ᵥ (ρ.toOp.mulVec (v i))).re := rfl
    _ = ρ.toOp.trace.re := sum_eigenbasis_quadraticForm_eq_trace ρ h_herm
    _ = (1 : ℂ).re := by rw [ρ.trace_one]
    _ = 1 := Complex.one_re

/-- Trace distance is at most 1. -/
theorem traceDistance_le_one {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    traceDistance ρ.toOp σ.toOp ≤ 1 := by
  rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
  have h_herm := densityOp_sub_isHermitian ρ σ
  -- The trace of (ρ - σ) is 0
  have h_tr : (ρ.toOp - σ.toOp).trace = 0 := by
    simp only [Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self]
  -- For density operators, D(ρ,σ) = (1/2) * Σᵢ|λᵢ| where λᵢ are eigenvalues of ρ-σ
  -- Since Tr(ρ-σ) = 0, the positive and negative eigenvalues balance
  -- The max eigenvalue of ρ-σ is at most 1, min is at least -1
  -- So Σᵢ|λᵢ| ≤ 2, giving D(ρ,σ) ≤ 1
  have h_sum_le : traceNormHermitian (ρ.toOp - σ.toOp) h_herm ≤ 2 := by
    unfold traceNormHermitian
    -- From trace = 0: positive and negative eigenvalue sums are equal
    have h_sum_zero : ∑ i, h_herm.eigenvalues i = 0 := by
      have h := h_herm.trace_eq_sum_eigenvalues
      rw [h_tr] at h
      have h' : (∑ j, (h_herm.eigenvalues j : ℂ)) = 0 := h.symm
      simp only [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h'
      exact h'
    -- Split |λᵢ| = max(0, λᵢ) + max(0, -λᵢ)
    have h_abs_split : ∀ i, |h_herm.eigenvalues i| =
        max 0 (h_herm.eigenvalues i) + max 0 (-h_herm.eigenvalues i) := by
      intro i
      by_cases hx : 0 ≤ h_herm.eigenvalues i
      · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
      · push Not at hx
        rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add,
            max_eq_right (neg_pos.mpr hx).le]
    -- pos_sum = neg_sum since trace = 0
    let pos_sum := ∑ i, max 0 (h_herm.eigenvalues i)
    let neg_sum := ∑ i, max 0 (-h_herm.eigenvalues i)
    have h_pos_neg_eq : pos_sum = neg_sum := by
      have h1 : (∑ i, h_herm.eigenvalues i : ℝ) =
          ∑ i, (max 0 (h_herm.eigenvalues i) - max 0 (-h_herm.eigenvalues i)) := by
        congr 1; ext i
        by_cases hx : 0 ≤ h_herm.eigenvalues i
        · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), sub_zero]
        · push Not at hx
          rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le, zero_sub, neg_neg]
      rw [h_sum_zero, Finset.sum_sub_distrib] at h1
      linarith
    -- Σ|λᵢ| = pos_sum + neg_sum = 2 * pos_sum ≤ 2
    have h_sum_abs : ∑ i, |h_herm.eigenvalues i| = pos_sum + neg_sum := by
      conv_lhs => rw [show ∑ i, |h_herm.eigenvalues i| =
          ∑ i, (max 0 (h_herm.eigenvalues i) + max 0 (-h_herm.eigenvalues i)) from
          Finset.sum_congr rfl (fun i _ => h_abs_split i)]
      rw [Finset.sum_add_distrib]
    rw [h_sum_abs, h_pos_neg_eq, ← two_mul]
    have h_pos_sum_le : pos_sum ≤ 1 := sum_positive_eigenvalues_le_one ρ σ h_herm
    linarith
  calc (1 : ℝ) / 2 * traceNormHermitian (ρ.toOp - σ.toOp) h_herm
      ≤ 1 / 2 * 2 := by
          apply mul_le_mul_of_nonneg_left h_sum_le
          norm_num
    _ = 1 := by norm_num

/-- Trace distance is symmetric. -/
theorem traceDistance_symm {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    traceDistance ρ.toOp σ.toOp = traceDistance σ.toOp ρ.toOp := by
  rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ,
      traceDistance_densityOp_eq_traceNormHermitian σ ρ]
  congr 1
  have herm1 := densityOp_sub_isHermitian ρ σ
  have herm2 := densityOp_sub_isHermitian σ ρ
  -- Key: ρ - σ = -(σ - ρ)
  have h_neg_mat : ρ.toOp - σ.toOp = -(σ.toOp - ρ.toOp) := by
    ext i j; simp only [Matrix.neg_apply, Matrix.sub_apply]; ring
  have h_neg_herm : (-(σ.toOp - ρ.toOp)).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_neg, herm2]
  -- Goal: traceNormHermitian (ρ.toOp - σ.toOp) _ = traceNormHermitian (σ.toOp - ρ.toOp) _
  calc traceNormHermitian (ρ.toOp - σ.toOp) herm1
      = traceNormHermitian (ρ.toOp - σ.toOp) (h_neg_mat ▸ h_neg_herm) :=
          traceNormHermitian_proof_irrel _ _ _
      _ = traceNormHermitian (-(σ.toOp - ρ.toOp)) h_neg_herm := by
          simp only [← h_neg_mat]
      _ = traceNormHermitian (σ.toOp - ρ.toOp) herm2 :=
          traceNormHermitian_neg _ herm2

/-- Trace distance satisfies triangle inequality. -/
theorem traceDistance_triangle {n : ℕ} [NeZero n] (ρ σ τ : DensityOp n) :
    traceDistance ρ.toOp τ.toOp ≤ traceDistance ρ.toOp σ.toOp + traceDistance σ.toOp τ.toOp := by
  rw [traceDistance_densityOp_eq_traceNormHermitian ρ τ,
      traceDistance_densityOp_eq_traceNormHermitian ρ σ,
      traceDistance_densityOp_eq_traceNormHermitian σ τ]
  have herm_ρτ := densityOp_sub_isHermitian ρ τ
  have herm_ρσ := densityOp_sub_isHermitian ρ σ
  have herm_στ := densityOp_sub_isHermitian σ τ
  -- (ρ - τ) = (ρ - σ) + (σ - τ)
  have h_split : ρ.toOp - τ.toOp = (ρ.toOp - σ.toOp) + (σ.toOp - τ.toOp) := by
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply]; ring
  have herm_sum : ((ρ.toOp - σ.toOp) + (σ.toOp - τ.toOp)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, herm_ρσ, herm_στ]
  calc (1 : ℝ) / 2 * traceNormHermitian (ρ.toOp - τ.toOp) herm_ρτ
      = 1 / 2 * traceNormHermitian ((ρ.toOp - σ.toOp) + (σ.toOp - τ.toOp)) (h_split ▸ herm_ρτ) := by
          simp only [h_split]
      _ = 1 / 2 * traceNormHermitian ((ρ.toOp - σ.toOp) + (σ.toOp - τ.toOp)) herm_sum := by
          congr 2
      _ ≤ 1 / 2 * (traceNormHermitian (ρ.toOp - σ.toOp) herm_ρσ +
                   traceNormHermitian (σ.toOp - τ.toOp) herm_στ) := by
          apply mul_le_mul_of_nonneg_left
          · exact traceNormHermitian_triangle _ _ herm_ρσ herm_στ
          · norm_num
      _ = 1 / 2 * traceNormHermitian (ρ.toOp - σ.toOp) herm_ρσ +
          1 / 2 * traceNormHermitian (σ.toOp - τ.toOp) herm_στ := by ring

/-- Trace distance is zero iff states are equal. -/
theorem traceDistance_eq_zero_iff {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    traceDistance ρ.toOp σ.toOp = 0 ↔ ρ = σ := by
  rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
  constructor
  · intro h
    -- (1/2) * traceNormHermitian = 0 implies traceNormHermitian = 0
    have h_herm := densityOp_sub_isHermitian ρ σ
    have h_traceNormHermitian_zero : traceNormHermitian (ρ.toOp - σ.toOp) h_herm = 0 := by
      have h1 : (1 : ℝ) / 2 * traceNormHermitian (ρ.toOp - σ.toOp) h_herm = 0 := h
      have h_sum_nonneg : 0 ≤ ∑ i : Fin n, |h_herm.eigenvalues i| := by
        apply Finset.sum_nonneg
        intro i _
        exact abs_nonneg _
      unfold traceNormHermitian at h1
      nlinarith
    -- traceNormHermitian = 0 implies ρ - σ = 0
    have h_sub_zero := (traceNormHermitian_eq_zero_iff (ρ.toOp - σ.toOp) _).mp
        h_traceNormHermitian_zero
    -- ρ - σ = 0 implies ρ = σ
    apply DensityOp.ext
    ext i j
    have := congrFun₂ h_sub_zero i j
    simp only [Matrix.sub_apply, Matrix.zero_apply] at this
    exact sub_eq_zero.mp this
  · intro h
    subst h
    -- ρ = ρ means ρ - ρ = 0, so trace distance = 0
    have h_herm := densityOp_sub_isHermitian ρ ρ
    -- Zero matrix eigenvalues are 0 (spectral theorem)
    have h_zero_eig : ∀ i, h_herm.eigenvalues i = 0 := by
      intro i
      have h_is_zero : ρ.toOp - ρ.toOp = 0 := sub_self _
      have h_eig_eq_zero : h_herm.eigenvalues = 0 :=
        (Matrix.IsHermitian.eigenvalues_eq_zero_iff h_herm).mpr h_is_zero
      exact congrFun h_eig_eq_zero i
    unfold traceNormHermitian
    simp only [h_zero_eig, abs_zero, Finset.sum_const_zero, mul_zero]

end Quantum.Metrics

end
