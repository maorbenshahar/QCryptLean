import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Quantum.Operators.Types

/-!
# Von Neumann Entropy — core definitions

This file contains the core definitions needed to define von Neumann entropy,
extracted so that `RelativeEntropy/Basic.lean` can import them without creating
a circular dependency through `VonNeumannEntropy/Basic.lean`.

## Main definitions
- `IsEigenvalueSpectrum`: Predicate for valid eigenvalue spectra of a density operator
- `eigenvaluesOf`: Canonical eigenvalues of a density operator
- `eigenvaluesOf_spec`: The extracted eigenvalues satisfy the predicate
- `vonNeumannEntropy`: S(ρ) = shannonEntropy(eigenvaluesOf ρ)
- `density_has_spectrum`: Every density operator has an eigenvalue spectrum
-/

open Math.ClassicalEntropy

noncomputable section

namespace InfoTheory.VonNeumannEntropy

open Quantum.Operators

/-!
## Eigenvalue Spectrum
-/

/-- Predicate that a function `Fin n → ℝ` gives the eigenvalues of a density operator.
    Requires: (1) non-negativity, (2) sum = 1, (3) each value ≤ 1 (derivable from 1 and 2,
    included for convenience), and (4) a unitary spectral decomposition. -/
def IsEigenvalueSpectrum {n : ℕ} (ρ : DensityOp n) (eigenvalues : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ eigenvalues i) ∧
  (∑ i, eigenvalues i = 1) ∧
  (∀ i, eigenvalues i ≤ 1) ∧
  -- ρ is diagonalized with these eigenvalues (spectral decomposition).
  -- Convention note: the stored `U` plays the role of U† in standard notation,
  -- i.e. ρ = U† · diag · U here, whereas many textbooks write ρ = U · diag · U†.
  ∃ (U : Op n), U† * U = 1 ∧ U * U† = 1 ∧
    ρ.toOp = U† * (Matrix.diagonal (fun i => (eigenvalues i : ℂ))) * U


/-- Extract eigenvalues from a density operator.
    Defined directly as Mathlib's `IsHermitian.eigenvalues` so that the bridge to
    spectral-theory lemmas (`weyl_eigenvalue_sum_bound`, etc.) is definitional. -/
def eigenvaluesOf {n : ℕ} (ρ : DensityOp n) : Fin n → ℝ :=
  ρ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues


/-- The extracted eigenvalues satisfy the IsEigenvalueSpectrum predicate. -/
theorem eigenvaluesOf_spec {n : ℕ} (ρ : DensityOp n) :
    IsEigenvalueSpectrum ρ (eigenvaluesOf ρ) := by
  have hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  have hPSD := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- Shared sub-proof: eigenvalues sum to 1 (used by both the sum=1 and ≤1 goals)
  have h_sum_one : ∑ i, hH.eigenvalues i = 1 := by
    have h_trace := ρ.trace_one
    have h_sum_eq := hH.trace_eq_sum_eigenvalues
    have h_eq : (1 : ℂ) = ∑ i, (hH.eigenvalues i : ℂ) := by
      calc (1 : ℂ) = ρ.toOp.trace := h_trace.symm
        _ = ∑ i, (hH.eigenvalues i : ℂ) := h_sum_eq
    have h_re_rhs : (∑ i, (hH.eigenvalues i : ℂ)).re = ∑ i, hH.eigenvalues i := by
      simp only [Complex.re_sum, Complex.ofReal_re]
    calc ∑ i, hH.eigenvalues i = (∑ i, (hH.eigenvalues i : ℂ)).re := h_re_rhs.symm
      _ = (1 : ℂ).re := by rw [← h_eq]
      _ = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; exact hPSD.eigenvalues_nonneg i
  · exact h_sum_one
  · -- eigenvalues ≤ 1 using single_le_sum
    intro i
    have h_nonneg : ∀ j, 0 ≤ hH.eigenvalues j := fun j => hPSD.eigenvalues_nonneg j
    calc hH.eigenvalues i ≤ ∑ j, hH.eigenvalues j :=
            Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
      _ = 1 := h_sum_one
  · -- Spectral decomposition
    let U := (hH.eigenvectorUnitary.val : Op n)
    let V := star U  -- V = U†
    use V
    have h_star_mul : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have h_mul_star : U * star U = 1 := by
      have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
      simp only [Unitary.coe_star] at h
      exact h
    constructor
    · calc star V * V = star (star U) * star U := rfl
        _ = U * star U := by rw [star_star]
        _ = 1 := h_mul_star
    constructor
    · calc V * star V = star U * star (star U) := rfl
        _ = star U * U := by rw [star_star]
        _ = 1 := h_star_mul
    · have h_spec := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h_spec
      calc ρ.toOp = U * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star U := h_spec
        _ = star (star U) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star U := by
            rw [star_star]
        _ = star V * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * V := rfl

/-- Every density operator has an eigenvalue spectrum (spectral theorem). -/
theorem density_has_spectrum {n : ℕ} (ρ : DensityOp n) :
    ∃ eigenvalues : Fin n → ℝ, IsEigenvalueSpectrum ρ eigenvalues :=
  ⟨eigenvaluesOf ρ, eigenvaluesOf_spec ρ⟩

/-!
## Von Neumann Entropy
-/

/-- Von Neumann entropy of a density operator: S(ρ) = H(λ) where λ are the
    eigenvalues of ρ (via `eigenvaluesOf`). Uses natural logarithm (nats). -/
def vonNeumannEntropy {n : ℕ} [NeZero n] (ρ : DensityOp n) : ℝ :=
  shannonEntropy (eigenvaluesOf ρ)

end InfoTheory.VonNeumannEntropy

end
