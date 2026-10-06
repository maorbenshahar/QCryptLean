import QCryptLean.Quantum.Channels.Stinespring.PartialTrace

/-!
# PSD Moore-Penrose Inverse — spectral construction for finite matrices

This file contains the low-level Moore-Penrose pseudoinverse existence theorem
for positive-semidefinite complex matrices.

## Main statements
- `psd_exists_moorePenrose_pinv`: PSD matrices admit a Hermitian Moore-Penrose pseudoinverse.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Moore-Penrose pseudoinverse for positive-semidefinite matrices.**

For a positive-semidefinite matrix `G : Op n`, there exists a
matrix `Gp` — the Moore-Penrose pseudoinverse — satisfying the four
Moore-Penrose identities specialized to the Hermitian (PSD) case:

* `G * Gp * G = G`            (first Moore-Penrose identity),
* `Gp * G * Gp = Gp`          (second Moore-Penrose identity),
* `(G * Gp).IsHermitian`      (third Moore-Penrose identity); since `G` itself
  is Hermitian, the fourth identity `(Gp * G).IsHermitian` is equivalent,
* `Gp.IsHermitian`            (the pseudoinverse of a Hermitian matrix is
  itself Hermitian).

Standard construction (via spectral decomposition): write
`G = U * D * Uᴴ` with `D` real-diagonal (Mathlib:
`Matrix.IsHermitian.spectral_theorem`); define `Dp` as the diagonal matrix
inverting the nonzero diagonal entries of `D` (and `0` on the kernel); then
`Gp := U * Dp * Uᴴ` satisfies all of the above.

References: Bhatia, *Matrix Analysis* (1997), §III; Horn-Johnson,
*Matrix Analysis* (2013), §7.3. -/
theorem psd_exists_moorePenrose_pinv
    {n : ℕ} {G : Op n} (hG : G.PosSemidef) :
    ∃ Gp : Op n,
      G * Gp * G = G ∧
      Gp * G * Gp = Gp ∧
      (G * Gp).IsHermitian ∧
      Gp.IsHermitian := by
  have hM : G.IsHermitian := hG.isHermitian
  have hSpec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpec
  set U : Op n :=
    (hM.eigenvectorUnitary : Op n) with hU_def
  set lam : Fin n → ℝ := hM.eigenvalues with hlam_def
  set D : Op n :=
    Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ lam) with hD_def
  set Dp : Op n :=
    Matrix.diagonal (fun i => if lam i = 0 then (0 : ℂ) else ((lam i : ℂ))⁻¹) with hDp_def
  have hstarU : (star U : Op n) = Uᴴ := rfl
  have hGeq : G = U * D * Uᴴ := by
    have h := hSpec
    exact h
  have hUstarU : Uᴴ * U = 1 := by
    have h := Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    simpa [hU_def, Matrix.star_eq_conjTranspose] using h
  -- Algebraic identities on the diagonal matrices.
  have hDDpD : D * Dp * D = D := by
    rw [hDp_def, hD_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      -- simp uses the global `mul_inv_cancel` simp lemma together with `hne`.
      simp [h, Function.comp, hne]
  have hDpDDp : Dp * D * Dp = Dp := by
    rw [hDp_def, hD_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp [h, Function.comp, hne]
  -- D * Dp is the 0/1 projector diagonal (Hermitian).
  have hDDp_herm : (D * Dp).IsHermitian := by
    rw [hD_def, hDp_def, Matrix.diagonal_mul_diagonal]
    change _ᴴ = _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp [h, hne]
  -- Dp is Hermitian (real diagonal).
  have hDp_herm : Dp.IsHermitian := by
    rw [hDp_def]
    change _ᴴ = _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp only [h, if_false, Pi.star_apply, RCLike.star_def, map_inv₀]
      rw [Complex.conj_ofReal]
  -- Hermiticity of `U * A * Uᴴ` when A is Hermitian.
  have hConjHerm : ∀ A : Op n, A.IsHermitian →
      (U * A * Uᴴ).IsHermitian := by
    intro A hA
    change _ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  refine ⟨U * Dp * Uᴴ, ?_, ?_, ?_, ?_⟩
  · -- G * Gp * G = G
    conv_lhs => rw [hGeq]
    calc (U * D * Uᴴ) * (U * Dp * Uᴴ) * (U * D * Uᴴ)
        = U * D * (Uᴴ * U) * Dp * (Uᴴ * U) * D * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * D * 1 * Dp * 1 * D * Uᴴ := by rw [hUstarU]
      _ = U * (D * Dp * D) * Uᴴ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * D * Uᴴ := by rw [hDDpD]
      _ = G := hGeq.symm
  · -- Gp * G * Gp = Gp
    conv_lhs => rw [hGeq]
    calc (U * Dp * Uᴴ) * (U * D * Uᴴ) * (U * Dp * Uᴴ)
        = U * Dp * (Uᴴ * U) * D * (Uᴴ * U) * Dp * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * Dp * 1 * D * 1 * Dp * Uᴴ := by rw [hUstarU]
      _ = U * (Dp * D * Dp) * Uᴴ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * Dp * Uᴴ := by rw [hDpDDp]
  · -- (G * Gp).IsHermitian
    have heq : G * (U * Dp * Uᴴ) = U * (D * Dp) * Uᴴ := by
      conv_lhs => rw [hGeq]
      calc (U * D * Uᴴ) * (U * Dp * Uᴴ)
          = U * D * (Uᴴ * U) * Dp * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * D * 1 * Dp * Uᴴ := by rw [hUstarU]
        _ = U * (D * Dp) * Uᴴ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [heq]
    exact hConjHerm _ hDDp_herm
  · -- Gp.IsHermitian
    exact hConjHerm _ hDp_herm

end Quantum.Channels

end -- noncomputable section
