import QCryptLean.Quantum.Channels.Stinespring.MoorePenrose

/-!
# Rectangular Gram Factorization — equal row Grams and partial isometries

This file contains the rectangular factorization step used by Kraus-form
Stinespring uniqueness.

## Main statements
- `rectangular_partial_isometry_of_grams_eq`: equal row Grams give a rectangular partial-isometry
factor.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Polar/SVD uniqueness for rectangular factorizations** — linear-algebra
core of Stinespring's uniqueness theorem.

If two rectangular matrices `W : Matrix (Fin n) (Fin k) ℂ` and
`W' : Matrix (Fin n) (Fin k') ℂ` share the same row-Gram product
`W * Wᴴ = W' * W'ᴴ`, then there is a partial isometry `V : Matrix (Fin k) (Fin k') ℂ`
(i.e., `V * Vᴴ * V = V`) such that `W' = W * V`.

When `k' > k`, the matrix `V` has more columns than rows, so `rank V ≤ k < k'`,
making the full-isometry condition `Vᴴ * V = 1_{k'}` impossible in general.
Explicit counterexample: `W = [[1]]`, `W' = [[1, 0]]` gives `W * Wᴴ = W' * W'ᴴ = [[1]]`
but no `V : Matrix (Fin 1) (Fin 2) ℂ` satisfies `Vᴴ * V = 1_2`.

The correct conclusion is the geometric definition of partial isometry: `V * Vᴴ * V = V`,
equivalently `Vᴴ * V` is a projection (Hermitian idempotent).

Reference: Bhatia, *Matrix Analysis* (1997), Theorem VII.3.2; Paulsen,
*Completely Bounded Maps and Operator Algebras* (2002), Lemma 4.1. -/
theorem rectangular_partial_isometry_of_grams_eq
    {n k k' : ℕ}
    (W : Matrix (Fin n) (Fin k) ℂ) (W' : Matrix (Fin n) (Fin k') ℂ)
    (hGram : W * Wᴴ = W' * W'ᴴ) :
    ∃ V : Matrix (Fin k) (Fin k') ℂ,
      V * Vᴴ * V = V ∧ W' = W * V := by
  -- Set G := W * Wᴴ.  By hypothesis G = W' * W'ᴴ as well.
  set G : Op n := W * Wᴴ with hG_def
  have hG_psd : G.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
  have hG' : W' * W'ᴴ = G := hGram.symm
  -- Moore-Penrose pseudoinverse Gp of the PSD matrix G.
  obtain ⟨Gp, hMP1, hMP2, hMP3, hGp_herm⟩ := psd_exists_moorePenrose_pinv hG_psd
  have hGp_eq : Gpᴴ = Gp := hGp_herm.eq
  -- Define V := Wᴴ * Gp * W'.
  refine ⟨Wᴴ * Gp * W', ?_, ?_⟩
  · -- Show V * Vᴴ * V = V.
    -- First simplify Vᴴ = W'ᴴ * Gp * W using hGp_eq.
    have hV_dag : (Wᴴ * Gp * W')ᴴ = W'ᴴ * Gp * W := by
      simp [Matrix.conjTranspose_mul, hGp_eq, Matrix.mul_assoc]
    -- Now compute V * Vᴴ * V step by step.
    have step :
        (Wᴴ * Gp * W') * (Wᴴ * Gp * W')ᴴ * (Wᴴ * Gp * W')
          = Wᴴ * Gp * W' := by
      calc (Wᴴ * Gp * W') * (Wᴴ * Gp * W')ᴴ * (Wᴴ * Gp * W')
          = (Wᴴ * Gp * W') * (W'ᴴ * Gp * W) * (Wᴴ * Gp * W') := by rw [hV_dag]
        _ = Wᴴ * Gp * (W' * W'ᴴ) * Gp * (W * Wᴴ) * Gp * W' := by
              simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * G * Gp * G * Gp * W' := by rw [hG', ← hG_def]
        _ = Wᴴ * (Gp * G * Gp) * G * Gp * W' := by simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * G * Gp * W' := by rw [hMP2]
        _ = Wᴴ * (Gp * G * Gp) * W' := by simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * W' := by rw [hMP2]
    exact step
  · -- Show W' = W * V, where V = Wᴴ * Gp * W'.  Equivalently, W' = G * Gp * W'.
    -- Strategy: show (1 - G * Gp) * W' = 0 by computing X * Xᴴ = 0,
    -- where X := (1 - G * Gp) * W'.
    -- Step 1: P := 1 - G * Gp is Hermitian.
    have hP_herm : ((1 : Op n) - G * Gp).IsHermitian := by
      have h1H : (1 : Op n).IsHermitian := Matrix.isHermitian_one
      exact h1H.sub hMP3
    -- Step 2: (1 - G * Gp) * G = 0 from hMP1.
    have hPG : ((1 : Op n) - G * Gp) * G = 0 := by
      rw [sub_mul, one_mul, hMP1, sub_self]
    -- Step 3: ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ = 0.
    have hXXH :
        ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ = 0 := by
      have hPh : ((1 : Op n) - G * Gp)ᴴ = 1 - G * Gp :=
        hP_herm.eq
      calc ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ
          = ((1 - G * Gp) * W') * (W'ᴴ * (1 - G * Gp)ᴴ) := by
                rw [Matrix.conjTranspose_mul]
        _ = ((1 - G * Gp) * W') * (W'ᴴ * (1 - G * Gp)) := by rw [hPh]
        _ = (1 - G * Gp) * (W' * W'ᴴ) * (1 - G * Gp) := by
                simp [Matrix.mul_assoc]
        _ = (1 - G * Gp) * G * (1 - G * Gp) := by rw [hG']
        _ = 0 * (1 - G * Gp) := by rw [hPG]
        _ = 0 := Matrix.zero_mul _
    -- Step 4: (1 - G * Gp) * W' = 0.
    have hPW' : (1 - G * Gp) * W' = 0 :=
      Matrix.self_mul_conjTranspose_eq_zero.mp hXXH
    -- Step 5: Rearrange to W' = G * Gp * W'.
    have hW'eq : W' = G * Gp * W' := by
      have h := hPW'
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
      exact h
    -- Conclude W' = W * V.
    calc W' = G * Gp * W' := hW'eq
      _ = (W * Wᴴ) * Gp * W' := by rw [hG_def]
      _ = W * (Wᴴ * Gp * W') := by
            simp [Matrix.mul_assoc]

end Quantum.Channels

end -- noncomputable section
