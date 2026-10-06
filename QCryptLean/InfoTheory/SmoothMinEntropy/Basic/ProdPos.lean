import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Metrics.FidelityOrder
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Renner thesis Lemma `lem:prodpos`

For `ρ, σ` nonnegative with `σ` invertible and `λ · σ - ρ` nonnegative,
`ρ^{1/2} σ⁻¹ ρ^{1/2} ≤ λ · I` in PSD order. The proof conjugates the
hypothesis `λσ - ρ ≥ 0` by `σ^{-1/2}`, swaps `T * Tᴴ` and `Tᴴ * T` (which
share spectra for square `T`), and concludes.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder

namespace InfoTheory.SmoothMinEntropy

/-- Conjugation by an arbitrary operator preserves positive semidefiniteness:
`Aᴴ * M * A` is PSD whenever `M` is PSD. -/
lemma nnprod_conj
    {n : ℕ} (M A : Op n) (hM : M.PosSemidef) :
    (Aᴴ * M * A).PosSemidef :=
  hM.conjTranspose_mul_mul_same A

/-- For a square operator `T`, if `lam • 1 - T * Tᴴ` is positive semidefinite
then so is `lam • 1 - Tᴴ * T`, since `T * Tᴴ` and `Tᴴ * T` share spectra. -/
lemma psd_lam_sub_swap {n : ℕ} (T : Op n) (lam : ℂ)
    (h : ((lam : ℂ) • (1 : Op n) - T * Tᴴ).PosSemidef) :
    ((lam : ℂ) • (1 : Op n) - Tᴴ * T).PosSemidef := by
  have hCpEq : (T * Tᴴ).charpoly = (Tᴴ * T).charpoly :=
    Matrix.charpoly_mul_comm T Tᴴ
  have hSpEq : spectrum ℂ (T * Tᴴ) = spectrum ℂ (Tᴴ * T) := by
    ext r; simp [Matrix.mem_spectrum_iff_isRoot_charpoly, hCpEq]
  rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg] at h
  refine Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mpr ⟨?_, ?_⟩
  · -- Hermitianness of `lam • 1 - Tᴴ * T`.
    have hHerm := h.1
    have hTTH : (T * Tᴴ).IsHermitian :=
      (Matrix.posSemidef_self_mul_conjTranspose T).isHermitian
    have hLam1 : (lam • (1 : Op n)).IsHermitian := by
      have eq : lam • (1 : Op n) = (lam • (1 : Op n) - T * Tᴴ) + T * Tᴴ := by abel
      rw [eq]
      exact hHerm.add hTTH
    have hTHT : (Tᴴ * T).IsHermitian :=
      (Matrix.posSemidef_conjTranspose_mul_self T).isHermitian
    exact hLam1.sub hTHT
  · -- Spectrum of `lam • 1 - Tᴴ * T` lies in `[0, ∞)`.
    have hShifted :
        spectrum ℂ (lam • (1 : Op n) - T * Tᴴ) =
          spectrum ℂ (lam • (1 : Op n) - Tᴴ * T) := by
      have eq1 : (lam • (1 : Op n) : Op n) = (algebraMap ℂ (Op n)) lam := by
        rw [Algebra.algebraMap_eq_smul_one]
      rw [eq1, ← spectrum.singleton_sub_eq, ← spectrum.singleton_sub_eq, hSpEq]
    rw [← hShifted]
    exact h.2

/-- **Renner `lem:prodpos`** (PSD-inequality form). For `ρ : PosSemidefOp n`
and `σ : Op n` PosDef (so invertible), if `λ · σ - ρ.toOp` is PSD with `λ ≥ 0`,
then `ρ^{1/2} · σ⁻¹ · ρ^{1/2} ≤ λ · I` in PSD order. -/
theorem prodpos
    {n : ℕ} (ρ : PosSemidefOp n) (σ : Op n) (lam : ℝ)
    (hσ : σ.PosDef) (_hlam : 0 ≤ lam)
    (hdom : ((lam : ℂ) • σ - ρ.toOp).PosSemidef) :
    (((lam : ℂ) • (1 : Op n)) -
        sqrtPosSemidefOp ρ * σ⁻¹ * sqrtPosSemidefOp ρ).PosSemidef := by
  -- Wrap σ as a `PosSemidefOp n` so we can use `sqrtPosSemidefOp`.
  let σPSD : PosSemidefOp n :=
    { toOp := σ
      isHermitian := hσ.isHermitian
      pos_semidef := fun x => posSemidef_re_quadraticForm_nonneg hσ.posSemidef x }
  set SqS : Op n := sqrtPosSemidefOp σPSD with hSqS_def
  set S : Op n := sqrtPosSemidefOp ρ with hS_def
  -- Algebraic facts about Σ
  have hSqS_sq : SqS * SqS = σ := sqrtPosSemidefOp_sq σPSD
  have hSqS_herm : SqS.IsHermitian := sqrtPosSemidefOp_isHermitian σPSD
  -- Σ is invertible (since σ = Σ * Σ is PosDef hence invertible).
  have hσ_unit : IsUnit σ := hσ.isUnit
  have hSqS_unit : IsUnit SqS := by
    have hSqUnit : IsUnit (SqS * SqS) := by rw [hSqS_sq]; exact hσ_unit
    have hdetSq : IsUnit (SqS * SqS).det := (Matrix.isUnit_iff_isUnit_det _).mp hSqUnit
    rw [Matrix.det_mul] at hdetSq
    have hSqSdet_ne : SqS.det ≠ 0 := by
      intro hzero
      apply hdetSq.ne_zero
      simp [hzero]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hSqSdet_ne)
  have hSqSinvL : SqS⁻¹ * SqS = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hSqS_unit)
  have hSqSinvR : SqS * SqS⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hSqS_unit)
  have hSqSinv_herm : SqS⁻¹.IsHermitian := by
    -- (Σ⁻¹)ᴴ = (Σᴴ)⁻¹ = Σ⁻¹
    change SqS⁻¹ᴴ = SqS⁻¹
    rw [Matrix.conjTranspose_nonsing_inv, hSqS_herm.eq]
  -- σ⁻¹ = Σ⁻¹ * Σ⁻¹
  have hσinv_eq : σ⁻¹ = SqS⁻¹ * SqS⁻¹ := by
    rw [← hSqS_sq, Matrix.mul_inv_rev]
  -- Σ⁻¹ * σ * Σ⁻¹ = 1
  have hkey : SqS⁻¹ * σ * SqS⁻¹ = 1 := by
    rw [← hSqS_sq]
    -- Σ⁻¹ * (Σ * Σ) * Σ⁻¹ = (Σ⁻¹ * Σ) * (Σ * Σ⁻¹) = 1 * 1 = 1
    rw [show SqS⁻¹ * (SqS * SqS) * SqS⁻¹ = (SqS⁻¹ * SqS) * (SqS * SqS⁻¹) by
      simp [Matrix.mul_assoc]]
    rw [hSqSinvL, hSqSinvR, Matrix.mul_one]
  -- S facts.
  have hS_sq : S * S = ρ.toOp := sqrtPosSemidefOp_sq ρ
  have hS_herm : S.IsHermitian := sqrtPosSemidefOp_isHermitian ρ
  -- Step 1: Conjugate `lam • σ - ρ` by `Σ⁻¹` to get `lam • 1 - Σ⁻¹ * ρ * Σ⁻¹` PSD.
  have hStep1 : ((lam : ℂ) • (1 : Op n) - SqS⁻¹ * ρ.toOp * SqS⁻¹).PosSemidef := by
    have hConj := nnprod_conj ((lam : ℂ) • σ - ρ.toOp) SqS⁻¹ hdom
    -- hConj : (SqS⁻¹ᴴ * ((lam : ℂ) • σ - ρ.toOp) * SqS⁻¹).PosSemidef
    rw [hSqSinv_herm.eq] at hConj
    -- hConj : (SqS⁻¹ * ((lam : ℂ) • σ - ρ.toOp) * SqS⁻¹).PosSemidef
    -- Distribute and simplify.
    have hExpand :
        SqS⁻¹ * ((lam : ℂ) • σ - ρ.toOp) * SqS⁻¹ =
          (lam : ℂ) • (1 : Op n) - SqS⁻¹ * ρ.toOp * SqS⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul, hkey]
    rw [hExpand] at hConj
    exact hConj
  -- Step 2: Set T := Σ⁻¹ * S. Then Σ⁻¹ * ρ * Σ⁻¹ = T * Tᴴ.
  set T : Op n := SqS⁻¹ * S with hT_def
  have hT_conjT : Tᴴ = S * SqS⁻¹ := by
    change (SqS⁻¹ * S)ᴴ = S * SqS⁻¹
    rw [Matrix.conjTranspose_mul, hS_herm.eq, hSqSinv_herm.eq]
  have hTTH : T * Tᴴ = SqS⁻¹ * ρ.toOp * SqS⁻¹ := by
    rw [hT_def, hT_conjT, ← hS_sq]
    -- (Σ⁻¹ * S) * (S * Σ⁻¹) = Σ⁻¹ * (S * S) * Σ⁻¹
    simp [Matrix.mul_assoc]
  have hStep1' : ((lam : ℂ) • (1 : Op n) - T * Tᴴ).PosSemidef := by
    rw [hTTH]; exact hStep1
  -- Step 3: Apply swap to get lam • 1 - Tᴴ * T PSD.
  have hStep2 : ((lam : ℂ) • (1 : Op n) - Tᴴ * T).PosSemidef :=
    psd_lam_sub_swap T (lam : ℂ) hStep1'
  -- Step 4: Show Tᴴ * T = S * σ⁻¹ * S.
  have hTHT : Tᴴ * T = S * σ⁻¹ * S := by
    rw [hT_def, hT_conjT, hσinv_eq]
    -- (S * Σ⁻¹) * (Σ⁻¹ * S) = S * (Σ⁻¹ * Σ⁻¹) * S
    simp [Matrix.mul_assoc]
  rw [← hTHT]
  exact hStep2

end InfoTheory.SmoothMinEntropy
