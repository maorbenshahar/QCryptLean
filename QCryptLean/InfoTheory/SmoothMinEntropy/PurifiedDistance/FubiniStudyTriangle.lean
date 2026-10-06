import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fubini–Study / Bures-angle triangle inequalities — pure states

The textbook Fubini–Study triangle inequality on projective Hilbert space
(Tomamichel 2016, eq. 3.27 / Lemma 3.5), phrased on `Ket n` and lifted to
`DensityOp.fromPure`.

## Main statements
- `fidelity_pure_eq_abs_inner`  — pure-state fidelity equals `‖⟨ψ|φ⟩‖`
- `fubiniStudy_triangle_pure`   — `arccos ‖⟨·|·⟩‖` satisfies the triangle inequality
- `fidelityAngle_triangle_pure` — the same, packaged via `DensityOp.fidelity`
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Sandwich factorization on `Ket`/`Bra`:
    `⟨φ|(|ψ⟩⟨ψ|)|φ⟩ = ⟨φ|ψ⟩⟨ψ|φ⟩`. Used in `fidelity_pure_eq_abs_inner`. -/
private lemma ketbra_sandwich_eq_inner_mul_inner {n : ℕ} (ψ φ : Ket n) :
    (φ.dag * (ψ * ψ.dag) * φ : ℂ) = (φ.dag * ψ) * (ψ.dag * φ) := by
  rw [bra_mul_ketbra, smul_bra_mul_ket]
  rfl

/-- Pure-state fidelity equals the absolute value of the inner product:
for normalized kets `|ψ⟩, |φ⟩`, the Uhlmann fidelity of the pure-state
density operators `|ψ⟩⟨ψ|` and `|φ⟩⟨φ|` equals `‖⟨ψ|φ⟩‖`. -/
theorem fidelity_pure_eq_abs_inner
    {n : ℕ} [NeZero n] (ψ φ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) :
    DensityOp.fidelity (DensityOp.fromPure ψ hψ) (DensityOp.fromPure φ hφ)
      = ‖(ψ.dag * φ : ℂ)‖ := by
  -- Reduce to `Real.sqrt ((φ.dag * (ψ * ψ.dag) * φ).re)`.
  rw [fidelity_fromPure (DensityOp.fromPure ψ hψ) φ hφ]
  have h_toOp : (DensityOp.fromPure ψ hψ).toOp = ψ * ψ.dag := rfl
  rw [h_toOp]
  -- Factor the sandwich using the helper.
  rw [ketbra_sandwich_eq_inner_mul_inner ψ φ]
  -- Identify `ψ.dag * φ = conj (φ.dag * ψ)` to expose `z * conj z`.
  have h_conj : (ψ.dag * φ : ℂ) = star (φ.dag * ψ : ℂ) := Ket.inner_conj ψ φ
  have h_star : star (φ.dag * ψ : ℂ) = (starRingEnd ℂ) (φ.dag * ψ) := rfl
  rw [h_conj, h_star, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _), Complex.norm_conj]

/-!
### Helper lemmas for the Fubini–Study triangle inequality

The proof below goes through a small ladder of helpers that identify the
`Bra * Ket` pairing with the Mathlib `EuclideanSpace ℂ (Fin n)` inner product,
then exposes Cauchy–Schwarz, orthogonal splitting along `|φ⟩`, and finally the
algebraic inequality `c ≥ ab − √(1 − a²) √(1 − b²)` that the main theorem
consumes after its case split on `α + β ≥ π/2`.
-/

/-- Bridge lemma: `ψ.dag * φ` on `Ket n` equals the `EuclideanSpace ℂ (Fin n)`
inner product of the underlying vectors. -/
private lemma ket_inner_eq_euclid_inner {n : ℕ} (ψ φ : Ket n) :
    (ψ.dag * φ : ℂ)
      = @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (WithLp.toLp 2 ψ.vec) (WithLp.toLp 2 φ.vec) := by
  rw [bra_mul_ket_eq, EuclideanSpace.inner_toLp_toLp]
  -- RHS: `φ.vec ⬝ᵥ star ψ.vec = ∑ i, φ.vec i * star (ψ.vec i)`.
  unfold dotProduct
  simp only [Ket.dag_vec, Pi.star_apply, starRingEnd_apply, mul_comm]

/-- Norm of the EuclideanSpace embedding equals `√((ψ.dag * ψ).re)`. -/
private lemma ket_euclid_norm_sq {n : ℕ} (ψ : Ket n) :
    ‖(WithLp.toLp 2 ψ.vec : EuclideanSpace ℂ (Fin n))‖ ^ 2 = (ψ.dag * ψ).re := by
  have h := InnerProductSpace.norm_sq_eq_re_inner
      (𝕜 := ℂ) (WithLp.toLp 2 ψ.vec : EuclideanSpace ℂ (Fin n))
  rw [h, ← ket_inner_eq_euclid_inner]
  rfl

private lemma ket_euclid_norm_eq_sqrt {n : ℕ} (ψ : Ket n) :
    ‖(WithLp.toLp 2 ψ.vec : EuclideanSpace ℂ (Fin n))‖
      = Real.sqrt (ψ.dag * ψ).re := by
  rw [show ((ψ.dag * ψ).re : ℝ)
        = ‖(WithLp.toLp 2 ψ.vec : EuclideanSpace ℂ (Fin n))‖ ^ 2 from
      (ket_euclid_norm_sq ψ).symm]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- Cauchy–Schwarz on kets:
`‖ψ.dag * φ‖ ≤ √((ψ.dag * ψ).re) * √((φ.dag * φ).re)`. -/
lemma ket_cauchy_schwarz {n : ℕ} (ψ φ : Ket n) :
    ‖(ψ.dag * φ : ℂ)‖
      ≤ Real.sqrt (ψ.dag * ψ).re * Real.sqrt (φ.dag * φ).re := by
  rw [ket_inner_eq_euclid_inner, ← ket_euclid_norm_eq_sqrt,
      ← ket_euclid_norm_eq_sqrt]
  exact norm_inner_le_norm _ _

/-- For normalized kets, the inner-product modulus lies in `[0, 1]`. -/
lemma ket_inner_abs_le_one {n : ℕ} {ψ φ : Ket n}
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) :
    ‖(ψ.dag * φ : ℂ)‖ ≤ 1 := by
  have h := ket_cauchy_schwarz ψ φ
  rw [hψ, hφ] at h
  simpa using h

/-- Norm symmetry of the bra-ket inner product. -/
private lemma ket_inner_norm_symm {n : ℕ} (ψ φ : Ket n) :
    ‖(ψ.dag * φ : ℂ)‖ = ‖(φ.dag * ψ : ℂ)‖ := by
  have h := Ket.inner_conj ψ φ
  simp only [Ket.inner] at h
  rw [h]
  exact norm_star _

/-- Orthogonal projection expansion of the inner product:
`ψ.dag * χ = star ⟨φ|ψ⟩ · ⟨φ|χ⟩ + ⟨ψ⊥|χ⊥⟩` where
`ψ⊥ := ψ − ⟨φ|ψ⟩ • φ` and `χ⊥ := χ − ⟨φ|χ⟩ • φ`. -/
lemma ket_perp_inner_expand {n : ℕ} (ψ χ φ : Ket n) (hφ : φ.dag * φ = 1) :
    (ψ.dag * χ : ℂ)
      = star (φ.dag * ψ : ℂ) * (φ.dag * χ : ℂ)
        + ((ψ - (φ.dag * ψ : ℂ) • φ).dag
            * (χ - (φ.dag * χ : ℂ) • φ) : ℂ) := by
  have hψφ : (ψ.dag * φ : ℂ) = star (φ.dag * ψ : ℂ) := by
    have h := Ket.inner_conj ψ φ
    simpa [Ket.inner] using h
  simp only [Ket.dag_sub, Ket.dag_smul, bra_sub_mul_ket, bra_mul_sub_ket,
             smul_bra_mul_ket, bra_mul_smul_ket, smul_eq_mul]
  rw [hφ, hψφ]
  ring

/-- Norm-squared of the orthogonal complement along `|φ⟩`:
`(ψ⊥.dag * ψ⊥).re = (ψ.dag * ψ).re − ‖⟨φ|ψ⟩‖²`. -/
lemma ket_perp_norm_sq {n : ℕ} (ψ φ : Ket n) (hφ : φ.dag * φ = 1) :
    ((ψ - (φ.dag * ψ : ℂ) • φ).dag * (ψ - (φ.dag * ψ : ℂ) • φ) : ℂ).re
      = (ψ.dag * ψ).re - ‖(φ.dag * ψ : ℂ)‖ ^ 2 := by
  set α : ℂ := (φ.dag * ψ : ℂ) with hα
  have hψφ : (ψ.dag * φ : ℂ) = star α := by
    have h := Ket.inner_conj ψ φ
    simpa [Ket.inner, hα] using h
  have hcomplex :
      ((ψ - α • φ).dag * (ψ - α • φ) : ℂ)
        = (ψ.dag * ψ : ℂ) - α * star α := by
    simp only [Ket.dag_sub, Ket.dag_smul, bra_sub_mul_ket, bra_mul_sub_ket,
               smul_bra_mul_ket, bra_mul_smul_ket, smul_eq_mul]
    rw [hφ, hψφ]
    ring
  rw [hcomplex, Complex.sub_re]
  congr 1
  rw [show star α = (starRingEnd ℂ) α from rfl, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The algebraic core of the Fubini–Study triangle inequality:
for normalized kets `ψ, φ, χ`, with
`a := ‖⟨ψ|φ⟩‖`, `b := ‖⟨φ|χ⟩‖`, `c := ‖⟨ψ|χ⟩‖`,
`c ≥ a·b − √(1 − a²) · √(1 − b²)`. -/
lemma fubiniStudy_algebraic_inequality {n : ℕ} (ψ φ χ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) (hχ : χ.dag * χ = 1) :
    let a := ‖(ψ.dag * φ : ℂ)‖
    let b := ‖(φ.dag * χ : ℂ)‖
    let c := ‖(ψ.dag * χ : ℂ)‖
    a * b - Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) ≤ c := by
  intro a b c
  -- Notation for orthogonal complements.
  set αψ : ℂ := (φ.dag * ψ : ℂ) with hαψ
  set αχ : ℂ := (φ.dag * χ : ℂ) with hαχ
  set ψperp : Ket n := ψ - αψ • φ with hψperp
  set χperp : Ket n := χ - αχ • φ with hχperp
  have ha : a = ‖αψ‖ := by
    simp [a, ket_inner_norm_symm ψ φ, hαψ]
  have hb : b = ‖αχ‖ := by simp [b, hαχ]
  -- Orthogonal expansion: ψ.dag * χ = star αψ * αχ + ψperp.dag * χperp.
  have hexpand := ket_perp_inner_expand ψ χ φ hφ
  rw [← hαψ, ← hαχ, ← hψperp, ← hχperp] at hexpand
  -- Rearrange: star αψ * αχ = (ψ.dag * χ) - (ψperp.dag * χperp).
  have hsubst :
      (star αψ * αχ : ℂ) = (ψ.dag * χ : ℂ) - (ψperp.dag * χperp : ℂ) := by
    linear_combination -hexpand
  -- `|star αψ * αχ| = a * b`.
  have hab : ‖(star αψ * αχ : ℂ)‖ = a * b := by
    rw [norm_mul, norm_star, ha, hb]
  -- Triangle inequality: ab ≤ c + ‖ψperp.dag * χperp‖.
  have htri : a * b ≤ c + ‖(ψperp.dag * χperp : ℂ)‖ := by
    have h1 : ‖(ψ.dag * χ : ℂ) - (ψperp.dag * χperp : ℂ)‖
        ≤ ‖(ψ.dag * χ : ℂ)‖ + ‖(ψperp.dag * χperp : ℂ)‖ :=
      norm_sub_le _ _
    rw [← hsubst, hab] at h1
    exact h1
  -- Cauchy–Schwarz on ψperp and χperp.
  have hcs : ‖(ψperp.dag * χperp : ℂ)‖
      ≤ Real.sqrt (ψperp.dag * ψperp).re
          * Real.sqrt (χperp.dag * χperp).re :=
    ket_cauchy_schwarz ψperp χperp
  -- Norm-squared identities.
  have hψperp_sq : (ψperp.dag * ψperp : ℂ).re = 1 - a ^ 2 := by
    have h := ket_perp_norm_sq ψ φ hφ
    rw [← hαψ, ← hψperp] at h
    rw [h, hψ, Complex.one_re, ha]
  have hχperp_sq : (χperp.dag * χperp : ℂ).re = 1 - b ^ 2 := by
    have h := ket_perp_norm_sq χ φ hφ
    rw [← hαχ, ← hχperp] at h
    rw [h, hχ, Complex.one_re, hb]
  rw [hψperp_sq, hχperp_sq] at hcs
  linarith

/-- Pure-state Fubini–Study (projective) triangle inequality: on normalized
kets, the angle `arccos ‖⟨·|·⟩‖` satisfies the triangle inequality. This is
the textbook Fubini–Study metric on `ℂP^{n-1}`. -/
theorem fubiniStudy_triangle_pure
    {n : ℕ} [NeZero n] (ψ φ χ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) (hχ : χ.dag * χ = 1) :
    Real.arccos ‖(ψ.dag * χ : ℂ)‖
      ≤ Real.arccos ‖(ψ.dag * φ : ℂ)‖
          + Real.arccos ‖(φ.dag * χ : ℂ)‖ := by
  set a : ℝ := ‖(ψ.dag * φ : ℂ)‖ with ha_def
  set b : ℝ := ‖(φ.dag * χ : ℂ)‖ with hb_def
  set c : ℝ := ‖(ψ.dag * χ : ℂ)‖ with hc_def
  have ha_nn : 0 ≤ a := norm_nonneg _
  have hb_nn : 0 ≤ b := norm_nonneg _
  have hc_nn : 0 ≤ c := norm_nonneg _
  have ha_le : a ≤ 1 := ket_inner_abs_le_one hψ hφ
  have hb_le : b ≤ 1 := ket_inner_abs_le_one hφ hχ
  have hc_le : c ≤ 1 := ket_inner_abs_le_one hψ hχ
  have ha1_nn : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hb1_nn : (0 : ℝ) ≤ 1 - b ^ 2 := by nlinarith
  have hα_nn : 0 ≤ Real.arccos a := Real.arccos_nonneg _
  have hβ_nn : 0 ≤ Real.arccos b := Real.arccos_nonneg _
  by_cases hsum : Real.pi / 2 ≤ Real.arccos a + Real.arccos b
  · -- Easy branch: `γ ≤ π/2 ≤ α + β`.
    have hγ_le : Real.arccos c ≤ Real.pi / 2 :=
      (Real.arccos_le_pi_div_two).mpr hc_nn
    linarith
  · push_neg at hsum
    -- Hard branch: use cos addition formula plus the algebraic inequality.
    have hα_le_pi2 : Real.arccos a ≤ Real.pi / 2 :=
      (Real.arccos_le_pi_div_two).mpr ha_nn
    have hβ_le_pi2 : Real.arccos b ≤ Real.pi / 2 :=
      (Real.arccos_le_pi_div_two).mpr hb_nn
    have hsum_nn : 0 ≤ Real.arccos a + Real.arccos b := by linarith
    have hsum_le_pi : Real.arccos a + Real.arccos b ≤ Real.pi := by
      have : Real.pi / 2 ≤ Real.pi := by
        have hpi : 0 ≤ Real.pi := Real.pi_nonneg
        linarith
      linarith
    -- cos(α+β) = a*b - √(1-a²)√(1-b²)
    have hcos_add :
        Real.cos (Real.arccos a + Real.arccos b)
          = a * b - Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) := by
      rw [Real.cos_add, Real.cos_arccos (by linarith) ha_le,
          Real.cos_arccos (by linarith) hb_le,
          Real.sin_arccos, Real.sin_arccos]
    -- Algebraic inequality: c ≥ ab - √(1-a²)√(1-b²).
    have halg := fubiniStudy_algebraic_inequality ψ φ χ hψ hφ hχ
    simp only at halg
    rw [← ha_def, ← hb_def, ← hc_def] at halg
    -- So cos(α+β) ≤ c, i.e. c ≥ cos(α+β).
    have h_c_ge : Real.cos (Real.arccos a + Real.arccos b) ≤ c := by
      rw [hcos_add]; exact halg
    -- Convert via arccos (monotonicity, decreasing).
    have h_le :
        Real.arccos c
          ≤ Real.arccos (Real.cos (Real.arccos a + Real.arccos b)) :=
      Real.arccos_le_arccos h_c_ge
    rw [Real.arccos_cos hsum_nn hsum_le_pi] at h_le
    exact h_le

/-- Pure-state Bures-angle triangle inequality, packaged on
`DensityOp.fromPure`: obtained by rewriting `DensityOp.fidelity` as
`‖⟨·|·⟩‖` via `fidelity_pure_eq_abs_inner` and invoking
`fubiniStudy_triangle_pure`. -/
theorem fidelityAngle_triangle_pure
    {n : ℕ} [NeZero n] (ψ φ χ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) (hχ : χ.dag * χ = 1) :
    Real.arccos (DensityOp.fidelity
        (DensityOp.fromPure ψ hψ) (DensityOp.fromPure χ hχ))
      ≤ Real.arccos (DensityOp.fidelity
            (DensityOp.fromPure ψ hψ) (DensityOp.fromPure φ hφ))
        + Real.arccos (DensityOp.fidelity
            (DensityOp.fromPure φ hφ) (DensityOp.fromPure χ hχ)) := by
  rw [fidelity_pure_eq_abs_inner ψ χ hψ hχ,
      fidelity_pure_eq_abs_inner ψ φ hψ hφ,
      fidelity_pure_eq_abs_inner φ χ hφ hχ]
  exact fubiniStudy_triangle_pure ψ φ χ hψ hφ hχ

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
