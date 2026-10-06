import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Löwner-order ↔ inverse-square-root sandwich (the `opLe`/`σ^{-1/2}`-geometry bridge)

For a positive-definite reference `σ` and a real scale `s`, the Löwner inequality
`A ⪯ s·σ` is equivalent to the bounded-sandwich inequality
`σ^{-1/2}·A·σ^{-1/2} ⪯ s·1`.

This file is the σ-coordinate dictionary: passing to the coordinates
`X ↦ σ^{-1/2} X σ^{-1/2}` in which the reference becomes the identity.  Besides the
upper half above it contains

* the **lower** half `s·σ ⪯ A ↔ s·1 ⪯ σ^{-1/2}Aσ^{-1/2}`
  (`smul_opLe_iff_smul_one_opLe_inverseSqrt_sandwich`), so that a two-sided ball
  around the reference transports in one step, and
* the algebraic **conjugation transport** `inverseSqrt_conj_sandwich`: conjugating by
  a fixed `K` commutes with passing to σ-coordinates once `K` is replaced by
  `N = σ^{-1/2} K σ^{1/2}`.  No positivity of `K` or `X` is required.

This is the iff-packaging of the two one-directional sandwich lemmas in
`InverseSqrt.lean`:

* forward (`A ⪯ s·σ ⟹ σ^{-1/2}Aσ^{-1/2} ⪯ s·1`) is `Matrix.PosDef.inverseSqrt_sandwich_of_opLe`
  (Tomamichel 2016, Prop 7.1, eq. 7.37–7.38);
* reverse (`σ^{-1/2}Aσ^{-1/2} ⪯ s·1 ⟹ A ⪯ s·σ`) conjugates back by `σ^{1/2} = CFC.sqrt σ`,
  using the support-full cancellation `σ^{1/2}·σ^{-1/2} = 1` (σ PosDef ⟹ full rank), proved here
  via the `CFC.rpow` arithmetic `σ^{1/2}·σ^{-1/2}·… = σ^0 = 1` (same engine as
  `Matrix.PosDef.inverseFourthRoot_sandwich_sigmaSqrt`).

It is the clean reduction that turns a Löwner-order register-restoration domination
`block ⪯ (2·polyDim·t)·σER` into the eigenvalue bound
`λ_max(σER^{-1/2}·block·σER^{-1/2}) ≤ 2·polyDim·t`, and back.

Reference: Tomamichel 2016 §7.3.2, Prop 7.1 (eq. 7.37–7.41); Bhatia *Matrix Analysis* IX.2
(Löwner order under PSD congruence).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace Matrix.PosDef

/-- `σ^{1/2} · σ^{-1/2} = 1` for positive-definite `σ` (support-full cancellation). -/
theorem sqrt_mul_inverseSqrt {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    CFC.sqrt σ * hσ.inverseSqrt = 1 := by
  have hunit : IsUnit σ := hσ.isUnit
  have hinvS : hσ.inverseSqrt = σ ^ (-(1 / 2) : ℝ) := by
    unfold inverseSqrt
    have h_inv : σ⁻¹ = σ ^ (-1 : ℝ) := by
      simpa using (CFC.rpow_neg_one_eq_inv hunit.unit).symm
    rw [h_inv, CFC.sqrt_rpow hunit (by norm_num)]
    norm_num
  rw [hinvS, CFC.sqrt_eq_rpow, ← CFC.rpow_add hunit]
  norm_num
  exact CFC.rpow_zero σ

/-- `σ^{-1/2} · σ^{1/2} = 1` for positive-definite `σ`. -/
theorem inverseSqrt_mul_sqrt {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    hσ.inverseSqrt * CFC.sqrt σ = 1 := by
  have hunit : IsUnit σ := hσ.isUnit
  have hinvS : hσ.inverseSqrt = σ ^ (-(1 / 2) : ℝ) := by
    unfold inverseSqrt
    have h_inv : σ⁻¹ = σ ^ (-1 : ℝ) := by
      simpa using (CFC.rpow_neg_one_eq_inv hunit.unit).symm
    rw [h_inv, CFC.sqrt_rpow hunit (by norm_num)]
    norm_num
  rw [hinvS, CFC.sqrt_eq_rpow, ← CFC.rpow_add hunit]
  norm_num
  exact CFC.rpow_zero σ

/-- `σ^{1/2} · σ^{1/2} = σ` for positive-definite `σ`. -/
theorem sqrt_mul_sqrt {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    CFC.sqrt σ * CFC.sqrt σ = σ :=
  CFC.sqrt_mul_sqrt_self σ hσ.posSemidef.nonneg

/-- **Reverse sandwich (U1 reverse): bounded sandwich ⟹ Löwner domination.**

If `σ^{-1/2}·A·σ^{-1/2} ⪯ s·1` then `A ⪯ s·σ`.

Conjugate by the Hermitian `σ^{1/2} = CFC.sqrt σ` and cancel `σ^{1/2}·σ^{-1/2} = 1`. -/
theorem opLe_of_inverseSqrt_sandwich_le_smul_one {n : ℕ}
    {σ : Op n} (hσ : σ.PosDef)
    {A : Op n} {s : ℝ}
    (h : opLe (hσ.inverseSqrt * A * hσ.inverseSqrt)
      (Complex.ofReal s • (1 : Op n))) :
    opLe A (Complex.ofReal s • σ) := by
  have hS : (CFC.sqrt σ).IsHermitian := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have hconj := Quantum.Operators.opLe_sandwich_of_isHermitian hS h
  -- LHS: σ^{1/2}·(σ^{-1/2}·A·σ^{-1/2})·σ^{1/2} = A
  have hL : CFC.sqrt σ * (hσ.inverseSqrt * A * hσ.inverseSqrt) * CFC.sqrt σ = A := by
    have h1 : CFC.sqrt σ * hσ.inverseSqrt = 1 := hσ.sqrt_mul_inverseSqrt
    have h2 : hσ.inverseSqrt * CFC.sqrt σ = 1 := hσ.inverseSqrt_mul_sqrt
    calc CFC.sqrt σ * (hσ.inverseSqrt * A * hσ.inverseSqrt) * CFC.sqrt σ
        = (CFC.sqrt σ * hσ.inverseSqrt) * A * (hσ.inverseSqrt * CFC.sqrt σ) := by
          noncomm_ring
      _ = 1 * A * 1 := by rw [h1, h2]
      _ = A := by rw [one_mul, mul_one]
  -- RHS: σ^{1/2}·(s·1)·σ^{1/2} = s·σ
  have hR : CFC.sqrt σ * (Complex.ofReal s • (1 : Op n)) * CFC.sqrt σ
      = Complex.ofReal s • σ := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hσ.sqrt_mul_sqrt]
  rw [hL, hR] at hconj
  exact hconj

/-- **(U1) Löwner domination ↔ bounded inverse-square-root sandwich.**

For positive-definite `σ` and real scale `s`:
`A ⪯ s·σ  ↔  σ^{-1/2}·A·σ^{-1/2} ⪯ s·1`.

Forward: `Matrix.PosDef.inverseSqrt_sandwich_of_opLe`; reverse:
`opLe_of_inverseSqrt_sandwich_le_smul_one`. -/
theorem opLe_iff_inverseSqrt_sandwich_le_smul_one {n : ℕ}
    {σ : Op n} (hσ : σ.PosDef)
    {A : Op n} {s : ℝ} :
    opLe A (Complex.ofReal s • σ) ↔
      opLe (hσ.inverseSqrt * A * hσ.inverseSqrt)
        (Complex.ofReal s • (1 : Op n)) :=
  ⟨fun h => hσ.inverseSqrt_sandwich_of_opLe h,
   fun h => hσ.opLe_of_inverseSqrt_sandwich_le_smul_one h⟩

/-! ## The lower half of the σ-coordinate order dictionary

`opLe_iff_inverseSqrt_sandwich_le_smul_one` transports an *upper* Löwner bound into
σ-coordinates.  The two lemmas below are its companions for a *lower* bound, so that
a two-sided ball `s·σ ⪯ A ⪯ s'·σ` becomes the σ-coordinate ball
`s·1 ⪯ σ^{-1/2}Aσ^{-1/2} ⪯ s'·1` in one step. -/

/-- **Lower Löwner bound ⟹ lower σ-coordinate bound.**  If `s·σ ⪯ A` then
`s·1 ⪯ σ^{-1/2} A σ^{-1/2}`.

This is the companion of `Matrix.PosDef.inverseSqrt_sandwich_of_opLe`, which handles
the upper bound. -/
theorem inverseSqrt_sandwich_of_smul_le {n : ℕ} {σ : Op n} (hσ : σ.PosDef)
    {A : Op n} {s : ℝ} (h : opLe (Complex.ofReal s • σ) A) :
    opLe (Complex.ofReal s • (1 : Op n)) (hσ.inverseSqrt * A * hσ.inverseSqrt) := by
  have h1 := hσ.inverseSqrt_sandwich_mono h
  have heq : hσ.inverseSqrt * (Complex.ofReal s • σ) * hσ.inverseSqrt
      = Complex.ofReal s • (1 : Op n) := by
    rw [mul_smul_comm, smul_mul_assoc, hσ.inverseSqrt_sandwich_eq_one]
  rwa [heq] at h1

/-- **Lower σ-coordinate bound ⟹ lower Löwner bound.**  If
`s·1 ⪯ σ^{-1/2} A σ^{-1/2}` then `s·σ ⪯ A`. -/
theorem smul_le_of_smul_one_le_inverseSqrt_sandwich {n : ℕ} {σ : Op n} (hσ : σ.PosDef)
    {A : Op n} {s : ℝ}
    (h : opLe (Complex.ofReal s • (1 : Op n)) (hσ.inverseSqrt * A * hσ.inverseSqrt)) :
    opLe (Complex.ofReal s • σ) A := by
  have hconj := Quantum.Operators.opLe_sandwich_of_isHermitian
    (CFC.sqrt_nonneg σ).posSemidef.isHermitian h
  have hL : CFC.sqrt σ * (Complex.ofReal s • (1 : Op n)) * CFC.sqrt σ
      = Complex.ofReal s • σ := by
    rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hσ.sqrt_mul_sqrt]
  have hR : CFC.sqrt σ * (hσ.inverseSqrt * A * hσ.inverseSqrt) * CFC.sqrt σ = A := by
    calc CFC.sqrt σ * (hσ.inverseSqrt * A * hσ.inverseSqrt) * CFC.sqrt σ
        = (CFC.sqrt σ * hσ.inverseSqrt) * A * (hσ.inverseSqrt * CFC.sqrt σ) := by
          noncomm_ring
      _ = A := by
          rw [hσ.sqrt_mul_inverseSqrt, hσ.inverseSqrt_mul_sqrt, one_mul, mul_one]
  rwa [hL, hR] at hconj

/-- **The lower half of the σ-coordinate order dictionary**:
`s·σ ⪯ A ↔ s·1 ⪯ σ^{-1/2} A σ^{-1/2}`.

Paired with `Matrix.PosDef.opLe_iff_inverseSqrt_sandwich_le_smul_one` this transports a
two-sided ball `s·σ ⪯ A ⪯ s'·σ` into the σ-coordinate ball `s·1 ⪯ … ⪯ s'·1`. -/
theorem smul_opLe_iff_smul_one_opLe_inverseSqrt_sandwich {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) {A : Op n} {s : ℝ} :
    opLe (Complex.ofReal s • σ) A ↔
      opLe (Complex.ofReal s • (1 : Op n)) (hσ.inverseSqrt * A * hσ.inverseSqrt) :=
  ⟨fun h => hσ.inverseSqrt_sandwich_of_smul_le h,
   fun h => hσ.smul_le_of_smul_one_le_inverseSqrt_sandwich h⟩

/-! ## σ-coordinate transport of a conjugation -/

/-- **σ-coordinate conjugation transport.**  With `N := σ^{-1/2} K σ^{1/2}`,

`σ^{-1/2} (K X Kᴴ) σ^{-1/2} = N (σ^{-1/2} X σ^{-1/2}) Nᴴ`.

Pure algebra: the two support-full cancellations `σ^{1/2} σ^{-1/2} = 1` and
`σ^{-1/2} σ^{1/2} = 1` move the reference past `K`.  No hypothesis on `K` or `X`, so
this also covers non-positive and non-Hermitian `X`. -/
theorem inverseSqrt_conj_sandwich {n : ℕ} {σ : Op n} (hσ : σ.PosDef) (K X : Op n) :
    hσ.inverseSqrt * (K * X * Kᴴ) * hσ.inverseSqrt
      = (hσ.inverseSqrt * K * CFC.sqrt σ) * (hσ.inverseSqrt * X * hσ.inverseSqrt)
          * (hσ.inverseSqrt * K * CFC.sqrt σ)ᴴ := by
  have hSS : CFC.sqrt σ * hσ.inverseSqrt = 1 := hσ.sqrt_mul_inverseSqrt
  have hSSrev : hσ.inverseSqrt * CFC.sqrt σ = 1 := hσ.inverseSqrt_mul_sqrt
  have hNdag : (hσ.inverseSqrt * K * CFC.sqrt σ)ᴴ
      = CFC.sqrt σ * Kᴴ * hσ.inverseSqrt := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (CFC.sqrt_nonneg σ).posSemidef.isHermitian.eq, hσ.inverseSqrt_isHermitian.eq,
      Matrix.mul_assoc]
  rw [hNdag]
  calc hσ.inverseSqrt * (K * X * Kᴴ) * hσ.inverseSqrt
      = hσ.inverseSqrt * K * (CFC.sqrt σ * hσ.inverseSqrt) * X
          * (hσ.inverseSqrt * CFC.sqrt σ) * Kᴴ * hσ.inverseSqrt := by
        rw [hSS, hSSrev]; noncomm_ring
    _ = (hσ.inverseSqrt * K * CFC.sqrt σ) * (hσ.inverseSqrt * X * hσ.inverseSqrt)
          * (CFC.sqrt σ * Kᴴ * hσ.inverseSqrt) := by noncomm_ring

end Matrix.PosDef

end -- noncomputable section
