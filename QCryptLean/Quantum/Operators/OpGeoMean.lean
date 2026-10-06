import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.InverseSqrtSandwichIff
import QCryptLean.Quantum.Operators.MatrixSqrt
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.Trace
import Mathlib.Analysis.Matrix.Order

/-!
# The operator geometric mean `A # B` (Ando 1979; Bhatia *Matrix Analysis* IX.2)

This file develops the operator geometric mean of two positive operators and its
basic Löwner-order facts (the "GM ladder" GM0–GM5).  It is a self-contained,
BB84-free, reusable matrix-analysis module: Mathlib has the CFC square root and
its monotonicity (`CFC.sqrt_le_sqrt`) but does **not** have the operator
geometric mean or any of its order properties.

## Main definitions

- `opGeoMean` (GM0): `A # B := A^{1/2} · (A^{-1/2} · B · A^{-1/2})^{1/2} · A^{1/2}`
  for positive-definite `A` and arbitrary `B`.

## Main statements

- `opGeoMean_posSemidef` (GM1): `A # B` is positive semidefinite when `B` is.
- `opGeoMean_le_arith` (GM2): the AM–GM inequality `A # B ⪯ (A + B)/2`
  (Bhatia IX.2.1), via the scalar `√C ⪯ (1 + C)/2` and the congruence
  `A^{1/2} · C · A^{1/2} = B` with `C = A^{-1/2} B A^{-1/2}`.
- `opGeoMean_smul_one_le` (GM3): the spectral bound
  `A ⪯ a·1, B ⪯ b·1, 0 ≤ a ⟹ A # B ⪯ √(a·b)·1`
  (`λ_max(A # B) ≤ √(λ_max A · λ_max B)`), stated in `opLe` form.
- `opGeoMean_eq_of_riccati`: Riccati uniqueness `G A⁻¹ G = B, G ⪰ 0 ⟹ G = A # B`
  (Bhatia IX.2).
- `opGeoMean_congr` (GM4): congruence-covariance
  `(X A Xᴴ) # (X B Xᴴ) = X (A # B) Xᴴ` for invertible `X` (Ando 1979).

## References

- Ando, "Concavity of certain maps on positive definite matrices and
  applications to Hadamard products", *Lin. Alg. Appl.* 26 (1979).
- Bhatia, *Matrix Analysis*, §IX.2 (the operator geometric mean `A # B`, its
  Löwner monotonicity, joint concavity, AM–GM `A # B ⪯ (A+B)/2`, and the
  congruence-covariance `(X A Xᴴ) # (X B Xᴴ) = X (A # B) Xᴴ`).
- Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) Thm 3, main.tex:1341–:1413 (Appendix
B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}` (main.tex:1356–:1362), the
Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed min-entropy bound
`\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting step
`\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413): the marginal
  register-transport this module is built to dominate.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-- **(GM0) The operator geometric mean `A # B`** (Ando 1979; Bhatia IX.2).

For positive-definite `A` and arbitrary `B`,
`A # B := A^{1/2} · (A^{-1/2} · B · A^{-1/2})^{1/2} · A^{1/2}`,
using the CFC square root `CFC.sqrt` and the inverse square root
`Matrix.PosDef.inverseSqrt`.

When `B` is positive semidefinite this is the usual geometric mean; the
definition is well-typed for arbitrary `B` because `A^{-1/2} · B · A^{-1/2}` is
fed to `CFC.sqrt` (which is the CFC of `NNReal.sqrt`, hence defined on every
matrix). -/
def opGeoMean {n : ℕ} {A : Op n} (hA : A.PosDef) (B : Op n) : Op n :=
  CFC.sqrt A * CFC.sqrt (hA.inverseSqrt * B * hA.inverseSqrt) * CFC.sqrt A

/-- **(GM1) The operator geometric mean is positive semidefinite.**

`A # B = √A · √C · √A` with `C := A^{-1/2} B A^{-1/2}`, and for PSD `B` the
middle factor `C` is PSD (`Matrix.PosSemidef.mul_mul_conjTranspose_same` with the
Hermitian `A^{-1/2}`), so `√C` is PSD and the sandwich `√A · √C · √A` is PSD. -/
theorem opGeoMean_posSemidef {n : ℕ} {A : Op n} (hA : A.PosDef) {B : Op n}
    (hB : B.PosSemidef) : (opGeoMean hA B).PosSemidef := by
  unfold opGeoMean
  set S : Op n := hA.inverseSqrt with hS
  have hSherm : S.IsHermitian := hA.inverseSqrt_isHermitian
  -- C = S * B * S is PSD: it is `B` conjugated by the Hermitian `S`.
  have hC : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    simpa [hSherm.eq] using h
  -- √C is PSD, √A is PSD.
  have hsqrtC : (CFC.sqrt (S * B * S)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  -- √A · √C · √A is `√C` conjugated by the Hermitian `√A`.
  have hsqrtA_herm : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have h := hsqrtC.mul_mul_conjTranspose_same (CFC.sqrt A)
  rw [hsqrtA_herm.eq] at h
  -- reassociate `√A * √C * √A`
  simpa [mul_assoc] using h

/-! ### Bridge between `opLe` and Mathlib's Löwner order `≤`

The GM ladder is most naturally proved in Mathlib's `≤` on `Op n` (where
`CFC.sqrt_le_sqrt` and the `StarOrderedRing` algebra live).  This helper
translates from Mathlib's order to the project's `opLe`. -/

/-- From Mathlib's Löwner `≤` to the project's `opLe`. -/
lemma opLe_of_matrix_le {n : ℕ} {A B : Op n} (h : A ≤ B) : opLe A B :=
  opLe_of_posSemidef_sub (Matrix.le_iff.mp h)

/-- **(GM2 — scalar core) `√C ⪯ (1 + C)/2` for positive-semidefinite `C`.**

This is the operator AM–GM in the special form `C^{1/2} ≤ (1 + C)/2`, the
operator analogue of `√x ≤ (1+x)/2`.  Proof: `(1 - √C)² ⪰ 0`, i.e.
`1 - 2·√C + C ⪰ 0`, since `1` and `√C` commute (both are CFC of `C`). -/
lemma sqrt_le_one_add_div_two {n : ℕ} {C : Op n} (hC : C.PosSemidef) :
    CFC.sqrt C ≤ (1 / 2 : ℝ) • ((1 : Op n) + C) := by
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  set R : Op n := CFC.sqrt C with hR
  have hRherm : R.IsHermitian := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have hRR : R * R = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  rw [Matrix.le_iff]
  have hH : ((1 : Op n) - R)ᴴ = (1 : Op n) - R := by
    rw [conjTranspose_sub, conjTranspose_one, hRherm.eq]
  have hgram_psd := ((1 : Op n) - R).posSemidef_conjTranspose_mul_self
  -- `(1/2)•(1 + C) - R = (1/2)•((1 - R) * (1 - R))`, half a Gram matrix, hence PSD.
  have hhalf : ((1 / 2 : ℝ) • ((1 : Op n) + C)) - R =
      (1 / 2 : ℝ) • (((1 : Op n) - R)ᴴ * ((1 : Op n) - R)) := by
    rw [hH]
    have hexp : ((1 : Op n) - R) * ((1 : Op n) - R) = (1 : Op n) - R - R + C := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
          Matrix.mul_one, Matrix.one_mul, hRR]
      noncomm_ring
    rw [hexp]
    module
  rw [hhalf]
  exact hgram_psd.smul (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))

/-- **(GM2) Operator AM–GM: `A # B ⪯ (A + B)/2`** (Bhatia IX.2.1).

The geometric mean is below the arithmetic mean.  Proof: with
`C := A^{-1/2} B A^{-1/2}` (PSD), the scalar core
`sqrt_le_one_add_div_two` gives `√C ⪯ (1/2)•(1 + C)`; conjugating by the
Hermitian `√A` and using the cancellations `√A·A^{-1/2} = 1`,
`A^{-1/2}·√A = 1`, `√A·√A = A` turns this into
`√A·√C·√A ⪯ (1/2)•(A + B)`, i.e. `A # B ⪯ (A + B)/2`. -/
theorem opGeoMean_le_arith {n : ℕ} {A : Op n} (hA : A.PosDef) {B : Op n}
    (hB : B.PosSemidef) : opLe (opGeoMean hA B) ((1 / 2 : ℝ) • (A + B)) := by
  set S : Op n := hA.inverseSqrt with hS
  have hSherm : S.IsHermitian := hA.inverseSqrt_isHermitian
  set C : Op n := S * B * S with hC
  have hCpsd : C.PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    simpa [hC, hSherm.eq] using h
  -- scalar core in Mathlib `≤`
  have hscalar : CFC.sqrt C ≤ (1 / 2 : ℝ) • ((1 : Op n) + C) :=
    sqrt_le_one_add_div_two hCpsd
  have hscalar_opLe : opLe (CFC.sqrt C) ((1 / 2 : ℝ) • ((1 : Op n) + C)) :=
    opLe_of_matrix_le hscalar
  -- conjugate by the Hermitian `√A`
  have hAsqrt_herm : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hconj := opLe_sandwich_of_isHermitian hAsqrt_herm hscalar_opLe
  -- LHS sandwich = `A # B`
  have hLHS : CFC.sqrt A * CFC.sqrt C * CFC.sqrt A = opGeoMean hA B := by
    rfl
  -- RHS sandwich = `(1/2)•(A + B)`
  have hcancel : CFC.sqrt A * C * CFC.sqrt A = B := by
    have h1 : CFC.sqrt A * S = 1 := hA.sqrt_mul_inverseSqrt
    have h2 : S * CFC.sqrt A = 1 := hA.inverseSqrt_mul_sqrt
    calc CFC.sqrt A * C * CFC.sqrt A
        = (CFC.sqrt A * S) * B * (S * CFC.sqrt A) := by rw [hC]; noncomm_ring
      _ = 1 * B * 1 := by rw [h1, h2]
      _ = B := by rw [one_mul, mul_one]
  have hAA : CFC.sqrt A * (1 : Op n) * CFC.sqrt A = A := by
    rw [mul_one, hA.sqrt_mul_sqrt]
  have hRHS : CFC.sqrt A * ((1 / 2 : ℝ) • ((1 : Op n) + C)) * CFC.sqrt A
      = (1 / 2 : ℝ) • (A + B) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_add, Matrix.add_mul, hAA, hcancel]
  rw [hLHS, hRHS] at hconj
  exact hconj

/-- **(Right homogeneity of the geometric mean.)** Scaling the second argument
by a nonnegative real `μ` pulls out its real square root:
`A # (μ • B) = √μ • (A # B)` (Bhatia IX.2; Ando 1979).

This is the single-`√`-pull special case (only `B` is scaled), enough to derive
the spectral bound (GM3). -/
lemma opGeoMean_ofReal_smul_right {n : ℕ} {A : Op n} (hA : A.PosDef)
    {μ : ℝ} (hμ : 0 ≤ μ) (B : Op n) (hB : B.PosSemidef) :
    opGeoMean hA ((Complex.ofReal μ) • B)
      = (Complex.ofReal (Real.sqrt μ)) • opGeoMean hA B := by
  unfold opGeoMean
  set S : Op n := hA.inverseSqrt with hSdef
  have hSherm : S.IsHermitian := hA.inverseSqrt_isHermitian
  -- middle argument: S (μ•B) S = μ • (S B S)
  have hmid : S * ((Complex.ofReal μ) • B) * S = (Complex.ofReal μ) • (S * B * S) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hSBS_psd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    rwa [hSherm.eq] at h
  rw [hmid, sqrt_ofReal_smul hμ hSBS_psd]
  -- √A * (√μ • √(SBS)) * √A = √μ • (√A √(SBS) √A)
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **(GM3) Spectral bound: `A # B ⪯ √(a·b)·1`** (`λ_max(A # B) ≤
√(λ_max A · λ_max B)`).

If `A ⪯ a·1`, `B ⪯ b·1` and `0 ≤ a`, then `A # B ⪯ √(a·b)·1`, stated in `opLe`
form (the project carries no `λ_max` function).

Proof: for `b = 0` the second operand is `0` (PSD and `⪯ 0`), so `A # B = 0`.
For `b > 0`, by right homogeneity `A # B = (1/√μ)·(A # (μ•B))` with `μ := a/b`;
the AM–GM (GM2) gives `A # (μ•B) ⪯ (A + μ•B)/2 ⪯ ((a + μ·b)/2)·1`, and the scalar
optimum `(a + (a/b)·b)/(2·√(a/b)) = √(a·b)` yields the claim. -/
theorem opGeoMean_smul_one_le {n : ℕ} {A : Op n} (hA : A.PosDef) {B : Op n}
    (hB : B.PosSemidef) {a b : ℝ}
    (ha : opLe A ((Complex.ofReal a) • (1 : Op n)))
    (hb : opLe B ((Complex.ofReal b) • (1 : Op n))) (hab : 0 ≤ a) :
    opLe (opGeoMean hA B) ((Complex.ofReal (Real.sqrt (a * b))) • (1 : Op n)) := by
  classical
  -- Trivial in dimension 0 (`opLe` is vacuous: every operator is the zero matrix).
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    intro w
    have h1 : opGeoMean hA B = 0 := Subsingleton.elim _ _
    have h2 : (Complex.ofReal (Real.sqrt (a * b))) • (1 : Op 0) = 0 := Subsingleton.elim _ _
    rw [h1, h2]
  -- `b ≥ 0` from `B` PSD and `B ⪯ b·1` (evaluate at a basis vector).
  have hb0 : 0 ≤ b := by
    set v : Fin n → ℂ := Pi.single ⟨0, hnpos⟩ 1 with hv
    have hbv := hb v
    have hBnn : 0 ≤ (quadraticForm B v).re := posSemidef_re_quadraticForm_nonneg hB v
    have hone : (quadraticForm ((Complex.ofReal b) • (1 : Op n)) v).re = b := by
      rw [quadraticForm_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
      have h1 : (quadraticForm (1 : Op n) v).re = 1 := by
        simp only [quadraticForm, Matrix.one_mulVec, hv]
        rw [dotProduct_single, Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
        simp
      rw [h1, mul_one]
    rw [hone] at hbv
    linarith
  -- `a > 0`: `A` PosDef and `A ⪯ a·1` forces `a > 0` (some positive eigenvalue).
  have hapos : 0 < a := by
    set v : Fin n → ℂ := Pi.single ⟨0, hnpos⟩ 1 with hv
    have hav := ha v
    have hv_ne : v ≠ 0 := by
      intro hcontra
      have := congrFun hcontra ⟨0, hnpos⟩
      simp [hv, Pi.single_eq_same] at this
    have hApos : 0 < (quadraticForm A v).re := hA.re_dotProduct_pos hv_ne
    have hone : (quadraticForm ((Complex.ofReal a) • (1 : Op n)) v).re = a := by
      rw [quadraticForm_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
      have h1 : (quadraticForm (1 : Op n) v).re = 1 := by
        simp only [quadraticForm, Matrix.one_mulVec, hv]
        rw [dotProduct_single, Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
        simp
      rw [h1, mul_one]
    rw [hone] at hav
    linarith
  rcases eq_or_lt_of_le hb0 with hb_eq | hb_pos
  · -- b = 0 ⟹ B ⪯ 0 ⟹ B = 0 ⟹ A # B = A # 0 = 0 ⪯ 0 = √(a·0)·1
    have hBzero : B = 0 := by
      have hBmulVec : ∀ w : Fin n → ℂ, B.mulVec w = 0 := by
        intro w
        refine (hB.dotProduct_mulVec_zero_iff w).mp ?_
        have hle : (quadraticForm B w).re ≤ 0 := by
          have hbw := hb w
          rw [← hb_eq, Complex.ofReal_zero, zero_smul] at hbw
          have hzero : (quadraticForm (0 : Op n) w).re = 0 := by
            simp [quadraticForm, Matrix.zero_mulVec, dotProduct_zero]
          rwa [hzero] at hbw
        have hge : 0 ≤ (quadraticForm B w).re := posSemidef_re_quadraticForm_nonneg hB w
        have hre0 : (quadraticForm B w).re = 0 := le_antisymm hle hge
        have him0 : (quadraticForm B w).im = 0 :=
          quadraticForm_im_of_isHermitian B hB.isHermitian w
        exact Complex.ext hre0 him0
      ext i j
      have := congrFun (hBmulVec (Pi.single j 1)) i
      simpa [Matrix.mulVec_single] using this
    rw [hBzero, ← hb_eq]
    have hgm0 : opGeoMean hA (0 : Op n) = 0 := by
      simp [opGeoMean, CFC.sqrt_zero]
    rw [hgm0]
    simp only [mul_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
    exact fun w => le_refl _
  · -- b > 0: choose μ = a/b
    set μ : ℝ := a / b with hμdef
    have hμposlt : 0 < μ := by rw [hμdef]; positivity
    have hμpos : 0 ≤ μ := le_of_lt hμposlt
    have hsqμpos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμposlt
    -- right homogeneity: A # (μ•B) = √μ • (A # B)
    have hhom : opGeoMean hA ((Complex.ofReal μ) • B)
        = (Complex.ofReal (Real.sqrt μ)) • opGeoMean hA B :=
      opGeoMean_ofReal_smul_right hA hμpos B hB
    -- GM2 at (A, μ•B): A # (μ•B) ⪯ (1/2)•(A + μ•B)
    have hμB_psd : ((Complex.ofReal μ) • B).PosSemidef :=
      hB.smul (by rw [Complex.le_def]; exact ⟨by simpa using hμpos, by simp⟩)
    have hgm2 := opGeoMean_le_arith hA hμB_psd
    -- (A + μ•B) ⪯ (a + μ·b)•1
    have hAB_le : opLe (A + (Complex.ofReal μ) • B)
        ((Complex.ofReal (a + μ * b)) • (1 : Op n)) := by
      intro w
      have h1 := ha w
      have h2 : (quadraticForm ((Complex.ofReal μ) • B) w).re
          ≤ (quadraticForm ((Complex.ofReal (μ * b)) • (1 : Op n)) w).re := by
        rw [show (Complex.ofReal (μ * b)) • (1 : Op n)
            = (Complex.ofReal μ) • ((Complex.ofReal b) • (1 : Op n)) by
          rw [smul_smul, ← Complex.ofReal_mul]]
        rw [quadraticForm_smul, quadraticForm_smul, Complex.mul_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_mul, sub_zero]
        exact mul_le_mul_of_nonneg_left (hb w) hμpos
      have hsum : (quadraticForm (A + (Complex.ofReal μ) • B) w).re
          = (quadraticForm A w).re + (quadraticForm ((Complex.ofReal μ) • B) w).re := by
        unfold quadraticForm
        rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      have hrhs : (quadraticForm ((Complex.ofReal (a + μ * b)) • (1 : Op n)) w).re
          = (quadraticForm ((Complex.ofReal a) • (1 : Op n)) w).re
            + (quadraticForm ((Complex.ofReal (μ * b)) • (1 : Op n)) w).re := by
        rw [quadraticForm_smul, quadraticForm_smul, quadraticForm_smul,
            Complex.ofReal_add, add_mul, Complex.add_re]
      rw [hsum, hrhs]
      exact add_le_add h1 h2
    -- (1/2)•(A + μ•B) ⪯ ((a + μ·b)/2)•1
    have hhalf_le : opLe ((1 / 2 : ℝ) • (A + (Complex.ofReal μ) • B))
        ((Complex.ofReal ((a + μ * b) / 2)) • (1 : Op n)) := by
      have hsc := opLe_smul_nonneg (t := (1 / 2 : ℝ)) (by norm_num) hAB_le
      have heq : (Complex.ofReal (1 / 2 : ℝ)) • ((Complex.ofReal (a + μ * b)) • (1 : Op n))
          = (Complex.ofReal ((a + μ * b) / 2)) • (1 : Op n) := by
        rw [smul_smul, ← Complex.ofReal_mul]; ring_nf
      have hlhs : (Complex.ofReal (1 / 2 : ℝ)) • (A + (Complex.ofReal μ) • B)
          = (1 / 2 : ℝ) • (A + (Complex.ofReal μ) • B) := by
        rw [Complex.coe_smul]
      rw [hlhs, heq] at hsc
      exact hsc
    -- chain: √μ • (A#B) = A#(μB) ⪯ ((a+μb)/2)•1
    have hchain : opLe ((Complex.ofReal (Real.sqrt μ)) • opGeoMean hA B)
        ((Complex.ofReal ((a + μ * b) / 2)) • (1 : Op n)) := by
      rw [← hhom]
      exact opLe_trans hgm2 hhalf_le
    -- scale by (√μ)⁻¹ ≥ 0 to cancel the √μ on the left
    have hscaled := opLe_smul_nonneg (t := (Real.sqrt μ)⁻¹) (by positivity) hchain
    -- LHS: (√μ)⁻¹ • √μ • (A#B) = A#B
    have hLcancel : (Complex.ofReal (Real.sqrt μ)⁻¹) •
        ((Complex.ofReal (Real.sqrt μ)) • opGeoMean hA B) = opGeoMean hA B := by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hsqμpos),
          Complex.ofReal_one, one_smul]
    -- RHS: (√μ)⁻¹ • ((a+μb)/2)•1 = √(ab)•1
    have hRcancel : (Complex.ofReal (Real.sqrt μ)⁻¹) •
        ((Complex.ofReal ((a + μ * b) / 2)) • (1 : Op n))
        = (Complex.ofReal (Real.sqrt (a * b))) • (1 : Op n) := by
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      -- (√μ)⁻¹ * ((a + μ·b)/2) = √(ab), with μ = a/b
      rw [hμdef]
      have hbne : b ≠ 0 := ne_of_gt hb_pos
      rw [show a / b * b = a from by field_simp]
      rw [Real.sqrt_div hab b, Real.sqrt_mul hab b]
      have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt hab
      have hsqb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
      field_simp
      nlinarith [hsqa, hsqb]
    rw [hLcancel, hRcancel] at hscaled
    exact hscaled

/-- **Riccati characterization of the geometric mean.** For positive-definite
`A` and PSD `G`, if `G · A⁻¹ · G = B` then `G = A # B` (Bhatia IX.2: `A # B` is
the unique PSD solution of the Riccati equation `G A⁻¹ G = B`).

Proof: set `Y := A^{-1/2} G A^{-1/2}` (PSD).  The Riccati equation becomes
`A^{1/2} Y² A^{1/2} = B`, i.e. `Y² = A^{-1/2} B A^{-1/2} = C`, so `Y = √C` by the
uniqueness of the PSD square root (`CFC.sqrt_eq_iff`); hence
`G = A^{1/2} Y A^{1/2} = A^{1/2} √C A^{1/2} = A # B`. -/
theorem opGeoMean_eq_of_riccati {n : ℕ} {A : Op n} (hA : A.PosDef) {B G : Op n}
    (hG : G.PosSemidef) (hric : G * A⁻¹ * G = B) :
    G = opGeoMean hA B := by
  set Sinv : Op n := hA.inverseSqrt with hSinv
  set Ssqrt : Op n := CFC.sqrt A with hSsqrt
  have hSinv_herm : Sinv.IsHermitian := hA.inverseSqrt_isHermitian
  have hSsqrt_herm : Ssqrt.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  -- Y := A^{-1/2} G A^{-1/2}, PSD
  set Y : Op n := Sinv * G * Sinv with hY
  have hYpsd : Y.PosSemidef := by
    have h := hG.mul_mul_conjTranspose_same Sinv
    rwa [hSinv_herm.eq] at h
  -- C := A^{-1/2} B A^{-1/2}, PSD, and Y² = C
  set C : Op n := Sinv * B * Sinv with hCdef
  -- A⁻¹ = Sinv * Sinv
  have hAinv : A⁻¹ = Sinv * Sinv := (hA.inverseSqrt_sq).symm
  have hYsq : Y * Y = C := by
    rw [hY, hCdef, ← hric, hAinv]
    -- (Sinv G Sinv)(Sinv G Sinv) = Sinv (G (Sinv Sinv) G) Sinv
    noncomm_ring
  -- so Y = √C  (C = Y² is PSD since Y is Hermitian PSD)
  have hCpsd : C.PosSemidef := by
    rw [← hYsq]
    have h2 := hYpsd.mul_mul_conjTranspose_same Y
    rw [hYpsd.isHermitian.eq] at h2
    -- h2 : (Y * Y * Y).PosSemidef ?  no — conjugation form
    have hYY : Y * Y = Yᴴ * Y := by rw [hYpsd.isHermitian.eq]
    rw [hYY]
    exact Matrix.posSemidef_conjTranspose_mul_self Y
  have hYeq : Y = CFC.sqrt C := by
    rw [eq_comm, CFC.sqrt_eq_iff _ _ hCpsd.nonneg hYpsd.nonneg]
    exact hYsq
  -- G = A^{1/2} Y A^{1/2}
  have hGfromY : G = Ssqrt * Y * Ssqrt := by
    rw [hY]
    have h1 : Ssqrt * Sinv = 1 := hA.sqrt_mul_inverseSqrt
    have h2 : Sinv * Ssqrt = 1 := hA.inverseSqrt_mul_sqrt
    calc G = 1 * G * 1 := by rw [one_mul, mul_one]
      _ = (Ssqrt * Sinv) * G * (Sinv * Ssqrt) := by rw [h1, h2]
      _ = Ssqrt * (Sinv * G * Sinv) * Ssqrt := by noncomm_ring
  rw [hGfromY, hYeq]
  rfl

/-- Congruence by an invertible operator preserves positive-definiteness:
`IsUnit X → A.PosDef → (X · A · Xᴴ).PosDef` (`Xᴴ = star X` for matrices). -/
theorem _root_.IsUnit.isUnit_conj_posDef {n : ℕ} {X : Op n} (hX : IsUnit X)
    {A : Op n} (hA : A.PosDef) : (X * A * Xᴴ).PosDef := by
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := A) hX).mpr hA
  simpa [Matrix.star_eq_conjTranspose] using h

/-- **(GM4) Congruence-covariance of the geometric mean** (Ando 1979; Bhatia
IX.2): for invertible `X` and positive-semidefinite `B`,
`(X A Xᴴ) # (X B Xᴴ) = X (A # B) Xᴴ`.

The load-bearing key: with `X = σ^{-1/2}` it gives the σ-coordinate identity
`σ^{-1/2} (A # B) σ^{-1/2} = (σ^{-1/2} A σ^{-1/2}) # (σ^{-1/2} B σ^{-1/2})` used to
pull the reference-coordinate conjugation through `#`. The PSD hypothesis on `B`
is the regime the marginal-transport application lives in (`B₁, B₂` are PSD).

Proof: `G := X (A # B) Xᴴ` is PSD; using the Riccati equation
`(A#B) A⁻¹ (A#B) = B` (from `opGeoMean_eq_of_riccati` applied to the PSD square
root `√C`, `C = A^{-1/2}BA^{-1/2}`), and `(X A Xᴴ)⁻¹ = (Xᴴ)⁻¹ A⁻¹ X⁻¹`, `G`
satisfies the Riccati equation `G (X A Xᴴ)⁻¹ G = X B Xᴴ` for the conjugated pair;
uniqueness (`opGeoMean_eq_of_riccati`) gives `G = (X A Xᴴ) # (X B Xᴴ)`. -/
theorem opGeoMean_congr {n : ℕ} {A : Op n} (hA : A.PosDef) {B : Op n}
    (hB : B.PosSemidef) {X : Op n} (hX : IsUnit X) :
    opGeoMean (hX.isUnit_conj_posDef hA) (X * B * Xᴴ)
      = X * (opGeoMean hA B) * Xᴴ := by
  symm
  have hAposDef := hX.isUnit_conj_posDef hA
  -- G := X (A#B) Xᴴ is PSD
  have hGpsd : (X * (opGeoMean hA B) * Xᴴ).PosSemidef := by
    have h := (opGeoMean_posSemidef hA hB).mul_mul_conjTranspose_same X
    simpa [mul_assoc] using h
  -- The Riccati equation for the original pair: (A#B) A⁻¹ (A#B) = B.
  have hric0 : (opGeoMean hA B) * A⁻¹ * (opGeoMean hA B) = B := by
    set S : Op n := hA.inverseSqrt with hS
    set Ssq : Op n := CFC.sqrt A with hSsq
    set C : Op n := S * B * S with hC
    have hCpsd : C.PosSemidef := by
      have h := hB.mul_mul_conjTranspose_same S
      rwa [hA.inverseSqrt_isHermitian.eq] at h
    have hsqrtC : CFC.sqrt C * CFC.sqrt C = C := CFC.sqrt_mul_sqrt_self C hCpsd.nonneg
    have hAinv : A⁻¹ = S * S := (hA.inverseSqrt_sq).symm
    have h1 : Ssq * S = 1 := hA.sqrt_mul_inverseSqrt
    have h2 : S * Ssq = 1 := hA.inverseSqrt_mul_sqrt
    -- A#B = Ssq * √C * Ssq, and (Ssq √C Ssq)(S S)(Ssq √C Ssq) = Ssq √C √C Ssq = Ssq C Ssq = B
    have hGdef : opGeoMean hA B = Ssq * CFC.sqrt C * Ssq := rfl
    rw [hGdef, hAinv]
    calc Ssq * CFC.sqrt C * Ssq * (S * S) * (Ssq * CFC.sqrt C * Ssq)
        = Ssq * CFC.sqrt C * (Ssq * S) * (S * Ssq) * CFC.sqrt C * Ssq := by noncomm_ring
      _ = Ssq * CFC.sqrt C * 1 * 1 * CFC.sqrt C * Ssq := by rw [h1, h2]
      _ = Ssq * (CFC.sqrt C * CFC.sqrt C) * Ssq := by noncomm_ring
      _ = Ssq * C * Ssq := by rw [hsqrtC]
      _ = Ssq * (S * B * S) * Ssq := by rw [hC]
      _ = (Ssq * S) * B * (S * Ssq) := by noncomm_ring
      _ = B := by rw [h1, h2, one_mul, mul_one]
  -- conjugated inverse: (X A Xᴴ)⁻¹ = (Xᴴ)⁻¹ A⁻¹ X⁻¹
  have hXunit : IsUnit X := hX
  have hXAXH_inv : (X * A * Xᴴ)⁻¹ = (Xᴴ)⁻¹ * A⁻¹ * X⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    -- (X A Xᴴ)⁻¹ = (Xᴴ)⁻¹ * (X A)⁻¹ = (Xᴴ)⁻¹ * (A⁻¹ * X⁻¹)
    rw [mul_assoc]
  -- Riccati for the conjugated pair, discharged via hric0.
  apply opGeoMean_eq_of_riccati hAposDef hGpsd
  rw [hXAXH_inv]
  have hXinvX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det X).mp hX)
  have hXHunit : IsUnit (Xᴴ) := (Matrix.isUnit_conjTranspose X).mpr hX
  have hXHXHinv : Xᴴ * (Xᴴ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Xᴴ ((Matrix.isUnit_iff_isUnit_det Xᴴ).mp hXHunit)
  calc (X * opGeoMean hA B * Xᴴ) * ((Xᴴ)⁻¹ * A⁻¹ * X⁻¹) * (X * opGeoMean hA B * Xᴴ)
      = X * opGeoMean hA B * (Xᴴ * (Xᴴ)⁻¹) * A⁻¹ * (X⁻¹ * X) * opGeoMean hA B * Xᴴ := by
        noncomm_ring
    _ = X * opGeoMean hA B * 1 * A⁻¹ * 1 * opGeoMean hA B * Xᴴ := by rw [hXHXHinv, hXinvX]
    _ = X * (opGeoMean hA B * A⁻¹ * opGeoMean hA B) * Xᴴ := by noncomm_ring
    _ = X * B * Xᴴ := by rw [hric0]

end Quantum.Operators

end -- noncomputable section
