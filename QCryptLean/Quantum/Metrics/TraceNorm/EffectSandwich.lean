import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.InfoTheory.DistanceBounds.TraceNormContraction

/-!
# The effect-sandwich trace-norm bound

For a positive semidefinite `P` and an effect `0 ⪯ G ⪯ 1` on the same space, the sandwiched
operator `G P G` differs from `P` in trace norm by at most the square root of the trace gap:

```
‖P − G P G‖₁ ≤ √((Tr P − Tr (G P G)) · (Tr P + 3 · Tr (G P G)))      (sharp face)
             ≤ 2 · √(Tr P · (Tr P − Tr (G P G)))                     (homogeneous face)
```

The matrix-analysis sources
are Bhatia, *Matrix Analysis*, Thm IV.2.2 and Prob. IV.5.4 (the symmetrised-product trace-norm
bound) and Watrous, *The Theory of Quantum Information*, §1.1.3 (`‖W Wᴴ‖₁ = ‖W‖_F²`); the effect
inequality `G ⪰ G²` is Bhatia V.1.8 at `α = 1/2`.

## Main results

* `traceNorm_sub_effectSandwich_le_sharp` — the sharp face.
* `traceNorm_sub_effectSandwich_le_homogeneous` — the homogeneous face.

Both at `P G : Op d` with `P.PosSemidef`, `G.PosSemidef` and `(1 − G).PosSemidef`.

## The route

With `X := √P`, `Y := G X`, `U := X + Y` and `V := X − Y`, the algebraic core is

```
X Xᴴ − Y Yᴴ = W₊ W₊ᴴ − W₋ W₋ᴴ ,   W± := a • U ± b • V ,   4 a b = 1 ,
```

so the trace-norm triangle plus `‖W Wᴴ‖₁ = Tr (W Wᴴ)` gives
`‖X Xᴴ − Y Yᴴ‖₁ ≤ 2 a² ‖U‖_F² + 2 b² ‖V‖_F²`, and the scale `a, b` is then optimised to
`‖U‖_F ‖V‖_F` (`traceNorm_sub_mulConjTranspose_le_frobenius`).  Writing `p = Tr P`,
`f = Tr (P G)`, `q = Tr (G P G)`, the two Frobenius quantities are exactly `p ± 2 f + q`, so the
product is `(p + q)² − 4 f²`; the effect inequalities `q ≤ f ≤ p` then give the two faces.

## Sharpness and hypotheses

The sharp face is attained: at `d = 2`, `G = diag (1, 0)` and `P = x xᴴ` with
`x = (√(1 − e), √e)` both sides equal `√(4 e − 3 e²)`, so the constant `2` in the homogeneous
face cannot be lowered.  Each hypothesis is pinned by a counterexample.  Dropping
`G.PosSemidef`: at `G = diag (−1, 1)` and `x = (1, 1)/√2` one has `Tr P = Tr (G P G) = 1` while
`‖P − G P G‖₁ = 2`.  Dropping `(1 − G).PosSemidef`: at `G = diag (√2, 0)` on the same `x` one has
`Tr P = Tr (G P G) = 1` while `‖P − G P G‖₁ = √2`.  In both the right-hand side vanishes.
No rank hypothesis on `P` is used, and none is needed.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

variable {d : ℕ}

/-! ### Trace norm of a Gram operator -/

/-- `‖W Wᴴ‖₁ = Tr (W Wᴴ)`: the Gram operator is positive semidefinite, so its trace norm is its
trace.  (Watrous, *TQI* §1.1.3.) -/
lemma traceNorm_mulConjTranspose_self [NeZero d] (W : Op d) :
    traceNorm (W * W†) = (W * W†).trace.re := by
  have h : (W * W†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
  rw [traceNorm_hermitian_eq _ h.1]
  exact Quantum.Metrics.traceNormHermitian_of_posSemidef _ h

/-- The trace norm of the zero operator vanishes. -/
lemma traceNorm_zero_op [NeZero d] : traceNorm (0 : Op d) = 0 := by
  rw [traceNorm_hermitian_eq _ (Matrix.isHermitian_zero (n := Fin d) (α := ℂ))]
  exact (traceNormHermitian_eq_zero_iff _ _).mpr rfl

/-! ### The two algebraic identities -/

/-- Step 2 of the derivation: the symmetrised product of the sum and the difference is twice the
difference of the two Gram operators. -/
lemma sub_mulConjTranspose_eq_half_symmetrised (X Y : Op d) :
    (X + Y) * (X - Y)† + (X - Y) * (X + Y)† = (X * X† - Y * Y†) + (X * X† - Y * Y†) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
  noncomm_ring

/-- Step 3 of the derivation: with a free scale `a, b` subject to `4 a b = 1`, the difference of
two Gram operators is itself a difference of two Gram operators. -/
lemma symmetrised_eq_psd_difference (X Y : Op d) {a b : ℝ} (hab : 4 * a * b = 1) :
    X * X† - Y * Y†
      = ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y))†
        - ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y))† := by
  have hstar : ∀ (c : ℝ) (A : Op d), ((c : ℂ) • A)† = (c : ℂ) • A† := by
    intro c A
    simp [Matrix.conjTranspose_smul]
  have hexpand :
      ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y))†
        - ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y))†
        = ((2 * a * b : ℝ) : ℂ) • ((X + Y) * (X - Y)† + (X - Y) * (X + Y)†) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hstar, add_mul, mul_add,
      sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_sub]
    match_scalars <;> ring
  have hcoeff : ((2 * a * b : ℝ) : ℂ) + ((2 * a * b : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_add]
    norm_cast
    linarith
  rw [hexpand, sub_mulConjTranspose_eq_half_symmetrised X Y, smul_add, ← add_smul, hcoeff,
    one_smul]

/-! ### The scaled trace-norm bound -/

/-- Step 4 of the derivation: for every scale `a, b` with `4 a b = 1`, the trace norm of the
difference of two Gram operators is bounded by the scaled sum of the two Frobenius squares. -/
theorem traceNorm_sub_le_half_scaled_frobenius [NeZero d] (X Y : Op d) {a b : ℝ}
    (hab : 4 * a * b = 1) :
    traceNorm (X * X† - Y * Y†)
      ≤ 2 * a ^ 2 * ((X + Y) * (X + Y)†).trace.re
        + 2 * b ^ 2 * ((X - Y) * (X - Y)†).trace.re := by
  have hstar : ∀ (c : ℝ) (A : Op d), ((c : ℂ) • A)† = (c : ℂ) • A† := by
    intro c A
    simp [Matrix.conjTranspose_smul]
  set U : Op d := X + Y with hU
  set V : Op d := X - Y with hV
  set Wp : Op d := (a : ℂ) • U + (b : ℂ) • V with hWp
  set Wm : Op d := (a : ℂ) • U - (b : ℂ) • V with hWm
  have hsplit : X * X† - Y * Y† = Wp * Wp† - Wm * Wm† :=
    symmetrised_eq_psd_difference X Y hab
  have hPp : (Wp * Wp†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Wp
  have hPm : (Wm * Wm†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Wm
  have hneg : ((-(Wm * Wm†) : Op d)).IsHermitian := hPm.1.neg
  -- triangle inequality for the Hermitian difference
  have htri : traceNorm (Wp * Wp† - Wm * Wm†)
      ≤ traceNorm (Wp * Wp†) + traceNorm (Wm * Wm†) := by
    have hsum : (Wp * Wp† - Wm * Wm†) = (Wp * Wp†) + (-(Wm * Wm†)) := by abel
    have hflip : traceNormHermitian (-(Wm * Wm†)) hneg = traceNormHermitian (Wm * Wm†) hPm.1 :=
      traceNormHermitian_neg _ hPm.1
    rw [hsum, traceNorm_hermitian_eq _ (hPp.1.add hneg),
      traceNorm_hermitian_eq _ hPp.1, traceNorm_hermitian_eq _ hPm.1, ← hflip]
    exact traceNormHermitian_triangle _ _ hPp.1 hneg
  -- the two Gram traces add up to the scaled Frobenius sum
  have hsumMat : Wp * Wp† + Wm * Wm†
      = ((2 * a ^ 2 : ℝ) : ℂ) • (U * U†) + ((2 * b ^ 2 : ℝ) : ℂ) • (V * V†) := by
    simp only [hWp, hWm, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hstar, add_mul,
      mul_add, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    match_scalars <;> ring
  have htrace : (Wp * Wp†).trace.re + (Wm * Wm†).trace.re
      = 2 * a ^ 2 * (U * U†).trace.re + 2 * b ^ 2 * (V * V†).trace.re := by
    have h0 : (Wp * Wp† + Wm * Wm†).trace
        = (((2 * a ^ 2 : ℝ) : ℂ) • (U * U†) + ((2 * b ^ 2 : ℝ) : ℂ) • (V * V†)).trace :=
      congrArg Matrix.trace hsumMat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul] at h0
    have hre := congrArg Complex.re h0
    rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
    exact hre
  rw [hsplit]
  calc traceNorm (Wp * Wp† - Wm * Wm†)
      ≤ traceNorm (Wp * Wp†) + traceNorm (Wm * Wm†) := htri
    _ = (Wp * Wp†).trace.re + (Wm * Wm†).trace.re := by
        rw [traceNorm_mulConjTranspose_self, traceNorm_mulConjTranspose_self]
    _ = _ := htrace

/-- Steps 4 and 8′ of the derivation: optimising the scale gives the Cauchy–Schwarz form
`‖X Xᴴ − Y Yᴴ‖₁ ≤ ‖X + Y‖_F · ‖X − Y‖_F`. -/
theorem traceNorm_sub_mulConjTranspose_le_frobenius [NeZero d] (X Y : Op d) :
    traceNorm (X * X† - Y * Y†)
      ≤ Real.sqrt (((X + Y) * (X + Y)†).trace.re * ((X - Y) * (X - Y)†).trace.re) := by
  have hzero : ∀ W : Op d, (W * W†).trace.re = 0 → W = 0 := by
    intro W hW
    have hpsd : (W * W†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
    have hnn := hpsd.trace_nonneg
    have him : (W * W†).trace.im = 0 := ((Complex.nonneg_iff.mp hnn).2).symm
    exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (Complex.ext hW him)
  set U : Op d := X + Y with hU
  set V : Op d := X - Y with hV
  set nU : ℝ := (U * U†).trace.re with hnU
  set nV : ℝ := (V * V†).trace.re with hnV
  have hUpsd : (U * U†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose U
  have hVpsd : (V * V†).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hnU0 : 0 ≤ nU := (Complex.nonneg_iff.mp hUpsd.trace_nonneg).1
  have hnV0 : 0 ≤ nV := (Complex.nonneg_iff.mp hVpsd.trace_nonneg).1
  rcases eq_or_lt_of_le hnU0 with hU0 | hUpos
  · -- `X + Y = 0`, so the two Gram operators coincide
    have hUeq : U = 0 := hzero U hU0.symm
    have hXY : Y = -X := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hUeq
    have hMzero : X * X† - Y * Y† = 0 := by
      rw [hXY, Matrix.conjTranspose_neg, neg_mul_neg]
      abel
    rw [hMzero, traceNorm_zero_op]
    exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hnV0 with hV0 | hVpos
  · -- `X − Y = 0`, same conclusion
    have hVeq : V = 0 := hzero V hV0.symm
    have hXY : Y = X := (sub_eq_zero.mp hVeq).symm
    have hMzero : X * X† - Y * Y† = 0 := by rw [hXY]; abel
    rw [hMzero, traceNorm_zero_op]
    exact Real.sqrt_nonneg _
  -- the generic branch: the scale that equalises the two terms
  have hUne : nU ≠ 0 := ne_of_gt hUpos
  have hVne : nV ≠ 0 := ne_of_gt hVpos
  set r : ℝ := Real.sqrt (nU * nV) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (mul_pos hUpos hVpos)
  set a : ℝ := Real.sqrt (r / (4 * nU)) with ha
  set b : ℝ := Real.sqrt (r / (4 * nV)) with hb
  have hrU : 0 ≤ r / (4 * nU) := div_nonneg hrpos.le (mul_pos zero_lt_four hUpos).le
  have hrV : 0 ≤ r / (4 * nV) := div_nonneg hrpos.le (mul_pos zero_lt_four hVpos).le
  have ha2 : a ^ 2 = r / (4 * nU) := by rw [ha, Real.sq_sqrt hrU]
  have hb2 : b ^ 2 = r / (4 * nV) := by rw [hb, Real.sq_sqrt hrV]
  have hr2 : r ^ 2 = nU * nV := by rw [hr, Real.sq_sqrt (mul_pos hUpos hVpos).le]
  have hab : 4 * a * b = 1 := by
    -- `a b = √(r² / (16 nU nV)) = 1/4`.
    have hprod : a * b = Real.sqrt ((r / (4 * nU)) * (r / (4 * nV))) := by
      rw [ha, hb, ← Real.sqrt_mul hrU]
    have harg : (r / (4 * nU)) * (r / (4 * nV)) = (1 / 4 : ℝ) ^ 2 := by
      rw [div_mul_div_comm, ← pow_two, hr2]
      field_simp
    rw [mul_assoc, hprod, harg, Real.sqrt_sq (by norm_num)]
    norm_num
  have hbound := traceNorm_sub_le_half_scaled_frobenius X Y hab
  rw [← hU, ← hV, ← hnU, ← hnV] at hbound
  refine hbound.trans (le_of_eq ?_)
  rw [ha2, hb2]
  field_simp
  ring

/-! ### The effect inequalities -/

/-- An effect dominates its own square: `0 ⪯ G ⪯ 1 → G − G G ⪰ 0`.  (Bhatia V.1.8 at `α = 1/2`,
specialised.) -/
lemma posSemidef_sub_sq_of_le_one {G : Op d} (hG : G.PosSemidef)
    (hG1 : ((1 : Op d) - G).PosSemidef) :
    (G - G * G).PosSemidef := by
  set Gp : PosSemidefOp d := ⟨⟨G, hG.1⟩, posSemidef_re_quadraticForm_nonneg hG⟩ with hGp
  set S : Op d := sqrtPosSemidefOp Gp with hS
  have hSS : S * S = G := sqrtPosSemidefOp_sq Gp
  have hSh : S† = S := sqrtPosSemidefOp_isHermitian Gp
  have hcomm : S * G = G * S := by rw [← hSS, ← mul_assoc]
  have hkey : S * ((1 : Op d) - G) * S† = G - G * G := by
    rw [hSh, show S * ((1 : Op d) - G) * S = S * S - S * G * S by noncomm_ring, hSS, hcomm,
      mul_assoc, hSS]
  rw [← hkey]
  exact hG1.mul_mul_conjTranspose_same S

/-! ### The two faces -/

/-- **The effect-sandwich trace-norm bound, sharp face.**  For `P` positive semidefinite and `G`
an effect (`0 ⪯ G ⪯ 1`),

```
‖P − G P G‖₁ ≤ √((Tr P − Tr (G P G)) · (Tr P + 3 · Tr (G P G))) .
```

The bound is
attained at `G = diag (1, 0)` and `P = x xᴴ`, `x = (√(1 − e), √e)`.  No rank hypothesis on `P`. -/
theorem traceNorm_sub_effectSandwich_le_sharp [NeZero d] {P G : Op d}
    (hP : P.PosSemidef) (hG : G.PosSemidef) (hG1 : ((1 : Op d) - G).PosSemidef) :
    traceNorm (P - G * P * G)
      ≤ Real.sqrt ((P.trace.re - (G * P * G).trace.re)
          * (P.trace.re + 3 * (G * P * G).trace.re)) := by
  set Pp : PosSemidefOp d := ⟨⟨P, hP.1⟩, posSemidef_re_quadraticForm_nonneg hP⟩ with hPp
  set X : Op d := sqrtPosSemidefOp Pp with hX
  set Y : Op d := G * X with hY
  have hXX2 : X * X = P := sqrtPosSemidefOp_sq Pp
  have hXh : X† = X := sqrtPosSemidefOp_isHermitian Pp
  have hGh : G† = G := hG.1
  have hXXd : X * X† = P := by rw [hXh, hXX2]
  have hYYd : Y * Y† = G * P * G := by
    rw [hY, Matrix.conjTranspose_mul, hXh, hGh, mul_assoc G X (X * G), ← mul_assoc X X G,
      ← mul_assoc, hXX2]
  have hXYd : X * Y† = P * G := by
    rw [hY, Matrix.conjTranspose_mul, hXh, hGh, ← mul_assoc, hXX2]
  have hYXd : Y * X† = G * P := by rw [hY, hXh, mul_assoc, hXX2]
  set p : ℝ := P.trace.re with hp
  set q : ℝ := (G * P * G).trace.re with hq
  set f : ℝ := (P * G).trace.re with hf
  -- the two Frobenius squares, exactly
  have hUexp : (X + Y) * (X + Y)† = P + P * G + G * P + G * P * G := by
    rw [Matrix.conjTranspose_add, add_mul, mul_add, mul_add, hXXd, hXYd, hYXd, hYYd,
      ← add_assoc]
  have hVexp : (X - Y) * (X - Y)† = P - P * G - G * P + G * P * G := by
    rw [Matrix.conjTranspose_sub, sub_mul, mul_sub, mul_sub, hXXd, hXYd, hYXd, hYYd]
    abel
  have hGP : (G * P).trace = (P * G).trace := Matrix.trace_mul_comm G P
  have hnU : ((X + Y) * (X + Y)†).trace.re = p + 2 * f + q := by
    rw [hUexp]
    simp only [Matrix.trace_add, Complex.add_re, hGP]
    rw [hp, hf, hq]; ring
  have hnV : ((X - Y) * (X - Y)†).trace.re = p - 2 * f + q := by
    rw [hVexp]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, hGP]
    rw [hp, hf, hq]; ring
  -- the effect inequalities `0 ≤ q ≤ f ≤ p`
  have hcyc : (G * P * G).trace = (P * (G * G)).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm G (P * G), mul_assoc]
  have hfq : q ≤ f := by
    have h := trace_mul_psd_nonneg P (G - G * G) hP (posSemidef_sub_sq_of_le_one hG hG1)
    rw [mul_sub] at h
    simp only [Matrix.trace_sub, Complex.sub_re] at h
    rw [hq, hcyc, hf]
    linarith
  have hfp : f ≤ p := by
    have h := trace_mul_psd_nonneg P ((1 : Op d) - G) hP hG1
    rw [mul_sub, mul_one] at h
    simp only [Matrix.trace_sub, Complex.sub_re] at h
    rw [hp, hf]
    linarith
  have hq0 : 0 ≤ q := by
    have hgpg := Matrix.PosSemidef.mul_mul_conjTranspose_same hP G
    rw [hGh] at hgpg
    rw [hq]
    exact (Complex.nonneg_iff.mp hgpg.trace_nonneg).1
  have hmaster := traceNorm_sub_mulConjTranspose_le_frobenius X Y
  rw [hXXd, hYYd, hnU, hnV] at hmaster
  refine hmaster.trans (Real.sqrt_le_sqrt ?_)
  -- `(p - q)(p + 3q) - (p + 2f + q)(p - 2f + q) = 4 (f - q)(f + q) ≥ 0`, as `0 ≤ q ≤ f`.
  have hkey : 0 ≤ (f - q) * (f + q) := mul_nonneg (sub_nonneg.mpr hfq) (by linarith)
  rw [← sub_nonneg]
  calc 0 ≤ 4 * ((f - q) * (f + q)) := mul_nonneg zero_le_four hkey
    _ = _ := by ring

/-- **The effect-sandwich trace-norm bound, homogeneous face.**  For `P` positive semidefinite and
`G` an effect (`0 ⪯ G ⪯ 1`),

```
‖P − G P G‖₁ ≤ 2 · √(Tr P · (Tr P − Tr (G P G))) .
```

The constant `2`
is not improvable: the ratio of this face to `traceNorm_sub_effectSandwich_le_sharp` tends to `1`
along the family `G = diag (1, 0)`, `P = x xᴴ` with `x = (√(1 − e), √e)`, `e → 0`.  No rank
hypothesis on `P`. -/
theorem traceNorm_sub_effectSandwich_le_homogeneous [NeZero d] {P G : Op d}
    (hP : P.PosSemidef) (hG : G.PosSemidef) (hG1 : ((1 : Op d) - G).PosSemidef) :
    traceNorm (P - G * P * G)
      ≤ 2 * Real.sqrt (P.trace.re * (P.trace.re - (G * P * G).trace.re)) := by
  have hsharp := traceNorm_sub_effectSandwich_le_sharp hP hG hG1
  set p : ℝ := P.trace.re with hp
  set q : ℝ := (G * P * G).trace.re with hq
  have hq0 : 0 ≤ q := by
    have hgpg := Matrix.PosSemidef.mul_mul_conjTranspose_same hP G
    rw [hG.1] at hgpg
    rw [hq]
    exact (Complex.nonneg_iff.mp hgpg.trace_nonneg).1
  have hp0 : 0 ≤ p := by
    rw [hp]
    exact (Complex.nonneg_iff.mp hP.trace_nonneg).1
  refine hsharp.trans ?_
  by_cases hlt : 0 < p - q
  · have h2 : Real.sqrt (4 * (p * (p - q))) = 2 * Real.sqrt (p * (p - q)) := by
      rw [show (4 : ℝ) * (p * (p - q)) = 2 ^ 2 * (p * (p - q)) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [← h2]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hlt.le (show (0 : ℝ) ≤ 3 * (p - q) by linarith)]
  · have hle : p - q ≤ 0 := not_lt.mp hlt
    have h1 : Real.sqrt ((p - q) * (p + 3 * q)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hle (by linarith))
    rw [h1]
    positivity

end Quantum.Metrics

end
