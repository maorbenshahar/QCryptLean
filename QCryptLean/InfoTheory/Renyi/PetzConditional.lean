import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.TensorProducts.CastDim
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.Foundations
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Petz conditional Rényi entropy — the DOWN variant, and its nonnegativity on cq states

Statement surface for Dupuis–Fawzi's `H'_α(A|B)`, the **Petz** conditional Rényi entropy
with the reference operator **pinned** to the marginal `ρ_B` (the "down" variant).

Source: arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex`,
`\label{def:petz-renyi-divergence}` at `:294` (the divergence `D'_α`) and the notation
table at `:254` (`H'_α(A|B)_ρ := −D'_α(ρ_AB ‖ 1_A ⊗ ρ_B)`).

## Variant discipline

Three inequivalent objects sit within one line of each other in the source; this file
formalises exactly one of them.

* **Petz**, not sandwiched. `D'_α(ρ‖σ) = 1/(α−1) · log Tr[ρ^α σ^{1−α}]` (`:294`, label
  `def:petz-renyi-divergence`). The *sandwiched* divergence (`:285`) is
  `1/(α−1) · log Tr[(σ^{(1−α)/2α} ρ σ^{(1−α)/2α})^α]` and is a different quantity; the
  two are related by `D_α ≤ D'_α` (`:782`), which is **not** proved here.
* **DOWN**, not up. `:254` pins the second argument to `1_A ⊗ ρ_B`; there is no
  optimisation over reference states. The up variant satisfies `H'^↑ ≥ H'^↓`, so a
  theorem about the up variant is strictly weaker and does not discharge the uses at
  `:450`, `:877` or `:973`.
* **Base 2** logarithms (`:246`).

## Main declarations

* `petzTrace` — `Tr[ρ^α σ^{1−α}]`, the argument of `D'_α`.
* `petzRenyiDivergence` — `D'_α(ρ‖σ)` on the branch `1 < α ≤ 2`, `Supp ρ ⊆ Supp σ`.
* `condPetzRenyiDown` — `H'_α(X|B)_ρ` for a classical-quantum state.
* `condRenyiPetz_nonneg_of_cq` — `0 ≤ H'_α(X|B)_ρ` for `α ∈ (1,2]`.
* `condVonNeumann_nonneg_of_cq` — `0 ≤ H(X|B)_ρ`.
* `renyiCondEntropy_down_tensorPower` — `H'_α(X^m|B^m)_{ρ^{⊗m}} = m · H'_α(X|B)_ρ`.

## Exponent convention

`CFC.rpow` at a negative exponent is the support pseudo-inverse power:
`CFC.rpow a y = cfc (fun t : ℝ≥0 => t ^ y) a` and `NNReal.rpow 0 y = 0` for `y ≠ 0`.
On `Supp ρ ⊆ Supp σ` — which is what `:294` assumes on this branch, and which holds
automatically for the cq instance below since `σ_x ≤ ρ_B` — this agrees with the
source's convention.

## Scope

`Matrix.Norms.L2Operator` is opened because the `CStarRing` / `NormedRing` /
`NormedAlgebra` instances on `Matrix m m ℂ` are `scoped` in it
(`Mathlib/Analysis/CStarAlgebra/Matrix.lean`), and `CFC.rpow` needs them.
-/

open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

/-!
## The Petz Rényi divergence
-/

/-- `Tr[ρ^α σ^{1−α}]`, the argument of the Petz Rényi divergence
(Dupuis–Fawzi `\label{def:petz-renyi-divergence}`, `:294`).

Both powers are `CFC.rpow`; at the negative exponent `1 − α < 0` this is the support
pseudo-inverse power (see the module docstring). The index type is left general because
the cq instance below evaluates it on `Matrix (Fin n × X) (Fin n × X) ℂ`, not on
`Op n`. -/
def petzTrace {m : Type*} [Fintype m] [DecidableEq m]
    (α : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  ((ρ ^ (α : ℝ)) * (σ ^ (1 - α : ℝ))).trace.re

/-- `D'_α(ρ‖σ) = 1/(α−1) · log₂ Tr[ρ^α σ^{1−α}]`, Dupuis–Fawzi `:294`.

This is the `1 < α ≤ 2`, `Supp ρ ⊆ Supp σ` branch of `:294` only. The `α = 1`,
`0 < α < 1` and out-of-support (`+∞`) branches of that definition are **not** part of
this declaration and must not be assumed of it. -/
def petzRenyiDivergence {m : Type*} [Fintype m] [DecidableEq m]
    (α : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  (1 / (α - 1)) * Real.logb 2 (petzTrace α ρ σ)

/-!
## The conditional entropy on a classical-quantum state
-/

/-- `H'_α(X|B)_ρ = −D'_α(ρ_XB ‖ 1_X ⊗ ρ_B)` for a classical-quantum state,
Dupuis–Fawzi `:254`. **Petz, DOWN**: the second argument is the marginal `ρ_B`,
pinned, not optimised.

In the project's block-diagonal layout for cq states (`CQState.toJointOp`, which is
`Matrix.blockDiagonal (fun x => (stateMap x).toOp)` on `Fin n × X`), the reference
`1_X ⊗ ρ_B` is `Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)`. -/
def condPetzRenyiDown {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) : ℝ :=
  - petzRenyiDivergence α ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))

/-!
## Operator-monotonicity toolkit

The mathematical content of both obligations is Dupuis–Fawzi `:493`: for `0 ≤ Xm ≤ Ym`,
operator monotonicity of `t ↦ t^ν` on `ν ∈ (0,1]` (Löwner–Heinz) bounds
`Tr[Xm^{1+ν} Ym^{-ν}] ≤ Tr[Xm]`, and its `ν → 0` shadow bounds
`Tr[Xm log Xm] ≤ Tr[Xm log Ym]`.

Everything here is stated on a general square-matrix algebra `Matrix m m ℂ` because the
cq instance evaluates it on the block-diagonal joint operator over `Fin n × X`, not on
`Op n`. Since the real spectrum of a matrix is finite (`Matrix.finite_real_spectrum`),
*every* real function is `ContinuousOn` it (`contOn_spec`); this is what makes the
`cfc`-side conditions of the negative powers and of `Real.log` discharge without any
positive-definiteness hypothesis.
-/

section Toolkit

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `CStarAlgebra (Matrix m m ℂ)`, assembled from the `Matrix.Norms.L2Operator` scoped
`NormedRing` / `NormedAlgebra` / `CStarRing` instances that are already open in this file.
Löwner–Heinz (`CFC.rpow_le_rpow`), the C⋆-identity and `CFC.log_le_log` are all stated for
`[CStarAlgebra A]`. Declared as a `local instance` so the L2Operator `NormedRing` does not
leak into downstream typeclass synthesis (same pattern as
`InfoTheory.DeFinetti.instCStarAlgebraOp_def`). -/
@[implicit_reducible] private noncomputable def instCStarAlgebraMatrix
    (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

attribute [local instance] instCStarAlgebraMatrix

/-- The real matrix power `A ^ (r : ℝ)` (`CFC.rpow`), stated once for this section. It is the
instance typeclass search finds; declaring it short-circuits that search, which is slow here and
would otherwise rerun at every `^`. -/
private local instance instHPowRealMatrix : HPow (Matrix m m ℂ) ℝ (Matrix m m ℂ) :=
  inferInstance

/-- The real spectrum of a matrix is finite, hence discrete, hence every real function is
continuous on it. This is what lets `cfc` be used at `t ^ (-ν)` and at `Real.log`, both of
which are discontinuous at `0`, without excluding singular operators. -/
private lemma contOn_spec (f : ℝ → ℝ) (a : Matrix m m ℂ) : ContinuousOn f (spectrum ℝ a) :=
  (Matrix.finite_real_spectrum (A := a)).continuousOn f

omit [DecidableEq m] in
/-- Conjugation preserves the Loewner order. -/
private lemma conj_le_conj (A B R : Matrix m m ℂ) (h : A ≤ B) : Rᴴ * A * R ≤ Rᴴ * B * R := by
  rw [Matrix.le_iff] at h ⊢
  rw [show Rᴴ * B * R - Rᴴ * A * R = Rᴴ * (B - A) * R by rw [mul_sub, sub_mul]]
  exact h.conjTranspose_mul_mul_same _

omit [DecidableEq m] in
/-- The Loewner order dominates the real trace. -/
private lemma trace_re_mono (A B : Matrix m m ℂ) (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  rw [Matrix.le_iff] at h
  have h2 := h.trace_nonneg
  rw [Matrix.trace_sub] at h2
  have h3 := (Complex.nonneg_iff.mp h2).1
  simp only [Complex.sub_re] at h3
  linarith

omit [Fintype m] [DecidableEq m] in
private lemma selfadj_of_nonneg {A : Matrix m m ℂ} (h : 0 ≤ A) : Aᴴ = A :=
  (Matrix.nonneg_iff_posSemidef.mp h).isHermitian

omit [DecidableEq m] in
private lemma conj_nonneg (D R : Matrix m m ℂ) (hD : 0 ≤ D) : 0 ≤ Rᴴ * D * R := by
  simpa using conj_le_conj 0 D R hD

/-- `CFC.rpow` through the real functional calculus, where the spectrum is finite. -/
private lemma rpow_eq_cfc (a : Matrix m m ℂ) (ha : 0 ≤ a) (y : ℝ) :
    a ^ y = cfc (fun t : ℝ => t ^ y) a := CFC.rpow_eq_cfc_real ha

private lemma rpow_mul_rpow_eq (a : Matrix m m ℂ) (ha : 0 ≤ a) (x y : ℝ) :
    a ^ x * a ^ y = cfc (fun t : ℝ => t ^ x * t ^ y) a := by
  rw [rpow_eq_cfc a ha x, rpow_eq_cfc a ha y,
    ← cfc_mul _ _ a (contOn_spec _ a) (contOn_spec _ a)]

/-- `a^x · a^y = a^(x+y)` for a positive semidefinite `a`, with **no** invertibility
hypothesis (unlike Mathlib's `CFC.rpow_add`). The three `≠ 0` side conditions are exactly
what the pseudo-inverse convention `0 ^ y = 0` (`y ≠ 0`) needs at the kernel of `a`. -/
private lemma rpow_add_ne (a : Matrix m m ℂ) (ha : 0 ≤ a) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) : a ^ x * a ^ y = a ^ (x + y) := by
  rw [rpow_mul_rpow_eq a ha x y, rpow_eq_cfc a ha (x + y)]
  refine cfc_congr fun t ht => ?_
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg ha ht) with h | h
  · simp [← h, Real.zero_rpow hx, Real.zero_rpow hy, Real.zero_rpow hxy]
  · rw [Real.rpow_add h]

private lemma rpow_half_mul_self (a : Matrix m m ℂ) (ha : 0 ≤ a) :
    a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rw [rpow_add_ne a ha (by norm_num) (by norm_num) (by norm_num),
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, CFC.rpow_one a ha]

/-- `a^{-ν/2} a^ν a^{-ν/2}` is the support projection of `a`, hence `≤ 1`. -/
private lemma rpow_sandwich_self_le_one (a : Matrix m m ℂ) (ha : 0 ≤ a) {ν : ℝ} (hν : 0 < ν) :
    a ^ (-ν / 2) * a ^ ν * a ^ (-ν / 2) ≤ 1 := by
  rw [rpow_mul_rpow_eq a ha (-ν / 2) ν, rpow_eq_cfc a ha (-ν / 2),
    ← cfc_mul _ _ a (contOn_spec _ a) (contOn_spec _ a)]
  refine cfc_le_one _ _ fun t ht => ?_
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg ha ht) with h | h
  · simp [← h, Real.zero_rpow (by linarith : -ν / 2 ≠ 0), Real.zero_rpow hν.ne']
  · rw [← Real.rpow_add h, ← Real.rpow_add h,
      show -ν / 2 + ν + -ν / 2 = 0 by ring, Real.rpow_zero]

/-- **The Löwner–Heinz step**, Dupuis–Fawzi `:493` with the exponent `-1/2` generalised to
`-ν`: for `0 ≤ A ≤ B` and `ν ∈ (0,1]`, `A^{ν/2} B^{-ν} A^{ν/2} ≤ 1`.

`ν ≤ 1` is used exactly once, in `CFC.rpow_le_rpow`; that is the whole reason the range of
the main theorem is `(1,2]`. Douglas' lemma is replaced by the C⋆-identity
`‖T*T‖ = ‖T‖² = ‖TT*‖`, which is in Mathlib. -/
private lemma sandwich_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    A ^ (ν / 2) * B ^ (-ν) * A ^ (ν / 2) ≤ 1 := by
  have hB : 0 ≤ B := hA.trans hAB
  -- The half exponents are nonzero, and each pair of halves adds up to the full exponent.
  have hν2 : (ν / 2 : ℝ) ≠ 0 := (half_pos hν0).ne'
  have hnν2 : (-ν / 2 : ℝ) ≠ 0 := by rw [neg_div]; exact neg_ne_zero.mpr hν2
  have hsaA : (A ^ (ν / 2 : ℝ))ᴴ = A ^ (ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  have hsaB : (B ^ (-ν / 2 : ℝ))ᴴ = B ^ (-ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  set T : Matrix m m ℂ := B ^ (-ν / 2 : ℝ) * A ^ (ν / 2 : ℝ) with hTdef
  have hTstar : star T = A ^ (ν / 2 : ℝ) * B ^ (-ν / 2 : ℝ) := by
    rw [hTdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hsaA, hsaB]
  have hTT : star T * T = A ^ (ν / 2 : ℝ) * B ^ (-ν) * A ^ (ν / 2 : ℝ) := by
    rw [hTstar, hTdef, ← mul_assoc, mul_assoc (A ^ (ν / 2 : ℝ)),
      rpow_add_ne B hB hnν2 hnν2 (by rw [add_halves]; exact neg_ne_zero.mpr hν0.ne'),
      add_halves]
  have hTTstar : T * star T = B ^ (-ν / 2 : ℝ) * A ^ ν * B ^ (-ν / 2 : ℝ) := by
    rw [hTstar, hTdef, ← mul_assoc, mul_assoc (B ^ (-ν / 2 : ℝ)),
      rpow_add_ne A hA hν2 hν2 (by rw [add_halves]; exact hν0.ne'), add_halves]
  have hstep : T * star T ≤ 1 := by
    rw [hTTstar]
    calc B ^ (-ν / 2 : ℝ) * A ^ ν * B ^ (-ν / 2 : ℝ)
        ≤ B ^ (-ν / 2 : ℝ) * B ^ ν * B ^ (-ν / 2 : ℝ) := by
          have := conj_le_conj (A ^ ν) (B ^ ν) (B ^ (-ν / 2 : ℝ))
            (CFC.rpow_le_rpow ⟨hν0.le, hν1⟩ hAB)
          rwa [hsaB] at this
      _ ≤ 1 := rpow_sandwich_self_le_one B hB hν0
  have hTTs_nonneg : 0 ≤ T * star T := by
    have := Matrix.posSemidef_conjTranspose_mul_self (star T)
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at this
    exact Matrix.nonneg_iff_posSemidef.mpr this
  have hsTT_nonneg : 0 ≤ star T * T := by
    have := Matrix.posSemidef_conjTranspose_mul_self T
    rw [← Matrix.star_eq_conjTranspose] at this
    exact Matrix.nonneg_iff_posSemidef.mpr this
  have hnorm1 : ‖T * star T‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hTTs_nonneg).mpr hstep
  have hnorm2 : ‖star T * T‖ ≤ 1 := by
    exact ((CStarRing.norm_star_mul_self (x := T)).trans
      (CStarRing.norm_self_mul_star (x := T)).symm).le.trans hnorm1
  rw [← hTT]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hsTT_nonneg).mp hnorm2

/-- **Dupuis–Fawzi `:493`, in trace form.** For `0 ≤ A ≤ B` and `ν ∈ (0,1]`,
`0 ≤ Tr[A^{1+ν} B^{-ν}] ≤ Tr[A]`. No support or positive-definiteness hypothesis is
needed: the sandwich by `A^{ν/2}` projects onto `Supp A ⊆ Supp B` automatically. -/
private lemma petzTrace_bound {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    0 ≤ (A ^ (1 + ν) * B ^ (-ν)).trace.re ∧
      (A ^ (1 + ν) * B ^ (-ν)).trace.re ≤ A.trace.re := by
  have hsaN : (A ^ (ν / 2 : ℝ))ᴴ = A ^ (ν / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  have hsaH : (A ^ (1 / 2 : ℝ))ᴴ = A ^ (1 / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  set M : Matrix m m ℂ := A ^ (ν / 2 : ℝ) * B ^ (-ν) * A ^ (ν / 2 : ℝ) with hMdef
  have hM1 : M ≤ 1 := sandwich_le_one hν0 hν1 A B hA hAB
  have hM0 : 0 ≤ M := by
    have := conj_nonneg (B ^ (-ν)) (A ^ (ν / 2 : ℝ)) CFC.rpow_nonneg
    rwa [hsaN] at this
  have hAnu : A ^ (ν / 2 : ℝ) * A * A ^ (ν / 2 : ℝ) = A ^ (1 + ν) := by
    have hAnu' : A ^ (ν / 2 : ℝ) * A ^ (1 : ℝ) * A ^ (ν / 2 : ℝ) = A ^ (1 + ν) := by
      rw [rpow_add_ne A hA (by positivity) one_ne_zero (by positivity),
        rpow_add_ne A hA (by positivity) (by positivity) (by positivity),
        show (ν / 2 + 1 + ν / 2 : ℝ) = 1 + ν by ring]
    rwa [CFC.rpow_one A hA] at hAnu'
  have htr : (A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ)).trace
      = (A ^ (1 + ν) * B ^ (-ν)).trace := by
    rw [Matrix.trace_mul_comm (A ^ (1 / 2 : ℝ) * M) (A ^ (1 / 2 : ℝ)), ← mul_assoc,
      rpow_half_mul_self A hA, hMdef, ← mul_assoc, ← mul_assoc,
      Matrix.trace_mul_comm (A * A ^ (ν / 2 : ℝ) * B ^ (-ν)) (A ^ (ν / 2 : ℝ)),
      ← mul_assoc, ← mul_assoc]
    congr 2
  refine ⟨?_, ?_⟩
  · rw [← htr]
    have h0 : (0 : Matrix m m ℂ) ≤ A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ) := by
      have := conj_nonneg M (A ^ (1 / 2 : ℝ)) hM0
      rwa [hsaH] at this
    simpa using trace_re_mono 0 _ h0
  · rw [← htr]
    have h1 : A ^ (1 / 2 : ℝ) * M * A ^ (1 / 2 : ℝ) ≤ A := by
      have := conj_le_conj M 1 (A ^ (1 / 2 : ℝ)) hM1
      rwa [hsaH, mul_one, rpow_half_mul_self A hA] at this
    exact trace_re_mono _ _ h1

omit [DecidableEq m] in
private lemma trace_mul_nonneg (A D : Matrix m m ℂ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ (A * D).trace.re := by
  classical
  have h := conj_nonneg D (A ^ (1 / 2 : ℝ)) hD
  rw [selfadj_of_nonneg (CFC.rpow_nonneg : (0 : Matrix m m ℂ) ≤ A ^ (1 / 2 : ℝ))] at h
  have htr : (A * D).trace = (A ^ (1 / 2 : ℝ) * D * A ^ (1 / 2 : ℝ)).trace := by
    rw [Matrix.trace_mul_comm (A ^ (1 / 2 : ℝ) * D) (A ^ (1 / 2 : ℝ)), ← mul_assoc,
      rpow_half_mul_self A hA]
  rw [htr]
  simpa using trace_re_mono 0 _ h

omit [DecidableEq m] in
private lemma trace_mul_mono (A C D : Matrix m m ℂ) (hA : 0 ≤ A) (h : C ≤ D) :
    (A * C).trace.re ≤ (A * D).trace.re := by
  have h2 := trace_mul_nonneg A (D - C) hA (sub_nonneg.mpr h)
  rw [mul_sub, Matrix.trace_sub] at h2
  simp only [Complex.sub_re] at h2
  linarith

private lemma isStrictlyPositive_smul_one {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive (ε • (1 : Matrix m m ℂ)) :=
  ⟨smul_nonneg hε.le zero_le_one,
    ⟨⟨ε • (1 : Matrix m m ℂ), ε⁻¹ • (1 : Matrix m m ℂ),
      by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hε.ne', one_smul],
      by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hε.ne', one_smul]⟩, rfl⟩⟩

private lemma add_smul_one_eq_cfc (a : Matrix m m ℂ) (ha : 0 ≤ a) (ε : ℝ) :
    a + ε • (1 : Matrix m m ℂ) = cfc (fun t : ℝ => t + ε) a := by
  rw [cfc_add a (fun t : ℝ => t) (fun _ : ℝ => ε) (contOn_spec _ a) (contOn_spec _ a),
    cfc_id' ℝ a ha.isSelfAdjoint, cfc_const ε a ha.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]

private lemma log_add_smul_one (a : Matrix m m ℂ) (ha : 0 ≤ a) (ε : ℝ) :
    CFC.log (a + ε • (1 : Matrix m m ℂ)) = cfc (fun t : ℝ => Real.log (t + ε)) a := by
  rw [add_smul_one_eq_cfc a ha ε]
  exact (cfc_comp Real.log (fun t : ℝ => t + ε) a ha.isSelfAdjoint
    (((Matrix.finite_real_spectrum (A := a)).image _).continuousOn _) (contOn_spec _ a)).symm

private lemma mul_cfc_eq (a : Matrix m m ℂ) (ha : 0 ≤ a) (g : ℝ → ℝ) :
    a * cfc g a = cfc (fun t : ℝ => t * g t) a := by
  rw [cfc_mul (fun t : ℝ => t) g a (contOn_spec _ a) (contOn_spec _ a),
    cfc_id' ℝ a ha.isSelfAdjoint]

private lemma log_eq_cfc (a : Matrix m m ℂ) : CFC.log a = cfc Real.log a := rfl

/-- `Tr[A log A] ≤ Tr[A log (A + ε)]`: both sides are `cfc`s of the *same* operator, so
this is the pointwise `t log t ≤ t log (t + ε)` on `[0,∞)` — no operator monotonicity, and
in particular no positive-definiteness, is involved. -/
private lemma mul_log_le_mul_log_add (A : Matrix m m ℂ) (hA : 0 ≤ A) {ε : ℝ} (hε0 : 0 < ε) :
    A * CFC.log A ≤ A * CFC.log (A + ε • (1 : Matrix m m ℂ)) := by
  rw [log_eq_cfc A, log_add_smul_one A hA ε, mul_cfc_eq A hA Real.log,
    mul_cfc_eq A hA (fun t : ℝ => Real.log (t + ε))]
  refine cfc_mono (fun t ht => ?_) (contOn_spec _ A) (contOn_spec _ A)
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg hA ht) with h | h
  · simp [← h]
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (by linarith)) h.le

/-- `log (B + ε) ≤ log B + ε · B⁻¹` (pseudo-inverse), for `0 < ε ≤ 1`. Again both sides are
`cfc`s of `B`; pointwise this is `log ε ≤ 0` at `t = 0` and `log (1 + ε/t) ≤ ε/t` at
`t > 0`. This is what replaces an `ε → 0` limit of `CFC.log (B + ε)`, which does **not**
converge when `B` is singular. -/
private lemma log_add_le_log_add_smul (B : Matrix m m ℂ) (hB : 0 ≤ B) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    CFC.log (B + ε • (1 : Matrix m m ℂ)) ≤ CFC.log B + ε • cfc (fun t : ℝ => t⁻¹) B := by
  rw [log_add_smul_one B hB ε, log_eq_cfc B,
    ← cfc_smul ε (fun t : ℝ => t⁻¹) B (contOn_spec _ B),
    ← cfc_add B Real.log (fun t : ℝ => ε • t⁻¹) (contOn_spec _ B) (contOn_spec _ B)]
  refine cfc_mono (fun t ht => ?_) (contOn_spec _ B) (contOn_spec _ B)
  rcases eq_or_lt_of_le (spectrum_nonneg_of_nonneg hB ht) with h | h
  · simp [← h, Real.log_nonpos hε0.le hε1]
  · have h1 : Real.log ((t + ε) / t) ≤ (t + ε) / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) h.ne'] at h1
    have h2 : (t + ε) / t - 1 = ε * t⁻¹ := by field_simp; ring
    simp only [smul_eq_mul]
    linarith

private lemma trace_mul_log_le_aux (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (A * CFC.log A).trace.re
      ≤ (A * CFC.log B).trace.re + ε * (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := by
  have hB : 0 ≤ B := hA.trans hAB
  have hsp : IsStrictlyPositive (A + ε • (1 : Matrix m m ℂ)) :=
    IsStrictlyPositive.nonneg_add hA (isStrictlyPositive_smul_one hε0)
  have stepB : CFC.log (A + ε • (1 : Matrix m m ℂ))
      ≤ CFC.log (B + ε • (1 : Matrix m m ℂ)) :=
    CFC.log_le_log (add_le_add hAB (le_refl (ε • (1 : Matrix m m ℂ)))) hsp
  calc (A * CFC.log A).trace.re
      ≤ (A * CFC.log (A + ε • (1 : Matrix m m ℂ))).trace.re :=
        trace_re_mono _ _ (mul_log_le_mul_log_add A hA hε0)
    _ ≤ (A * CFC.log (B + ε • (1 : Matrix m m ℂ))).trace.re :=
        trace_mul_mono A _ _ hA stepB
    _ ≤ (A * (CFC.log B + ε • cfc (fun t : ℝ => t⁻¹) B)).trace.re :=
        trace_mul_mono A _ _ hA (log_add_le_log_add_smul B hB hε0 hε1)
    _ = (A * CFC.log B).trace.re + ε * (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := by
        rw [mul_add, Matrix.trace_add, Complex.add_re, mul_smul_comm, Matrix.trace_smul]
        simp

/-- **The `ν → 0` shadow of `:493`** (Tomamichel `cond.tex:577`): for `0 ≤ A ≤ B`,
`Tr[A log A] ≤ Tr[A log B]`, with `CFC.log = cfc Real.log` and `Real.log 0 = 0`.

The *operator* inequality `log A ≤ log B` is false on `ker A`; the proof therefore runs the
operator-monotone step on the strictly positive `A + ε`, `B + ε`, and pays for removing the
`ε` with the two same-operator `cfc` comparisons above, whose cost `ε · Tr[A B⁻¹]` vanishes
as `ε → 0`. -/
private lemma trace_mul_log_le_of_le (A B : Matrix m m ℂ) (hA : 0 ≤ A) (hAB : A ≤ B) :
    (A * CFC.log A).trace.re ≤ (A * CFC.log B).trace.re := by
  have hB : 0 ≤ B := hA.trans hAB
  have hC0 : (0 : Matrix m m ℂ) ≤ cfc (fun t : ℝ => t⁻¹) B :=
    cfc_nonneg fun t ht => inv_nonneg.mpr (spectrum_nonneg_of_nonneg hB ht)
  have hK0 : 0 ≤ (A * cfc (fun t : ℝ => t⁻¹) B).trace.re := trace_mul_nonneg A _ hA hC0
  set K : ℝ := (A * cfc (fun t : ℝ => t⁻¹) B).trace.re with hKdef
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hε0 : 0 < min 1 (δ / (K + 1)) := lt_min one_pos (by positivity)
  have hkey := trace_mul_log_le_aux A B hA hAB hε0 (min_le_left _ _)
  rw [← hKdef] at hkey
  have hεb : min 1 (δ / (K + 1)) ≤ δ / (K + 1) := min_le_right _ _
  have hεK : min 1 (δ / (K + 1)) * K ≤ δ := by
    have h1 : min 1 (δ / (K + 1)) * K ≤ δ / (K + 1) * K :=
      mul_le_mul_of_nonneg_right hεb hK0
    have h2 : δ / (K + 1) * K ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
      nlinarith
    linarith
  linarith

end Toolkit

attribute [local instance] instCStarAlgebraMatrix

/-!
## Blockwise facts about a classical-quantum state
-/

/-- Each cq block is dominated by the quantum marginal: `σ_x ≤ ρ_B`, because
`ρ_B − σ_x = ∑_{y ≠ x} σ_y` is a sum of positive semidefinite blocks. This is the cq
instance of Tomamichel's `ρ_AB ≤ 1_A ⊗ ρ_B` (`cond.tex:576`). -/
private lemma stateMap_le_quantumMarginalOp {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) : (ρ.stateMap x).toOp ≤ ρ.quantumMarginalOp := by
  classical
  have hsplit : ρ.quantumMarginalOp - (ρ.stateMap x).toOp
      = ∑ y ∈ Finset.univ.erase x, (ρ.stateMap y).toOp := by
    rw [CQState.quantumMarginalOp, ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
      add_sub_cancel_left]
  rw [Matrix.le_iff, hsplit]
  refine Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun y _ => ?_)
  exact Matrix.nonneg_iff_posSemidef.mpr
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap y).toPosSemidefOp)

/-- Block diagonals are ordered blockwise. -/
private lemma blockDiagonal_mono {X : Type*} [Finite X] [DecidableEq X] {n : ℕ}
    (M N : X → Op n) (h : ∀ x, M x ≤ N x) :
    Matrix.blockDiagonal M ≤ Matrix.blockDiagonal N := by
  rw [Matrix.le_iff, ← Matrix.blockDiagonal_sub]
  exact Matrix.posSemidef_blockDiagonal fun x => by
    simpa [Pi.sub_apply] using Matrix.le_iff.mp (h x)

/-!
## The two obligations
-/

/-- **Nonnegativity of the Petz-DOWN conditional Rényi entropy on a classical-quantum
state, for `α ∈ (1,2]`.**

Dupuis–Fawzi `:973` ("in the case where the `A_i` are classical, we have `η₁, η₂ ≥ 0`",
with `η₁ = H'_α` and `η₂ = H'_2` fixed at `:953‑955`); Tomamichel,
arXiv:1504.00233, `cond.tex:552‑560` `\label{lm:lubounds}`, the separable
clause, which Dupuis–Fawzi cite at `:450` as `\cite[Lemma 5.2]{Tom15book}`.

**Hypothesis encoding.** The hypothesis carried here is *`A` classical*: `CQState X n`
is classical by construction. This matches the head of `\label{lem_var_dim}` at `:429`.
Dupuis–Fawzi's proof at `:450` argues under the weaker *`ρ_AB` separable*; since
cq implies separable, the classical encoding is the stronger hypothesis and this
statement is a special case of theirs. The separable statement is not formalised here.

**Range.** `α ≤ 2` is sharp: at `p = (1/2,1/2)`, `ρ_0 = |0⟩⟨0|`, `ρ_1 = |+⟩⟨+|` the
Petz trace equals `1` at `α = 2` and exceeds `1` for every `α > 2`. The bound
`α ≤ 2` enters through Löwner–Heinz operator monotonicity of `t ↦ t^{α−1}`.

**`hnorm`.** The inequality does not need it — `CQState.weight_le_one` already gives
`Tr[ρ^α σ^{1−α}] ≤ ∑_x Tr σ_x ≤ 1`. It is carried because `:294`'s `D'_α` is stated
for a state, so the statement stays faithful to the source. -/
theorem condRenyiPetz_nonneg_of_cq {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    0 ≤ condPetzRenyiDown α ρ := by
  have hν0 : 0 < α - 1 := by linarith
  have hν1 : α - 1 ≤ 1 := by linarith
  have hJ0 : (0 : Matrix (Fin n × X) (Fin n × X) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef
  have hJS : ρ.toJointOp ≤ Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp) :=
    blockDiagonal_mono _ _ fun x => stateMap_le_quantumMarginalOp ρ x
  have hbound := petzTrace_bound hν0 hν1 ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) hJ0 hJS
  rw [show (1 : ℝ) + (α - 1) = α by ring, show -(α - 1) = 1 - α by ring] at hbound
  have hJtr : (ρ.toJointOp).trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  have h0 : 0 ≤ petzTrace α ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) := hbound.1
  have h1 : petzTrace α ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) ≤ 1 :=
    le_trans hbound.2 (le_of_eq hJtr)
  have hlog : Real.logb 2 (petzTrace α ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))) ≤ 0 :=
    Real.logb_nonpos one_lt_two h0 h1
  have hinv : (0 : ℝ) < 1 / (α - 1) := by positivity
  simp only [condPetzRenyiDown, petzRenyiDivergence, neg_nonneg]
  have hmul := mul_nonneg hinv.le (neg_nonneg.mpr hlog)
  rw [mul_neg] at hmul
  linarith

/-- **Nonnegativity of the von Neumann conditional entropy on a classical-quantum
state**, `H(X|B)_ρ = −D(ρ_XB ‖ 1_X ⊗ ρ_B) ≥ 0`.

The second half of Dupuis–Fawzi `:450`'s `0 ≤ H_⋆(A|⋆)`, and the `α = 1` member of
Tomamichel `cond.tex:554` `\label{lm:lubounds}`. Together with
`condRenyiPetz_nonneg_of_cq` this is what upgrades `\label{lem_var_dim}`'s classical
variance bound from `log²(d_A + d_A² + 1)` to `log²(2 d_A + 1)`; the Rényi obligation
alone gives only the former (at `d_A = 2`: `log²7 = 7.881241658401056` versus
`log²5 = 5.391350077827256`).

The relative entropy is written out blockwise rather than through a conditional-entropy
definition, because for a cq state `log ρ_XB` is block-diagonal with blocks
`log (stateMap x).toOp`, so
`D(ρ_XB ‖ 1_X ⊗ ρ_B) = ∑_x Tr[σ_x (log σ_x − log ρ_B)]`.

**Support convention, stated because it is load-bearing.** `CFC.log = cfc Real.log` and
`Real.log 0 = 0`. The *operator* inequality `log σ_x ≤ log ρ_B` is therefore false on
`ker σ_x` and this statement does **not** assert it; the trace form written here samples
only `Supp σ_x` and is the unrestricted claim. No positive-definiteness hypothesis is
carried. A
`PosDef`-restricted variant would exclude the equality witness of
`condRenyiPetz_nonneg_of_cq` and this project's own BB84 Eve-conditioned blocks.
No normalisation hypothesis is carried either: each block inequality uses only
`σ_x ⪯ ρ_B`, so the trace form holds for sub-normalised cq states. -/
theorem condVonNeumann_nonneg_of_cq {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    0 ≤ - ∑ x : X, ((ρ.stateMap x).toOp
          * (CFC.log (ρ.stateMap x).toOp - CFC.log ρ.quantumMarginalOp)).trace.re := by
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun x _ => ?_
  have hA : (0 : Op n) ≤ (ρ.stateMap x).toOp :=
    Matrix.nonneg_iff_posSemidef.mpr
      (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  have hkey := trace_mul_log_le_of_le _ _ hA (stateMap_le_quantumMarginalOp ρ x)
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

/-!
## Blockwise and tensor-factorised form of the Petz trace

The content of the additivity theorem below is the factorisation
`Tr[(ρ ⊗ τ)^α (σ ⊗ ω)^{1−α}] = Tr[ρ^α σ^{1−α}] · Tr[τ^α ω^{1−α}]`, together with the
blockwise evaluation of the Petz trace on the block-diagonal cq layout. Both are
carried here on the **complex** trace `ptC` (no `.re`), so that no reality argument is
needed until the very last step.
-/

section TensorPowerToolkit

open Quantum.TensorProducts

/-- The complex Petz trace `Tr[A^α B^{1−α}]`; `petzTrace` is its real part
(`petzTrace_eq_ptC_re`, definitional). Working in `ℂ` keeps the multiplicativity
below free of `Complex.mul_re` side conditions. -/
private def ptC {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (A B : Matrix ι ι ℂ) : ℂ :=
  ((A ^ (α : ℝ)) * (B ^ (1 - α : ℝ))).trace

private lemma petzTrace_eq_ptC_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (A B : Matrix ι ι ℂ) : petzTrace α A B = (ptC α A B).re := rfl

/-! ### Block-diagonal functional calculus -/

/-- Polynomial application is blockwise on a block-diagonal matrix: `blockDiagonal` is a
unital algebra map, so it commutes with `Polynomial.aeval`. -/
private lemma aeval_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (q : Polynomial ℝ) :
    (Polynomial.aeval (Matrix.blockDiagonal M)) q
      = Matrix.blockDiagonal (fun x => (Polynomial.aeval (M x)) q) := by
  classical
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hp, hr, ← Matrix.blockDiagonal_add]
      exact congrArg _ (funext fun x => (map_add (Polynomial.aeval (M x)) p r).symm)
  | monomial k c =>
      have hR : (fun x => (Polynomial.aeval (M x)) (Polynomial.monomial k c))
          = fun x => (c : ℝ) • (M x) ^ k := by
        funext x
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [hR, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, ← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_smul]
      rfl

/-- **The continuous functional calculus is blockwise on block-diagonal matrices.**
`cfc f (blockDiagonal M) = blockDiagonal (cfc f ∘ M)`.

Proof by Lagrange interpolation on the *union* of the real spectra of
`blockDiagonal M` and of all the blocks `M x` — a finite set, since matrix spectra are
finite (`Matrix.finite_real_spectrum`). On that union the interpolating polynomial `q`
agrees with `f`, so `cfc f` equals `aeval q` simultaneously at `blockDiagonal M` and at
every block (`cfc_polynomial`, `cfc_congr`), and `aeval` is blockwise
(`aeval_blockDiagonal`). Taking the union avoids having to prove the spectral inclusion
`spectrum (M x) ⊆ spectrum (blockDiagonal M)`. -/
private lemma cfc_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (hM : ∀ x, IsSelfAdjoint (M x)) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal M) = Matrix.blockDiagonal (fun x => cfc f (M x)) := by
  classical
  have hBD : IsSelfAdjoint (Matrix.blockDiagonal M) := by
    change (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
    rw [Matrix.blockDiagonal_conjTranspose]
    exact congrArg _ (funext fun x => hM x)
  set s : Finset ℝ :=
    (Matrix.finite_real_spectrum (A := Matrix.blockDiagonal M)).toFinset ∪
      Finset.univ.biUnion (fun x : X => (Matrix.finite_real_spectrum (A := M x)).toFinset)
    with hs
  set q : Polynomial ℝ := Lagrange.interpolate s id f with hq
  have hval : ∀ μ ∈ s, Polynomial.eval μ q = f μ := by
    intro μ hμ
    exact Lagrange.eval_interpolate_at_node (s := s) (v := (id : ℝ → ℝ)) f (Set.injOn_id _) hμ
  have hmain : cfc f (Matrix.blockDiagonal M)
      = (Polynomial.aeval (Matrix.blockDiagonal M)) q := by
    rw [← cfc_polynomial (R := ℝ) q (Matrix.blockDiagonal M) hBD]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hμ)
  have hblk : ∀ x, cfc f (M x) = (Polynomial.aeval (M x)) q := by
    intro x
    rw [← cfc_polynomial (R := ℝ) q (M x) (hM x)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x,
        by rw [Set.Finite.mem_toFinset]; exact hμ⟩)
  rw [hmain, aeval_blockDiagonal]
  exact congrArg _ (funext fun x => (hblk x).symm)

/-- The `CFC.rpow` real power is blockwise on block-diagonal PSD matrices. -/
private lemma rpow_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (hM : ∀ x, (0 : Op N) ≤ M x) (y : ℝ) :
    (Matrix.blockDiagonal M) ^ y = Matrix.blockDiagonal (fun x => (M x) ^ y) := by
  have hBD : (0 : Matrix (Fin N × X) (Fin N × X) ℂ) ≤ Matrix.blockDiagonal M := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_blockDiagonal fun x => Matrix.nonneg_iff_posSemidef.mp (hM x)
  rw [CFC.rpow_eq_cfc_real hBD,
    cfc_blockDiagonal M (fun x => (Matrix.nonneg_iff_posSemidef.mp (hM x)).isHermitian)
      (fun t : ℝ => t ^ y)]
  exact congrArg _ (funext fun x => (CFC.rpow_eq_cfc_real (hM x)).symm)

/-- **Blockwise evaluation of the Petz trace.** On the block-diagonal cq layout the Petz
trace is the sum of the per-block Petz traces. -/
private lemma ptC_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (α : ℝ) (M R : X → Op N) (hM : ∀ x, (0 : Op N) ≤ M x) (hR : ∀ x, (0 : Op N) ≤ R x) :
    ptC α (Matrix.blockDiagonal M) (Matrix.blockDiagonal R)
      = ∑ x : X, ptC α (M x) (R x) := by
  unfold ptC
  rw [rpow_blockDiagonal M hM, rpow_blockDiagonal R hR, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal]

/-! ### Tensor factorisation -/

/-- **The Petz trace factorises over tensor products.** This is the whole analytic
content of tensor-power additivity: `Op.tensor_rpow` (the functional calculus commutes
with `⊗`), `Op.tensor_mul` and `Op.trace_tensor`. -/
private lemma ptC_tensor {p q : ℕ} (α : ℝ) (A C : Op p) (B D : Op q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ptC α (Op.tensor A B) (Op.tensor C D) = ptC α A C * ptC α B D := by
  unfold ptC
  rw [Op.tensor_rpow A B hA hB, Op.tensor_rpow C D hC hD, Op.tensor_mul, Op.trace_tensor]

/-- Dimension casts are invisible to the Petz trace. -/
private lemma ptC_castDim {p q : ℕ} (h : p = q) (α : ℝ) (A B : Op p) :
    ptC α (Op.castDim h A) (Op.castDim h B) = ptC α A B := by
  subst h; rfl

-- The cast and tensor finite-sum transport below is the shared family
-- `Quantum.TensorProducts.Op.castDim_sum` and `Op.tensor_zero_left`/`_right`,
-- `Op.tensor_finsetSum_left`/`_right`.

/-- `Op.tensor` of two finite sums, expanded over the product index. The one-sided laws are
`Quantum.TensorProducts.Op.tensor_finsetSum_left`/`_right`. -/
private lemma op_tensor_sum_sum {p q : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Op p) (B : κ → Op q) :
    Op.tensor (∑ i, A i) (∑ j, B j) = ∑ r : ι × κ, Op.tensor (A r.1) (B r.2) := by
  rw [Op.tensor_finsetSum_left, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Op.tensor_finsetSum_right _ _ _

/-- Reindexing a sum over `Fin (k+1) → X` as a sum over `X × (Fin k → X)`, splitting off
the first coordinate. Same `Fin.consEquiv` reindexing as
`CQState.tensorPower_sum_trace`. -/
private lemma sum_fin_succ_arrow {X : Type*} [Fintype X] {M : Type*} [AddCommMonoid M]
    {k : ℕ} (F : X → (Fin k → X) → M) :
    ∑ f : Fin (k + 1) → X, F (f 0) (fun i => f i.succ)
      = ∑ r : X × (Fin k → X), F r.1 r.2 := by
  refine Finset.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => X)).symm
    (fun _ => by simp) (fun f _ => ?_)
  rw [Fin.consEquiv_symm_apply]
  rfl

/-! ### The cq Petz trace and its tensor-power multiplicativity -/

/-- `Tr[ρ_XB^α (1_X ⊗ ρ_B)^{1−α}]` on a cq state, as a complex number. -/
private def cqPT {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) : ℂ :=
  ptC α ρ.toJointOp (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))

private lemma stateMap_toOp_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) : (0 : Op n) ≤ (ρ.stateMap x).toOp :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)

private lemma quantumMarginalOp_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : (0 : Op n) ≤ ρ.quantumMarginalOp :=
  Finset.sum_nonneg fun x _ => stateMap_toOp_nonneg ρ x

private lemma cqPT_eq_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) :
    cqPT α ρ = ∑ x : X, ptC α (ρ.stateMap x).toOp ρ.quantumMarginalOp :=
  ptC_blockDiagonal α _ _ (stateMap_toOp_nonneg ρ) (fun _ => quantumMarginalOp_nonneg ρ)

/-- The `(k+1)`-fold cq tensor power has blocks `ρ_{f 0} ⊗ (ρ^{⊗k})_{tail f}`, up to the
dimension cast `n · n^k = n^{k+1}` built into `CQState.tensorPower`. -/
private lemma tensorPower_succ_stateMap_toOp {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (k : ℕ) (f : Fin (k + 1) → X) :
    ((CQState.tensorPower ρ (k + 1)).stateMap f).toOp
      = Op.castDim (by ring) (Op.tensor (ρ.stateMap (f 0)).toOp
          (((CQState.tensorPower ρ k).stateMap (fun i => f i.succ)).toOp)) := by
  rw [show (CQState.tensorPower ρ (k + 1)).stateMap f
      = SubDensityOp.castDim (by ring)
        ((ρ.stateMap (f 0)).tensor
          ((CQState.tensorPower ρ k).stateMap (fun i => f i.succ))) from rfl,
    SubDensityOp.castDim_toOp]
  rfl

/-- The quantum marginal of the `(k+1)`-fold cq tensor power is the tensor product of the
single-copy marginal with the `k`-fold one. -/
private lemma tensorPower_succ_marginal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (k : ℕ) :
    (CQState.tensorPower ρ (k + 1)).quantumMarginalOp
      = Op.castDim (by ring) (Op.tensor ρ.quantumMarginalOp
          (CQState.tensorPower ρ k).quantumMarginalOp) := by
  rw [CQState.quantumMarginalOp, CQState.quantumMarginalOp, CQState.quantumMarginalOp,
    op_tensor_sum_sum, Op.castDim_sum]
  simp_rw [tensorPower_succ_stateMap_toOp]
  exact sum_fin_succ_arrow
    (fun x g => Op.castDim (by ring) (Op.tensor (ρ.stateMap x).toOp
      (((CQState.tensorPower ρ k).stateMap g).toOp)))

/-- **Multiplicativity of the cq Petz trace on tensor powers**, the content of the
additivity theorem. Induction on `m` through the binary recursion defining
`CQState.tensorPower`; each step is `ptC_tensor` (tensor factorisation of the Petz trace)
followed by the `Fin.consEquiv` reindexing of the block sum. No `[NeZero n]` is needed:
the recursion is used directly, not through `SubDensityOp.tensorFinProd`. -/
private lemma cqPT_tensorPower {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) (m : ℕ) :
    cqPT α (CQState.tensorPower ρ m) = (cqPT α ρ) ^ m := by
  induction m with
  | zero =>
      rw [show (cqPT α ρ) ^ 0 = 1 from pow_zero _, cqPT_eq_sum]
      have hstate : ∀ xs : Fin 0 → X,
          ((CQState.tensorPower ρ 0).stateMap xs).toOp = (1 : Op 1) := by
        intro xs
        rw [show (CQState.tensorPower ρ 0).stateMap xs
            = SubDensityOp.castDim (by simp) SubDensityOp.trivialOne from rfl,
          SubDensityOp.castDim_toOp]
        change Op.castDim (by simp) (SubDensityOp.trivialOne.toOp) = (1 : Op 1)
        rw [show SubDensityOp.trivialOne.toOp = (1 : Op 1) by
          ext i j; fin_cases i; fin_cases j; rfl]
        rfl
      have hmarg : (CQState.tensorPower ρ 0).quantumMarginalOp = (1 : Op 1) := by
        rw [CQState.quantumMarginalOp, Finset.sum_congr rfl (fun xs _ => hstate xs)]
        change (∑ _ : Fin 0 → X, (1 : Op 1)) = (1 : Op 1)
        simp
      rw [Fintype.sum_unique, hstate, hmarg]
      unfold ptC
      change ((1 : Op 1) ^ α * (1 : Op 1) ^ (1 - α)).trace = 1
      rw [CFC.one_rpow, CFC.one_rpow, one_mul, Matrix.trace_one]
      simp
  | succ k ih =>
      rw [cqPT_eq_sum]
      have hstep : ∀ f : Fin (k + 1) → X,
          ptC α (((CQState.tensorPower ρ (k + 1)).stateMap f).toOp)
              ((CQState.tensorPower ρ (k + 1)).quantumMarginalOp)
            = ptC α (ρ.stateMap (f 0)).toOp ρ.quantumMarginalOp
              * ptC α (((CQState.tensorPower ρ k).stateMap (fun i => f i.succ)).toOp)
                  ((CQState.tensorPower ρ k).quantumMarginalOp) := by
        intro f
        rw [tensorPower_succ_stateMap_toOp, tensorPower_succ_marginal, ptC_castDim]
        exact ptC_tensor α _ _ _ _ (stateMap_toOp_nonneg ρ (f 0))
          (stateMap_toOp_nonneg (CQState.tensorPower ρ k) (fun i => f i.succ))
          (quantumMarginalOp_nonneg ρ) (quantumMarginalOp_nonneg _)
      rw [Finset.sum_congr rfl (fun f _ => hstep f),
        sum_fin_succ_arrow (fun x g => ptC α (ρ.stateMap x).toOp ρ.quantumMarginalOp
          * ptC α (((CQState.tensorPower ρ k).stateMap g).toOp)
              ((CQState.tensorPower ρ k).quantumMarginalOp)),
        Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← cqPT_eq_sum, ← cqPT_eq_sum, ih, pow_succ, mul_comm]

/-- The cq Petz trace is a nonnegative real: `Tr[ρ^α σ^{1−α}] = Tr[ρ^{α/2} σ^{1−α} ρ^{α/2}]`
is the trace of a positive semidefinite operator. This is what lets the complex identity
above be read off as a real one. -/
private lemma cqPT_nonneg {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) : 0 ≤ cqPT α ρ := by
  classical
  set A : Matrix (Fin n × X) (Fin n × X) ℂ := ρ.toJointOp ^ (α : ℝ) with hA
  set B : Matrix (Fin n × X) (Fin n × X) ℂ :=
    (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) ^ (1 - α : ℝ) with hB
  have hA0 : 0 ≤ A := CFC.rpow_nonneg
  have hB0 : 0 ≤ B := CFC.rpow_nonneg
  have hsa : (A ^ (1 / 2 : ℝ))ᴴ = A ^ (1 / 2 : ℝ) := selfadj_of_nonneg CFC.rpow_nonneg
  have hconj : (0 : Matrix (Fin n × X) (Fin n × X) ℂ)
      ≤ A ^ (1 / 2 : ℝ) * B * A ^ (1 / 2 : ℝ) := by
    have := conj_nonneg B (A ^ (1 / 2 : ℝ)) hB0
    rwa [hsa] at this
  have htr : (A * B).trace = (A ^ (1 / 2 : ℝ) * B * A ^ (1 / 2 : ℝ)).trace := by
    rw [Matrix.trace_mul_comm (A ^ (1 / 2 : ℝ) * B) (A ^ (1 / 2 : ℝ)), ← mul_assoc,
      rpow_half_mul_self A hA0]
  change (0 : ℂ) ≤ (A * B).trace
  rw [htr]
  exact (Matrix.nonneg_iff_posSemidef.mp hconj).trace_nonneg

end TensorPowerToolkit

/-!
## Additivity on tensor powers
-/

/-- **Tensor-power additivity of the Petz-DOWN conditional Rényi entropy.**

`H'_α(X^m | B^m)_{ρ^{⊗m}} = m · H'_α(X|B)_ρ`, on the `m`-fold CQ tensor power
`CQState.tensorPower`.

**Source.** Tomamichel, *Quantum Information Processing with Finite Resources*
(arXiv:1504.00233). The object is `cond.tex:91` `\label{eq:had}`,
`H̄^↓_α(A|B)_ρ := −D̄_α(ρ_AB ‖ 1_A ⊗ ρ_B)` — `D̄` is the *old*, i.e. Petz, divergence
(`book.tex:107`) and `↓` pins the reference to `ρ_B` — which is exactly what
`condPetzRenyiDown` formalises. Its additivity is `cond.tex:487`: "the corresponding
additivity relations for `H̃^↓_α` and `H̄^↓_α` are evident from the respective definition."

**Which additivity this is, and which it is not.** The boxed corollary at `cond.tex:451`
(Corollary 5.2) states additivity for `H̃^↑_α` — *sandwiched*, with the reference
*optimised*. That corollary is the one the comparator cites at
arXiv:2311.01600, `adaptivepaper.tex:1097` `\label{lemma:additivity}` and applies
at `:682`, and every rung of the comparator's chain runs on that one object
(`:1067` `\label{def:renyientropy}`, identified as Tomamichel `H̃^↑` at `:1084`). The
additivity proved here is for the *Petz-down* object `H̄^↓_α` instead — `cond.tex:91`
`\label{eq:had}` — whose additivity is `cond.tex:487` (*"evident from the respective
definition"*), and which needs no duality argument, whereas Corollary 5.2's proof does. The
up/sandwiched variants are not formalised in this file and this statement does not cover them.

**It does not slot into the comparator's chain, and it does not need to.** `H̄^↓_α` is the
smallest of the three (`H̄^↓_α ≤ H̃^↓_α ≤ H̃^↑_α`), so this rung cannot license the collapse at
`adaptivepaper.tex:682`. It licenses a *different and complete* chain, which is
Dupuis–Fawzi's own: their continuity corollary
(arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:781`–`:790`
`\label{cor:continuity-bound-halpha_new}`) bounds *sandwiched-down* `H_α` (`:252`) and is
derived at `:782` by applying `\label{lem_HalphaH_second_order_new}` (`:711`) — proved at the
**Petz** level via Nussbaum–Szkoła — and then `D_α ≤ D'_α`. So the route is
`H̃^↑_α ≥ H̃^↓_α ≥ H̄'_α(ρ^{⊗n}) = n · H̄'_α(ρ)` *(this rung)* `≥ n·(H − (α−1)(ln2/2)·V −
(α−1)²K(α))`
*(`:711`, per round)*. Being the smallest is what makes the first two inequalities free.

A lower bound through `H̄^↓_α` can be stronger than one through Corollary 5.2: at
`d_Z = 2` the Petz route carries the constant `1.868500`, against the comparator's asserted
`2.512106` and its own cited lemma's `5.391350`.

**Equality, not inequality.** `condPetzRenyiDown` is `ℝ`-valued and is an explicit formula —
no `ENNReal`, and no `sInf`/`sSup` over reference states, which is what the `↑` variant would
introduce — so the mathematical equality is directly statable. The chain's use is the `≥`
direction, obtained from this by `ge_of_eq`; no separate inequality declaration is added.

**Order of application.** This rung collapses `m` rounds to one *before* the continuity bound
it composes with — which is arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:711`
`\label{lem_HalphaH_second_order_new}`, middle inequality, the Petz-level statement Cor IV.2 is
derived from. *(Not `adaptivepaper.tex:1109` `\label{lemma:contrenyi}`, which is a bound on the
sandwiched-up object and does not compose with this rung.)* In the other order the continuity
term is evaluated at `m`-fold quantities: the `K(α)` factor `2^{(α−1)(H − H'_α)}` becomes
extensive and can grow exponentially with `m`.

**Hypotheses.** None on `α`: the identity holds for every real `α` (at `α = 1` both sides
are `0` through the `1/(1−α)` prefactor). In particular it holds at `α = 0.5`, `3`, `5`. The range
`1 < α ≤ 2` on which
`petzRenyiDivergence` is the source's `D̄_α` (see that declaration's docstring), and on which
the companion `condRenyiPetz_nonneg_of_cq` is stated, is imposed by the consumers.

Normalisation is absent. `condRenyiPetz_nonneg_of_cq` carries
`∑ x, (ρ.stateMap x).trace = 1` because `:294` states `D'_α` for a state; the content here is
the factorisation `Tr[(ρ ⊗ τ)^α (σ ⊗ ω)^{1−α}] = Tr[ρ^α σ^{1−α}] · Tr[τ^α ω^{1−α}]`, which
does not see the total weight.

`[NeZero n]` is absent: at `n = 0` the index type `Fin 0 × X` is empty, so both sides are `0`
via `Real.log 0 = 0`. A proof routed through `CQState.tensorPower_stateMap_toOp`, which
assumes `[NeZero n]`, has to split that case off separately.

**Reference slot.** The `↓` variant pins its reference, so `SubDensityOp.tensorPower` does not
appear here.

The BB84 collective-Bennett per-σ smooth-min-entropy floor already carries
`n_copies · (single-copy von Neumann conditional entropy)` through Renner's IID AEP; it has no
Rényi object. The shared `CQState.tensorPower` alone does not identify it with the statement
here. `tensorPower_quantumMarginal_eq` supplies
`(CQState.tensorPower ρ m).quantumMarginal = SubDensityOp.tensorPower ρ.quantumMarginal m`.
A Rényi-based key-rate argument additionally requires the variance `V(A|B)`, Corollary IV.2,
and an `H_α → H_min^ε` conversion. -/
theorem renyiCondEntropy_down_tensorPower {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) (m : ℕ) :
    condPetzRenyiDown α (CQState.tensorPower ρ m) = (m : ℝ) * condPetzRenyiDown α ρ := by
  -- the Petz trace of the `m`-fold power is the `m`-th power of the single-copy Petz trace
  have hmul : cqPT α (CQState.tensorPower ρ m) = (cqPT α ρ) ^ m := cqPT_tensorPower α ρ m
  have him : (cqPT α ρ).im = 0 := ((Complex.nonneg_iff.mp (cqPT_nonneg α ρ)).2).symm
  have hre : ((cqPT α ρ) ^ m).re = ((cqPT α ρ).re) ^ m := by
    have hz : cqPT α ρ = (((cqPT α ρ).re : ℝ) : ℂ) :=
      Complex.ext_iff.mpr ⟨by simp, by simp [him]⟩
    conv_lhs => rw [hz]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hkey : petzTrace α (CQState.tensorPower ρ m).toJointOp
        (Matrix.blockDiagonal
          (fun _ : Fin m → X => (CQState.tensorPower ρ m).quantumMarginalOp))
      = (petzTrace α ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))) ^ m := by
    rw [petzTrace_eq_ptC_re, petzTrace_eq_ptC_re,
      show ptC α (CQState.tensorPower ρ m).toJointOp
          (Matrix.blockDiagonal
            (fun _ : Fin m → X => (CQState.tensorPower ρ m).quantumMarginalOp))
        = cqPT α (CQState.tensorPower ρ m) from rfl,
      show ptC α ρ.toJointOp (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        = cqPT α ρ from rfl, hmul, hre]
  -- and `logb 2` turns the `m`-th power into the factor `m`
  have hlog : ∀ t : ℝ, Real.logb 2 (t ^ m) = (m : ℝ) * Real.logb 2 t := by
    intro t
    rw [Real.logb, Real.logb, Real.log_pow]
    ring
  simp only [condPetzRenyiDown, petzRenyiDivergence]
  rw [hkey, hlog]
  ring

end InfoTheory.Renyi

end
