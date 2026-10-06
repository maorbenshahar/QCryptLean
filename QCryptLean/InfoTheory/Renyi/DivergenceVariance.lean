import QCryptLean.InfoTheory.Renyi.PetzConditional
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Divergence variance and the Dupuis–Fawzi continuity bound (Petz, DOWN, pinned reference)

Statement surface for Dupuis–Fawzi's divergence variance `V(ρ‖σ)`, its conditional form
`V(A|B)_ρ`, the second-order continuity bound `H'_α(A|B) ≥ H(A|B) − …`, and improved
classical-`A` variance caps. At `d_A = 2` the cap `log₂²(1+√2)` gives the per-round constant
`(ln 2 / 2) · log₂²(1+√2) = 0.5603567…`, which the BB84 penalty charges
(`condDivergenceVariance_le_logb_one_add_sqrt_two`, consumed via `bb84SharpVarianceCap`).

Source: arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex`.

## What this file states

* `relEntropyBase2` — `D(ρ‖σ) = (1/Tr[ρ]) · Tr[ρ (log₂ ρ − log₂ σ)]`,
  definition block `:265`–`:269`, `\label{def:petz-divergence}` at `:268`.
* `petzDivergenceVariance` — `V(ρ‖σ)`, definition block `:349`–`:355`, the `:=` form at
  `:352` and the expanded form transcribed here at `:353`.
* `condVonNeumann` — `H(A|B)_ρ = −D(ρ_AB ‖ 1_A ⊗ ρ_B)`, definition block `:271`–`:275`,
  `\label{def:von-neumann-entropy}` at `:274`.
* `condDivergenceVariance` — `V(A|B)_ρ = V(ρ_AB ‖ 1_A ⊗ ρ_B)`, definition block
  `:358`–`:363`, the display at `:361`.
* `petzDivergenceVariance_le` — the general variance bound, lemma head `:394`
  `\label{lem:divergence-variance-general-bounds}`, equation `\label{eq:bound_dalpha}` at
  `:398` with the display at `:399`.
* `condDivergenceVariance_le_logb_sqrt_card` — an improved classical-`A` cap
  `V(X|B)_ρ ≤ log₂²(√d_A + √(d_A − 1))`; it refines DF's `:429` `\label{lem_var_dim}`
  classical-`A` clause `log₂²(2 d_A + 1)` (`:435`–`:437`, proof at `:450`) for every `d_A`.
* `petzContinuityK`, `petzRenyiDivergence_le_relEntropy_add` — the lemma at `:710`
  `\label{lem_HalphaH_second_order_new}`, statement at `:713`, `K_{ρ,σ}(α,μ)` at `:715`.
* `secondOrderK`, `condPetzRenyiDown_ge_condVonNeumann_sub` — the corollary at `:783`
  `\label{cor:continuity-bound-halpha_new}` at `:784`, statement at `:787`, `K(α)` at
  `:789`; the `μ = 2 − α` recipe is at `:782`.

## Variant discipline

The object formalised here is the **Petz** divergence, the **DOWN** conditional variant,
with the reference **pinned** to `1_X ⊗ ρ_B`, and **base-2** logarithms — the same three
choices as `InfoTheory.Renyi.condPetzRenyiDown` in `PetzConditional.lean`.

* **Petz, not sandwiched.** DF `:713` states a chain `D_α ≤ D'_α ≤ …`. Only the second
  inequality (the Petz one) is stated here. The first is about the sandwiched divergence
  `:285` and is a different quantity.
* **DOWN, not up.** No optimisation over reference states; `condVonNeumann` and
  `condDivergenceVariance` reuse `condPetzRenyiDown`'s pinned reference expression
  `Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)` verbatim, so the three
  conditional quantities are comparable term by term.
* **DF `:787` is stated for the sandwiched `H_α`**, and DF reach it from the Petz form via
  `D_α ≤ D'_α` (`:782`). `condPetzRenyiDown_ge_condVonNeumann_sub` is the Petz-DOWN form,
  i.e. the stronger intermediate `H_α ≥ H'_α ≥ RHS`, and it is the one that composes with
  `renyiCondEntropy_down_tensorPower`.
* **Base 2 is load-bearing.** `CFC.log` is the natural logarithm, so `relEntropyBase2`
  carries `/ Real.log 2` and `petzDivergenceVariance` carries `/ (Real.log 2)^2`. Dropping
  them does not merely rescale: at `P = (0.3,0.7)`, `Q = (0.05,0.95)`, `μ = 2 − α` the
  base-2 form of `petzRenyiDivergence_le_relEntropy_add` has margin `+0.1983130144` at
  `α = 1.2` while the natural-log form has margin `−0.0142409907`, i.e. is false.

## The `α ∈ (0,1)` branch: no new divergence definition

`petzRenyiDivergence` is declared as the `1 < α ≤ 2`, `Supp ρ ⊆ Supp σ` branch of `:294`
only. DF's proof of the classical-`A` clause at `:450` passes through `D'_{1−ν}` with
`1 − ν ∈ (0,1)`, which that declaration does not cover. This file does **not** introduce a
second divergence definition for that branch. Instead every quantity at order `1 − ν` is
carried by `petzTrace`, which is defined at every real order and carries no branch pin:
`2^{−ν D'_{1−ν}(ρ‖σ)} = Tr[ρ^{1−ν} σ^{ν}] = petzTrace (1−ν) ρ σ` (DF `:424`). This is why
`petzDivergenceVariance_le` and `petzTrace_one_sub_le_card_rpow` are stated through
`petzTrace` rather than through `D'`.

`petzRenyiDivergence_le_relEntropy_add` carries no cap `α + μ ≤ 2`. `K_{ρ,σ}(α,μ)` contains
`D'_{α+μ}`, and DF's own definition restricts `D'_β` to `β ∈ [0,2]` (`:289`); the Lean formula
`petzRenyiDivergence` is defined at every real order and the proof never uses the range. The
statement therefore covers DF `:712`'s full range `α > 1, μ ∈ (0,1)` (indeed every `μ > 0`),
including the only use, `μ = 2 − α` at `:782`; for `α + μ > 2` the `D'_{α+μ}` inside `K` is
the same formula outside DF's declared range.

## Hypothesis notes

* `hnorm : ρ.trace.re = 1` is carried on `petzDivergenceVariance_le` even though DF `:395`
  state the lemma for arbitrary positive semidefinite `ρ`. Their proof applies Jensen to
  `⟨φ|·|φ⟩`, which is an expectation only when `Tr[ρ] = 1`. Without it the statement is
  false: at `P = (0.05,0.05)`, `Q = (0.2,0.8)`, `ν = 1/2` the left side is `1.000000000000`
  and the right side `0.308129029876`.
* `hsupp` is the project's encoding of `Supp ρ ⊆ Supp σ` as kernel inclusion, the phrasing
  of `InfoTheory/RelativeEntropy/Basic.lean:595`. On the cq instance it is discharged by
  `toJointOp_ker_sub`.

## Source locations

In arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex`, `def:petz-divergence` is at `:268`;
`:288`–`:292` gives the Petz Rényi definition. `def:von-neumann-entropy` is at `:274`,
`eq:bound_dalpha` at `:398` with its display at `:399`, and the two `petzTrace` identities
in the `:394` proof are at `:420` and `:424`.

## Proof architecture

Everything rests on one primitive, the **Nussbaum–Szkoła spectral
bridge** `trace_cfc_mul_cfc_eq_ns` (DF `:770`–`:774`), which evaluates
`Tr[f(ρ) g(σ)]` as the classical double sum `∑_{x,y} f(λ_x) g(μ_y) |⟨e_x|f_y⟩|²`. Every
statement above is then a finite-sum real-analysis fact about the weights
`w_{xy} = λ_x |⟨e_x|f_y⟩|²` and the log-likelihood ratios `ℓ_{xy} = ln λ_x − ln μ_y`:

* `classical_var_le` — the `(w, ℓ)` form of DF `:399`, valid at every `ν > 0`; it feeds
  `petzDivergenceVariance_le` (at `ν < 1`).
* `classical_var_le_log_sqrt_budget` — the sharp two-budget variance cap
  `Var_w(Y) ≤ log²(√(ab) + √(ab−1))` under `∑ w e^{±Y} ≤ a, b`; it feeds
  `condDivergenceVariance_le_logb_sqrt_card` at `a = 1`, `b = d_A`.
* `classical_continuity_le` — the `(w, ℓ)` form of DF `:713`; its Taylor step uses
  `exp_le_taylor_three` (`exp u ≤ 1 + u + u²/2 + (u³/6) exp u`), which is what removes
  DF's unjustified `sup_{0<γ≤ν}` at `:731`.
* `holder_three` and `klein_scaled` — Hölder and Klein-with-rescaling on the NS pair;
  they give `petzTrace_one_sub_le_card_rpow` and `condVonNeumann_le_logb_card`.

`ns_support` is where `hsupp` enters: it forces the NS weight to vanish wherever
`μ_y = 0`, which is exactly what makes the totalised `Real.log 0 = 0` value the
mathematically correct one.

`condDivergenceVariance_le_logb_sqrt_card` reads the `ν = 1` endpoint facts directly: the two
exponential-moment budgets `∑ w e^{ℓ} = petzTrace 2 ≤ 1` and `∑ w e^{−ℓ} ≤ Tr σ = d_A` enter
`classical_var_le_log_sqrt_budget`, whose shift `c = (log a − log b)/2` makes the two budgets
meet. No `ν → 1` limit and no `α < 1` divergence object appear.
-/

open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

/-!
## The divergence variance and its conditional form
-/

/-- `D(ρ‖σ) = (1/Tr[ρ]) · Tr[ρ (log₂ ρ − log₂ σ)]`, DF `:265`–`:269`,
`\label{def:petz-divergence}` at `:268`.

`CFC.log` is the NATURAL log, so the `/ Real.log 2` is the base-2 conversion and is
load-bearing. -/
def relEntropyBase2 {m : Type*} [Fintype m] [DecidableEq m]
    (ρ σ : Matrix m m ℂ) : ℝ :=
  (ρ * (CFC.log ρ - CFC.log σ)).trace.re / (ρ.trace.re * Real.log 2)

/-- `V(ρ‖σ) = (1/Tr[ρ]) · Tr[ρ (log₂ ρ − log₂ σ)²] − D(ρ‖σ)²`, DF `:353`. -/
def petzDivergenceVariance {m : Type*} [Fintype m] [DecidableEq m]
    (ρ σ : Matrix m m ℂ) : ℝ :=
  (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re / (ρ.trace.re * (Real.log 2) ^ 2)
    - (relEntropyBase2 ρ σ) ^ 2

/-- `H(X|B)_ρ = −D(ρ_XB ‖ 1_X ⊗ ρ_B)`, DF `:271`–`:275`
`\label{def:von-neumann-entropy}` at `:274`, at the same PINNED reference as
`condPetzRenyiDown`. -/
def condVonNeumann {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : ℝ :=
  - relEntropyBase2 ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))

/-- `V(X|B)_ρ = V(ρ_XB ‖ 1_X ⊗ ρ_B)`, DF `:361`, same pinned reference. -/
def condDivergenceVariance {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : ℝ :=
  petzDivergenceVariance ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))

/-! ### The Nussbaum–Szkoła bridge -/

section NS

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Nussbaum–Szkoła overlap `c x y = |⟨e_x | f_y⟩|²`. -/
private def nsOverlap {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (x y : m) : ℝ :=
  Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix m m ℂ)
    * (hσ.eigenvectorUnitary : Matrix m m ℂ)) x y)

private lemma nsOverlap_nonneg {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (x y : m) : 0 ≤ nsOverlap hρ hσ x y := Complex.normSq_nonneg _

/-- **The Nussbaum–Szkoła spectral bridge** (DF `:770`–`:774`). -/
private lemma trace_cfc_mul_cfc_eq_ns {ρ σ : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f ρ * cfc g σ).trace
      = ((∑ x : m, ∑ y : m,
          f (hρ.eigenvalues x) * g (hσ.eigenvalues y) * nsOverlap hρ hσ x y : ℝ) : ℂ) := by
  classical
  rw [hρ.cfc_eq, hσ.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix m m ℂ := (hρ.eigenvectorUnitary : Matrix m m ℂ) with hUdef
  set W : Matrix m m ℂ := (hσ.eigenvectorUnitary : Matrix m m ℂ) with hWdef
  set Df : Matrix m m ℂ := diagonal (RCLike.ofReal ∘ f ∘ hρ.eigenvalues) with hDf
  set Dg : Matrix m m ℂ := diagonal (RCLike.ofReal ∘ g ∘ hσ.eigenvalues) with hDg
  set M : Matrix m m ℂ := star U * W with hMdef
  have hcyc : (U * Df * star U * (W * Dg * star W)).trace
      = (Df * M * Dg * star M).trace := by
    rw [hMdef, StarMul.star_mul, star_star]
    simp only [mul_assoc]
    rw [Matrix.trace_mul_comm U]
    simp only [mul_assoc]
  rw [hcyc]
  have hrow : ∀ x y : m, (Df * M * Dg) x y
      = ((f (hρ.eigenvalues x) : ℝ) : ℂ) * M x y * ((g (hσ.eigenvalues y) : ℝ) : ℂ) := by
    intro x y
    rw [hDg, Matrix.mul_diagonal, hDf, Matrix.diagonal_mul]
    simp [Function.comp_def]
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hrow x y, Matrix.star_apply, RCLike.star_def,
    show ((f (hρ.eigenvalues x) : ℝ) : ℂ) * M x y * ((g (hσ.eigenvalues y) : ℝ) : ℂ)
        * (starRingEnd ℂ) (M x y)
      = ((f (hρ.eigenvalues x) : ℝ) : ℂ) * ((g (hσ.eigenvalues y) : ℝ) : ℂ)
        * (M x y * (starRingEnd ℂ) (M x y)) from by ring, Complex.mul_conj]
  push_cast [nsOverlap, hMdef]
  ring

private lemma contOn_spec' (f : ℝ → ℝ) (a : Matrix m m ℂ) : ContinuousOn f (spectrum ℝ a) :=
  (Matrix.finite_real_spectrum (A := a)).continuousOn f

private lemma cfc_one_eq {a : Matrix m m ℂ} (ha : a.IsHermitian) :
    cfc (fun _ : ℝ => (1 : ℝ)) a = 1 := by
  rw [cfc_const (1 : ℝ) a ha.isSelfAdjoint]; simp

private lemma cfc_id_mul_log (a : Matrix m m ℂ) (ha : a.IsHermitian) :
    cfc (fun t : ℝ => t * Real.log t) a = a * CFC.log a := by
  rw [cfc_mul (fun t : ℝ => t) Real.log a (contOn_spec' _ a) (contOn_spec' _ a),
    cfc_id' ℝ a ha.isSelfAdjoint]
  rfl

private lemma cfc_id_mul_log_mul_log (a : Matrix m m ℂ) (ha : a.IsHermitian) :
    cfc (fun t : ℝ => t * Real.log t * Real.log t) a = a * CFC.log a * CFC.log a := by
  rw [cfc_mul (fun t : ℝ => t * Real.log t) Real.log a (contOn_spec' _ a) (contOn_spec' _ a),
    cfc_id_mul_log a ha]
  rfl

private lemma cfc_log_mul_log (a : Matrix m m ℂ) :
    cfc (fun t : ℝ => Real.log t * Real.log t) a = CFC.log a * CFC.log a := by
  rw [cfc_mul Real.log Real.log a (contOn_spec' _ a) (contOn_spec' _ a)]
  rfl

private lemma ns_trace_rho {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ρ.trace.re = ∑ x : m, ∑ y : m, hρ.eigenvalues x * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, cfc_one_eq hσ, mul_one] at h
  rw [h, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma ns_trace_sigma {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    σ.trace.re = ∑ x : m, ∑ y : m, hσ.eigenvalues y * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t)
  rw [cfc_id' ℝ σ hσ.isSelfAdjoint, cfc_one_eq hρ, one_mul] at h
  rw [h, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma ns_petzTrace {ρ σ : Matrix m m ℂ} (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (a : ℝ) :
    petzTrace a ρ σ
      = ∑ x : m, ∑ y : m,
          hρ.eigenvalues x ^ a * hσ.eigenvalues y ^ (1 - a) * nsOverlap hρ hσ x y := by
  have h := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t ^ a) (fun t : ℝ => t ^ (1 - a))
  rw [← CFC.rpow_eq_cfc_real hρ0, ← CFC.rpow_eq_cfc_real hσ0] at h
  rw [petzTrace, h, Complex.ofReal_re]

private lemma log_eq_cfc' (a : Matrix m m ℂ) : CFC.log a = cfc Real.log a := rfl

private lemma ns_trace_relEnt {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * (CFC.log ρ - CFC.log σ)).trace.re
      = ∑ x : m, ∑ y : m, hρ.eigenvalues x
          * (Real.log (hρ.eigenvalues x) - Real.log (hσ.eigenvalues y))
          * nsOverlap hρ hσ x y := by
  have h1 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t) (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id_mul_log ρ hρ, cfc_one_eq hσ, mul_one] at h1
  have h2 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) Real.log
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, ← log_eq_cfc' σ] at h2
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, h1, h2, Complex.ofReal_re, Complex.ofReal_re,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma ns_trace_relEntSq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re
      = ∑ x : m, ∑ y : m, hρ.eigenvalues x
          * (Real.log (hρ.eigenvalues x) - Real.log (hσ.eigenvalues y)) ^ 2
          * nsOverlap hρ hσ x y := by
  have hcomm : CFC.log ρ * ρ = ρ * CFC.log ρ := by
    have h1 : cfc (fun t : ℝ => Real.log t * t) ρ = CFC.log ρ * ρ := by
      rw [cfc_mul Real.log (fun t : ℝ => t) ρ (contOn_spec' _ ρ) (contOn_spec' _ ρ),
        cfc_id' ℝ ρ hρ.isSelfAdjoint]
      rfl
    have hfun : (fun t : ℝ => Real.log t * t) = (fun t : ℝ => t * Real.log t) := by
      funext t; ring
    rw [← h1, hfun, cfc_id_mul_log ρ hρ]
  have h1 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t * Real.log t)
    (fun _ : ℝ => (1 : ℝ))
  rw [cfc_id_mul_log_mul_log ρ hρ, cfc_one_eq hσ, mul_one] at h1
  have h2 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t * Real.log t) Real.log
  rw [cfc_id_mul_log ρ hρ, ← log_eq_cfc' σ] at h2
  have h4 := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t)
    (fun t : ℝ => Real.log t * Real.log t)
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, cfc_log_mul_log σ] at h4
  have h3 : (ρ * (CFC.log σ * CFC.log ρ)).trace = (ρ * CFC.log ρ * CFC.log σ).trace := by
    rw [← mul_assoc, Matrix.trace_mul_comm (ρ * CFC.log σ) (CFC.log ρ), ← mul_assoc, hcomm]
  have hexp : ρ * (CFC.log ρ - CFC.log σ) ^ 2
      = ρ * CFC.log ρ * CFC.log ρ - ρ * CFC.log ρ * CFC.log σ
        - (ρ * (CFC.log σ * CFC.log ρ) - ρ * (CFC.log σ * CFC.log σ)) := by
    rw [pow_two]; noncomm_ring
  rw [hexp, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, h3, h1, h2, h4,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_re, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma ns_eigenvalues_nonneg {ρ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hρ0 : 0 ≤ ρ)
    (x : m) : 0 ≤ hρ.eigenvalues x :=
  (Matrix.nonneg_iff_posSemidef.mp hρ0).eigenvalues_nonneg x

/-- The support condition, lifted to the NS pair: if `μ y = 0` then the whole `y`-column of
the NS weight `λ x · c x y` vanishes. -/
private lemma ns_support {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {y : m} (hy : hσ.eigenvalues y = 0) (x : m) :
    hρ.eigenvalues x * nsOverlap hρ hσ x y = 0 := by
  classical
  set g : ℝ → ℝ := fun t => if t = 0 then (1 : ℝ) else 0 with hg
  set P : Matrix m m ℂ := cfc g σ with hP
  have hσP : σ * P = 0 := by
    have hmul : cfc (fun t : ℝ => t * g t) σ = σ * P := by
      rw [cfc_mul (fun t : ℝ => t) g σ (contOn_spec' _ σ) (contOn_spec' _ σ),
        cfc_id' ℝ σ hσ.isSelfAdjoint]
    rw [← hmul]
    have hfun : (fun t : ℝ => t * g t) = fun _ : ℝ => (0 : ℝ) := by
      funext t; by_cases h : t = 0 <;> simp [hg, h]
    rw [hfun, cfc_const (0 : ℝ) σ hσ.isSelfAdjoint, map_zero]
  have hcol : ∀ j : m, σ.mulVec (fun k => P k j) = 0 := by
    intro j
    funext i
    have h0 : (σ * P) i j = 0 := by rw [hσP]; simp
    rw [Matrix.mul_apply] at h0
    simpa [Matrix.mulVec, dotProduct] using h0
  have hρP : ρ * P = 0 := by
    ext i j
    have h1 := hsupp _ (hcol j)
    have h2 : ρ.mulVec (fun k => P k j) i = 0 := by rw [h1]; rfl
    rw [Matrix.mulVec, dotProduct] at h2
    simpa [Matrix.mul_apply] using h2
  have htr : (ρ * P).trace = 0 := by rw [hρP, Matrix.trace_zero]
  have hns := trace_cfc_mul_cfc_eq_ns hρ hσ (fun t : ℝ => t) g
  rw [cfc_id' ℝ ρ hρ.isSelfAdjoint, ← hP, htr] at hns
  have hsum : (∑ x : m, ∑ y : m,
      hρ.eigenvalues x * g (hσ.eigenvalues y) * nsOverlap hρ hσ x y) = 0 := by
    exact_mod_cast hns.symm
  have hnn : ∀ x' : m, 0 ≤ ∑ y' : m,
      hρ.eigenvalues x' * g (hσ.eigenvalues y') * nsOverlap hρ hσ x' y' := by
    intro x'
    refine Finset.sum_nonneg fun y' _ => ?_
    have h1 : 0 ≤ g (hσ.eigenvalues y') := by
      by_cases h : hσ.eigenvalues y' = 0 <;> simp [hg, h]
    exact mul_nonneg (mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 x') h1)
      (nsOverlap_nonneg hρ hσ x' y')
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun x' _ => hnn x').mp hsum x (Finset.mem_univ x)
  have hcell := (Finset.sum_eq_zero_iff_of_nonneg fun y' _ => by
      have h1 : 0 ≤ g (hσ.eigenvalues y') := by
        by_cases h : hσ.eigenvalues y' = 0 <;> simp [hg, h]
      exact mul_nonneg (mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 x) h1)
        (nsOverlap_nonneg hρ hσ x y')).mp hrow y (Finset.mem_univ y)
  simpa [hg, hy] using hcell

end NS

/-! ### The classical core -/

section ClassicalCore

/-- **C1**, the Taylor bound with an exponential third-order remainder. -/
private lemma exp_le_taylor_three (u : ℝ) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 * Real.exp u := by
  set g : ℝ → ℝ := fun u => (1 + u + u ^ 2 / 2) * Real.exp (-u) + u ^ 3 / 6 - 1 with hgdef
  have hg' : ∀ v : ℝ, HasDerivAt g (v ^ 2 / 2 * (1 - Real.exp (-v))) v := by
    intro v
    have h1 : HasDerivAt (fun u : ℝ => 1 + u + u ^ 2 / 2) (1 + v) v := by
      have hA : HasDerivAt (fun u : ℝ => 1 + u) 1 v := (hasDerivAt_id v).const_add 1
      have hB : HasDerivAt (fun u : ℝ => u ^ 2 / 2) (2 * v ^ 1 / 2) v :=
        (hasDerivAt_pow 2 v).div_const 2
      have := hA.add hB
      apply this.congr_deriv
      ring
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-v)) v := by
      have := (Real.hasDerivAt_exp (-v)).comp v ((hasDerivAt_id v).neg)
      exact this.congr_deriv (by ring)
    have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (3 * v ^ 2 / 6) v :=
      (hasDerivAt_pow 3 v).div_const 6
    have h4 := ((h1.mul h2).add h3).sub_const 1
    apply h4.congr_deriv
    ring
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hdiff : Differentiable ℝ g := fun v => (hg' v).differentiableAt
  have hgnn : ∀ v : ℝ, 0 ≤ g v := by
    intro v
    rcases le_total 0 v with hv | hv
    · have hmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).differentiableWithinAt) fun x hx => ?_
        rw [interior_Ici] at hx
        rw [(hg' x).deriv]
        have hx0 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by simpa using hx.le)
        nlinarith [sq_nonneg x]
      have := hmono (Set.self_mem_Ici) hv hv
      linarith [hg0 ▸ this]
    · have hanti : AntitoneOn g (Set.Iic (0 : ℝ)) := by
        refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
          (fun x _ => (hdiff x).differentiableWithinAt) fun x hx => ?_
        rw [interior_Iic] at hx
        rw [(hg' x).deriv]
        have hx0 : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (by simpa using hx.le)
        nlinarith [sq_nonneg x]
      have := hanti hv (Set.self_mem_Iic) hv
      linarith [hg0 ▸ this]
  have hv := hgnn u
  have hexp : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hmul : 0 ≤ g u * Real.exp u := mul_nonneg hv hexp.le
  have hcancel : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]; simp
  have : g u * Real.exp u
      = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 * Real.exp u - Real.exp u := by
    simp only [hgdef]
    linear_combination (1 + u + u ^ 2 / 2) * hcancel
  linarith [this ▸ hmul]

/-- **C2**. -/
private lemma sq_log_le_sq_log_add (t : ℝ) (ht : 0 < t) :
    (Real.log t) ^ 2 ≤ (Real.log (t + t⁻¹ + 1)) ^ 2 := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have h1 : Real.log t ≤ Real.log (t + t⁻¹ + 1) := Real.log_le_log ht (by linarith)
  have h2 : Real.log t⁻¹ ≤ Real.log (t + t⁻¹ + 1) := Real.log_le_log hti (by linarith)
  rw [Real.log_inv] at h2
  exact sq_le_sq' (by linarith) h1

/-- **C3**. -/
private lemma concaveOn_sq_log :
    ConcaveOn ℝ (Set.Ici (Real.exp 1)) (fun s : ℝ => (Real.log s) ^ 2) := by
  have hderiv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun x : ℝ => (Real.log x) ^ 2) (2 * (Real.log s / s)) s := by
    intro s hs
    have h := (Real.hasDerivAt_log hs.ne').pow 2
    apply h.congr_deriv
    ring
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _) ?_ ?_ ?_
  · exact fun s hs =>
      ((hderiv s (lt_of_lt_of_le (Real.exp_pos 1) hs)).continuousAt).continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact ((hderiv s (lt_trans (Real.exp_pos 1) hs)).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := lt_trans (Real.exp_pos 1) ha
    have hb' : (0 : ℝ) < b := lt_trans (Real.exp_pos 1) hb
    rw [(hderiv a ha').deriv, (hderiv b hb').deriv]
    have h := Real.log_div_self_antitoneOn (Set.mem_ofPred.mpr ha.le)
      (Set.mem_ofPred.mpr hb.le) hab
    simp only at h
    linarith

private lemma sq_log_div_antitoneOn :
    AntitoneOn (fun s : ℝ => (Real.log s) ^ 2 / s) (Set.Ici (Real.exp 2)) := by
  have key : ∀ s : ℝ, 0 < s → (Real.log s) ^ 2 / s = (Real.log s / s ^ (1 / 2 : ℝ)) ^ 2 := by
    intro s hs
    rw [div_pow, ← Real.rpow_natCast (s ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hs.le]
    norm_num
  have hnn : ∀ s : ℝ, Real.exp 2 ≤ s → 0 ≤ Real.log s / s ^ (1 / 2 : ℝ) := by
    intro s hs
    have hs' : (0 : ℝ) < s := lt_of_lt_of_le (Real.exp_pos 2) hs
    have h2 : (2 : ℝ) ≤ Real.log s := (Real.le_log_iff_exp_le hs').mpr hs
    exact div_nonneg (by linarith) (Real.rpow_nonneg hs'.le _)
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := lt_of_lt_of_le (Real.exp_pos 2) ha
  have hb' : (0 : ℝ) < b := lt_of_lt_of_le (Real.exp_pos 2) hb
  change (Real.log b) ^ 2 / b ≤ (Real.log a) ^ 2 / a
  have hanti := Real.log_div_self_rpow_antitoneOn (a := 1 / 2) (by norm_num)
  have hhalf : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
  have hmemA : Real.exp (1 / 2 : ℝ)⁻¹ ≤ a := by rw [hhalf]; exact ha
  have hmemB : Real.exp (1 / 2 : ℝ)⁻¹ ≤ b := by rw [hhalf]; exact hb
  have h : Real.log b / b ^ (1 / 2 : ℝ) ≤ Real.log a / a ^ (1 / 2 : ℝ) := hanti hmemA hmemB hab
  rw [key a ha', key b hb']
  exact pow_le_pow_left₀ (hnn b hb) h 2

/-- **C4**. -/
private lemma concaveOn_cube_log_add :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => (Real.log (t + Real.exp 2)) ^ 3) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < t + Real.exp 2 := by
    intro t ht; have := Real.exp_pos 2; linarith
  have hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun x : ℝ => (Real.log (x + Real.exp 2)) ^ 3)
        (3 * ((Real.log (t + Real.exp 2)) ^ 2 / (t + Real.exp 2))) t := by
    intro t ht
    have h0 : HasDerivAt (fun x : ℝ => x + Real.exp 2) 1 t := (hasDerivAt_id t).add_const _
    have h1 : HasDerivAt (fun x : ℝ => Real.log (x + Real.exp 2)) (1 / (t + Real.exp 2)) t :=
      h0.log (hpos t ht).ne'
    have h2 := h1.pow 3
    apply h2.congr_deriv
    ring
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici _) ?_ ?_ ?_
  · exact fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact ((hderiv t ht.le).differentiableAt).differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    rw [(hderiv a ha.le).deriv, (hderiv b hb.le).deriv]
    have hma : Real.exp 2 ≤ a + Real.exp 2 := by simp only [Set.mem_Ioi] at ha; linarith
    have hmb : Real.exp 2 ≤ b + Real.exp 2 := by simp only [Set.mem_Ioi] at hb; linarith
    have h := sq_log_div_antitoneOn hma hmb (by linarith)
    simp only at h
    linarith

private lemma exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  norm_num at h
  linarith

/-- **The classical variance bound**, valid at every `ν > 0`. -/
private lemma classical_var_le {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ν : ℝ} (hν : 0 < ν) :
    ∑ i, w i * (Y i) ^ 2
      ≤ (1 / ν ^ 2) * (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by
  classical
  have hginv : ∀ i : ι, (Real.exp (ν * Y i))⁻¹ = Real.exp (-ν * Y i) := by
    intro i; rw [← Real.exp_neg]; ring_nf
  have hg3 : ∀ i : ι, (3 : ℝ) ≤ Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1 := by
    intro i
    have h1 : Real.exp (ν * Y i) * Real.exp (-ν * Y i) = 1 := by
      rw [← Real.exp_add, show ν * Y i + -ν * Y i = 0 by ring, Real.exp_zero]
    have h2 : 0 < Real.exp (ν * Y i) := Real.exp_pos _
    nlinarith [sq_nonneg (Real.exp (ν * Y i) - 1)]
  have hpt : ∀ i : ι, (ν * Y i) ^ 2
      ≤ (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2 := by
    intro i
    have h := sq_log_le_sq_log_add (Real.exp (ν * Y i)) (Real.exp_pos _)
    rw [Real.log_exp, hginv i] at h
    exact h
  have hsplit : ∑ i, w i * (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
      = (∑ i, w i * Real.exp (ν * Y i)) + (∑ i, w i * Real.exp (-ν * Y i)) + 1 := by
    have hterm : ∀ i : ι, w i * (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
        = w i * Real.exp (ν * Y i) + w i * Real.exp (-ν * Y i) + w i := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, hw1]
  have hjensen : ∑ i, w i * (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2
      ≤ (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by
    have h := concaveOn_sq_log.le_map_sum (t := (Finset.univ : Finset ι)) (w := w)
      (p := fun i => Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)
      (fun i _ => hw i) hw1 (fun i _ => le_trans exp_one_le_three (hg3 i))
    simp only [smul_eq_mul] at h
    rw [hsplit] at h
    exact h
  have hstep : ∑ i, w i * (ν * Y i) ^ 2
      ≤ ∑ i, w i * (Real.log (Real.exp (ν * Y i) + Real.exp (-ν * Y i) + 1)) ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw i)
  have hfac : ∑ i, w i * (ν * Y i) ^ 2 = ν ^ 2 * ∑ i, w i * (Y i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hν2 : (0 : ℝ) < ν ^ 2 := by positivity
  rw [hfac] at hstep
  have hchain := hstep.trans hjensen
  rw [← le_div_iff₀' hν2] at hchain
  calc ∑ i, w i * (Y i) ^ 2
      ≤ (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 / ν ^ 2 := hchain
    _ = (1 / ν ^ 2) * (Real.log ((∑ i, w i * Real.exp (ν * Y i))
          + (∑ i, w i * Real.exp (-ν * Y i)) + 1)) ^ 2 := by ring

/-- `sinh x < x · cosh x` for `x > 0`: the function `x·cosh x − sinh x` has derivative
`x·sinh x > 0` on `(0, ∞)` and vanishes at `0`. -/
private lemma sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : Real.sinh x < x * Real.cosh x := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
      (y * Real.sinh y) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => z * Real.cosh z)
        (1 * Real.cosh y + y * Real.sinh y) y := (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
    have h2 : HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
        (1 * Real.cosh y + y * Real.sinh y - Real.cosh y) y := h1.sub (Real.hasDerivAt_sinh y)
    simpa using h2
  have hdiff : Differentiable ℝ (fun z : ℝ => z * Real.cosh z - Real.sinh z) :=
    fun y => (hderiv y).differentiableAt
  have hmono : StrictMonoOn (fun z : ℝ => z * Real.cosh z - Real.sinh z) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hdiff.continuous.continuousOn ?_
    rw [interior_Ici]
    intro y hy
    rw [(hderiv y).deriv]
    exact mul_pos (Set.mem_Ioi.mp hy) (Real.sinh_pos_iff.mpr (Set.mem_Ioi.mp hy))
  have hgt := hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx.le) hx
  simp only at hgt
  norm_num at hgt
  linarith

/-- `sinh x / x` is strictly increasing on `(0, ∞)`: its derivative
`(x·cosh x − sinh x)/x²` is positive there, by `sinh_lt_mul_cosh`. -/
private lemma sinh_div_strictMonoOn :
    StrictMonoOn (fun x : ℝ => Real.sinh x / x) (Set.Ioi 0) := by
  have hderiv : ∀ y ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z : ℝ => Real.sinh z / z)
      ((Real.cosh y * y - Real.sinh y) / y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => Real.sinh z) (Real.cosh y) y := Real.hasDerivAt_sinh y
    have h2 : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have h3 := h1.div h2 (ne_of_gt hy)
    simp only [mul_one] at h3
    exact h3
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => Real.sinh z / z) (Set.Ioi 0) :=
    fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hdiff.continuousOn ?_
  rw [interior_Ioi]
  intro y hy
  rw [(hderiv y hy).deriv]
  have hnum : (0 : ℝ) < Real.cosh y * y - Real.sinh y := by linarith [sinh_lt_mul_cosh hy]
  exact div_pos hnum (pow_pos hy 2)

/-- **The tangent majorant.** For `L > 0` and every real `z`,
`z² ≤ L² + (2L/sinh L)·(cosh z − cosh L)`, with equality exactly at `z = ±L`: the even function
`z ↦ L² + (2L/sinh L)(cosh z − cosh L) − z²` is antitone on `[0, L]` and monotone on `[L, ∞)`
because its derivative `k·sinh x − 2x` is negative on `(0, L)` and positive on `(L, ∞)`, which
follows from the strict monotonicity of `sinh x / x`. -/
private lemma sq_le_cosh_tangent (L : ℝ) (hL : 0 < L) (z : ℝ) :
    z ^ 2 ≤ L ^ 2 + (2 * L / Real.sinh L) * (Real.cosh z - Real.cosh L) := by
  classical
  set k : ℝ := 2 * L / Real.sinh L with hk
  have hsinhL : (0 : ℝ) < Real.sinh L := Real.sinh_pos_iff.mpr hL
  have hkpos : (0 : ℝ) < k := by rw [hk]; positivity
  have hkL : k * Real.sinh L = 2 * L := by rw [hk]; field_simp
  set f : ℝ → ℝ := fun x => L ^ 2 + k * (Real.cosh x - Real.cosh L) - x ^ 2 with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (k * Real.sinh x - 2 * x) x := by
    intro x
    have h0 : HasDerivAt (fun z : ℝ => Real.cosh z - Real.cosh L) (Real.sinh x) x := by
      simpa using (Real.hasDerivAt_cosh x).sub_const (Real.cosh L)
    have h1 : HasDerivAt (fun z : ℝ => k * (Real.cosh z - Real.cosh L)) (k * Real.sinh x) x :=
      h0.const_mul k
    have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact (h1.const_add (L ^ 2)).sub h2
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  -- the derivative of `f` is negative on `(0, L)` and positive on `(L, ∞)`
  have hsign : ∀ x ∈ Set.Ioo 0 L, deriv f x < 0 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hmono : Real.sinh x / x < Real.sinh L / L :=
      sinh_div_strictMonoOn (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hL) hx.2
    have hcross : L * Real.sinh x < x * Real.sinh L := by
      rw [mul_comm L (Real.sinh x), mul_comm x (Real.sinh L)]
      exact (div_lt_div_iff₀ hx0 hL).mp hmono
    rw [(hderiv x).deriv]
    have hstep : k * Real.sinh x < 2 * x := by
      rw [show (2 : ℝ) * x = (2 * L * x) / L from by field_simp, lt_div_iff₀ hL]
      calc k * Real.sinh x * L = k * (L * Real.sinh x) := by ring
        _ < k * (x * Real.sinh L) := mul_lt_mul_of_pos_left hcross hkpos
        _ = (2 * L) * x := by rw [← hkL]; ring
        _ = 2 * L * x := by ring
    linarith
  have hsign' : ∀ x ∈ Set.Ioi L, deriv f x > 0 := by
    intro x hx
    have hsx : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr (lt_trans hL hx)
    have hxpos : (0 : ℝ) < x := lt_trans hL hx
    have hmono : Real.sinh L / L < Real.sinh x / x :=
      sinh_div_strictMonoOn (Set.mem_Ioi.mpr hL) (Set.mem_Ioi.mpr (lt_trans hL hx)) hx
    have hcross : x * Real.sinh L < L * Real.sinh x := by
      rw [mul_comm x (Real.sinh L), mul_comm L (Real.sinh x)]
      exact (div_lt_div_iff₀ hL hxpos).mp hmono
    rw [(hderiv x).deriv]
    have hstep : (2 : ℝ) * x < k * Real.sinh x := by
      rw [show k * Real.sinh x = k * Real.sinh x * L / L from by field_simp, lt_div_iff₀ hL]
      calc 2 * x * L = k * (x * Real.sinh L) := by rw [mul_left_comm, hkL]; ring
        _ < k * (L * Real.sinh x) := mul_lt_mul_of_pos_left hcross hkpos
        _ = k * Real.sinh x * L := by ring
    linarith
  -- `f` decreases on `[0, L]` and increases on `[L, ∞)`, so `f ≥ f L = 0` everywhere
  have hfL : f L = 0 := by simp only [hf]; ring
  have hanti : AntitoneOn f (Set.Icc 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L) hdiff.continuous.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun x _ => (hdiff x).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have := hsign x ⟨hx.1, hx.2⟩
      linarith
  have hmono' : MonotoneOn f (Set.Ici L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici L) hdiff.continuous.continuousOn ?_ ?_
    · rw [interior_Ici]
      exact fun x _ => (hdiff x).differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have := hsign' x hx
      linarith
  have hpos : ∀ x : ℝ, 0 < x → (0 : ℝ) ≤ f x := by
    intro x hx
    rcases le_or_gt L x with hLx | hLx
    · have h1 := hmono' (Set.mem_Ici.mpr (le_refl L)) (Set.mem_Ici.mpr hLx) hLx
      rw [hfL] at h1
      exact h1
    · have h1 := hanti (Set.mem_Icc.mpr ⟨hx.le, hLx.le⟩)
        (Set.mem_Icc.mpr ⟨hL.le, le_refl L⟩) hLx.le
      rw [hfL] at h1
      exact h1
  have heven : ∀ x : ℝ, f x = f (-x) := by
    intro x
    simp only [hf]
    rw [Real.cosh_neg]
    ring
  have hfz : (0 : ℝ) ≤ f z := by
    rcases le_or_gt 0 z with hz | hz
    · rcases le_or_gt L z with hLz | hLz
      · have h1 := hmono' (Set.mem_Ici.mpr (le_refl L)) (Set.mem_Ici.mpr hLz) hLz
        rw [hfL] at h1
        exact h1
      · have h1 := hanti (Set.mem_Icc.mpr ⟨hz, hLz.le⟩)
          (Set.mem_Icc.mpr ⟨hL.le, le_refl L⟩) hLz.le
        rw [hfL] at h1
        exact h1
    · rw [heven z]
      exact hpos (-z) (neg_pos.mpr hz)
  simp only [hf] at hfz
  linarith

/-- The mean minimises the second moment.  Only `∑ w = 1` is used — there is NO `0 ≤ w` binder. -/
private lemma classical_var_le_shift {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw1 : ∑ i, w i = 1) (c : ℝ) :
    ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2 ≤ ∑ i, w i * (Y i - c) ^ 2 := by
  classical
  set D : ℝ := ∑ j, w j * Y j with hD
  have hgen : ∀ a : ℝ, ∑ i, w i * (Y i - a) ^ 2
      = (∑ i, w i * (Y i) ^ 2) - 2 * a * D + a ^ 2 := by
    intro a
    have hterm : ∀ i : ι, w i * (Y i - a) ^ 2
        = w i * (Y i) ^ 2 - 2 * a * (w i * Y i) + a ^ 2 * w i := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, ← hD]
    ring
  rw [hgen D, hgen c]
  nlinarith [sq_nonneg (D - c)]

/-- `exp (log x / 2) = √x` for `x > 0`. -/
private lemma exp_log_half {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  have h : Real.exp (Real.log x / 2) ^ 2 = x := by
    rw [sq, ← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring,
      Real.exp_log hx]
  have h2 : Real.sqrt x = Real.sqrt (Real.exp (Real.log x / 2) ^ 2) := by rw [h]
  rw [h2, Real.sqrt_sq (Real.exp_pos _).le]

/-- `cosh t ≥ 1 + t²/2`, equivalently `t² ≤ 2(cosh t − 1)`. -/
private lemma cosh_ge_one_add_sq_half (t : ℝ) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h := Real.cosh_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  have hcs := Real.cosh_sq (t / 2)
  have hsq : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := by
    rcases le_or_gt (0:ℝ) (t / 2) with h0 | h0
    · have := Real.self_le_sinh_iff.mpr h0
      nlinarith
    · have h1 : (0 : ℝ) ≤ -(t / 2) := by linarith
      have h2 := Real.self_le_sinh_iff.mpr h1
      rw [Real.sinh_neg] at h2
      nlinarith
  nlinarith [hsq, h, hcs]

/-- **Jensen's shadow**: the centred moment generating function is at least `1`. -/
private lemma classical_M_ge_one {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hY0 : ∑ i, w i * Y i = 0) (s : ℝ) :
    (1 : ℝ) ≤ ∑ i, w i * Real.exp (s * Y i) := by
  have hle : ∀ i : ι, w i * (1 + s * Y i) ≤ w i * Real.exp (s * Y i) := fun i =>
    mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (s * Y i)]) (hw i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  have hcomp : ∑ i, w i * (1 + s * Y i) = 1 := by
    have hterm : ∀ i : ι, w i * (1 + s * Y i) = w i + s * (w i * Y i) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hw1,
      ← Finset.mul_sum, hY0]
    ring
  rw [hcomp] at hsum
  exact hsum

private lemma cube_le_cube {a b : ℝ} (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- **The classical second-order continuity bound**. -/
private lemma classical_continuity_le {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hY0 : ∑ i, w i * Y i = 0)
    {ν μ : ℝ} (hν : 0 < ν) (hμ : 0 < μ) :
    Real.log (∑ i, w i * Real.exp (ν * Y i))
      ≤ ν ^ 2 * (∑ i, w i * (Y i) ^ 2) / 2
        + ν ^ 3 / (6 * μ ^ 3) * (∑ i, w i * Real.exp (ν * Y i))
          * (Real.log ((∑ i, w i * Real.exp ((ν + μ) * Y i)) + Real.exp 2)) ^ 3 := by
  classical
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  set Mv : ℝ := ∑ i, w i * Real.exp (ν * Y i) with hMv
  set Mvm : ℝ := ∑ i, w i * Real.exp ((ν + μ) * Y i) with hMvm
  set V : ℝ := ∑ i, w i * (Y i) ^ 2 with hV
  set R : ℝ := ∑ i, w i * ((Y i) ^ 3 * Real.exp (ν * Y i)) with hR
  have hweight : ∀ i : ι, 0 ≤ w i * Real.exp (ν * Y i) :=
    fun i => mul_nonneg (hw i) (Real.exp_pos _).le
  have hM1 : (1 : ℝ) ≤ Mv := by
    have hle : ∀ i : ι, w i * (1 + ν * Y i) ≤ w i * Real.exp (ν * Y i) := fun i =>
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (ν * Y i)]) (hw i)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
    have hcomp : ∑ i, w i * (1 + ν * Y i) = 1 := by
      have hterm : ∀ i : ι, w i * (1 + ν * Y i) = w i + ν * (w i * Y i) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hw1,
        ← Finset.mul_sum, hY0]
      ring
    rw [hcomp] at hsum
    exact hsum
  have hMpos : (0 : ℝ) < Mv := lt_of_lt_of_le zero_lt_one hM1
  have hMvmnn : (0 : ℝ) ≤ Mvm :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  have htaylor : Mv ≤ 1 + ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
    have hle : ∀ i : ι, w i * Real.exp (ν * Y i)
        ≤ w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
            + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i)) := fun i =>
      mul_le_mul_of_nonneg_left (exp_le_taylor_three (ν * Y i)) (hw i)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
    have hrhs : ∑ i, w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
          + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i))
        = 1 + ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
      have hterm : ∀ i : ι, w i * (1 + ν * Y i + (ν * Y i) ^ 2 / 2
            + (ν * Y i) ^ 3 / 6 * Real.exp (ν * Y i))
          = w i + ν * (w i * Y i) + ν ^ 2 / 2 * (w i * (Y i) ^ 2)
            + ν ^ 3 / 6 * (w i * ((Y i) ^ 3 * Real.exp (ν * Y i))) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, hw1, hY0, ← hV, ← hR]
      ring
    rw [hrhs] at hsum
    exact hsum
  have hlogle : Real.log Mv ≤ ν ^ 2 * V / 2 + ν ^ 3 * R / 6 := by
    have h1 : Real.log Mv ≤ Mv - 1 := Real.log_le_sub_one_of_pos hMpos
    linarith
  -- the third-order remainder
  have hstep1 : R ≤ (1 / μ ^ 3) * ∑ i, (w i * Real.exp (ν * Y i))
      * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 := by
    rw [hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hcube : (Y i) ^ 3 = (1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i))) ^ 3 := by
      rw [Real.log_exp]; field_simp
    have hmono : (Real.log (Real.exp (μ * Y i))) ^ 3
        ≤ (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 :=
      cube_le_cube (Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_pos 2]))
    calc w i * ((Y i) ^ 3 * Real.exp (ν * Y i))
        = (w i * Real.exp (ν * Y i))
            * ((1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i))) ^ 3) := by rw [← hcube]; ring
      _ ≤ (w i * Real.exp (ν * Y i))
            * ((1 / μ ^ 3) * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (hweight i)
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (1 / μ ^ 3) * ((w i * Real.exp (ν * Y i))
            * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3) := by ring
  have hJ : ∑ i, (w i * Real.exp (ν * Y i))
      * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
      ≤ Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3 := by
    have hvnn : ∀ i : ι, 0 ≤ w i * Real.exp (ν * Y i) / Mv :=
      fun i => div_nonneg (hweight i) hMpos.le
    have hv1 : ∑ i, w i * Real.exp (ν * Y i) / Mv = 1 := by
      rw [← Finset.sum_div, ← hMv]
      exact div_self hMpos.ne'
    have hjen := concaveOn_cube_log_add.le_map_sum (t := (Finset.univ : Finset ι))
      (w := fun i => w i * Real.exp (ν * Y i) / Mv)
      (p := fun i => Real.exp (μ * Y i)) (fun i _ => hvnn i) hv1
      (fun i _ => (Real.exp_pos _).le)
    simp only [smul_eq_mul] at hjen
    have hpt : ∑ i, w i * Real.exp (ν * Y i) / Mv * Real.exp (μ * Y i) = Mvm / Mv := by
      rw [hMvm, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add,
        show ν * Y i + μ * Y i = (ν + μ) * Y i from by ring]
    rw [hpt] at hjen
    have hmul := mul_le_mul_of_nonneg_left hjen hMpos.le
    calc ∑ i, (w i * Real.exp (ν * Y i))
          * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
        = Mv * ∑ i, w i * Real.exp (ν * Y i) / Mv
            * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
      _ ≤ Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3 := hmul
  have hdiv : Mvm / Mv ≤ Mvm := div_le_self hMvmnn hM1
  have hlast : (Real.log (Mvm / Mv + Real.exp 2)) ^ 3
      ≤ (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    refine cube_le_cube (Real.log_le_log ?_ (by linarith))
    have hq : (0:ℝ) ≤ Mvm / Mv := div_nonneg hMvmnn hMpos.le
    linarith [Real.exp_pos 2]
  have hRbound : R ≤ (1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    have h1 : (1 / μ ^ 3) * ∑ i, (w i * Real.exp (ν * Y i))
        * (Real.log (Real.exp (μ * Y i) + Real.exp 2)) ^ 3
        ≤ (1 / μ ^ 3) * (Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have h2 : (1 / μ ^ 3) * (Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3)
        ≤ (1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
      have : Mv * (Real.log (Mvm / Mv + Real.exp 2)) ^ 3
          ≤ Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left hlast hMpos.le
      nlinarith [this, (by positivity : (0:ℝ) < 1 / μ ^ 3)]
    linarith
  have hν3 : (0 : ℝ) < ν ^ 3 / 6 := by positivity
  have hfin : ν ^ 3 * R / 6
      ≤ ν ^ 3 / (6 * μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hRbound hν3.le
    calc ν ^ 3 * R / 6 = ν ^ 3 / 6 * R := by ring
      _ ≤ ν ^ 3 / 6 * ((1 / μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3) := this
      _ = ν ^ 3 / (6 * μ ^ 3) * Mv * (Real.log (Mvm + Real.exp 2)) ^ 3 := by
          field_simp
  linarith

/-- **C6**, Hölder in the three-factor (NS) form. -/
private lemma holder_three {ι : Type*} [Fintype ι] (a b wt : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hwt : ∀ i, 0 ≤ wt i)
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1)
    (hA : 0 < ∑ i, a i * wt i) (hB : 0 < ∑ i, b i * wt i) :
    ∑ i, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ (∑ i, a i * wt i) ^ (1 - ν) * (∑ i, b i * wt i) ^ ν := by
  classical
  set A : ℝ := ∑ i, a i * wt i with hAdef
  set B : ℝ := ∑ i, b i * wt i with hBdef
  have key : ∀ i : ι, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ (A ^ (1 - ν) * B ^ ν) * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) := by
    intro i
    have hgm := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - ν) hν0.le
      (div_nonneg (ha i) hA.le) (div_nonneg (hb i) hB.le) (by ring)
    have h1 : A ^ (1 - ν) * (a i / A) ^ (1 - ν) = (a i) ^ (1 - ν) := by
      rw [← Real.mul_rpow hA.le (div_nonneg (ha i) hA.le)]
      congr 1
      field_simp
    have h2 : B ^ ν * (b i / B) ^ ν = (b i) ^ ν := by
      rw [← Real.mul_rpow hB.le (div_nonneg (hb i) hB.le)]
      congr 1
      field_simp
    have hfact : (a i) ^ (1 - ν) * (b i) ^ ν
        = (A ^ (1 - ν) * B ^ ν) * ((a i / A) ^ (1 - ν) * (b i / B) ^ ν) := by
      rw [← h1, ← h2]; ring
    calc (a i) ^ (1 - ν) * (b i) ^ ν * wt i
        = (A ^ (1 - ν) * B ^ ν) * (((a i / A) ^ (1 - ν) * (b i / B) ^ ν) * wt i) := by
          rw [hfact]; ring
      _ ≤ (A ^ (1 - ν) * B ^ ν) * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgm (hwt i)) (by positivity)
  calc ∑ i, (a i) ^ (1 - ν) * (b i) ^ ν * wt i
      ≤ ∑ i, (A ^ (1 - ν) * B ^ ν)
          * (((1 - ν) * (a i / A) + ν * (b i / B)) * wt i) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (A ^ (1 - ν) * B ^ ν)
          * ∑ i, ((1 - ν) * (a i / A) + ν * (b i / B)) * wt i := by rw [Finset.mul_sum]
    _ = A ^ (1 - ν) * B ^ ν := by
        have hterm : ∀ i : ι, ((1 - ν) * (a i / A) + ν * (b i / B)) * wt i
            = ((1 - ν) / A) * (a i * wt i) + (ν / B) * (b i * wt i) := fun i => by ring
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← hAdef, ← hBdef]
        field_simp
        ring

/-- **C7**, Klein's inequality with the reference rescaled, in three-factor (NS) form. -/
private lemma klein_scaled {ι : Type*} [Fintype ι] (a b wt : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hwt : ∀ i, 0 ≤ wt i)
    (hA : ∑ i, a i * wt i = 1) (hB : 0 < ∑ i, b i * wt i)
    (hsupp : ∀ i, b i = 0 → a i * wt i = 0) :
    - Real.log (∑ i, b i * wt i)
      ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) * wt i := by
  classical
  set Q : ℝ := ∑ i, b i * wt i with hQdef
  have key : ∀ i : ι, a i * wt i - b i * wt i / Q
      ≤ a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i := by
    intro i
    rcases eq_or_lt_of_le (hwt i) with hw0 | hwpos
    · simp [← hw0]
    rcases eq_or_lt_of_le (ha i) with ha0 | hapos
    · have : b i * wt i / Q ≥ 0 := div_nonneg (mul_nonneg (hb i) (hwt i)) hB.le
      simp only [← ha0]
      nlinarith
    have hbne : b i ≠ 0 := by
      intro h0
      have := hsupp i h0
      nlinarith
    have hbpos : 0 < b i := lt_of_le_of_ne (hb i) (Ne.symm hbne)
    have hs : 0 < b i / (a i * Q) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hs
    rw [Real.log_div hbne (by positivity), Real.log_mul (ne_of_gt hapos) (ne_of_gt hB)] at hlog
    have hstep : a i * (Real.log (a i) - Real.log (b i) + Real.log Q) ≥ a i - b i / Q := by
      have h2 := mul_le_mul_of_nonneg_left hlog hapos.le
      have h3 : a i * (b i / (a i * Q) - 1) = b i / Q - a i := by field_simp
      rw [h3] at h2
      linarith
    have := mul_le_mul_of_nonneg_right hstep hwpos.le
    calc a i * wt i - b i * wt i / Q = (a i - b i / Q) * wt i := by field_simp
      _ ≤ a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i := this
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  have hlhs : ∑ i, (a i * wt i - b i * wt i / Q) = 0 := by
    rw [Finset.sum_sub_distrib, hA, ← Finset.sum_div, ← hQdef, div_self (ne_of_gt hB)]
    ring
  have hrhs : ∑ i, a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i
      = (∑ i, a i * (Real.log (a i) - Real.log (b i)) * wt i) + Real.log Q := by
    have hterm : ∀ i : ι, a i * (Real.log (a i) - Real.log (b i) + Real.log Q) * wt i
        = a i * (Real.log (a i) - Real.log (b i)) * wt i + Real.log Q * (a i * wt i) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum, hA]
    ring
  rw [hlhs, hrhs] at hsum
  linarith

end ClassicalCore

/-! ### The `(w, ℓ)` reduction -/

section NSWeights

variable {m : Type*} [Fintype m] [DecidableEq m]

private def nsW {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (p : m × m) : ℝ :=
  hρ.eigenvalues p.1 * nsOverlap hρ hσ p.1 p.2

private def nsL {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (p : m × m) : ℝ :=
  Real.log (hρ.eigenvalues p.1) - Real.log (hσ.eigenvalues p.2)

private lemma nsW_nonneg {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (p : m × m) : 0 ≤ nsW hρ hσ p :=
  mul_nonneg (ns_eigenvalues_nonneg hρ hρ0 p.1) (nsOverlap_nonneg hρ hσ p.1 p.2)

private lemma nsW_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p = ρ.trace.re := by
  rw [ns_trace_rho hρ hσ, Fintype.sum_prod_type]
  rfl

private lemma nsWL_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p * nsL hρ hσ p
      = (ρ * (CFC.log ρ - CFC.log σ)).trace.re := by
  rw [ns_trace_relEnt hρ hσ, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    simp only [nsW, nsL]; ring

private lemma nsWL2_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p) ^ 2
      = (ρ * (CFC.log ρ - CFC.log σ) ^ 2).trace.re := by
  rw [ns_trace_relEntSq hρ hσ, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    simp only [nsW, nsL]; ring

/-- The `petzTrace` at every positive order, in `(w, ℓ)` form. This is where `hsupp` enters. -/
private lemma nsW_exp_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {a : ℝ} (ha : 0 < a) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp ((a - 1) * nsL hρ hσ p) = petzTrace a ρ σ := by
  rw [ns_petzTrace hρ0 hσ0 hρ hσ a, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [nsW, nsL]
  by_cases hc : nsOverlap hρ hσ x y = 0
  · rw [hc]; ring
  rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hρ hρ0 x) with hlam | hlam
  · rw [← hlam, Real.zero_rpow (ne_of_gt ha)]; ring
  have hmu : 0 < hσ.eigenvalues y := by
    rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hσ hσ0 y) with hm | hm
    · exfalso
      rcases mul_eq_zero.mp (ns_support hρ hσ hρ0 hsupp hm.symm x) with h | h
      · linarith
      · exact hc h
    · exact hm
  obtain ⟨L, hL⟩ : ∃ L : ℝ, hρ.eigenvalues x = Real.exp L :=
    ⟨Real.log (hρ.eigenvalues x), (Real.exp_log hlam).symm⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, hσ.eigenvalues y = Real.exp N :=
    ⟨Real.log (hσ.eigenvalues y), (Real.exp_log hmu).symm⟩
  rw [hL, hN, Real.log_exp, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos L), Real.rpow_def_of_pos (Real.exp_pos N),
    Real.log_exp, Real.log_exp, ← Real.exp_add]
  rw [show Real.exp L * nsOverlap hρ hσ x y * Real.exp ((a - 1) * (L - N))
      = Real.exp (L + (a - 1) * (L - N)) * nsOverlap hρ hσ x y from by
        rw [Real.exp_add]; ring]
  congr 2
  ring

/-- The `ν = 1` endpoint of the reference sum: `∑ w e^{−ℓ} ≤ Tr σ`. -/
private lemma nsW_exp_neg_le {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp (-(nsL hρ hσ p)) ≤ σ.trace.re := by
  rw [ns_trace_sigma hρ hσ, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  simp only [nsW, nsL]
  by_cases hc : nsOverlap hρ hσ x y = 0
  · rw [hc]; simp
  rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hρ hρ0 x) with hlam | hlam
  · rw [← hlam]
    simp only [zero_mul]
    exact mul_nonneg (ns_eigenvalues_nonneg hσ hσ0 y) (nsOverlap_nonneg hρ hσ x y)
  have hmu : 0 < hσ.eigenvalues y := by
    rcases eq_or_lt_of_le (ns_eigenvalues_nonneg hσ hσ0 y) with hm | hm
    · exfalso
      rcases mul_eq_zero.mp (ns_support hρ hσ hρ0 hsupp hm.symm x) with h | h
      · linarith
      · exact hc h
    · exact hm
  obtain ⟨L, hL⟩ : ∃ L : ℝ, hρ.eigenvalues x = Real.exp L :=
    ⟨Real.log (hρ.eigenvalues x), (Real.exp_log hlam).symm⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, hσ.eigenvalues y = Real.exp N :=
    ⟨Real.log (hσ.eigenvalues y), (Real.exp_log hmu).symm⟩
  rw [hL, hN, Real.log_exp, Real.log_exp,
    show Real.exp L * nsOverlap hρ hσ x y * Real.exp (-(L - N))
      = Real.exp (L + -(L - N)) * nsOverlap hρ hσ x y from by rw [Real.exp_add]; ring,
    show L + -(L - N) = N from by ring]

private lemma nsRef_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ p : m × m, hσ.eigenvalues p.2 * nsOverlap hρ hσ p.1 p.2 = σ.trace.re := by
  rw [ns_trace_sigma hρ hσ, Fintype.sum_prod_type]

private def nsD {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : ℝ :=
  ∑ p : m × m, nsW hρ hσ p * nsL hρ hσ p

private lemma ns_sum_one {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) : ∑ p : m × m, nsW hρ hσ p = 1 := by
  rw [nsW_sum hρ hσ, hnorm]

private lemma ns_relEnt_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    relEntropyBase2 ρ σ = nsD hρ hσ / Real.log 2 := by
  rw [relEntropyBase2, hnorm, one_mul, nsD, nsWL_sum hρ hσ]

private lemma ns_Y_sum {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    ∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) = 0 := by
  have hterm : ∀ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ)
      = nsW hρ hσ p * nsL hρ hσ p - nsD hρ hσ * nsW hρ hσ p := fun p => by ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ns_sum_one hρ hσ hnorm, mul_one, ← nsD]
  ring

private lemma ns_divVar_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) :
    petzDivergenceVariance ρ σ
      = (∑ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) ^ 2) / (Real.log 2) ^ 2 := by
  have hexp : ∀ p : m × m, nsW hρ hσ p * (nsL hρ hσ p - nsD hρ hσ) ^ 2
      = nsW hρ hσ p * (nsL hρ hσ p) ^ 2
        - 2 * nsD hρ hσ * (nsW hρ hσ p * nsL hρ hσ p)
        + (nsD hρ hσ) ^ 2 * nsW hρ hσ p := fun p => by ring
  rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ns_sum_one hρ hσ hnorm, mul_one, ← nsD,
    nsWL2_sum hρ hσ, petzDivergenceVariance, hnorm, one_mul,
    ns_relEnt_eq hρ hσ hnorm]
  have hl2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  field_simp
  ring

private lemma ns_M_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0)
    {s : ℝ} (hs : 0 < 1 + s) :
    ∑ p : m × m, nsW hρ hσ p * Real.exp (s * (nsL hρ hσ p - nsD hρ hσ))
      = Real.exp (-(s * nsD hρ hσ)) * petzTrace (1 + s) ρ σ := by
  have hterm : ∀ p : m × m, nsW hρ hσ p * Real.exp (s * (nsL hρ hσ p - nsD hρ hσ))
      = Real.exp (-(s * nsD hρ hσ))
        * (nsW hρ hσ p * Real.exp ((1 + s - 1) * nsL hρ hσ p)) := by
    intro p
    rw [show (1 : ℝ) + s - 1 = s from by ring,
      show Real.exp (-(s * nsD hρ hσ)) * (nsW hρ hσ p * Real.exp (s * nsL hρ hσ p))
        = nsW hρ hσ p * (Real.exp (-(s * nsD hρ hσ)) * Real.exp (s * nsL hρ hσ p)) from by ring,
      ← Real.exp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum,
    nsW_exp_sum hρ hσ hρ0 hσ0 hsupp hs]

private lemma two_rpow_relEnt {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hnorm : ρ.trace.re = 1) (t : ℝ) :
    (2 : ℝ) ^ (t * relEntropyBase2 ρ σ) = Real.exp (t * nsD hρ hσ) := by
  have hl2 : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  rw [ns_relEnt_eq hρ hσ hnorm, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1
  field_simp

/-- `2^{(β−1)(D'_β − D)} = M(β−1)`, the identity that turns `petzContinuityK` into the
classical remainder. -/
private lemma ns_two_rpow_eq {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ) (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) {β : ℝ} (hβ : 1 < β) :
    (2 : ℝ) ^ ((β - 1) * (petzRenyiDivergence β ρ σ - relEntropyBase2 ρ σ))
      = ∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hβ1 : (0 : ℝ) < β - 1 := by linarith
  have hMv := ns_M_eq hρ hσ hρ0 hσ0 hsupp (s := β - 1) (by linarith)
  rw [show (1 : ℝ) + (β - 1) = β from by ring] at hMv
  have hM1 := classical_M_ge_one (nsW hρ hσ) (fun p => nsL hρ hσ p - nsD hρ hσ)
    (fun p => nsW_nonneg hρ hσ hρ0 p) (ns_sum_one hρ hσ hnorm) (ns_Y_sum hρ hσ hnorm) (β - 1)
  have hMpos : (0 : ℝ) < ∑ p : m × m, nsW hρ hσ p
      * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := lt_of_lt_of_le zero_lt_one hM1
  have hpt : petzTrace β ρ σ = Real.exp ((β - 1) * nsD hρ hσ)
      * ∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)) := by
    rw [hMv, ← mul_assoc, ← Real.exp_add,
      show (β - 1) * nsD hρ hσ + -((β - 1) * nsD hρ hσ) = 0 from by ring, Real.exp_zero, one_mul]
  have hdiv : petzRenyiDivergence β ρ σ - relEntropyBase2 ρ σ
      = Real.log (∑ p : m × m, nsW hρ hσ p * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ)))
        / ((β - 1) * Real.log 2) := by
    rw [petzRenyiDivergence, hpt, Real.logb,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hMpos), Real.log_exp,
      ns_relEnt_eq hρ hσ hnorm]
    field_simp
    ring
  rw [hdiv, show (β - 1) * (Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / ((β - 1) * Real.log 2))
      = Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / Real.log 2 from by
      field_simp,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * (Real.log (∑ p : m × m, nsW hρ hσ p
          * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) / Real.log 2)
      = Real.log (∑ p : m × m, nsW hρ hσ p
        * Real.exp ((β - 1) * (nsL hρ hσ p - nsD hρ hσ))) from by field_simp,
    Real.exp_log hMpos]

end NSWeights

/-!
## Order facts about the pinned reference

`PetzConditional.lean` proves the two block-level facts below as `private` lemmas, so they
are not reachable from here; the combined form `ρ_XB ≤ 1_X ⊗ ρ_B` that every side condition
in this file needs is stated publicly.
-/

/-- Each cq block is dominated by the quantum marginal: `σ_x ≤ ρ_B`, because
`ρ_B − σ_x = ∑_{y ≠ x} σ_y` is a sum of positive semidefinite blocks. -/
private lemma stateMap_toOp_le_marginal {X : Type*} [Fintype X] {n : ℕ}
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

/-- The quantum marginal is positive semidefinite. -/
private lemma quantumMarginalOp_nonneg' {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : (0 : Op n) ≤ ρ.quantumMarginalOp := by
  rw [CQState.quantumMarginalOp]
  exact Finset.sum_nonneg fun y _ => Matrix.nonneg_iff_posSemidef.mpr
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap y).toPosSemidefOp)

/-- The pinned reference `1_X ⊗ ρ_B` is positive semidefinite. -/
theorem blockDiagonal_quantumMarginalOp_nonneg {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (ρ : CQState X n) :
    (0 : Matrix (Fin n × X) (Fin n × X) ℂ)
      ≤ Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp) := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact Matrix.posSemidef_blockDiagonal fun _ =>
    Matrix.nonneg_iff_posSemidef.mp (quantumMarginalOp_nonneg' ρ)

/-- `ρ_XB ≤ 1_X ⊗ ρ_B`, the cq instance of Tomamichel's `ρ_AB ≤ 1_A ⊗ ρ_B`
(arXiv:1504.00233, `cond.tex:576`). -/
theorem toJointOp_le_blockDiagonal_quantumMarginalOp {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (ρ : CQState X n) :
    ρ.toJointOp ≤ Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp) := by
  rw [CQState.toJointOp, Matrix.le_iff, ← Matrix.blockDiagonal_sub]
  refine Matrix.posSemidef_blockDiagonal fun x => ?_
  simpa [Pi.sub_apply] using Matrix.le_iff.mp (stateMap_toOp_le_marginal ρ x)

/-- The Loewner order carries kernel inclusion backwards: `0 ≤ A ≤ B` forces
`ker B ⊆ ker A`. -/
private lemma mulVec_eq_zero_of_le {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) {v : m → ℂ}
    (hv : B.mulVec v = 0) : A.mulVec v = 0 := by
  have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA
  have hBA : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have h1 : (0 : ℂ) ≤ star v ⬝ᵥ ((B - A).mulVec v) := hBA.dotProduct_mulVec_nonneg v
  have h2 : (0 : ℂ) ≤ star v ⬝ᵥ (A.mulVec v) := hApsd.dotProduct_mulVec_nonneg v
  have h3 : star v ⬝ᵥ ((B - A).mulVec v) = - (star v ⬝ᵥ (A.mulVec v)) := by
    rw [Matrix.sub_mulVec, hv, dotProduct_sub, dotProduct_zero, zero_sub]
  rw [h3] at h1
  exact hApsd.dotProduct_mulVec_zero_iff.mp
    (le_antisymm (neg_nonneg.mp h1) h2)

/-- The `hsupp` side condition of the divergence bounds, on the cq instance: the pinned
reference `1_X ⊗ ρ_B` has kernel inside the kernel of `ρ_XB`. -/
theorem toJointOp_ker_sub {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (v : Fin n × X → ℂ)
    (hv : (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)).mulVec v = 0) :
    ρ.toJointOp.mulVec v = 0 :=
  mulVec_eq_zero_of_le (Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef)
    (toJointOp_le_blockDiagonal_quantumMarginalOp ρ) hv

private lemma aeval_blockDiagonal' {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
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

private lemma cfc_blockDiagonal' {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
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
    rw [← cfc_polynomial (R := ℝ) q (Matrix.blockDiagonal M)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hμ)
  have hblk : ∀ x, cfc f (M x) = (Polynomial.aeval (M x)) q := by
    intro x
    rw [← cfc_polynomial (R := ℝ) q (M x)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x,
        by rw [Set.Finite.mem_toFinset]; exact hμ⟩)
  rw [hmain, aeval_blockDiagonal']
  exact congrArg _ (funext fun x => (hblk x).symm)

section CQAux

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

omit [DecidableEq X] in
private lemma quantumMarginalOp_trace_re (ρ : CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) : ρ.quantumMarginalOp.trace.re = 1 := by
  rw [CQState.quantumMarginalOp, Matrix.trace_sum, Complex.re_sum]
  exact hnorm

private lemma ref_trace_re (ρ : CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)).trace.re
      = (Fintype.card X : ℝ) := by
  rw [Matrix.trace_blockDiagonal, Complex.re_sum, quantumMarginalOp_trace_re ρ hnorm]
  simp

omit [DecidableEq X] in
private lemma card_pos_of_norm (ρ : CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) : 0 < Fintype.card X := by
  by_contra h
  have hE : IsEmpty X := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (Nat.not_lt.mp h))
  simp at hnorm

end CQAux


/-!
## Bridge to the nonnegativity theorems
-/

/-- Blockwise evaluation of `condVonNeumann`. `condVonNeumann_nonneg_of_cq`
(`PetzConditional.lean`) is stated over the inline blockwise natural-log sum rather than
over any definition, so this identity is what transports it onto `condVonNeumann`.

Proof route: `cfc_blockDiagonal`
at `f = Real.log`, then `Matrix.blockDiagonal_sub`, `Matrix.blockDiagonal_mul` and
`Matrix.trace_blockDiagonal`. `cfc_blockDiagonal` is `private` in `PetzConditional.lean`
(`:603`). -/
theorem condVonNeumann_eq_blockwise {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    condVonNeumann ρ =
      (- ∑ x : X, ((ρ.stateMap x).toOp
          * (CFC.log (ρ.stateMap x).toOp - CFC.log ρ.quantumMarginalOp)).trace.re)
        / (ρ.toJointOp.trace.re * Real.log 2) := by
  have hsa : ∀ x : X, IsSelfAdjoint ((ρ.stateMap x).toOp) := fun x =>
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp).isHermitian
  have hsaB : ∀ _ : X, IsSelfAdjoint ρ.quantumMarginalOp := fun _ =>
    (Matrix.nonneg_iff_posSemidef.mp (quantumMarginalOp_nonneg' ρ)).isHermitian
  have hlogJ : CFC.log ρ.toJointOp
      = Matrix.blockDiagonal (fun x => CFC.log (ρ.stateMap x).toOp) := by
    rw [CQState.toJointOp, log_eq_cfc', cfc_blockDiagonal' _ hsa Real.log]
    rfl
  have hlogS : CFC.log (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
      = Matrix.blockDiagonal (fun _ : X => CFC.log ρ.quantumMarginalOp) := by
    rw [log_eq_cfc', cfc_blockDiagonal' _ hsaB Real.log]
    rfl
  have hnum : (ρ.toJointOp * (CFC.log ρ.toJointOp
      - CFC.log (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)))).trace.re
      = ∑ x : X, ((ρ.stateMap x).toOp
          * (CFC.log (ρ.stateMap x).toOp - CFC.log ρ.quantumMarginalOp)).trace.re := by
    rw [hlogJ, hlogS, CQState.toJointOp, ← Matrix.blockDiagonal_sub,
      ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal, Complex.re_sum]
    rfl
  rw [condVonNeumann, relEntropyBase2, hnum, neg_div]

/-- `0 ≤ H(X|B)_ρ` for a classical-quantum state, on the definition.

This is `condVonNeumann_nonneg_of_cq` (`PetzConditional.lean`, DF `:450`) transported
through `condVonNeumann_eq_blockwise`; the denominator is `Real.log 2 > 0` because `hnorm`
gives `Tr[ρ_XB] = 1`. -/
theorem condVonNeumann_nonneg {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    0 ≤ condVonNeumann ρ := by
  have hJtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  rw [condVonNeumann_eq_blockwise ρ, hJtr, one_mul]
  exact div_nonneg (condVonNeumann_nonneg_of_cq ρ) (Real.log_nonneg one_le_two)

/-!
## The general variance bound (DF `:394`)
-/

/-- **DF `:394` `\label{lem:divergence-variance-general-bounds}`**, equation
`\label{eq:bound_dalpha}` at `:398` with the display at `:399`.

`2^{ν D'_{1+ν}} = Tr[ρ^{1+ν}σ^{-ν}] = petzTrace (1+ν) ρ σ` (`:420`) and
`2^{-ν D'_{1-ν}} = Tr[ρ^{1-ν}σ^{ν}] = petzTrace (1-ν) ρ σ` (`:424`), so the source's
display is stated here through `petzTrace`, which is defined at EVERY real order. This is
what keeps the leaf inside the `1 < α ≤ 2` branch of `petzRenyiDivergence` — see the
module docstring.

`hnorm` strengthens DF `:395` and is required; see the module docstring.

Proof route: the classical chain
`V̂ ≤ ν⁻² ln²(M ν + M (−ν) + 1)` from `(log t)² ≤ (log (t + t⁻¹ + 1))²` and concavity of
`ln²` on `[e,∞)`, lifted to operators by the Nussbaum–Szkoła bridge (§2.2, DF
`:770`–`:774`). -/
theorem petzDivergenceVariance_le {m : Type*} [Fintype m] [DecidableEq m]
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (ρ σ : Matrix m m ℂ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    petzDivergenceVariance ρ σ ≤
      (1 / ν ^ 2) * (Real.logb 2
        ((2 : ℝ) ^ (-ν * relEntropyBase2 ρ σ) * petzTrace (1 + ν) ρ σ
          + (2 : ℝ) ^ (ν * relEntropyBase2 ρ σ) * petzTrace (1 - ν) ρ σ
          + 1)) ^ 2 := by
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  have hσh : σ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hσ).isHermitian
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : (2 : ℝ) ^ (-ν * relEntropyBase2 ρ σ) * petzTrace (1 + ν) ρ σ
      = ∑ p : m × m, nsW hρh hσh p * Real.exp (ν * (nsL hρh hσh p - nsD hρh hσh)) := by
    rw [two_rpow_relEnt hρh hσh hnorm (-ν),
      ns_M_eq hρh hσh hρ hσ hsupp (s := ν) (by linarith),
      show -ν * nsD hρh hσh = -(ν * nsD hρh hσh) from by ring]
  have hM2 : (2 : ℝ) ^ (ν * relEntropyBase2 ρ σ) * petzTrace (1 - ν) ρ σ
      = ∑ p : m × m, nsW hρh hσh p * Real.exp (-ν * (nsL hρh hσh p - nsD hρh hσh)) := by
    rw [two_rpow_relEnt hρh hσh hnorm ν,
      ns_M_eq hρh hσh hρ hσ hsupp (s := -ν) (by linarith),
      show (1 : ℝ) + -ν = 1 - ν from by ring,
      show -(-ν * nsD hρh hσh) = ν * nsD hρh hσh from by ring]
  have hcl := classical_var_le (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) hν0
  rw [← hM1, ← hM2] at hcl
  rw [ns_divVar_eq hρh hσh hnorm, Real.logb, div_le_iff₀ (by positivity : (0:ℝ) < Real.log 2 ^ 2)]
  refine hcl.trans (le_of_eq ?_)
  field_simp

/-!
## The conditional-entropy cap and the general-`ν` moment term (DF `:429`, `:450`)
-/

/-- The `2^{νD − νD'_{1−ν}}` term of `:399`, bounded by `d_A^ν`. This is DF's
`H'_{1−ν}(A|B) ≤ log d_A` (`:450`) rewritten so that no `α < 1` divergence appears.

Proof route: Hölder
`∑ p^{1−ν} q^ν ≤ (∑p)^{1−ν}(∑q)^ν` on the Nussbaum–Szkoła pair, with `∑ p = Tr[ρ_XB] = 1`
and `∑ q = Tr[1_X ⊗ ρ_B] = |X|`. Kept as the general-`ν` form of the `:399` term; the improved
classical-`A` cap `condDivergenceVariance_le_logb_sqrt_card` below uses only the `ν = 1`
endpoint facts. -/
theorem petzTrace_one_sub_le_card_rpow {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    petzTrace (1 - ν) ρ.toJointOp
        (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
      ≤ (Fintype.card X : ℝ) ^ ν := by
  have hR0 : (0 : Matrix (Fin n × X) (Fin n × X) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef
  have hS0 := blockDiagonal_quantumMarginalOp_nonneg ρ
  have hRh : ρ.toJointOp.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
  have hSh : (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hRtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  have hStr := ref_trace_re ρ hnorm
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast card_pos_of_norm ρ hnorm
  have hA : ∑ p : (Fin n × X) × (Fin n × X),
      hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2 = 1 := by
    rw [show (fun p : (Fin n × X) × (Fin n × X) =>
        hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2) = nsW hRh hSh from rfl,
      nsW_sum hRh hSh, hRtr]
  have hB : ∑ p : (Fin n × X) × (Fin n × X),
      hSh.eigenvalues p.2 * nsOverlap hRh hSh p.1 p.2 = (Fintype.card X : ℝ) := by
    rw [nsRef_sum hRh hSh, hStr]
  have hhold := holder_three (fun p : (Fin n × X) × (Fin n × X) => hRh.eigenvalues p.1)
    (fun p => hSh.eigenvalues p.2) (fun p => nsOverlap hRh hSh p.1 p.2)
    (fun p => ns_eigenvalues_nonneg hRh hR0 p.1) (fun p => ns_eigenvalues_nonneg hSh hS0 p.2)
    (fun p => nsOverlap_nonneg hRh hSh p.1 p.2) hν0 hν1
    (by rw [hA]; norm_num) (by rw [hB]; exact hcard)
  rw [hA, hB, Real.one_rpow, one_mul] at hhold
  rw [ns_petzTrace hR0 hS0 hRh hSh (1 - ν), show (1 : ℝ) - (1 - ν) = ν from by ring,
    ← Fintype.sum_prod_type (fun p : (Fin n × X) × (Fin n × X) =>
      hRh.eigenvalues p.1 ^ (1 - ν) * hSh.eigenvalues p.2 ^ ν * nsOverlap hRh hSh p.1 p.2)]
  exact hhold

/-- `H(X|B)_ρ ≤ log₂ d_A`, the upper half of Tomamichel Lemma 5.2, which DF cite at `:450`.
`condVonNeumann_nonneg` supplies only the lower half.

Proof route: Klein's inequality in the
rescaled form `∑ p (log p − log q) ≥ −log (∑ q)` on the Nussbaum–Szkoła pair, at
`∑ q = Tr[1_X ⊗ ρ_B] = |X|`. The unscaled operator Klein `D ≥ Tr ρ − Tr σ` is too weak: it
gives `1 − d`, and `1 − d < −ln d` for every `d ≥ 2`. -/
theorem condVonNeumann_le_logb_card {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    condVonNeumann ρ ≤ Real.logb 2 (Fintype.card X) := by
  have hR0 : (0 : Matrix (Fin n × X) (Fin n × X) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef
  have hS0 := blockDiagonal_quantumMarginalOp_nonneg ρ
  have hRh : ρ.toJointOp.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
  have hSh : (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hRtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  have hStr := ref_trace_re ρ hnorm
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast card_pos_of_norm ρ hnorm
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : ∑ p : (Fin n × X) × (Fin n × X),
      hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2 = 1 := by
    rw [show (fun p : (Fin n × X) × (Fin n × X) =>
        hRh.eigenvalues p.1 * nsOverlap hRh hSh p.1 p.2) = nsW hRh hSh from rfl,
      nsW_sum hRh hSh, hRtr]
  have hB : ∑ p : (Fin n × X) × (Fin n × X),
      hSh.eigenvalues p.2 * nsOverlap hRh hSh p.1 p.2 = (Fintype.card X : ℝ) := by
    rw [nsRef_sum hRh hSh, hStr]
  have hklein := klein_scaled (fun p : (Fin n × X) × (Fin n × X) => hRh.eigenvalues p.1)
    (fun p => hSh.eigenvalues p.2) (fun p => nsOverlap hRh hSh p.1 p.2)
    (fun p => ns_eigenvalues_nonneg hRh hR0 p.1) (fun p => ns_eigenvalues_nonneg hSh hS0 p.2)
    (fun p => nsOverlap_nonneg hRh hSh p.1 p.2)
    hA (by rw [hB]; exact hcard)
    (fun p hp => ns_support hRh hSh hR0 (toJointOp_ker_sub ρ) hp p.1)
  rw [hB] at hklein
  have hnsD : ∑ p : (Fin n × X) × (Fin n × X), hRh.eigenvalues p.1
      * (Real.log (hRh.eigenvalues p.1) - Real.log (hSh.eigenvalues p.2))
      * nsOverlap hRh hSh p.1 p.2 = nsD hRh hSh := by
    rw [nsD]
    exact Finset.sum_congr rfl fun p _ => by simp only [nsW, nsL]; ring
  rw [hnsD] at hklein
  rw [condVonNeumann, ns_relEnt_eq hRh hSh hRtr, Real.logb, ← neg_div,
    div_le_div_iff_of_pos_right hl2]
  linarith

/-!
## The second-order continuity bound (DF `:710`)
-/

/-- `K_{ρ,σ}(α,μ)` of DF `:715`, verbatim and with NO hidden `sup`: DF's `sup_{0<γ≤ν}` at
`:731` is internal to their proof, and the remainder is pointwise monotone in `γ`
(`∂_γ (z^γ ln³z) = z^γ ln⁴z ≥ 0`), so the supremum is superfluous and the statement carries
none. -/
def petzContinuityK {m : Type*} [Fintype m] [DecidableEq m]
    (α μ : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  (1 / (6 * μ ^ 3 * Real.log 2))
    * (2 : ℝ) ^ ((α - 1) * (petzRenyiDivergence α ρ σ - relEntropyBase2 ρ σ))
    * (Real.log ((2 : ℝ) ^ ((α + μ - 1)
        * (petzRenyiDivergence (α + μ) ρ σ - relEntropyBase2 ρ σ))
        + Real.exp 2)) ^ 3

/-- **DF `:713` (lemma head `:710`, `\label{lem_HalphaH_second_order_new}` at `:711`), the
`D'_α ≤ …` half only.** The `D_α ≤ D'_α` half is about the SANDWICHED divergence and is NOT
stated here.

No cap on `α + μ` is needed; see the module docstring.

Proof route: the classical MGF chain
`ln (M ν) ≤ ν²V̂/2 + (ν³/6)·R` from `exp u ≤ 1 + u + u²/2 + (u³/6)·exp u` and
`ln (1+x) ≤ x`, with `R` controlled by concavity of `t ↦ ln³(t + e²)`, lifted to operators
by the Nussbaum–Szkoła bridge (§2.2, DF `:770`–`:774`). -/
theorem petzRenyiDivergence_le_relEntropy_add {m : Type*} [Fintype m] [DecidableEq m]
    (α μ : ℝ) (hα : 1 < α) (hμ0 : 0 < μ)
    (ρ σ : Matrix m m ℂ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hnorm : ρ.trace.re = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    petzRenyiDivergence α ρ σ
      ≤ relEntropyBase2 ρ σ
        + ((α - 1) * Real.log 2 / 2) * petzDivergenceVariance ρ σ
        + (α - 1) ^ 2 * petzContinuityK α μ ρ σ := by
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  have hσh : σ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hσ).isHermitian
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hν : (0 : ℝ) < α - 1 := by linarith
  have hβ2 : (1 : ℝ) < α + μ := by linarith
  -- `Mv` and `Mvm`
  have hMv := ns_two_rpow_eq hρh hσh hρ hσ hnorm hsupp hα
  have hMvm := ns_two_rpow_eq hρh hσh hρ hσ hnorm hsupp hβ2
  rw [show α + μ - 1 = (α - 1) + μ from by ring] at hMvm
  -- `D'_α − D`
  have hMge := classical_M_ge_one (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) (ns_Y_sum hρh hσh hnorm)
    (α - 1)
  have hMpos : (0 : ℝ) < ∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh)) := lt_of_lt_of_le zero_lt_one hMge
  have hdiff : petzRenyiDivergence α ρ σ - relEntropyBase2 ρ σ
      = Real.log (∑ p : m × m, nsW hρh hσh p
          * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh))) / ((α - 1) * Real.log 2) := by
    have h := hMv
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    have hlog := congrArg Real.log h
    rw [Real.log_exp] at hlog
    field_simp at hlog ⊢
    linarith [hlog]
  -- the classical bound
  have hcl := classical_continuity_le (nsW hρh hσh) (fun p => nsL hρh hσh p - nsD hρh hσh)
    (fun p => nsW_nonneg hρh hσh hρ p) (ns_sum_one hρh hσh hnorm) (ns_Y_sum hρh hσh hnorm)
    hν hμ0
  rw [petzContinuityK, show α + μ - 1 = α - 1 + μ from by ring, hMv, hMvm,
    ns_divVar_eq hρh hσh hnorm]
  set A : ℝ := Real.log (∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh))) with hA
  set B : ℝ := ∑ p : m × m, nsW hρh hσh p * (nsL hρh hσh p - nsD hρh hσh) ^ 2 with hB
  set Mv : ℝ := ∑ p : m × m, nsW hρh hσh p
      * Real.exp ((α - 1) * (nsL hρh hσh p - nsD hρh hσh)) with hMvdef
  set L3 : ℝ := (Real.log ((∑ p : m × m, nsW hρh hσh p
      * Real.exp (((α - 1) + μ) * (nsL hρh hσh p - nsD hρh hσh))) + Real.exp 2)) ^ 3 with hL3
  have hgoal : A / ((α - 1) * Real.log 2)
      ≤ (α - 1) * Real.log 2 / 2 * (B / Real.log 2 ^ 2)
        + (α - 1) ^ 2 * (1 / (6 * μ ^ 3 * Real.log 2) * Mv * L3) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (α - 1) * Real.log 2)]
    have hrw : ((α - 1) * Real.log 2 / 2 * (B / Real.log 2 ^ 2)
          + (α - 1) ^ 2 * (1 / (6 * μ ^ 3 * Real.log 2) * Mv * L3)) * ((α - 1) * Real.log 2)
        = (α - 1) ^ 2 * B / 2 + (α - 1) ^ 3 / (6 * μ ^ 3) * Mv * L3 := by
      field_simp
    rw [hrw]
    exact hcl
  have := hdiff
  linarith [hgoal, hdiff]

/-!
## Corollary IV.2 in Petz-DOWN form (DF `:783`)
-/

/-- `K(α)` of DF `:789`, written for the Petz-DOWN object: `D'_α − D = −H'_α + H` and
`α + μ − 1 = 1` at `μ = 2 − α`, so `D'_{α+μ} − D = −H'_2 + H`. -/
def secondOrderK {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) : ℝ :=
  (1 / (6 * (2 - α) ^ 3 * Real.log 2))
    * (2 : ℝ) ^ ((α - 1) * (condVonNeumann ρ - condPetzRenyiDown α ρ))
    * (Real.log ((2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ)
        + Real.exp 2)) ^ 3

/-- `secondOrderK` is `petzContinuityK` at `μ = 2 − α` and the pinned reference; this makes the
`μ = 2 − α` instantiation of DF `:782` literal. -/
theorem secondOrderK_eq_petzContinuityK {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α : ℝ) (ρ : CQState X n) :
    secondOrderK α ρ = petzContinuityK α (2 - α) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) := by
  have h2 : α + (2 - α) = 2 := by ring
  simp only [secondOrderK, petzContinuityK, condVonNeumann, condPetzRenyiDown, h2]
  rw [show (α - 1) * (-relEntropyBase2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        - -petzRenyiDivergence α ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)))
      = (α - 1) * (petzRenyiDivergence α ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        - relEntropyBase2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))) from by ring,
    show -relEntropyBase2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        - -petzRenyiDivergence 2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
      = (2 - 1) * (petzRenyiDivergence 2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        - relEntropyBase2 ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))) from by ring]

/-- **DF `:787` `\label{cor:continuity-bound-halpha_new}` (at `:784`), Petz-DOWN form.**

The source states it for the SANDWICHED-down `H_α` and gets there from the Petz statement
by `D_α ≤ D'_α` (`:782`); the Petz-down form proved here is the STRONGER intermediate
(`H_α ≥ H'_α ≥ RHS`) and is the one that composes with `renyiCondEntropy_down_tensorPower`.

`hα2 : α < 2` is strict because `secondOrderK` divides by `(2 − α)³`; `condPetzRenyiDown 2 ρ`
inside `secondOrderK` sits at the endpoint of the `1 < α ≤ 2` branch, which is legal.

**Ordering.** `V(X|B)` is additive while the variance–dimension cap
(`condDivergenceVariance_le_logb_sqrt_card`, the `card X = 2` corollary
`condDivergenceVariance_le_logb_one_add_sqrt_two`) is
constant in the block count, so on an `m`-fold tensor power
`renyiCondEntropy_down_tensorPower` must be applied FIRST and this bound per round afterwards
(`PetzConditional.lean:896`). -/
theorem condPetzRenyiDown_ge_condVonNeumann_sub {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    condVonNeumann ρ
        - ((α - 1) * Real.log 2 / 2) * condDivergenceVariance ρ
        - (α - 1) ^ 2 * secondOrderK α ρ
      ≤ condPetzRenyiDown α ρ := by
  have hJtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  have hkey := petzRenyiDivergence_le_relEntropy_add (m := Fin n × X) α (2 - α) hα1
    (by linarith) ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
    (Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef)
    (blockDiagonal_quantumMarginalOp_nonneg ρ) hJtr (toJointOp_ker_sub ρ)
  rw [← secondOrderK_eq_petzContinuityK α ρ] at hkey
  simp only [condVonNeumann, condDivergenceVariance, condPetzRenyiDown]
  linarith

/-! ### The sharp variance cap from two exponential-moment budgets -/

/-- **Variance under two exponential-moment budgets.** If a probability vector `w` and a real
`Y` satisfy `∑ w e^{Y} ≤ a` and `∑ w e^{−Y} ≤ b`, then the variance of `Y` under `w` is at most
`log²(√(ab) + √(ab − 1)) = arcosh²√(ab)`. The bound is attained by a two-point law. -/
theorem classical_var_le_log_sqrt_budget {ι : Type*} [Fintype ι] (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {a b : ℝ}
    (hMp : ∑ i, w i * Real.exp (Y i) ≤ a) (hMm : ∑ i, w i * Real.exp (-(Y i)) ≤ b) :
    ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2
      ≤ Real.log (Real.sqrt (a * b) + Real.sqrt (a * b - 1)) ^ 2 := by
  classical
  set t : ℝ := Real.sqrt (a * b) with htdef
  set s : ℝ := Real.sqrt (a * b - 1) with hsdef
  set E1 : ℝ := ∑ i, w i * Real.exp (Y i) with hE1def
  set E2 : ℝ := ∑ i, w i * Real.exp (-(Y i)) with hE2def
  set c : ℝ := (Real.log a - Real.log b) / 2 with hcdef
  -- strict positivity of the two budgets: both moments are strictly positive
  have hwpos : ∃ i, 0 < w i := by
    by_contra hcon
    push Not at hcon
    have h := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hcon i)
    rw [hw1] at h
    norm_num at h
  have hEp : (0 : ℝ) < E1 := by
    obtain ⟨i, hi⟩ := hwpos
    rw [hE1def]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have hEm : (0 : ℝ) < E2 := by
    obtain ⟨i, hi⟩ := hwpos
    rw [hE2def]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have ha : (0 : ℝ) < a := lt_of_lt_of_le hEp hMp
  have hb : (0 : ℝ) < b := lt_of_lt_of_le hEm hMm
  -- the shift `c` makes the two budgeted moments meet at `√(ab) = t`
  have hkey1 : Real.exp (-c) * E1 ≤ t := by
    have hlogE1 : Real.log E1 ≤ Real.log a := Real.log_le_log hEp hMp
    have hexp : Real.exp (-c) * E1 = Real.exp (-c + Real.log E1) := by
      rw [← Real.exp_log hEp, ← Real.exp_add, Real.log_exp]
    have hkey : Real.exp (-c + Real.log E1) ≤ Real.exp (Real.log (a * b) / 2) := by
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb), hcdef]
      linarith
    calc Real.exp (-c) * E1 = Real.exp (-c + Real.log E1) := hexp
      _ ≤ Real.exp (Real.log (a * b) / 2) := hkey
      _ = t := by rw [htdef, exp_log_half (mul_pos ha hb)]
  have hkey2 : Real.exp c * E2 ≤ t := by
    have hlogE2 : Real.log E2 ≤ Real.log b := Real.log_le_log hEm hMm
    have hexp : Real.exp c * E2 = Real.exp (c + Real.log E2) := by
      rw [← Real.exp_log hEm, ← Real.exp_add, Real.log_exp]
    have hkey : Real.exp (c + Real.log E2) ≤ Real.exp (Real.log (a * b) / 2) := by
      refine Real.exp_le_exp.mpr ?_
      rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb), hcdef]
      linarith
    calc Real.exp c * E2 = Real.exp (c + Real.log E2) := hexp
      _ ≤ Real.exp (Real.log (a * b) / 2) := hkey
      _ = t := by rw [htdef, exp_log_half (mul_pos ha hb)]
  -- the shifted `cosh` moment combines the two budgets
  have hcosh_sum : ∑ i, w i * Real.cosh (Y i - c)
      = (Real.exp (-c) * E1 + Real.exp c * E2) / 2 := by
    have hterm : ∀ i : ι, w i * Real.cosh (Y i - c)
        = (Real.exp (-c) * (w i * Real.exp (Y i))
          + Real.exp c * (w i * Real.exp (-(Y i)))) / 2 := by
      intro i
      have e1 : Real.exp (Y i - c) = Real.exp (-c) * Real.exp (Y i) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : Real.exp (-(Y i - c)) = Real.exp c * Real.exp (-(Y i)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [Real.cosh_eq, e1, e2]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hE1def, ← hE2def]
  -- Cauchy–Schwarz: `1 = (∑ w)² ≤ E1 · E2 ≤ a · b`
  have hab1 : (1 : ℝ) ≤ a * b := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => Real.sqrt (w i * Real.exp (Y i)))
      (fun i => Real.sqrt (w i * Real.exp (-(Y i))))
    have hterm : ∀ i : ι, Real.sqrt (w i * Real.exp (Y i))
        * Real.sqrt (w i * Real.exp (-(Y i))) = w i := by
      intro i
      rw [← Real.sqrt_mul (mul_nonneg (hw i) (Real.exp_pos _).le) (w i * Real.exp (-(Y i)))]
      have huv : w i * Real.exp (Y i) * (w i * Real.exp (-(Y i))) = w i ^ 2 := by
        rw [mul_mul_mul_comm, ← Real.exp_add, show (Y i : ℝ) + -(Y i) = 0 from by ring,
          Real.exp_zero]
        ring
      rw [huv, Real.sqrt_sq (hw i)]
    have hsum : ∑ i, Real.sqrt (w i * Real.exp (Y i))
        * Real.sqrt (w i * Real.exp (-(Y i))) = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i), hw1]
    have hE1sq : ∑ i, Real.sqrt (w i * Real.exp (Y i)) ^ 2 = E1 :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le))
    have hE2sq : ∑ i, Real.sqrt (w i * Real.exp (-(Y i))) ^ 2 = E2 :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le))
    rw [hE1sq, hE2sq, hsum, sq] at hcs
    have h2 : E1 * E2 ≤ a * b := mul_le_mul hMp hMm hEm.le ha.le
    linarith
  rcases eq_or_lt_of_le hab1 with hab_eq | hab1'
  · -- degenerate case `ab = 1`: Cauchy–Schwarz is tight and the variance vanishes
    have habeq : a * b = 1 := hab_eq.symm
    have ht1 : t = 1 := by rw [htdef, habeq, Real.sqrt_one]
    have hs0 : s = 0 := by rw [hsdef, habeq, sub_self, Real.sqrt_zero]
    have hb1 : Real.exp (-c) * E1 ≤ 1 := by rw [← ht1]; exact hkey1
    have hb2 : Real.exp c * E2 ≤ 1 := by rw [← ht1]; exact hkey2
    have hsumcosh : ∑ i, w i * Real.cosh (Y i - c) ≤ 1 := by
      rw [hcosh_sum]
      have hle : Real.exp (-c) * E1 + Real.exp c * E2 ≤ 2 := by linarith
      linarith
    have hshift : ∑ i, w i * (Y i - c) ^ 2 ≤ 0 := by
      have hpoint : ∀ i : ι, w i * (Y i - c) ^ 2
          ≤ 2 * (w i * Real.cosh (Y i - c)) - 2 * w i := by
        intro i
        have h1 : (Y i - c) ^ 2 ≤ 2 * Real.cosh (Y i - c) - 2 := by
          have hc := cosh_ge_one_add_sq_half (Y i - c)
          linarith
        calc w i * (Y i - c) ^ 2
            ≤ w i * (2 * Real.cosh (Y i - c) - 2) := mul_le_mul_of_nonneg_left h1 (hw i)
          _ = 2 * (w i * Real.cosh (Y i - c)) - 2 * w i := by ring
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
      have hsplit : (∑ i, (2 * (w i * Real.cosh (Y i - c)) - 2 * w i))
          = 2 * (∑ i, w i * Real.cosh (Y i - c)) - 2 * (∑ i, w i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [hsplit, hw1] at hsum
      linarith
    refine (classical_var_le_shift w Y hw1 c).trans ?_
    rw [ht1, hs0, add_zero, Real.log_one]
    norm_num
    exact hshift
  · -- the non-degenerate case `ab > 1`
    have ht1 : (1 : ℝ) < t := by
      rw [htdef]
      calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
        _ < Real.sqrt (a * b) := Real.sqrt_lt_sqrt zero_le_one hab1'
    have hts : (0 : ℝ) < t + s := by
      have := Real.sqrt_nonneg (a * b - 1)
      linarith
    have hs_nn : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
    set L : ℝ := Real.log (t + s) with hLdef
    have hL : (0 : ℝ) < L := Real.log_pos (by linarith)
    -- `cosh L = t`
    have hmul : (t + s) * (t - s) = 1 := by
      have h1 : (t + s) * (t - s) = t * t - s * s := by ring
      have ht2 : t * t = a * b := by
        rw [htdef, Real.mul_self_sqrt (mul_nonneg ha.le hb.le)]
      have hs2 : s * s = a * b - 1 := by rw [hsdef, Real.mul_self_sqrt (by linarith)]
      rw [h1, ht2, hs2]
      linarith
    have hinv : (t + s)⁻¹ = t - s :=
      (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm
    have hcoshL : Real.cosh L = t := by
      rw [hLdef, Real.cosh_eq, Real.exp_log hts, Real.exp_neg, Real.exp_log hts, hinv]
      ring
    -- the tangent majorant, summed against `w`
    have ht_nn : (0 : ℝ) ≤ t := by rw [htdef]; exact Real.sqrt_nonneg _
    have hcoef : (0 : ℝ) ≤ 2 * L / Real.sinh L := by positivity
    have hsumcosh : ∑ i, w i * Real.cosh (Y i - c) ≤ Real.cosh L := by
      have hnum : Real.exp (-c) * E1 + Real.exp c * E2 ≤ t + t := by
        have h1 := hkey1
        have h2 := hkey2
        linarith
      have hstep : (Real.exp (-c) * E1 + Real.exp c * E2) / 2 ≤ (t + t) / 2 :=
        div_le_div₀ (show (0 : ℝ) ≤ t + t by linarith) hnum zero_lt_two (le_refl 2)
      rw [hcosh_sum]
      refine hstep.trans ?_
      rw [show (t + t) / 2 = t from by ring, hcoshL]
    have hshift : ∑ i, w i * (Y i - c) ^ 2 ≤ L ^ 2 := by
      have hpoint : ∀ i : ι, w i * (Y i - c) ^ 2
          ≤ w i * (L ^ 2 + (2 * L / Real.sinh L) * (Real.cosh (Y i - c) - Real.cosh L)) :=
        fun i => mul_le_mul_of_nonneg_left (sq_le_cosh_tangent L hL (Y i - c)) (hw i)
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
      have hsplit : ∑ i, w i * (L ^ 2 + (2 * L / Real.sinh L)
            * (Real.cosh (Y i - c) - Real.cosh L))
          = L ^ 2 + (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
            - (2 * L / Real.sinh L) * Real.cosh L := by
        have hexpand : ∑ i, w i * (L ^ 2 + (2 * L / Real.sinh L)
              * (Real.cosh (Y i - c) - Real.cosh L))
            = L ^ 2 * (∑ i, w i) + (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
              - (2 * L / Real.sinh L) * Real.cosh L * (∑ i, w i) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hexpand, hw1]
        ring
      rw [hsplit] at hsum
      have hmid : (2 * L / Real.sinh L) * (∑ i, w i * Real.cosh (Y i - c))
          ≤ (2 * L / Real.sinh L) * Real.cosh L :=
        mul_le_mul_of_nonneg_left hsumcosh hcoef
      linarith
    calc ∑ i, w i * (Y i - ∑ j, w j * Y j) ^ 2
        ≤ ∑ i, w i * (Y i - c) ^ 2 := classical_var_le_shift w Y hw1 c
      _ ≤ L ^ 2 := hshift

/-- An improved classical-`A` variance cap. For every normalised cq state with classical
alphabet of size `d = card X`, `V(X|B)_ρ ≤ log₂²(√d + √(d − 1))`.

This improves Dupuis–Fawzi's `log₂²(2d + 1)` bound
(arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex`, `\label{lem_var_dim}`).
Attainment of the two-moment bound does not establish attainment by a cq state. -/
theorem condDivergenceVariance_le_logb_sqrt_card {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    condDivergenceVariance ρ
      ≤ Real.logb 2 (Real.sqrt (Fintype.card X) + Real.sqrt ((Fintype.card X : ℝ) - 1)) ^ 2 := by
  -- the cq-state bookkeeping: hermiticity, traces, support, `card X > 0`
  have hR0 : (0 : Matrix (Fin n × X) (Fin n × X) ℂ) ≤ ρ.toJointOp :=
    Matrix.nonneg_iff_posSemidef.mpr ρ.toJointOp_posSemidef
  have hS0 := blockDiagonal_quantumMarginalOp_nonneg ρ
  have hRh : ρ.toJointOp.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
  have hSh : (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hRtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  have hStr := ref_trace_re ρ hnorm
  have hsupp := toJointOp_ker_sub ρ
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast card_pos_of_norm ρ hnorm
  -- `(M+)`: `∑ w e^ℓ = petzTrace 2 ≤ 1`, via `condRenyiPetz_nonneg_of_cq` at `α = 2`.
  have hM1ge : (1 : ℝ) ≤ ∑ p : (Fin n × X) × (Fin n × X), nsW hRh hSh p
      * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh)) :=
    classical_M_ge_one (nsW hRh hSh) (fun p => nsL hRh hSh p - nsD hRh hSh)
      (fun p => nsW_nonneg hRh hSh hR0 p) (ns_sum_one hRh hSh hRtr)
      (ns_Y_sum hRh hSh hRtr) 1
  have hM1eq : (∑ p : (Fin n × X) × (Fin n × X), nsW hRh hSh p
        * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh)))
      = Real.exp (-(1 * nsD hRh hSh))
        * petzTrace (1 + 1) ρ.toJointOp
          (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) :=
    ns_M_eq hRh hSh hR0 hS0 hsupp (s := 1) (by norm_num)
  have hpt2pos : (0 : ℝ) < petzTrace (1 + 1) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) := by
    by_contra hcon
    push Not at hcon
    have hle : (∑ p : (Fin n × X) × (Fin n × X), nsW hRh hSh p
        * Real.exp (1 * (nsL hRh hSh p - nsD hRh hSh))) ≤ 0 := by
      rw [hM1eq]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcon
    linarith
  have hpt2le : petzTrace (1 + 1) ρ.toJointOp
      (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)) ≤ 1 := by
    have hnn := condRenyiPetz_nonneg_of_cq 2 (by norm_num) (by norm_num) ρ hnorm
    rw [condPetzRenyiDown, petzRenyiDivergence, neg_nonneg] at hnn
    have hlogb : Real.logb 2 (petzTrace 2 ρ.toJointOp
        (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))) ≤ 0 := by
      nlinarith [hnn]
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2] at hpt2pos ⊢
    calc petzTrace 2 ρ.toJointOp (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
        = (2 : ℝ) ^ (Real.logb 2 (petzTrace 2 ρ.toJointOp
            (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp)))) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpt2pos).symm
      _ ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hlogb
      _ = 1 := Real.rpow_zero 2
  have hMp : ∑ p : (Fin n × X) × (Fin n × X), nsW hRh hSh p * Real.exp (nsL hRh hSh p) ≤ 1 := by
    have h := nsW_exp_sum hRh hSh hR0 hS0 hsupp (a := 2) (by norm_num)
    simp only [show (2 : ℝ) - 1 = 1 from by norm_num, one_mul] at h
    rw [h, show (2 : ℝ) = 1 + 1 from by norm_num]
    exact hpt2le
  -- `(M−)`: `∑ w e^{−ℓ} ≤ Tr σ = card X`.
  have hMm : ∑ p : (Fin n × X) × (Fin n × X), nsW hRh hSh p
      * Real.exp (-(nsL hRh hSh p)) ≤ (Fintype.card X : ℝ) := by
    have h := nsW_exp_neg_le hRh hSh hR0 hS0 hsupp
    rw [hStr] at h
    exact h
  rw [condDivergenceVariance, ns_divVar_eq hRh hSh hRtr,
    div_le_iff₀ (by positivity : (0 : ℝ) < Real.log 2 ^ 2)]
  refine (classical_var_le_log_sqrt_budget (nsW hRh hSh) (nsL hRh hSh)
    (fun p => nsW_nonneg hRh hSh hR0 p) (ns_sum_one hRh hSh hRtr) hMp hMm).trans ?_
  rw [one_mul, Real.logb, div_pow, div_mul_cancel₀ _
    (ne_of_gt (by positivity : (0 : ℝ) < Real.log 2 ^ 2))]

/-- The improved cap at `card X = 2`: `V(X|B)_ρ ≤ log₂²(1 + √2) = 1.6168…`.
This specializes `condDivergenceVariance_le_logb_sqrt_card` and improves Dupuis–Fawzi's
classical-register bound `log₂²(2d + 1)` at `d = 2`. -/
theorem condDivergenceVariance_le_logb_one_add_sqrt_two {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hcard : Fintype.card X = 2) :
    condDivergenceVariance ρ ≤ Real.logb 2 (1 + Real.sqrt 2) ^ 2 := by
  have h := condDivergenceVariance_le_logb_sqrt_card ρ hnorm
  rw [hcard] at h
  norm_num [add_comm] at h
  exact h

end InfoTheory.Renyi

end
