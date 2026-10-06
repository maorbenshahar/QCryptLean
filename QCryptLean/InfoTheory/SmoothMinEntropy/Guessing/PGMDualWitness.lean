import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.PGMOptimality
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# PGM-style SDP Dual Witness — Koenig–Renner–Schaffner construction for POVM guessing

Concrete construction of the SDP dual witness used in
`exists_sdp_dual_witness_of_optimal_povm`.  Given a CQ state `ρ` and a POVM
`M : X → Op n` attaining the guessing supremum, define

    T              := ∑ x, ρ_A(x) * M x
    pgmDualWitness := ½ · (T + Tᴴ)

(the Koenig–Renner–Schaffner symmetric construction).  This is **not** the
sqrt-sandwich PGM `pgmOp` — the Helstrom qubit counterexample rules out
`pgmOp` as a dual witness.

The core result is the KRS Löwner-domination condition: if `M` is an optimal
POVM for guessing the classical register, then `pgmDualWitness ρ M` dominates
each fibre `ρ_A(x)`.  The proof uses the normalization-preserving small
perturbation from `PGMOptimality.lean` and a first-order extraction from the
resulting quadratic inequality.  From domination we derive
`pgmDualWitness_posSemidef`.

## Main definitions

- `pgmDualWitness` : the symmetrized SDP dual witness `½ · (T + Tᴴ)`.

## Main statements

- `pgmDualWitness_isHermitian` : the witness is Hermitian.
- `pgmDualWitness_trace_re_eq` : its trace equals the POVM guessing objective.
- `pgmDualWitness_objective_diff` : algebraic identity for the perturbation
  step.
- `pgmDualWitness_dominates` : Löwner domination of each classical fibre.
- `pgmDualWitness_posSemidef` : PSD of the witness (derived from
  `pgmDualWitness_dominates`).
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The dual witness -/

/-- Unnormalized inner sum used in the dual witness. -/
private def pgmDualWitnessInner {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) : Op n :=
  ∑ x : X, (ρ.stateMap x).toOp * M x

/-- The Koenig–Renner–Schaffner **SDP dual witness** for the POVM guessing
problem:

    `pgmDualWitness ρ M := ½ · (T + Tᴴ)`, with `T := ∑ x, ρ_A(x) · M x`.

This is the Hermitian symmetrization of the (not necessarily Hermitian) sum
`T`. -/
noncomputable def pgmDualWitness {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) : Op n :=
  (Complex.ofReal (1/2)) •
    (pgmDualWitnessInner ρ M + (pgmDualWitnessInner ρ M).conjTranspose)

/-- `pgmDualWitness ρ M` is Hermitian (real-scalar multiple of `T + Tᴴ`). -/
lemma pgmDualWitness_isHermitian {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) :
    (pgmDualWitness ρ M).IsHermitian := by
  unfold pgmDualWitness
  exact isHermitian_real_smul
    (Matrix.isHermitian_add_transpose_self (pgmDualWitnessInner ρ M)) (1/2)

/-- Trace identity for the inner sum: `Re Tr(T) = ∑ x Re Tr(M x · ρ_A(x))`,
using only `Matrix.trace_sum`, `Complex.re_sum` and cyclicity. -/
private lemma pgmDualWitnessInner_trace_re {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) :
    (pgmDualWitnessInner ρ M).trace.re =
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re := by
  unfold pgmDualWitnessInner
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.trace_mul_comm]

/-- The real part of `Tr(Aᴴ)` equals the real part of `Tr(A)` (since
conjugation fixes the real part). -/
private lemma trace_re_conjTranspose_eq {n : ℕ} (A : Op n) :
    (A.conjTranspose.trace).re = A.trace.re := by
  rw [Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]

/-- Trace identity:
`Re Tr(pgmDualWitness ρ M) = ∑ x Re Tr(M x · ρ_A(x))`. -/
lemma pgmDualWitness_trace_re_eq {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) :
    (pgmDualWitness ρ M).trace.re =
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re := by
  unfold pgmDualWitness
  rw [trace_real_smul_re, Matrix.trace_add, Complex.add_re,
      trace_re_conjTranspose_eq, pgmDualWitnessInner_trace_re]
  ring

/-! ## Perturbation identities for the KRS argument

The proof of `pgmDualWitness_dominates` proceeds by the Koenig–Renner–Schaffner
perturbation argument.  For any Hermitian projector `E` and any `x₀ : X`, the
projection perturbation
    `perturbedPovm M x₀ E y = (1 - E) * M y * (1 - E) + [y = x₀] · E`
is a valid POVM (`perturbedPovm_posSemidef`, `perturbedPovm_sum_eq_one`).
The small perturbation `smallPerturbedPovm` preserves normalization for
`E = εP`; its objective expansion below gives a quadratic inequality in `ε`.
The first-order term is exactly the rank-one domination inequality. -/

/-- When each `M y` is Hermitian (and each `(ρ.stateMap y).toOp` is automatically
Hermitian), the conjugate transpose of `pgmDualWitnessInner ρ M = ∑ y, ρ_y · M y`
swaps the order of multiplication: it equals `∑ y, M y · ρ_y`. -/
private lemma pgmDualWitnessInner_conjTranspose_eq_sum_M_rho
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_herm : ∀ y : X, (M y).IsHermitian) :
    (pgmDualWitnessInner ρ M).conjTranspose
      = ∑ y : X, M y * (ρ.stateMap y).toOp := by
  unfold pgmDualWitnessInner
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.conjTranspose_mul, hM_herm y, (ρ.stateMap y).isHermitian]

/-- Pointwise matrix expansion of `ρ_y · perturbedPovm M x₀ E y`. -/
private lemma rho_mul_perturbedPovm_expand
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (x₀ : X) (E : Op n) (y : X) :
    (ρ.stateMap y).toOp * perturbedPovm M x₀ E y
      = (ρ.stateMap y).toOp * M y
        - (ρ.stateMap y).toOp * M y * E
        - (ρ.stateMap y).toOp * E * M y
        + (ρ.stateMap y).toOp * E * M y * E
        + (if y = x₀ then (ρ.stateMap y).toOp * E else 0) := by
  change (ρ.stateMap y).toOp
        * ((1 - E) * M y * (1 - E) + (if y = x₀ then E else 0)) = _
  rw [mul_add, mul_ite, mul_zero]
  have hsandwich :
      (ρ.stateMap y).toOp * ((1 - E) * M y * (1 - E))
        = (ρ.stateMap y).toOp * M y
          - (ρ.stateMap y).toOp * M y * E
          - (ρ.stateMap y).toOp * E * M y
          + (ρ.stateMap y).toOp * E * M y * E := by
    noncomm_ring
  rw [hsandwich]

/-- **Algebraic identity underlying the perturbation step**.

Let `T := pgmDualWitnessInner ρ M = ∑ y, (ρ.stateMap y).toOp * M y` and let
`E : Op n` be any operator.  Then the objective difference between the
perturbed POVM `perturbedPovm M x₀ E` and the original POVM `M` expands as:

    ∑ y, Tr((ρ.stateMap y).toOp * perturbedPovm M x₀ E y).re
      - ∑ y, Tr(M y * (ρ.stateMap y).toOp).re
    = Tr((ρ.stateMap x₀).toOp * E).re
      - Tr(E * (T + Tᴴ)).re
      + ∑ y, Tr(E * M y * E * (ρ.stateMap y).toOp).re

Given that each `M y` is Hermitian (needed to equate
`Re Tr(ρ_y E M_y) = Re Tr(ρ_y M_y E)` when combining the conjugated and
non-conjugated halves of `T + Tᴴ`), this is a pure trace-algebra identity:
expand `(1 - E) * M y * (1 - E)`, use `Matrix.trace_sum`,
`Matrix.trace_mul_comm`, and linearity of `.re`.  **No assumption on `E`** is
required (neither Hermiticity nor idempotence). -/
lemma pgmDualWitness_objective_diff
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (x₀ : X) {E : Op n}
    (hM_herm : ∀ y : X, (M y).IsHermitian) :
    (∑ y : X, ((ρ.stateMap y).toOp * perturbedPovm M x₀ E y).trace.re)
      - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re)
    = ((ρ.stateMap x₀).toOp * E).trace.re
      - (E * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re
      + ∑ y : X, (E * (M y) * E * (ρ.stateMap y).toOp).trace.re := by
  -- Reduce to ℂ-level identity then take `.re` of both sides.
  suffices hC :
    (∑ y : X, ((ρ.stateMap y).toOp * perturbedPovm M x₀ E y).trace)
      - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace)
    = ((ρ.stateMap x₀).toOp * E).trace
      - (E * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace
      + ∑ y : X, (E * (M y) * E * (ρ.stateMap y).toOp).trace by
    have h := congrArg Complex.re hC
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum] at h
    exact h
  -- (E * (T + Tᴴ)).trace splits.
  have hETTdag : (E * (pgmDualWitnessInner ρ M
        + (pgmDualWitnessInner ρ M).conjTranspose)).trace
      = (E * pgmDualWitnessInner ρ M).trace
        + (E * (pgmDualWitnessInner ρ M).conjTranspose).trace := by
    rw [mul_add, Matrix.trace_add]
  -- ∑ y, Tr(ρ_y · M y · E) = Tr(E · T).
  have hET : (∑ y : X, ((ρ.stateMap y).toOp * M y * E).trace)
      = (E * pgmDualWitnessInner ρ M).trace := by
    unfold pgmDualWitnessInner
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact Matrix.trace_mul_comm _ _
  -- T.conjTranspose = ∑ y, M y · ρ_y (uses hM_herm).
  have hTdag := pgmDualWitnessInner_conjTranspose_eq_sum_M_rho ρ M hM_herm
  -- ∑ y, Tr(ρ_y · E · M y) = Tr(E · Tᴴ).
  have hETdag : (∑ y : X, ((ρ.stateMap y).toOp * E * M y).trace)
      = (E * (pgmDualWitnessInner ρ M).conjTranspose).trace := by
    rw [hTdag, Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    -- Goal: (ρ_y * E * M y).trace = (E * (M y * ρ_y)).trace
    have hassoc : (ρ.stateMap y).toOp * E * M y
        = (ρ.stateMap y).toOp * (E * M y) := by noncomm_ring
    rw [hassoc, Matrix.trace_mul_comm, mul_assoc]
  -- ∑ y, Tr(ρ_y · E · M y · E) = ∑ y, Tr(E · M y · E · ρ_y).
  have hC2 : (∑ y : X, ((ρ.stateMap y).toOp * E * M y * E).trace)
      = ∑ y : X, (E * M y * E * (ρ.stateMap y).toOp).trace := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hassoc : (ρ.stateMap y).toOp * E * M y * E
        = (ρ.stateMap y).toOp * (E * M y * E) := by noncomm_ring
    rw [hassoc, Matrix.trace_mul_comm]
  -- ∑ y, Tr(M y · ρ_y) = ∑ y, Tr(ρ_y · M y) (per-term cyclicity).
  have hC1 : (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace)
      = ∑ y : X, ((ρ.stateMap y).toOp * (M y)).trace := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact Matrix.trace_mul_comm _ _
  -- Substitute the per-y matrix expansion and distribute `.trace` and `∑`.
  simp_rw [rho_mul_perturbedPovm_expand ρ M x₀ E,
           Matrix.trace_add, Matrix.trace_sub,
           apply_ite Matrix.trace, Matrix.trace_zero,
           Finset.sum_add_distrib, Finset.sum_sub_distrib,
           Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hC1, hET, hETdag, hC2, hETTdag]
  ring

/-- Objective expansion for the normalization-preserving small perturbation.

This is the projection-perturbation identity `pgmDualWitness_objective_diff`
applied with `E = εP`, plus the distinguished-outcome correction
`(ε - ε ^ 2)P`. -/
private lemma smallPerturbedPovm_objective_diff
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (x₀ : X) {ε : ℝ} {P : Op n}
    (hM_herm : ∀ y : X, (M y).IsHermitian) :
    (∑ y : X, ((ρ.stateMap y).toOp * smallPerturbedPovm M x₀ ε P y).trace.re)
      - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re)
    =
      ε * (2 * ((ρ.stateMap x₀).toOp * P).trace.re
        - (P * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re)
      + ε ^ 2 * ((∑ y : X, (P * (M y) * P * (ρ.stateMap y).toOp).trace.re)
        - ((ρ.stateMap x₀).toOp * P).trace.re) := by
  classical
  have hsmall_sum :
      (∑ y : X, ((ρ.stateMap y).toOp * smallPerturbedPovm M x₀ ε P y).trace.re)
        =
          (∑ y : X, ((ρ.stateMap y).toOp
              * perturbedPovm M x₀ ((Complex.ofReal ε) • P) y).trace.re)
          + ((ρ.stateMap x₀).toOp * ((Complex.ofReal (ε - ε ^ 2)) • P)).trace.re := by
    unfold smallPerturbedPovm
    simp_rw [mul_add, Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single x₀]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact False.elim (h (Finset.mem_univ x₀))
  have hhard := pgmDualWitness_objective_diff
    (ρ := ρ) (M := M) (x₀ := x₀)
    (E := (Complex.ofReal ε) • P) hM_herm
  have hscale_rho :
      (((ρ.stateMap x₀).toOp * ((Complex.ofReal ε) • P)).trace).re
        = ε * ((ρ.stateMap x₀).toOp * P).trace.re := by
    rw [Matrix.mul_smul, trace_real_smul_re]
  have hscale_witness :
      ((((Complex.ofReal ε) • P)
          * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace).re
        =
          ε * (P * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re := by
    rw [Matrix.smul_mul, trace_real_smul_re]
  have hscale_quad :
      (∑ y : X,
          (((Complex.ofReal ε) • P) * M y * ((Complex.ofReal ε) • P)
            * (ρ.stateMap y).toOp).trace.re)
        =
          ε ^ 2 * (∑ y : X, (P * M y * P * (ρ.stateMap y).toOp).trace.re) := by
    have hterm : ∀ y : X,
        ((((Complex.ofReal ε) • P) * M y * ((Complex.ofReal ε) • P)
            * (ρ.stateMap y).toOp).trace).re
          = ε ^ 2 * (P * M y * P * (ρ.stateMap y).toOp).trace.re := by
      intro y
      have hmat :
          ((Complex.ofReal ε) • P) * M y * ((Complex.ofReal ε) • P)
              * (ρ.stateMap y).toOp
            = (Complex.ofReal (ε ^ 2)) •
                (P * M y * P * (ρ.stateMap y).toOp) := by
        simp_rw [Matrix.smul_mul, Matrix.mul_smul]
        rw [Matrix.smul_mul]
        rw [smul_smul, ← Complex.ofReal_mul, pow_two]
      rw [hmat, trace_real_smul_re]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
  have hscale_corr :
      (((ρ.stateMap x₀).toOp * ((Complex.ofReal (ε - ε ^ 2)) • P)).trace).re
        = (ε - ε ^ 2) * ((ρ.stateMap x₀).toOp * P).trace.re := by
    rw [Matrix.mul_smul, trace_real_smul_re]
  calc
    (∑ y : X, ((ρ.stateMap y).toOp * smallPerturbedPovm M x₀ ε P y).trace.re)
        - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re)
        =
          ((∑ y : X, ((ρ.stateMap y).toOp
              * perturbedPovm M x₀ ((Complex.ofReal ε) • P) y).trace.re)
            - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re))
          + ((ρ.stateMap x₀).toOp * ((Complex.ofReal (ε - ε ^ 2)) • P)).trace.re := by
            rw [hsmall_sum]
            ring
    _ =
      ε * (2 * ((ρ.stateMap x₀).toOp * P).trace.re
        - (P * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re)
      + ε ^ 2 * ((∑ y : X, (P * (M y) * P * (ρ.stateMap y).toOp).trace.re)
        - ((ρ.stateMap x₀).toOp * P).trace.re) := by
        rw [hhard, hscale_rho, hscale_witness, hscale_quad, hscale_corr]
        ring

/-- First-order extraction from a nonpositive quadratic perturbation bound. -/
private lemma firstOrder_nonpos_of_quadratic_nonpos {A B : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ε * A + ε ^ 2 * B ≤ 0) :
    A ≤ 0 := by
  -- Dividing by `ε > 0` gives `A ≤ -ε·B ≤ ε·|B|` for every `ε ∈ (0, 1]`.
  have hle : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → A ≤ ε * |B| := by
    intro ε hε0 hε1
    have hdiv : ε * (A + ε * B) ≤ ε * 0 := by
      rw [mul_zero, mul_add, ← mul_assoc, ← sq]
      exact h ε hε0 hε1
    have hAB : A ≤ -(ε * B) := le_neg_iff_add_nonpos_right.mpr (le_of_mul_le_mul_left hdiv hε0)
    exact hAB.trans (by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs B) hε0.le)
  -- At `ε = min 1 (δ / (|B| + 1))` this is `A ≤ δ`, for every `δ > 0`.
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : 0 < |B| + 1 := by positivity
  have hε0 : 0 < min 1 (δ / (|B| + 1)) := lt_min one_pos (div_pos hδ hc)
  calc
    A ≤ min 1 (δ / (|B| + 1)) * |B| := hle _ hε0 (min_le_left _ _)
    _ ≤ δ / (|B| + 1) * (|B| + 1) :=
        mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one) (abs_nonneg B)
          (div_pos hδ hc).le
    _ = 0 + δ := by rw [div_mul_cancel₀ δ hc.ne', zero_add]

/-- Rank-one normalized-ket form of the KRS domination inequality. -/
private lemma pgmDualWitness_normalized_ket_quadratic_le
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ)
    (x₀ : X) (ψ : Ket n) (hψ : ψ.dag * ψ = 1) :
    (quadraticForm (ρ.stateMap x₀).toOp ψ.vec).re
      ≤ (quadraticForm (pgmDualWitness ρ M) ψ.vec).re := by
  classical
  let P : Op n := ψ * ψ.dag
  have hM_herm : ∀ y : X, (M y).IsHermitian := fun y => (hM_psd y).isHermitian
  have hP_psd : P.PosSemidef := by
    simpa [P] using ketbra_posSemidef ψ
  have hP_proj : P * P = P := by
    simpa [P] using ketbra_idempotent ψ hψ
  have hsmall_nonpos :
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (∑ y : X,
            ((ρ.stateMap y).toOp * smallPerturbedPovm M x₀ ε P y).trace.re)
          - (∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re) ≤ 0 := by
    intro ε hε0 hε1
    have hopt :=
      smallPerturbedPovm_objective_le (ρ := ρ) (M := M) (x₀ := x₀)
        (ε := ε) (P := P) hM_psd hM_sum hP_psd hP_proj
        (le_of_lt hε0) hε1
    linarith [hopt, hp_eq]
  have hfirst :
      2 * ((ρ.stateMap x₀).toOp * P).trace.re
        - (P * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re ≤ 0 := by
    refine firstOrder_nonpos_of_quadratic_nonpos
      (A := 2 * ((ρ.stateMap x₀).toOp * P).trace.re
        - (P * (pgmDualWitnessInner ρ M
            + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re)
      (B := (∑ y : X, (P * (M y) * P * (ρ.stateMap y).toOp).trace.re)
        - ((ρ.stateMap x₀).toOp * P).trace.re) ?_
    intro ε hε0 hε1
    have hnonpos := hsmall_nonpos ε hε0 hε1
    have hdiff := smallPerturbedPovm_objective_diff
      (ρ := ρ) (M := M) (x₀ := x₀) (ε := ε) (P := P) hM_herm
    rw [hdiff] at hnonpos
    exact hnonpos
  -- Convert the first-order trace inequality for `P = |ψ⟩⟨ψ|` into the
  -- quadratic-form inequality for `ψ`.
  have h_bra_qf : ∀ A : Op n, ψ.dag * A * ψ = quadraticForm A ψ.vec := by
    intro A
    rw [braop_mul_ket]
    simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
    unfold quadraticForm dotProduct
    rfl
  have htrace_rho :
      ((ρ.stateMap x₀).toOp * P).trace.re
        = (quadraticForm (ρ.stateMap x₀).toOp ψ.vec).re := by
    change (((ρ.stateMap x₀).toOp * (ψ * ψ.dag)).trace).re
      = (quadraticForm (ρ.stateMap x₀).toOp ψ.vec).re
    rw [Matrix.trace_mul_comm, trace_ketbra_mul, h_bra_qf]
  have htrace_witness :
      (P * (pgmDualWitnessInner ρ M
          + (pgmDualWitnessInner ρ M).conjTranspose)).trace.re
        = 2 * (quadraticForm (pgmDualWitness ρ M) ψ.vec).re := by
    change (((ψ * ψ.dag)
        * (pgmDualWitnessInner ρ M
          + (pgmDualWitnessInner ρ M).conjTranspose)).trace).re
        = 2 * (quadraticForm (pgmDualWitness ρ M) ψ.vec).re
    rw [trace_ketbra_mul, h_bra_qf]
    unfold pgmDualWitness
    rw [quadraticForm_ofReal_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  nlinarith

private lemma dotProduct_star_self_im_zero {n : ℕ} (v : Fin n → ℂ) :
    (dotProduct (star v) v).im = 0 :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).2.symm

private lemma dotProduct_star_self_re_pos {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) :
    0 < (dotProduct (star v) v).re :=
  (Complex.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hv)).1

private lemma ket_dag_mul_self_eq_dotProduct {n : ℕ} (ψ : Ket n) :
    ψ.dag * ψ = dotProduct (star ψ.vec) ψ.vec := by
  rw [bra_mul_ket_eq]
  unfold dotProduct
  simp only [Ket.dag_vec]
  congr 1

private lemma ket_normalized_of_dotProduct_re_eq_one {n : ℕ}
    (v : Fin n → ℂ) (hv : (dotProduct (star v) v).re = 1) :
    (⟨v⟩ : Ket n).dag * (⟨v⟩ : Ket n) = 1 := by
  rw [ket_dag_mul_self_eq_dotProduct]
  rw [Complex.ext_iff]
  constructor
  · simpa using hv
  · simpa using dotProduct_star_self_im_zero v

private lemma star_ofReal_smul_vec {n : ℕ} (c : ℝ) (v : Fin n → ℂ) :
    star ((c : ℂ) • v) = (c : ℂ) • star v := by
  ext i
  simp [smul_eq_mul, star_mul', Complex.conj_ofReal]

private lemma dotProduct_star_self_real_smul {n : ℕ}
    (c : ℝ) (v : Fin n → ℂ) :
    dotProduct (star ((c : ℂ) • v)) ((c : ℂ) • v)
      = (c : ℂ) * (c : ℂ) * dotProduct (star v) v := by
  rw [star_ofReal_smul_vec]
  rw [smul_dotProduct (c : ℂ) (star v) ((c : ℂ) • v)]
  rw [dotProduct_smul (c : ℂ) (star v) v]
  simp only [smul_eq_mul]
  ring

private lemma quadraticForm_real_smul_vec {n : ℕ}
    (A : Op n) (c : ℝ) (v : Fin n → ℂ) :
    quadraticForm A ((c : ℂ) • v)
      = (c : ℂ) * (c : ℂ) * quadraticForm A v := by
  unfold quadraticForm
  rw [star_ofReal_smul_vec, Matrix.mulVec_smul]
  rw [smul_dotProduct (c : ℂ) (star v) ((c : ℂ) • A.mulVec v)]
  rw [dotProduct_smul (c : ℂ) (star v) (A.mulVec v)]
  simp only [smul_eq_mul]
  ring

private lemma re_quadraticForm_real_smul_vec {n : ℕ}
    (A : Op n) (c : ℝ) (v : Fin n → ℂ) :
    (quadraticForm A ((c : ℂ) • v)).re
      = c * c * (quadraticForm A v).re := by
  rw [quadraticForm_real_smul_vec]
  have hcc : (c : ℂ) * (c : ℂ) = ((c * c : ℝ) : ℂ) := by norm_cast
  rw [hcc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private lemma normalized_vec_self_re_eq_one {n : ℕ}
    (v : Fin n → ℂ) (hv : v ≠ 0) :
    let q : ℝ := (dotProduct (star v) v).re
    let c : ℝ := (Real.sqrt q)⁻¹
    (dotProduct (star ((c : ℂ) • v)) ((c : ℂ) • v)).re = 1 := by
  intro q c
  have hq_pos : 0 < q := dotProduct_star_self_re_pos hv
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hscale := dotProduct_star_self_real_smul c v
  rw [hscale]
  have h_im : (dotProduct (star v) v).im = 0 := dotProduct_star_self_im_zero v
  have h_re :
      (((c : ℂ) * (c : ℂ) * dotProduct (star v) v).re)
        = c * c * q := by
    have hcc : (c : ℂ) * (c : ℂ) = ((c * c : ℝ) : ℂ) := by norm_cast
    rw [hcc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, h_im,
      zero_mul, sub_zero]
  rw [h_re]
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_pos.le
  have hc_sq : c * c = 1 / q := by
    unfold c
    field_simp [ne_of_gt hsqrt_pos]
    rw [hsqrt_sq]
  rw [hc_sq]
  field_simp [ne_of_gt hq_pos]

/-- A generic bridge from normalized-ket quadratic inequalities to `opLe`. -/
private lemma opLe_of_normalized_ket_quadratic_le {n : ℕ} {A B : Op n}
    (h : ∀ ψ : Ket n, ψ.dag * ψ = 1 →
      (quadraticForm A ψ.vec).re ≤ (quadraticForm B ψ.vec).re) :
    opLe A B := by
  intro v
  by_cases hv : v = 0
  · subst v
    simp [quadraticForm]
  · let q : ℝ := (dotProduct (star v) v).re
    let c : ℝ := (Real.sqrt q)⁻¹
    let ψ : Ket n := ⟨(c : ℂ) • v⟩
    have hq_pos : 0 < q := dotProduct_star_self_re_pos hv
    have hc_pos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hq_pos)
    have hc2_pos : 0 < c * c := mul_pos hc_pos hc_pos
    have hψ : ψ.dag * ψ = 1 := by
      refine ket_normalized_of_dotProduct_re_eq_one ψ.vec ?_
      exact normalized_vec_self_re_eq_one v hv
    have hscaled := h ψ hψ
    have hA :
        (quadraticForm A ψ.vec).re = c * c * (quadraticForm A v).re := by
      exact re_quadraticForm_real_smul_vec A c v
    have hB :
        (quadraticForm B ψ.vec).re = c * c * (quadraticForm B v).re := by
      exact re_quadraticForm_real_smul_vec B c v
    rw [hA, hB] at hscaled
    nlinarith

/-- **KRS Löwner-domination.**

Under the hypotheses of the strong-duality statement — each `M x` is PSD,
`∑ x M x = 1`, and `M` attains the POVM guessing supremum with value
`povmGuessingProb ρ` — the dual witness `pgmDualWitness ρ M` dominates each
classical fibre `ρ_A(x)` in the `opLe` (Löwner) order. -/
lemma pgmDualWitness_dominates {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    ∀ x : X, opLe (ρ.stateMap x).toOp (pgmDualWitness ρ M) := by
  classical
  intro x
  exact opLe_of_normalized_ket_quadratic_le
    (fun ψ hψ =>
      pgmDualWitness_normalized_ket_quadratic_le ρ M hM_psd hM_sum hp_eq x ψ hψ)

/-- PSD of the dual witness: given an inhabitant `x₀ : X`, we split
`Y = ρ_A(x₀) + (Y − ρ_A(x₀))` where both summands are PSD (ρ_A(x₀) is PSD
directly; the difference is PSD via `opLe.posSemidef_sub` applied to
`pgmDualWitness_dominates`). -/
lemma pgmDualWitness_posSemidef {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ)
    (x₀ : X) :
    (pgmDualWitness ρ M).PosSemidef := by
  have hρ_psd : Matrix.PosSemidef (ρ.stateMap x₀).toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x₀).toPosSemidefOp
  have hdom : opLe (ρ.stateMap x₀).toOp (pgmDualWitness ρ M) :=
    pgmDualWitness_dominates ρ M hM_psd hM_sum hp_eq x₀
  have hsub :
      Matrix.PosSemidef (pgmDualWitness ρ M - (ρ.stateMap x₀).toOp) :=
    opLe.posSemidef_sub (ρ.stateMap x₀).isHermitian
      (pgmDualWitness_isHermitian ρ M) hdom
  have hsum :
      Matrix.PosSemidef ((ρ.stateMap x₀).toOp
        + (pgmDualWitness ρ M - (ρ.stateMap x₀).toOp)) :=
    hρ_psd.add hsub
  have heq :
      (ρ.stateMap x₀).toOp + (pgmDualWitness ρ M - (ρ.stateMap x₀).toOp)
        = pgmDualWitness ρ M := by abel
  rw [heq] at hsum
  exact hsum

end InfoTheory.SmoothMinEntropy

end
