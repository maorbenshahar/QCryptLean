import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.Operators.PSDTraceBound
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.Hermitianization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Conditional Min-Entropy for CQ States — SDP, POVM guessing, weak duality, reference antitonicity

Conditional min-entropy `H_min(X|A)_ρ` for CQ states, following Tomamichel 2016.

Two equivalent formulations are provided:
1. The SDP / operator-constraint definition (Tomamichel Def 6.2)
2. The POVM guessing probability formula for CQ states (Tomamichel eq. 6.30)

Only the first is a `def`; the equivalence is a theorem stub. The weak-duality
direction (`povmGuessingProb ρ ≤ minFeasibleLambda ρ σ`) is proven, together
with the standard `[0, 1]` bounds on the POVM guessing probability.

## Main definitions

Semidefinite ordering and feasibility:
- `opLe`: PSD ordering `A ≤_PSD B` via pointwise real parts of the quadratic form.
- `isFeasible`: predicate that `t · σ` dominates each `ρ_A(x)` in the PSD sense.
- `minFeasibleLambda`: `λ* = inf {t ≥ 0 : t · σ ≥ ρ_A(x) ∀ x}`, so `H_min = -log₂ λ*`.
- `hasFeasibleLambda`: the feasible set for `(ρ, σ)` is nonempty.

Real-valued variants (arithmetic-friendly, for intermediate calculations):
- `conditionalMinEntropyReal`: `H_min(X|A)_{ρ|σ}` as a real number (Def 6.2).
- `conditionalMinEntropyOptReal`: optimized `H_min(X|A)_ρ = sup_σ H_min_{ρ|σ}` (Def 6.3).

ENNReal-valued definitions:
- `conditionalMinEntropy`: the positive part of `H_min(X|A)_{ρ|σ}` (Def 6.2).
- `conditionalMinEntropyOpt`: optimized `H_min(X|A)_ρ` as ENNReal (Def 6.3).

POVM guessing formulation:
- `povmGuessingProb`: `Pg(X|A)_ρ = max_{POVM} Σ_x Tr(M_x ρ_A(x))` (eq. 6.30), the
  maximum success probability for guessing X via a POVM measurement on A.

ENNReal value conventions for the positive part of the fixed-reference entropy:
- Positive feasible optimum: `ENNReal.ofReal H_min_real`, clipping negative entropy to zero.
- Feasible zero optimum (the zero state): `⊤`.
- Empty feasible set: `0`, the positive part of the true value `−∞`.

The optimized version `conditionalMinEntropyOpt` retains its supremum over feasible references.
Infeasible references contribute zero and therefore do not change that supremum.

## Main statements

- `povmTraceSum_le_of_isFeasible`: weak-duality core inequality bounding the
  expected guessing-probability trace sum by any feasible `λ`.
- `povmGuessingProb_nonneg`, `povmGuessingProb_le_one`: the POVM guessing
  probability lies in `[0, 1]`.
- `povmGuessingProb_le_minFeasibleLambda`: weak duality for the SDP/POVM pair.
- `isFeasible_mono_t`: feasible scalars are upward closed.
- `minFeasibleLambda_le_of_isFeasible`: every feasible scalar bounds the optimum.
- `minFeasibleLambda_nonneg`: the feasible-λ infimum is always nonnegative.
- `hasFeasibleLambda_of_posDef`: a positive-definite reference makes the SDP
  feasible for every CQ state.
- `minFeasibleLambda_ge_inv_card`: for a normalized CQ state, every feasible `t` is at
  least `1/|X|`, hence so is the infimum.
- `conditionalMinEntropyReal_le_log_card` / `conditionalMinEntropyOptReal_le_log_card`:
  real-valued upper bound `H_min(X|A)_ρ ≤ log₂ |X|` for normalized CQ states.
- `conditionalMinEntropyReal_antitone_sigma` / `conditionalMinEntropy_antitone_sigma`:
  min-entropy is antitone in the reference operator `σ` (Löwner order).

The POVM-guessing-probability equivalence `conditionalMinEntropyReal_cq_guess_eq`
lives in the companion file `MinEntropyGuess.lean`.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Operator Semidefinite Order

`opLe` and its elementary laws — in particular `opLe_trans`,
`quadraticForm_ofReal_smul` and `opLe_smul_nonneg`, used throughout the antitonicity
proofs below — live with their subject in the Quantum.TensorProducts.PSDOrder module
(imported above), and are available here through `open Quantum.Operators`.
-/

/-!
## Conditional Min-Entropy

Def 6.2 (Tomamichel 2016):
  H_min(X|A)_{ρ|σ} = -log₂ λ*

where λ* = inf {λ ≥ 0 : λ · 1_X ⊗ σ ≥ ρ_{XA}}.

For a CQ state ρ_{XA} = Σ_x |x⟩⟨x| ⊗ ρ_A(x) and reference σ ∈ S•(A):
  λ* = max_x {(ρ_A(x))_σ-norm}

This is encoded below via the infimum over feasible λ.
-/

/-- Predicate: t is a feasible lower bound for the min-entropy problem.

    A real number t ≥ 0 is feasible for (ρ, σ) iff t · σ dominates ρ_A(x)
    in the PSD sense for every classical outcome x of ρ. -/
def isFeasible {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ x : X, opLe (ρ.stateMap x).toOp (Complex.ofReal t • σ.toOp)

/-- The smallest feasible t for (ρ, σ). Equals exp(-H_min(X|A)_{ρ|σ}).

    Tomamichel 2016, Def 6.2 (reformulated): the infimum over all t ≥ 0 such that
    t · σ dominates ρ_A(x) for all classical outcomes x. -/
noncomputable def minFeasibleLambda {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : ℝ :=
  sInf (setOf (isFeasible ρ σ))

/-- Predicate: the feasible set for (ρ, σ) is nonempty. -/
def hasFeasibleLambda {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : Prop :=
  ∃ t : ℝ, isFeasible ρ σ t

/-- The real optimum is zero for an empty feasible set. This totalization is
separate from the entropy convention of Tomamichel 2016, Definition 6.2. -/
lemma minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda
    {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d)
    (h : ¬ hasFeasibleLambda ρ σ) :
    minFeasibleLambda ρ σ = 0 := by
  unfold minFeasibleLambda
  have hEmpty : setOf (isFeasible ρ σ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨t, ht⟩
    exact h ⟨t, ht⟩
  rw [hEmpty, Real.sInf_empty]

/-- Feasibility is monotone in the reference: if `τ ≼ σ` in the Löwner order and
    `t` is feasible for the reference `τ`, then `t` is feasible for `σ`. -/
lemma isFeasible_of_opLe {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ τ : SubDensityOp n)
    (h : opLe τ.toOp σ.toOp) {t : ℝ} (ht : isFeasible ρ τ t) : isFeasible ρ σ t := by
  refine ⟨ht.1, fun x => ?_⟩
  exact opLe_trans (ht.2 x) (opLe_smul_nonneg ht.1 h)

/-- Upward-closure of feasibility. If `t` is feasible for `(ρ, σ)` and
`t ≤ s`, then `s` is feasible. -/
lemma isFeasible_mono_t {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : SubDensityOp n}
    {t s : ℝ} (ht : isFeasible ρ σ t) (hts : t ≤ s) :
    isFeasible ρ σ s := by
  refine ⟨ht.1.trans hts, fun x => ?_⟩
  have hopLe : opLe (Complex.ofReal t • σ.toOp) (Complex.ofReal s • σ.toOp) := by
    intro v
    simp only [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
               Complex.ofReal_im, zero_mul, sub_zero]
    have hqf_re_nn : 0 ≤ (quadraticForm σ.toOp v).re := σ.pos_semidef v
    exact mul_le_mul_of_nonneg_right hts hqf_re_nn
  exact opLe_trans (ht.2 x) hopLe

/-- The feasible set is bounded below by `0`. -/
lemma minFeasibleLambda_bddBelow {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : BddBelow (setOf (isFeasible ρ σ)) :=
  ⟨0, fun _ ht => ht.1⟩

/-- Every feasible scalar is an upper bound for `minFeasibleLambda`. -/
lemma minFeasibleLambda_le_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ}
    (ht : isFeasible ρ σ t) :
    minFeasibleLambda ρ σ ≤ t := by
  unfold minFeasibleLambda
  exact csInf_le (minFeasibleLambda_bddBelow ρ σ) ht

/-- Feasibility at a scaled optimum extends to every larger feasible scalar. -/
lemma isFeasible_mul_minFeasibleLambda_mono
    {X Y : Type*} [Fintype X] [Fintype Y] {n m : ℕ}
    (ρA : CQState X n) (σA : SubDensityOp n)
    (ρB : CQState Y m) (σB : SubDensityOp m) {c t : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hmin : isFeasible ρB σB (c * minFeasibleLambda ρA σA))
    (ht : isFeasible ρA σA t) :
    isFeasible ρB σB (c * t) := by
  exact isFeasible_mono_t hmin
    (mul_le_mul_of_nonneg_left
      (minFeasibleLambda_le_of_isFeasible ρA σA ht) hc_nonneg)

/-- The infimum `minFeasibleLambda` is nonnegative. -/
lemma minFeasibleLambda_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : 0 ≤ minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  by_cases h : (setOf (isFeasible ρ σ)).Nonempty
  · exact le_csInf h (fun _ ht => ht.1)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty]

/-- The feasible set for a fixed CQ state/reference is closed as a subset of
real scalars. -/
lemma isFeasible_isClosed {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    IsClosed (setOf (isFeasible ρ σ)) := by
  classical
  unfold isFeasible opLe
  refine isClosed_Ici.inter ?_
  change IsClosed (setOf (fun t : ℝ =>
    ∀ (x : X) (v : Fin n → ℂ),
      (quadraticForm (ρ.stateMap x).toOp v).re ≤
        (quadraticForm (Complex.ofReal t • σ.toOp) v).re))
  rw [Set.setOf_forall]
  refine isClosed_iInter
    (f := fun x : X => setOf (fun t : ℝ =>
      ∀ v : Fin n → ℂ,
        (quadraticForm (ρ.stateMap x).toOp v).re ≤
          (quadraticForm (Complex.ofReal t • σ.toOp) v).re)) (fun x => ?_)
  change IsClosed (setOf (fun t : ℝ =>
    ∀ v : Fin n → ℂ,
      (quadraticForm (ρ.stateMap x).toOp v).re ≤
        (quadraticForm (Complex.ofReal t • σ.toOp) v).re))
  rw [Set.setOf_forall]
  refine isClosed_iInter
    (f := fun v : Fin n → ℂ => setOf (fun t : ℝ =>
      (quadraticForm (ρ.stateMap x).toOp v).re ≤
        (quadraticForm (Complex.ofReal t • σ.toOp) v).re)) (fun v => ?_)
  have hset :
      setOf (fun t : ℝ =>
          (quadraticForm (ρ.stateMap x).toOp v).re ≤
            (quadraticForm (Complex.ofReal t • σ.toOp) v).re) =
        setOf (fun t : ℝ =>
          (quadraticForm (ρ.stateMap x).toOp v).re ≤
            t * (quadraticForm σ.toOp v).re) := by
    ext t
    simp only [Set.mem_setOf_eq]
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  change IsClosed (setOf (fun t : ℝ =>
    (quadraticForm (ρ.stateMap x).toOp v).re ≤
      (quadraticForm (Complex.ofReal t • σ.toOp) v).re))
  rw [hset]
  exact isClosed_le continuous_const (continuous_id.mul continuous_const)

/-- A positive-definite reference makes the feasible-lambda set nonempty. -/
lemma hasFeasibleLambda_of_posDef
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef) :
    hasFeasibleLambda ρ σ := by
  classical
  have hPSD : ∀ x : X, (ρ.stateMap x).toOp.PosSemidef := fun x =>
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have hexist : ∀ x : X, ∃ t : ℝ,
      0 ≤ t ∧ opLe (ρ.stateMap x).toOp (Complex.ofReal t • σ.toOp) :=
    fun x => Matrix.PosDef.exists_smul_opLe_of_posSemidef hσ_pd (hPSD x)
  let f : X → ℝ := fun x => (hexist x).choose
  have hf_nn : ∀ x : X, 0 ≤ f x := fun x => (hexist x).choose_spec.1
  have hf_dom : ∀ x : X,
      opLe (ρ.stateMap x).toOp (Complex.ofReal (f x) • σ.toOp) :=
    fun x => (hexist x).choose_spec.2
  refine ⟨∑ x : X, f x, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun x _ => hf_nn x)
  · intro x v
    have h_le_sum : f x ≤ ∑ y : X, f y :=
      Finset.single_le_sum (f := f) (fun y _ => hf_nn y) (Finset.mem_univ x)
    have hqf_x := hf_dom x v
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] at hqf_x
    have hσ_qf : 0 ≤ (quadraticForm σ.toOp v).re := σ.pos_semidef v
    calc (quadraticForm (ρ.stateMap x).toOp v).re
        ≤ f x * (quadraticForm σ.toOp v).re := hqf_x
      _ ≤ (∑ y : X, f y) * (quadraticForm σ.toOp v).re :=
          mul_le_mul_of_nonneg_right h_le_sum hσ_qf

/-- At a positive-definite reference, the infimum defining
`minFeasibleLambda` is itself feasible. -/
lemma isFeasible_minFeasibleLambda_of_posDef
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ : σ.toOp.PosDef) :
    isFeasible ρ σ (minFeasibleLambda ρ σ) := by
  change sInf (setOf (isFeasible ρ σ)) ∈ setOf (isFeasible ρ σ)
  exact (isFeasible_isClosed ρ σ).csInf_mem
    (hasFeasibleLambda_of_posDef ρ σ hσ)
    (minFeasibleLambda_bddBelow ρ σ)

/-- For a *feasible* reference (only `hasFeasibleLambda`, no positive
definiteness), the infimum defining `minFeasibleLambda` is itself feasible.

This is the `PosDef`-free sibling of `isFeasible_minFeasibleLambda_of_posDef`:
the feasible set is closed (`isFeasible_isClosed`), nonempty (the feasibility
hypothesis), and bounded below (`minFeasibleLambda_bddBelow`), so the infimum is
attained by `IsClosed.csInf_mem`. -/
lemma isFeasible_minFeasibleLambda_of_hasFeasibleLambda
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ) :
    isFeasible ρ σ (minFeasibleLambda ρ σ) := by
  change sInf (setOf (isFeasible ρ σ)) ∈ setOf (isFeasible ρ σ)
  exact (isFeasible_isClosed ρ σ).csInf_mem hfeas
    (minFeasibleLambda_bddBelow ρ σ)

/-- Every sub-density operator is dominated by the identity in the quadratic-form
semidefinite order. -/
lemma SubDensityOp.opLe_one {n : ℕ} [NeZero n] (ρ : SubDensityOp n) :
    opLe ρ.toOp (1 : Op n) := by
  exact Quantum.Operators.opLe_of_posSemidef_sub
    (Quantum.Operators.psd_le_one_of_trace_le_one ρ.toOp
      (Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp)
      ρ.trace_le_one)

/-- A positive-definite reference gives a single feasible scalar that works for
every CQ state over the same finite classical alphabet. -/
lemma exists_uniform_isFeasible_of_posDef
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : CQState X n, isFeasible ρ σ C := by
  obtain ⟨C, hC_nonneg, hC_dom_one⟩ :=
    Matrix.PosDef.exists_smul_opLe_of_posSemidef hσ Matrix.PosSemidef.one
  refine ⟨C, hC_nonneg, fun ρ => ?_⟩
  refine ⟨hC_nonneg, fun x => ?_⟩
  exact opLe_trans (ρ.stateMap x).opLe_one hC_dom_one

/-- `sInf`-antitonicity: if `τ ≼ σ` (Löwner order) and the feasibility set for τ is
    nonempty, then `minFeasibleLambda ρ σ ≤ minFeasibleLambda ρ τ`. -/
lemma minFeasibleLambda_antitone_of_opLe {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ τ : SubDensityOp n)
    (h : opLe τ.toOp σ.toOp) (hfeas : hasFeasibleLambda ρ τ) :
    minFeasibleLambda ρ σ ≤ minFeasibleLambda ρ τ := by
  unfold minFeasibleLambda
  have hsub : setOf (isFeasible ρ τ) ⊆ setOf (isFeasible ρ σ) :=
    fun _ ht => isFeasible_of_opLe ρ σ τ h ht
  obtain ⟨t, ht⟩ := hfeas
  have hne : (setOf (isFeasible ρ τ)).Nonempty := ⟨t, ht⟩
  exact csInf_le_csInf (minFeasibleLambda_bddBelow ρ σ) hne hsub

/-- Feasibility is monotone in the CQ state: if every block of `ρ_small` is
dominated by the corresponding block of `ρ_big`, then any feasible scalar for
`ρ_big` is feasible for `ρ_small` with the same reference. -/
lemma isFeasible_of_stateMap_opLe {X : Type*} [Fintype X] {n : ℕ}
    (ρ_small ρ_big : CQState X n) (σ : SubDensityOp n)
    (hρ : ∀ x : X, opLe (ρ_small.stateMap x).toOp (ρ_big.stateMap x).toOp)
    {t : ℝ} (ht : isFeasible ρ_big σ t) :
    isFeasible ρ_small σ t := by
  refine ⟨ht.1, fun x => ?_⟩
  exact opLe_trans (hρ x) (ht.2 x)

/-- The feasible-lambda optimum is monotone in the CQ state: passing from a CQ
state to a blockwise dominated substate can only decrease the optimum `λ`. -/
lemma minFeasibleLambda_mono_stateMap_of_opLe {X : Type*} [Fintype X] {n : ℕ}
    (ρ_small ρ_big : CQState X n) (σ : SubDensityOp n)
    (hρ : ∀ x : X, opLe (ρ_small.stateMap x).toOp (ρ_big.stateMap x).toOp)
    (hfeas : hasFeasibleLambda ρ_big σ) :
    minFeasibleLambda ρ_small σ ≤ minFeasibleLambda ρ_big σ := by
  unfold minFeasibleLambda
  have hsub : setOf (isFeasible ρ_big σ) ⊆ setOf (isFeasible ρ_small σ) :=
    fun _ ht => isFeasible_of_stateMap_opLe ρ_small ρ_big σ hρ ht
  obtain ⟨t, ht⟩ := hfeas
  have hne : (setOf (isFeasible ρ_big σ)).Nonempty := ⟨t, ht⟩
  exact csInf_le_csInf (minFeasibleLambda_bddBelow ρ_small σ) hne hsub

/-!
## Real-valued conditional min-entropy (arithmetic-friendly variant)

These definitions return a real number. They are kept public for use in
intermediate arithmetic (subtraction, linear combinations). However, they
give the wrong answer at the boundaries (see module docstring). Use the
extended conditional min-entropies as the canonical mathematical objects.
-/

/-- Real-valued conditional min-entropy of X given A in state ρ relative to reference σ.

    Tomamichel 2016, Def 6.2 (eq. 6.4):
      H_min(X|A)_{ρ|σ} = -log₂(minFeasibleLambda ρ σ)

    This is `Real.log (minFeasibleLambda ρ σ) / Real.log 2` negated.
    Kept as a real-valued variant for arithmetic convenience. At the boundary
    `minFeasibleLambda ρ σ = 0` (empty feasible set or zero infimum), Lean's
    `Real.log 0 = 0` gives a silent sentinel; use `conditionalMinEntropy` (ENNReal)
    for its boundary-correct positive part. -/
noncomputable def conditionalMinEntropyReal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : ℝ :=
  -Real.log (minFeasibleLambda ρ σ) / Real.log 2

/-- A real-valued min-entropy lower bound is equivalently an upper bound on
the feasible-lambda optimum. -/
lemma minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (k : ℝ) (hk : k ≤ conditionalMinEntropyReal ρ σ) :
    minFeasibleLambda ρ σ ≤ 2 ^ (-k) := by
  set lam := minFeasibleLambda ρ σ with hlam_def
  have hlam_nn : 0 ≤ lam := minFeasibleLambda_nonneg ρ σ
  by_cases hpos : 0 < lam
  · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hH_def : conditionalMinEntropyReal ρ σ = -Real.log lam / Real.log 2 := rfl
    rw [hH_def] at hk
    have hk_mul : k * Real.log 2 ≤ -Real.log lam :=
      (le_div_iff₀ hlog2).mp hk
    have hlog_le2 : Real.log lam ≤ -k * Real.log 2 := by linarith
    have hlog_rpow : Real.log ((2 : ℝ) ^ (-k)) = -k * Real.log 2 :=
      Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-k)
    have hrpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-k) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h_log_le : Real.log lam ≤ Real.log ((2 : ℝ) ^ (-k)) := by
      rw [hlog_rpow]
      exact hlog_le2
    exact (Real.log_le_log_iff hpos hrpow_pos).mp h_log_le
  · push Not at hpos
    have hzero : lam = 0 := le_antisymm hpos hlam_nn
    rw [hzero]
    exact Real.rpow_nonneg (by norm_num) _

/-- Conversely, a positive feasible-lambda optimum bounded by `2 ^ (-k)`
gives the corresponding real-valued min-entropy lower bound. -/
lemma conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (k : ℝ)
    (hpos : 0 < minFeasibleLambda ρ σ)
    (hle : minFeasibleLambda ρ σ ≤ 2 ^ (-k)) :
    k ≤ conditionalMinEntropyReal ρ σ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-k) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlog_le : Real.log (minFeasibleLambda ρ σ) ≤ Real.log ((2 : ℝ) ^ (-k)) :=
    Real.log_le_log hpos hle
  have hlog_rpow : Real.log ((2 : ℝ) ^ (-k)) = -k * Real.log 2 :=
    Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-k)
  unfold conditionalMinEntropyReal
  rw [hlog_rpow] at hlog_le
  have hk_mul : k * Real.log 2 ≤ -Real.log (minFeasibleLambda ρ σ) := by
    linarith
  exact (le_div_iff₀ hlog2).mpr hk_mul

/-- A pointwise real min-entropy lower bound gives blockwise domination by
`2 ^ (-k) • σ`. -/
lemma stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ : σ.toOp.PosDef)
    {k : ℝ} (hk : k ≤ conditionalMinEntropyReal ρ σ) (x : X) :
    opLe (ρ.stateMap x).toOp (Complex.ofReal (2 ^ (-k)) • σ.toOp) := by
  have hlam_le :
      minFeasibleLambda ρ σ ≤ 2 ^ (-k) :=
    minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le ρ σ k hk
  have hfeas := isFeasible_minFeasibleLambda_of_posDef ρ σ hσ
  intro v
  have hdom := hfeas.2 x v
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hdom
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact hdom.trans
    (mul_le_mul_of_nonneg_right hlam_le (σ.pos_semidef v))

/-- A pointwise real min-entropy lower bound gives blockwise domination by
`2 ^ (-k) • σ`, requiring only feasibility of the reference (no positive
definiteness).

This is the `PosDef`-free sibling of
`stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le`: the only use of the
`PosDef` hypothesis there is to attain the feasible infimum, which here is
supplied by `isFeasible_minFeasibleLambda_of_hasFeasibleLambda`. -/
lemma stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le_of_hasFeasibleLambda
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ)
    {k : ℝ} (hk : k ≤ conditionalMinEntropyReal ρ σ) (x : X) :
    opLe (ρ.stateMap x).toOp (Complex.ofReal (2 ^ (-k)) • σ.toOp) := by
  have hlam_le :
      minFeasibleLambda ρ σ ≤ 2 ^ (-k) :=
    minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le ρ σ k hk
  have hfeas' := isFeasible_minFeasibleLambda_of_hasFeasibleLambda ρ σ hfeas
  intro v
  have hdom := hfeas'.2 x v
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hdom
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact hdom.trans
    (mul_le_mul_of_nonneg_right hlam_le (σ.pos_semidef v))

/-- Real-valued optimized conditional min-entropy, maximizing over all reference operators σ.

    Tomamichel 2016, Def 6.3 (eq. 6.7, rewritten with sup):
      H_min(X|A)_ρ = sup_{σ ∈ S•(A)} H_min(X|A)_{ρ|σ}

    This is the ℝ variant for arithmetic. Use `conditionalMinEntropyOpt` (ENNReal)
    for the boundary-correct canonical form. -/
noncomputable def conditionalMinEntropyOptReal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : ℝ :=
  sSup {h | ∃ σ : SubDensityOp n, h = conditionalMinEntropyReal ρ σ}

/-!
## ENNReal-valued conditional min-entropy (canonical)

The fixed-reference quantity is the positive part of the signed extended entropy.
The optimized CQ quantity is nonnegative before clipping (Tomamichel 2016, §6.1.4).
-/

open scoped Classical in
/-- The positive part of the true fixed-reference min-entropy, as an extended nonnegative
real (Tomamichel 2016, Definition 6.2): infeasibility has true value `−∞` and gives `0`;
a feasible zero optimum gives `⊤`; a positive optimum gives
`ENNReal.ofReal (-Real.log λ* / Real.log 2)`, clipping negative finite values to zero. -/
noncomputable def conditionalMinEntropy {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) : ENNReal :=
  if 0 < minFeasibleLambda ρ σ
  then ENNReal.ofReal (conditionalMinEntropyReal ρ σ)
  else if hasFeasibleLambda ρ σ then ⊤ else 0

/-- Optimized ENNReal conditional min-entropy (Tomamichel 2016, Definition 6.2):
`sup_{σ feasible for ρ} H_min(X|A)_{ρ|σ}`. The feasible-reference domain excludes the
true value `−∞`. With the positive-part convention, including infeasible references
would give the same supremum because their ENNReal contribution is zero. -/
noncomputable def conditionalMinEntropyOpt {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : ENNReal :=
  sSup {h | ∃ σ : SubDensityOp n, hasFeasibleLambda ρ σ ∧ h = conditionalMinEntropy ρ σ}

/-- An infeasible reference contributes zero to the positive-part entropy
(Tomamichel 2016, Definition 6.2). -/
lemma conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    (h : ¬ hasFeasibleLambda ρ σ) : conditionalMinEntropy ρ σ = 0 := by
  simp [conditionalMinEntropy, minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda ρ σ h, h]

/-- A feasible zero optimum has infinite entropy (Tomamichel 2016, Definition 6.2). -/
lemma conditionalMinEntropy_eq_top_of_minFeasibleLambda_eq_zero
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    (hfeas : hasFeasibleLambda ρ σ) (hzero : minFeasibleLambda ρ σ = 0) :
    conditionalMinEntropy ρ σ = ⊤ := by
  simp [conditionalMinEntropy, hzero, hfeas]

/-- The positive part of the signed real entropy is a lower bound on the extended positive part
(Tomamichel 2016, Definition 6.2); its zero-state sentinel is below `⊤`. -/
lemma ofReal_conditionalMinEntropyReal_le {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    ENNReal.ofReal (conditionalMinEntropyReal ρ σ) ≤ conditionalMinEntropy ρ σ := by
  by_cases hfeas : hasFeasibleLambda ρ σ
  · unfold conditionalMinEntropy
    split_ifs <;> simp_all
  · rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda ρ σ hfeas]
    simp [conditionalMinEntropyReal,
      minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda ρ σ hfeas]

/-- A feasible exponential coefficient certifies a real entropy floor without any weight
condition (Tomamichel 2016, Definition 6.2). -/
lemma ofReal_le_conditionalMinEntropy_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    (k : ℝ) (h : isFeasible ρ σ (2 ^ (-k))) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ := by
  by_cases hpos : 0 < minFeasibleLambda ρ σ
  · rw [conditionalMinEntropy, if_pos hpos]
    exact ENNReal.ofReal_le_ofReal
      (conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k ρ σ k hpos
        (minFeasibleLambda_le_of_isFeasible ρ σ h))
  · simp [conditionalMinEntropy, hpos, show hasFeasibleLambda ρ σ from ⟨_, h⟩]

/-- A strictly positive extended entropy floor yields an operator-domination certificate.
Positivity excludes clipping and infeasibility (Tomamichel 2016, Definition 6.2). -/
lemma isFeasible_of_ofReal_le_conditionalMinEntropy
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    {k : ℝ} (hk : 0 < k) (hH : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    isFeasible ρ σ (2 ^ (-k)) := by
  have hfeas : hasFeasibleLambda ρ σ := by
    by_contra h
    rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda ρ σ h] at hH
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hk)) hH
  apply isFeasible_mono_t (isFeasible_minFeasibleLambda_of_hasFeasibleLambda ρ σ hfeas)
  by_cases hpos : 0 < minFeasibleLambda ρ σ
  · rw [conditionalMinEntropy, if_pos hpos] at hH
    have hreal : k ≤ conditionalMinEntropyReal ρ σ := by
      rcases ENNReal.ofReal_le_ofReal_iff'.mp hH with h | h
      · exact h
      · exact (not_le_of_gt hk h).elim
    exact minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le ρ σ k hreal
  · exact (le_of_not_gt hpos).trans (Real.rpow_nonneg (by norm_num) _)

/-- A strict lower bound on the clipped entropy certifies its signed exponential coefficient.
The strict inequality excludes infeasibility even when the requested level is nonpositive. -/
lemma isFeasible_of_ofReal_lt_conditionalMinEntropy
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    {k : ℝ} (hH : ENNReal.ofReal k < conditionalMinEntropy ρ σ) :
    isFeasible ρ σ (2 ^ (-k)) := by
  have hfeas : hasFeasibleLambda ρ σ := by
    by_contra h
    rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda ρ σ h] at hH
    exact (not_lt_of_ge (zero_le)) hH
  apply isFeasible_mono_t (isFeasible_minFeasibleLambda_of_hasFeasibleLambda ρ σ hfeas)
  by_cases hpos : 0 < minFeasibleLambda ρ σ
  · rw [conditionalMinEntropy, if_pos hpos] at hH
    exact minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le ρ σ k
      (ENNReal.ofReal_lt_ofReal_iff'.mp hH).1.le
  · exact (le_of_not_gt hpos).trans (Real.rpow_nonneg (by norm_num) _)

/-- Zero is feasible at every nonnegative coefficient, as required at the boundary of
Tomamichel 2016, Definition 6.4. -/
lemma isFeasible_zeroCQ {X : Type*} [Fintype X] {n : ℕ}
    (σ : SubDensityOp n) {t : ℝ} (ht : 0 ≤ t) :
    isFeasible (zeroCQ (X := X)) σ t := by
  refine ⟨ht, fun _ => ?_⟩
  change opLe 0 (Complex.ofReal t • σ.toOp)
  intro v
  simp only [quadraticForm, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
  change 0 ≤ (quadraticForm (Complex.ofReal t • σ.toOp) v).re
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg ht (σ.pos_semidef v)

/-- The zero CQ state has infinite min-entropy at every reference
(Tomamichel 2016, Definition 6.2, extended to zero). -/
@[simp] lemma conditionalMinEntropy_zeroCQ {X : Type*} [Fintype X] {n : ℕ}
    (σ : SubDensityOp n) : conditionalMinEntropy (zeroCQ (X := X)) σ = ⊤ := by
  have hzero := isFeasible_zeroCQ (X := X) σ (t := 0) le_rfl
  apply conditionalMinEntropy_eq_top_of_minFeasibleLambda_eq_zero _ σ ⟨0, hzero⟩
  exact le_antisymm (minFeasibleLambda_le_of_isFeasible _ σ hzero)
    (minFeasibleLambda_nonneg _ σ)

/-- Infeasible references contribute zero, so the feasible-reference optimization equals
an unrestricted supremum (Tomamichel 2016, Definition 6.2). -/
lemma conditionalMinEntropyOpt_eq_iSup {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : conditionalMinEntropyOpt ρ = ⨆ σ, conditionalMinEntropy ρ σ := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨σ, _, rfl⟩
    exact le_iSup (fun σ => conditionalMinEntropy ρ σ) σ
  · refine iSup_le fun σ => ?_
    by_cases hfeas : hasFeasibleLambda ρ σ
    · exact le_sSup ⟨σ, hfeas, rfl⟩
    · rw [conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda ρ σ hfeas]
      exact zero_le

/-!
## POVM Guessing Probability Formulation

For CQ states, there is an alternative equivalent formula via POVM guessing probability
(Tomamichel 2016, eq. 6.30):
  exp(-H_min(X|A)_ρ) = max_{POVM {M_x}} Σ_x Tr(M_x ρ_A(x))
-/

/-- The POVM guessing probability for a CQ state ρ_{XA}:
      Pg(X|A)_ρ = max_{POVM {M_x}} Σ_x Tr(M_x ρ_A(x))

    Tomamichel 2016, eq. 6.30. -/
noncomputable def povmGuessingProb {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : ℝ :=
  sSup {p | ∃ (M : X → Op n),
    -- M is a valid POVM: all elements PSD
    (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
    -- M sums to identity
    (∑ x : X, M x = 1) ∧
    -- p equals the expected guessing probability
    p = ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re}

/-- Core weak-duality building block: for any POVM-like family `M` that is
Hermitian, PSD, and sums to the identity, and any feasible `t` for `(ρ, σ)`,
the expected guessing-probability is bounded by `t`.

Proof: `∑_x Tr(M_x · ρ_A(x)).re ≤ ∑_x Tr(M_x · t·σ).re = t · Tr((∑ M_x) · σ).re
= t · Tr(σ).re ≤ t`. -/
lemma povmTraceSum_le_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (M : X → Op n)
    (hM_herm : ∀ x : X, (M x).IsHermitian)
    (hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (hM_sum : ∑ x : X, M x = 1)
    {t : ℝ} (ht : isFeasible ρ σ t) :
    ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re ≤ t := by
  obtain ⟨ht_nn, ht_dom⟩ := ht
  -- Each M x is Mathlib-PSD
  have hM_psd : ∀ x : X, Matrix.PosSemidef (M x) := fun x =>
    posSemidef_of_isHermitian_of_quadraticForm_re_nonneg (hM_herm x) (hM_pos x)
  -- Hermiticity of t • σ.toOp
  have h_tσ_herm : ((Complex.ofReal t) • σ.toOp).IsHermitian :=
    isHermitian_real_smul σ.isHermitian t
  -- Per-x trace monotonicity: Tr(M_x · ρ_A(x)).re ≤ Tr(M_x · t·σ).re
  have h_each : ∀ x : X,
      ((M x) * (ρ.stateMap x).toOp).trace.re ≤
      ((M x) * ((Complex.ofReal t) • σ.toOp)).trace.re := fun x =>
    trace_mul_le_of_opLe (hM_psd x) (ρ.stateMap x).isHermitian h_tσ_herm (ht_dom x)
  -- Compute ∑_x Tr(M_x · (t•σ)).re = t · σ.trace
  have h_sum_rhs :
      ∑ x : X, ((M x) * ((Complex.ofReal t) • σ.toOp)).trace.re =
        t * σ.trace := by
    have h_re_smul : ∀ x : X,
        ((M x) * ((Complex.ofReal t) • σ.toOp)).trace.re =
        t * ((M x) * σ.toOp).trace.re := fun x => by
      rw [Matrix.mul_smul, trace_real_smul_re]
    simp_rw [h_re_smul]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hM_sum, one_mul]
    rfl
  -- chain the inequalities
  calc ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re
      ≤ ∑ x : X, ((M x) * ((Complex.ofReal t) • σ.toOp)).trace.re :=
        Finset.sum_le_sum (fun x _ => h_each x)
    _ = t * σ.trace := h_sum_rhs
    _ ≤ t * 1 :=
        mul_le_mul_of_nonneg_left σ.trace_le_one ht_nn
    _ = t := mul_one t

/-!
### Hermitianization of a raw POVM-like family

The definition of `povmGuessingProb` does not require Hermiticity of each
`M x`. Its symmetrization `H x := (1/2) • (M x + (M x)ᴴ)` is Hermitian, PSD,
and still sums to the identity; moreover, against any Hermitian target `B x`
(in particular `ρ.stateMap x`), the real part of the trace sum is unchanged.
This lets the weak-duality arguments below work with `M` directly.
-/

/-- Hermitianization of a raw POVM-like family `M`: `(1/2) • (M x + (M x)ᴴ)`. -/
noncomputable def symmFamily {X : Type*} {n : ℕ} (M : X → Op n) : X → Op n :=
  fun x => (1/2 : ℂ) • (M x + (M x)ᴴ)

lemma symmFamily_isHermitian {X : Type*} {n : ℕ}
    (M : X → Op n) (x : X) : (symmFamily M x).IsHermitian :=
  Quantum.Operators.isHermitian_symmetrization (M x)

lemma symmFamily_quadraticForm_re_nonneg {X : Type*} {n : ℕ}
    (M : X → Op n) (hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (x : X) (v : Fin n → ℂ) : 0 ≤ (quadraticForm (symmFamily M x) v).re := by
  unfold symmFamily
  rw [Quantum.Operators.quadraticForm_symmetrization_re]
  exact hM_pos x v

lemma symmFamily_sum_eq_one {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (hM_sum : ∑ x : X, M x = 1) :
    ∑ x : X, symmFamily M x = 1 :=
  Quantum.Operators.sum_symmetrization_eq_one M hM_sum

/-- Against any Hermitian family `B : X → Op n`, the symmetrized family `H`
and the raw family `M` produce the same trace-sum real parts. -/
lemma symmFamily_trace_sum_re_eq {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (B : X → Op n) (hB : ∀ x, (B x).IsHermitian) :
    ∑ x : X, ((symmFamily M x) * (B x)).trace.re =
      ∑ x : X, ((M x) * (B x)).trace.re := by
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold symmFamily
  exact Quantum.Operators.trace_mul_symmetrization_re_of_isHermitian (M x) (B x) (hB x)

/-!
### One-hot POVM witness

For nonempty `X`, the one-hot family `fun x => if x = x₀ then 1 else 0` is a
valid POVM-like family in the sense of `povmGuessingProb`. We record its three
defining properties here.
-/

/-- Quadratic form of the identity has nonneg real part for any vector. -/
private lemma zero_le_quadraticForm_one_re {n : ℕ} (v : Fin n → ℂ) :
    0 ≤ (quadraticForm (1 : Op n) v).re := by
  have h_ps : Matrix.PosSemidef (1 : Op n) := Matrix.PosSemidef.one
  have h_nn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h_ps).2 v
  exact (Complex.nonneg_iff.mp h_nn).1

/-- Quadratic form of the zero operator is zero. -/
private lemma quadraticForm_zero_re {n : ℕ} (v : Fin n → ℂ) :
    (quadraticForm (0 : Op n) v).re = 0 := by
  unfold quadraticForm
  simp [Matrix.zero_mulVec]

/-- The one-hot POVM-like family at `x₀`. -/
noncomputable def oneHotPovm {X : Type*} [DecidableEq X] {n : ℕ}
    (x₀ : X) : X → Op n := fun x => if x = x₀ then (1 : Op n) else 0

lemma oneHotPovm_quadraticForm_re_nonneg {X : Type*} [DecidableEq X] {n : ℕ}
    (x₀ : X) (x : X) (v : Fin n → ℂ) :
    0 ≤ (quadraticForm (oneHotPovm x₀ x : Op n) v).re := by
  unfold oneHotPovm
  by_cases hx : x = x₀
  · rw [if_pos hx]; exact zero_le_quadraticForm_one_re v
  · rw [if_neg hx, quadraticForm_zero_re]

lemma oneHotPovm_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (x₀ : X) : ∑ x : X, (oneHotPovm x₀ x : Op n) = 1 := by
  unfold oneHotPovm
  simp [Finset.sum_ite_eq']

/-- The trace sum against the one-hot witness collapses to the single term at `x₀`. -/
lemma oneHotPovm_trace_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (x₀ : X) :
    ∑ x : X, ((oneHotPovm x₀ x : Op n) * (ρ.stateMap x).toOp).trace.re =
      ((ρ.stateMap x₀).toOp).trace.re := by
  unfold oneHotPovm
  have h_each : ∀ x : X,
      ((if x = x₀ then (1 : Op n) else 0) * (ρ.stateMap x).toOp).trace.re =
      if x = x₀ then ((ρ.stateMap x).toOp).trace.re else 0 := by
    intro x
    by_cases hx : x = x₀
    · rw [if_pos hx, one_mul, if_pos hx]
    · rw [if_neg hx, zero_mul, Matrix.trace_zero, Complex.zero_re, if_neg hx]
  simp_rw [h_each]
  rw [Finset.sum_ite_eq' Finset.univ x₀]
  simp

/-- If a family of operators with nonnegative real quadratic form sums to the
identity, then each member is dominated by the identity in the semidefinite
ordering `opLe`. -/
lemma opLe_one_of_sum_eq_one {X : Type*} [Fintype X] {n : ℕ}
    (F : X → Op n)
    (hF_qf : ∀ y : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (F y) v).re)
    (hF_sum : ∑ y : X, F y = 1) (x : X) : opLe (F x) 1 := by
  intro v
  have h_qf_one : (quadraticForm (1 : Op n) v).re =
      ∑ y : X, (quadraticForm (F y) v).re := by
    rw [← hF_sum]
    unfold quadraticForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [h_qf_one]
  exact Finset.single_le_sum (f := fun y => (quadraticForm (F y) v).re)
    (fun y _ => hF_qf y v) (Finset.mem_univ x)

/-- For any raw POVM-like family `M` (nonnegative real quadratic form, summing
to the identity), the expected guessing-probability trace sum against a CQ
state is bounded by the total weight `∑_x Tr(ρ_A(x)).re` of the state. -/
private lemma povmLike_traceSum_le_weightSum {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (hM_sum : ∑ x : X, M x = 1) :
    ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re ≤
      ∑ x : X, ((ρ.stateMap x).toOp).trace.re := by
  have h_trace_eq :=
    symmFamily_trace_sum_re_eq M (fun x => (ρ.stateMap x).toOp)
      (fun x => (ρ.stateMap x).isHermitian)
  rw [← h_trace_eq]
  have hH_herm := symmFamily_isHermitian M
  have hH_qf := symmFamily_quadraticForm_re_nonneg M hM_pos
  have hH_sum := symmFamily_sum_eq_one M hM_sum
  have h_opLe := opLe_one_of_sum_eq_one (symmFamily M) hH_qf hH_sum
  have h_one_herm : (1 : Op n).IsHermitian := Matrix.isHermitian_one
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hρ_psd : Matrix.PosSemidef (ρ.stateMap x).toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have h := trace_mul_le_of_opLe hρ_psd (hH_herm x) h_one_herm (h_opLe x)
  rw [mul_one, Matrix.trace_mul_comm] at h
  exact h

/-- For any raw POVM-like family `M`, the expected guessing-probability trace
sum against a CQ state is at most `1`. Combines
`povmLike_traceSum_le_weightSum` with `CQState.weight_le_one`. -/
lemma povmLike_traceSum_le_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (hM_sum : ∑ x : X, M x = 1) :
    ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re ≤ 1 :=
  (povmLike_traceSum_le_weightSum ρ M hM_pos hM_sum).trans
    (by simpa [SubDensityOp.trace] using ρ.weight_le_one)

/-- The POVM guessing probability is nonnegative.

For nonempty `X`, the one-hot witness at any `x₀ : X` gives a value
`(ρ.stateMap x₀).toOp.trace.re ≥ 0` in the sSup-set. Boundedness above by `1`
follows from `povmLike_traceSum_le_one`, so `le_csSup` closes the bound. -/
lemma povmGuessingProb_nonneg {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) : 0 ≤ povmGuessingProb ρ := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      p = ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re}
  have hmem : ((ρ.stateMap x₀).toOp).trace.re ∈ S :=
    ⟨oneHotPovm x₀, oneHotPovm_quadraticForm_re_nonneg x₀,
      oneHotPovm_sum x₀, (oneHotPovm_trace_sum ρ x₀).symm⟩
  have hnonneg : 0 ≤ ((ρ.stateMap x₀).toOp).trace.re := (ρ.stateMap x₀).trace_nonneg
  have hBdd : BddAbove S := by
    refine ⟨1, fun p hp => ?_⟩
    obtain ⟨M, hM_pos, hM_sum, rfl⟩ := hp
    exact povmLike_traceSum_le_one ρ M hM_pos hM_sum
  calc 0 ≤ ((ρ.stateMap x₀).toOp).trace.re := hnonneg
    _ ≤ povmGuessingProb ρ := le_csSup hBdd hmem

/-- The POVM guessing probability is at most 1.

For any `M` in the sSup-set, `povmLike_traceSum_le_one` bounds the expected
trace sum by 1. When the set is empty, `sSup ∅ = 0 ≤ 1`. -/
lemma povmGuessingProb_le_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : povmGuessingProb ρ ≤ 1 := by
  classical
  unfold povmGuessingProb
  by_cases hne : ({p | ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      p = ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re} : Set ℝ).Nonempty
  · refine csSup_le hne ?_
    rintro p ⟨M, hM_pos, hM_sum, rfl⟩
    exact povmLike_traceSum_le_one ρ M hM_pos hM_sum
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact zero_le_one

/-- Weak duality: for any feasible reference `σ`, the POVM guessing
probability is at most the smallest feasible `λ`.

Proof: for any `M` in the sSup-set defining `povmGuessingProb`, Hermitianize
to `H x := (1/2) • (M x + (M x)ᴴ)`. The family `H` is Hermitian, PSD, and sums
to `1`, so `povmTraceSum_le_of_isFeasible` gives
`∑_x Tr(H_x · ρ_A(x)).re ≤ t` for every feasible `t`. And
`∑_x Tr(H_x · ρ_A(x)).re = ∑_x Tr(M_x · ρ_A(x)).re` because each
`ρ.stateMap x` is Hermitian. So each `p` in the sSup-set is ≤ every feasible
`t`. Finally `csSup_le` + `le_csInf` give the claim. -/
lemma povmGuessingProb_le_minFeasibleLambda {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ) :
    povmGuessingProb ρ ≤ minFeasibleLambda ρ σ := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  -- Shorthand: the sSup-set defining `povmGuessingProb`.
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      p = ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re}
  -- One-hot witness showing S is nonempty.
  have hS_ne : S.Nonempty :=
    ⟨_, oneHotPovm x₀, oneHotPovm_quadraticForm_re_nonneg x₀,
      oneHotPovm_sum x₀, rfl⟩
  -- For every feasible `t`, every `p ∈ S` satisfies `p ≤ t`.
  have h_bound : ∀ t ∈ setOf (isFeasible ρ σ), ∀ p ∈ S, p ≤ t := by
    intro t ht p hp
    obtain ⟨M, hM_pos, hM_sum, rfl⟩ := hp
    have h_trace_eq :
        ∑ x : X, ((symmFamily M x) * (ρ.stateMap x).toOp).trace.re =
          ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re :=
      symmFamily_trace_sum_re_eq M (fun x => (ρ.stateMap x).toOp)
        (fun x => (ρ.stateMap x).isHermitian)
    rw [← h_trace_eq]
    exact povmTraceSum_le_of_isFeasible ρ σ (symmFamily M)
      (symmFamily_isHermitian M)
      (symmFamily_quadraticForm_re_nonneg M hM_pos)
      (symmFamily_sum_eq_one M hM_sum)
      ht
  -- Now apply `csSup_le` to get `sSup S ≤ t`, then `le_csInf` to get `sSup S ≤ sInf feasible`.
  have h_pg_le : ∀ t ∈ setOf (isFeasible ρ σ), povmGuessingProb ρ ≤ t := by
    intro t ht
    change sSup S ≤ t
    exact csSup_le hS_ne (fun p hp => h_bound t ht p hp)
  apply le_csInf
  · exact hfeas
  · exact h_pg_le

/-!
## Helper lemmas for the `log_card` upper bound

These are low-level facts about `opLe`, `quadraticForm`, and the feasible set.
They are kept in this file because they are specific to this file's abstractions.
-/

/-- Plugging the standard basis vector `Pi.single i 1` into the quadratic form
    picks out the diagonal entry `A i i`. -/
lemma quadraticForm_stdBasis_diag {n : ℕ} (A : Op n) (i : Fin n) :
    quadraticForm A (Pi.single i 1) = A i i := by
  unfold quadraticForm
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- The PSD ordering `opLe` implies pointwise inequality of the real parts of
    the diagonal entries. -/
lemma opLe_re_diag_le {n : ℕ} {A B : Op n} (h : opLe A B) (i : Fin n) :
    (A i i).re ≤ (B i i).re := by
  have hq := h (Pi.single i 1)
  rwa [quadraticForm_stdBasis_diag, quadraticForm_stdBasis_diag] at hq

/-- The real part of a matrix trace is the sum of the real parts of the diagonal entries. -/
lemma trace_re_eq_sum_diag_re {n : ℕ} (A : Op n) :
    A.trace.re = ∑ i : Fin n, (A i i).re := by
  simp [Matrix.trace, Matrix.diag, Complex.re_sum]

/-- The PSD ordering `opLe` implies an inequality on the real part of the trace. -/
lemma opLe_trace_re_le {n : ℕ} {A B : Op n} (h : opLe A B) :
    A.trace.re ≤ B.trace.re := by
  rw [trace_re_eq_sum_diag_re, trace_re_eq_sum_diag_re]
  exact Finset.sum_le_sum (fun i _ => opLe_re_diag_le h i)

/-- Core pointwise bound: for any feasible `t`, the average weight
    `(∑_x Tr(ρ_A(x)).re)/|X|` is at most `t`.

    Per outcome `x`, `opLe` gives `Tr(ρ_A(x)).re ≤ t·Tr(σ).re ≤ t`. Summing and
    dividing by `|X|` yields the average. This is the shared arithmetic core of
    `minFeasibleLambda_ge_weight_div_card`, `minFeasibleLambda_ge_inv_card`, and
    `minFeasibleLambda_pos_of_hasFeasibleLambda`. -/
lemma weight_div_card_le_of_isFeasible {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ} (ht : isFeasible ρ σ t) :
    (∑ x : X, (ρ.stateMap x).trace) / (Fintype.card X : ℝ) ≤ t := by
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  obtain ⟨ht_nn, ht_dom⟩ := ht
  have h_smul_tr : ((Complex.ofReal t • σ.toOp).trace).re = t * σ.toOp.trace.re :=
    trace_real_smul_re t σ.toOp
  have h_each : ∀ x : X, (ρ.stateMap x).trace ≤ t * σ.toOp.trace.re := fun x => by
    have h1 := opLe_trace_re_le (ht_dom x)
    rw [h_smul_tr] at h1
    exact h1
  have h_sum : ∑ x : X, (ρ.stateMap x).trace ≤ ∑ _ : X, t * σ.toOp.trace.re :=
    Finset.sum_le_sum (fun x _ => h_each x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h_sum
  have hσ_le : σ.toOp.trace.re ≤ 1 := σ.trace_le_one
  have h3 : (∑ x : X, (ρ.stateMap x).trace) ≤ (Fintype.card X : ℝ) * t :=
    calc (∑ x : X, (ρ.stateMap x).trace)
        ≤ (Fintype.card X : ℝ) * (t * σ.toOp.trace.re) := h_sum
      _ ≤ (Fintype.card X : ℝ) * t := by
          apply mul_le_mul_of_nonneg_left _ hcard_pos.le
          calc t * σ.toOp.trace.re
              ≤ t * 1 := mul_le_mul_of_nonneg_left hσ_le ht_nn
            _ = t := mul_one t
  rw [div_le_iff₀ hcard_pos]
  linarith

/-- A strictly positive `minFeasibleLambda` rules out the empty feasible set
    (where `sInf ∅ = 0`), so the feasible set is nonempty. -/
private lemma feasibleSet_nonempty_of_minFeasibleLambda_pos {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hpos : 0 < minFeasibleLambda ρ σ) :
    (setOf (isFeasible ρ σ)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hem
  unfold minFeasibleLambda at hpos
  rw [hem, Real.sInf_empty] at hpos
  exact lt_irrefl _ hpos

/-- Sub-normalized bound on the feasible-λ infimum: whenever the feasible set is
    nontrivial (infimum strictly positive), the infimum is at least `w / |X|`,
    where `w = ∑_x (ρ.stateMap x).trace` is the total real weight of the CQ state. -/
lemma minFeasibleLambda_ge_weight_div_card {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hpos : 0 < minFeasibleLambda ρ σ) :
    (∑ x : X, (ρ.stateMap x).trace) / (Fintype.card X : ℝ) ≤ minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  exact le_csInf (feasibleSet_nonempty_of_minFeasibleLambda_pos ρ σ hpos)
    (fun _ ht => weight_div_card_le_of_isFeasible ρ σ ht)

/-- Whenever the feasible set is nontrivial (the infimum is strictly positive),
    every feasible `t` is at least `1/|X|`, so is the infimum.

    This is the key elementary bound in the proof that
    `conditionalMinEntropyOptReal ρ ≤ log₂ |X|` for a normalized CQ state. -/
lemma minFeasibleLambda_ge_inv_card {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : SubDensityOp n) (hpos : 0 < minFeasibleLambda ρ σ) :
    1 / (Fintype.card X : ℝ) ≤ minFeasibleLambda ρ σ := by
  have h := minFeasibleLambda_ge_weight_div_card ρ σ hpos
  rwa [hnorm] at h

/-- For a normalized CQ state, if the feasible set for `(ρ, σ)` is nonempty then
    `minFeasibleLambda ρ σ ≥ 1/|X| > 0`. -/
lemma minFeasibleLambda_pos_of_hasFeasibleLambda {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ) :
    0 < minFeasibleLambda ρ σ := by
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hinv_pos : (0 : ℝ) < 1 / (Fintype.card X : ℝ) := by positivity
  have h_ge : 1 / (Fintype.card X : ℝ) ≤ minFeasibleLambda ρ σ := by
    unfold minFeasibleLambda
    refine le_csInf hfeas (fun t ht => ?_)
    have := weight_div_card_le_of_isFeasible ρ σ ht
    rwa [hnorm] at this
  exact lt_of_lt_of_le hinv_pos h_ge

/-- Subnormalized positivity: if the total CQ weight is strictly positive and
the feasible set is nonempty, then the feasible-lambda optimum is strictly
positive. -/
lemma minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hweight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (hfeas : hasFeasibleLambda ρ σ) :
    0 < minFeasibleLambda ρ σ := by
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hdiv_pos :
      0 < (∑ x : X, (ρ.stateMap x).trace) / (Fintype.card X : ℝ) :=
    div_pos hweight_pos hcard_pos
  have h_ge :
      (∑ x : X, (ρ.stateMap x).trace) / (Fintype.card X : ℝ) ≤
        minFeasibleLambda ρ σ := by
    unfold minFeasibleLambda
    exact le_csInf hfeas (fun _ ht => weight_div_card_le_of_isFeasible ρ σ ht)
  exact lt_of_lt_of_le hdiv_pos h_ge

/-- A positive total CQ weight and a positive-definite reference force the
real feasible-lambda infimum to be strictly positive. -/
lemma minFeasibleLambda_pos_of_posDef_of_weight_pos
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ : σ.toOp.PosDef)
    (hρ_weight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace) :
    0 < minFeasibleLambda ρ σ := by
  haveI : Nonempty X := by
    by_contra hnot
    rw [not_nonempty_iff] at hnot
    have hsum_zero : (∑ x : X, (ρ.stateMap x).trace) = 0 := by
      simp
    linarith
  exact minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
    ρ σ hρ_weight_pos (hasFeasibleLambda_of_posDef ρ σ hσ)

/-- Bound on the real-valued conditional min-entropy: for a normalized CQ state,
    `H_min(X|A)_{ρ|σ} ≤ log₂ |X|` for every reference operator `σ`. -/
lemma conditionalMinEntropyReal_le_log_card {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : SubDensityOp n) :
    conditionalMinEntropyReal ρ σ ≤ Real.log (Fintype.card X) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard_pos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hcard_ge_one : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold conditionalMinEntropyReal
  -- Split on whether `minFeasibleLambda ρ σ > 0` or not.
  by_cases hm_pos : 0 < minFeasibleLambda ρ σ
  · -- Nontrivial case: use `minFeasibleLambda_ge_inv_card`.
    have hinv_pos : (0 : ℝ) < 1 / (Fintype.card X : ℝ) := by positivity
    have hm_ge : 1 / (Fintype.card X : ℝ) ≤ minFeasibleLambda ρ σ :=
      minFeasibleLambda_ge_inv_card ρ hnorm σ hm_pos
    have hlog_le :
        Real.log (1 / (Fintype.card X : ℝ)) ≤ Real.log (minFeasibleLambda ρ σ) :=
      Real.log_le_log hinv_pos hm_ge
    have hlog_inv :
        Real.log (1 / (Fintype.card X : ℝ)) = -Real.log (Fintype.card X) := by
      rw [one_div, Real.log_inv]
    rw [hlog_inv] at hlog_le
    -- Now `-Real.log |X| ≤ Real.log (minFeasibleLambda ρ σ)`.
    have h_neg : -Real.log (minFeasibleLambda ρ σ) ≤ Real.log (Fintype.card X) := by
      linarith
    gcongr
  · -- Degenerate case: `minFeasibleLambda ρ σ ≤ 0`, so the LHS is `0`.
    push Not at hm_pos
    have hm_zero : minFeasibleLambda ρ σ = 0 :=
      le_antisymm hm_pos (minFeasibleLambda_nonneg ρ σ)
    rw [hm_zero, Real.log_zero, neg_zero, zero_div]
    exact div_nonneg (Real.log_nonneg hcard_ge_one) hlog2.le

/-- The optimized real min-entropy is upper bounded in terms of the system size.

    For a normalized CQ state with |X| = Fintype.card X:
      H_min(X|A)_ρ ≤ log₂(|X|)

    The normalization hypothesis `hnorm` is required: for a sub-normalized state
    with total weight `w < 1`, the quantity `H_min` can exceed `log₂ |X|`. -/
theorem conditionalMinEntropyOptReal_le_log_card {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    [NeZero n] (ρ : CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    conditionalMinEntropyOptReal ρ ≤ Real.log (Fintype.card X) / Real.log 2 := by
  apply csSup_le
  · -- The set is nonempty: take σ = 0.
    exact ⟨conditionalMinEntropyReal ρ (0 : SubDensityOp n), (0 : SubDensityOp n), rfl⟩
  · rintro h ⟨σ, rfl⟩
    exact conditionalMinEntropyReal_le_log_card ρ hnorm σ

/-- The optimized ENNReal min-entropy is upper bounded in terms of the system size.

    H_min(X|A)_ρ ≤ ENNReal.ofReal (log₂ |X|) as an ENNReal bound.
    Follows from `conditionalMinEntropyOptReal_le_log_card`. -/
theorem conditionalMinEntropyOpt_le_log_card {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    [NeZero n] (ρ : CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    conditionalMinEntropyOpt ρ ≤
    ENNReal.ofReal (Real.log (Fintype.card X) / Real.log 2) := by
  unfold conditionalMinEntropyOpt
  apply sSup_le
  rintro h ⟨σ, hfeas, rfl⟩
  -- Obligation: conditionalMinEntropy ρ σ ≤ ENNReal.ofReal (log |X| / log 2)
  have hpos : 0 < minFeasibleLambda ρ σ :=
    minFeasibleLambda_pos_of_hasFeasibleLambda ρ hnorm σ hfeas
  unfold conditionalMinEntropy
  rw [if_pos hpos]
  exact ENNReal.ofReal_le_ofReal (conditionalMinEntropyReal_le_log_card ρ hnorm σ)

/-- Real min-entropy is antitone in σ: smaller reference operators give smaller
    min-entropy (equivalently, larger references give larger min-entropy).

    Under hypothesis `τ ≼ σ` (Löwner order) with feasibility on `τ`:
      H_min(X|A)_{ρ|τ} ≤ H_min(X|A)_{ρ|σ}.

    The feasibility side hypothesis `hasFeasibleLambda ρ τ` is needed because the
    real-valued variant uses Mathlib's `Real.log 0 = 0` sentinel at the boundary.

    The additional side condition `0 < minFeasibleLambda ρ σ` encodes finiteness
    of `H_min(X|A)_{ρ|σ}` (equivalently, `conditionalMinEntropy ρ σ < ⊤`).
    Without it, the boundary case `minFeasibleLambda ρ σ = 0` would require a
    PSD-limit argument to force `minFeasibleLambda ρ τ = 0` as well. -/
theorem conditionalMinEntropyReal_antitone_sigma {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ τ : SubDensityOp n)
    (h : ∀ v : Fin n → ℂ, (quadraticForm τ.toOp v).re ≤ (quadraticForm σ.toOp v).re)
    (hfeas : hasFeasibleLambda ρ τ)
    (hpos : 0 < minFeasibleLambda ρ σ) :
    conditionalMinEntropyReal ρ τ ≤ conditionalMinEntropyReal ρ σ := by
  set ls := minFeasibleLambda ρ σ
  set lt := minFeasibleLambda ρ τ
  have hle : ls ≤ lt := minFeasibleLambda_antitone_of_opLe ρ σ τ h hfeas
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log ls ≤ Real.log lt := Real.log_le_log hpos hle
  unfold conditionalMinEntropyReal
  exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le

/-- Real min-entropy is monotone under passing to a blockwise dominated CQ
substate, provided the dominated state has positive feasible-lambda infimum.

If `ρ_small(x) ≤ ρ_big(x)` for every classical block, then every feasible scalar
for `ρ_big` is feasible for `ρ_small`, so the feasible optimum for `ρ_small` is
no larger and the real min-entropy is no smaller. -/
theorem conditionalMinEntropyReal_mono_stateMap_of_opLe {X : Type*} [Fintype X] {n : ℕ}
    [NeZero n]
    (ρ_small ρ_big : CQState X n) (σ : SubDensityOp n)
    (hρ : ∀ x : X, opLe (ρ_small.stateMap x).toOp (ρ_big.stateMap x).toOp)
    (hfeas : hasFeasibleLambda ρ_big σ)
    (hpos : 0 < minFeasibleLambda ρ_small σ) :
    conditionalMinEntropyReal ρ_big σ ≤ conditionalMinEntropyReal ρ_small σ := by
  set ls := minFeasibleLambda ρ_small σ
  set lb := minFeasibleLambda ρ_big σ
  have hle : ls ≤ lb := by
    simpa [ls, lb] using
      minFeasibleLambda_mono_stateMap_of_opLe ρ_small ρ_big σ hρ hfeas
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log ls ≤ Real.log lb := Real.log_le_log hpos hle
  unfold conditionalMinEntropyReal
  exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le

/-- ENNReal min-entropy is antitone in σ: smaller reference operators give smaller
    min-entropy (equivalently, larger references give larger min-entropy).

    Derived from `conditionalMinEntropyReal_antitone_sigma` in its feasible, positive-optimum
    regime. Infeasible references have value zero under the positive-part convention
    (Tomamichel 2016, Definition 6.2). -/
theorem conditionalMinEntropy_antitone_sigma {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ τ : SubDensityOp n)
    (h : ∀ v : Fin n → ℂ, (quadraticForm τ.toOp v).re ≤ (quadraticForm σ.toOp v).re)
    (hfeas : hasFeasibleLambda ρ τ)
    (hpos : 0 < minFeasibleLambda ρ σ) :
    conditionalMinEntropy ρ τ ≤ conditionalMinEntropy ρ σ := by
  have hle : minFeasibleLambda ρ σ ≤ minFeasibleLambda ρ τ :=
    minFeasibleLambda_antitone_of_opLe ρ σ τ h hfeas
  have hpos_tau : 0 < minFeasibleLambda ρ τ := lt_of_lt_of_le hpos hle
  unfold conditionalMinEntropy
  rw [if_pos hpos, if_pos hpos_tau]
  exact ENNReal.ofReal_le_ofReal
    (conditionalMinEntropyReal_antitone_sigma ρ σ τ h hfeas hpos)

/-- Subtracting a base-two logarithmic penalty multiplies the feasible coefficient. -/
lemma two_rpow_neg_sub_log (k : ℝ) {c : ℝ} (hc : 0 < c) :
    (2 : ℝ) ^ (-(k - Real.log c / Real.log 2)) = c * 2 ^ (-k) := by
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _))
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  ring

/-- Transporting every feasible coefficient increases the extended positive-part entropy. -/
lemma conditionalMinEntropy_le_of_isFeasible_imp
    {X Y : Type*} [Fintype X] [Fintype Y] {n m : ℕ}
    (ρ : CQState X n) (τ : CQState Y m) (σ : SubDensityOp n) (ω : SubDensityOp m)
    (h : ∀ t, isFeasible ρ σ t → isFeasible τ ω t) :
    conditionalMinEntropy ρ σ ≤ conditionalMinEntropy τ ω := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  have hpos : 0 < (r : ℝ) := hr
  have hfloor : ENNReal.ofReal (r : ℝ) ≤ conditionalMinEntropy ρ σ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hlt.le
  simpa only [ENNReal.ofReal_coe_nnreal] using
    ofReal_le_conditionalMinEntropy_of_isFeasible τ ω r
      (h _ (isFeasible_of_ofReal_le_conditionalMinEntropy ρ σ hpos hfloor))

/-- A signed exponential-coefficient transport gives an extended entropy comparison with
the positive part of its real penalty. -/
lemma conditionalMinEntropy_le_add_of_isFeasible_imp
    {X Y : Type*} [Fintype X] [Fintype Y] {n m : ℕ}
    (ρ : CQState X n) (τ : CQState Y m) (σ : SubDensityOp n) (ω : SubDensityOp m)
    (p : ℝ)
    (h : ∀ k : ℝ, isFeasible ρ σ (2 ^ (-k)) → isFeasible τ ω (2 ^ (-(k - p)))) :
    conditionalMinEntropy ρ σ ≤ conditionalMinEntropy τ ω + ENNReal.ofReal p := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  have hpos : 0 < (r : ℝ) := hr
  have hfloor : ENNReal.ofReal (r : ℝ) ≤ conditionalMinEntropy ρ σ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hlt.le
  have htarget := ofReal_le_conditionalMinEntropy_of_isFeasible τ ω ((r : ℝ) - p)
    (h _ (isFeasible_of_ofReal_le_conditionalMinEntropy ρ σ hpos hfloor))
  calc
    (r : ENNReal) = ENNReal.ofReal (((r : ℝ) - p) + p) := by simp
    _ ≤ ENNReal.ofReal ((r : ℝ) - p) + ENNReal.ofReal p := ENNReal.ofReal_add_le
    _ ≤ conditionalMinEntropy τ ω + ENNReal.ofReal p := add_le_add htarget le_rfl


/-- Feasibility at `2 ^ (-k)` gives the signed conditional entropy floor `k` for a
positive-weight state against a positive-definite reference. -/
lemma conditionalMinEntropyReal_ge_of_isFeasible_pow_neg_of_weight_pos
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ : σ.toOp.PosDef)
    (k : ℝ)
    (hweight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (hfeasible : isFeasible ρ σ ((2 : ℝ) ^ (-k))) :
    k ≤ conditionalMinEntropyReal ρ σ := by
  have hlam_le :
      minFeasibleLambda ρ σ ≤ (2 : ℝ) ^ (-k) :=
    csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeasible
  have hfeas : hasFeasibleLambda ρ σ :=
    hasFeasibleLambda_of_posDef ρ σ hσ
  have hpos : 0 < minFeasibleLambda ρ σ :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
      ρ σ hweight_pos hfeas
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
    ρ σ k hpos hlam_le

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
