import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.OfBlocks
import QCryptLean.Quantum.Operators.RankOneOrder

/-!
# The superposition penalty: Bouman–Fehr Lemma 1

Measuring a *superposition* of `|J|` orthogonal branches produces at most `log₂ |J|` bits less
uncertainty than measuring the corresponding *dephased mixture*.  This is Lemma 1 of

> N. J. Bouman and S. Fehr, *Sampling in a Quantum Population, and Applications*, CRYPTO 2010,
> [arXiv:0907.4246v5](https://arxiv.org/abs/0907.4246), §4.3 (statement) and Appendix C (proof),

where it is stated for the pure state `|φ_AE⟩ = ∑_{i ∈ J} αᵢ |i⟩|φⁱ_E⟩` and the hybrid states
`ρ_WE`, `ρ^mix_WE` obtained by measuring `A` in an orthonormal basis `{|w⟩}`:

  `H_min(ρ_WE | E) ≥ H_min(ρ^mix_WE | E) − log |J|`.

## What is abstracted, and how it matches the paper

Writing out the measurement (Appendix C) gives, for each outcome `w`, the blocks

  `ρ_WE(w) = |∑_{i ∈ J} vᵢ(w)⟩⟨∑_{i ∈ J} vᵢ(w)|`,  `ρ^mix_WE(w) = ∑_{i ∈ J} |vᵢ(w)⟩⟨vᵢ(w)|`,
  with `vᵢ(w) := αᵢ ⟨w|i⟩ · φⁱ_E`.

Only this *block shape* is used, so `SuperpositionMixture` below records exactly it: an arbitrary
family of Eve-side vectors `v w i`, a finite index set `J`, and two CQ states whose blocks are the
rank-one operator of the sum and the dephased sum of rank-one operators.  Bouman–Fehr's
measurement data is the special case named above; `SuperpositionMixture.ofVectors` constructs the
pair from the vectors alone, so nothing here is conditional on states that might not exist.

The paper's proof has two steps, kept separate here:

1. the Löwner bound `ρ_WE ⪯ |J| · ρ^mix_WE`, which is Cauchy–Schwarz applied blockwise
   (`Quantum.Operators.vecMulVec_sum_opLe_card_smul_sum_vecMulVec`); and
2. the resulting rescaling of the min-entropy semidefinite program, which is the library's
   `conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling`.

Step 1 holds **for every reference `σ` separately**, which is why both the fixed-reference and
the optimized (`sup_σ`) forms are available below.

## Conventions and boundaries (read before using)

* `conditionalMinEntropyReal ρ σ` is the **fixed-reference** `H_min(ρ|σ) = −log₂ λ*(ρ, σ)`; it is
  *not* the optimized `H_min(X|E)`.  The optimized form of the paper's statement is
  `conditionalMinEntropyOpt_mixture_le_superposition_add_logb_card`.
* Logarithms are base two throughout (`Real.logb 2`), matching `conditionalMinEntropyReal`.
* `conditionalMinEntropyReal` returns the sentinel `0` when `λ* = 0`, so the real-valued form
  genuinely needs `0 < minFeasibleLambda` on *both* states.  It is not a bookkeeping nuisance:
  with `J = {0, 1}`, `v w 0 = x`, `v w 1 = -x` the superposition state is `0` while the mixture
  is `2|x⟩⟨x|`, so `λ*_sup = 0` while `H_min` of the mixture is unbounded above as `x → 0`.
  The `ENNReal`-valued forms — which give `⊤` there, the mathematically correct value — need
  **no** positivity side condition and no `0 < |J|`; they are the recommended statements.
* `J = ∅` gives two zero states; `|J| = 1` makes the two states equal and the penalty `0`.
* `dE = 0` and empty `W` are allowed: all statements degenerate to `⊤ ≤ ⊤`.

## Main definitions

* `InfoTheory.SmoothMinEntropy.SuperpositionMixture` — the Bouman–Fehr decomposition data.
* `InfoTheory.SmoothMinEntropy.SuperpositionMixture.ofVectors` — its construction from vectors.

## Main statements

* `isFeasible_superposition_of_isFeasible_mixture` — the feasibility scaling `t ↦ |J| · t`.
* `minFeasibleLambda_superposition_le_card_mul_mixture` — `λ*_sup ≤ |J| · λ*_mix`.
* `conditionalMinEntropyReal_superposition_ge_mixture_sub_logb_card` — the real-valued,
  fixed-reference form (with the two positivity side conditions).
* `conditionalMinEntropy_mixture_le_superposition_add_logb_card` — the boundary-correct
  fixed-reference form.
* `conditionalMinEntropyOpt_mixture_le_superposition_add_logb_card` — **Bouman–Fehr Lemma 1**
  in the paper's optimized form `H_min(ρ_WE|E) ≥ H_min(ρ^mix_WE|E) − log₂|J|`.
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {W : Type*} [Fintype W] {dE : ℕ} {ι : Type*}

/-! ## Two missing halves of the min-entropy interface

Both lemmas below are generic facts about `conditionalMinEntropy`/`conditionalMinEntropyOpt`
whose natural home is `QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy`, next to the
definitions; they are stated here because this is where they are first needed. -/

/-- Every feasible reference bounds the optimized conditional min-entropy from below:
`H_min(ρ|σ) ≤ H_min(ρ|E)` whenever `σ` is feasible for `ρ`. -/
lemma conditionalMinEntropy_le_conditionalMinEntropyOpt {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ) :
    conditionalMinEntropy ρ σ ≤ conditionalMinEntropyOpt ρ := by
  unfold conditionalMinEntropyOpt
  exact le_sSup ⟨σ, hfeas, rfl⟩

/-- **A feasible scalar is a min-entropy floor.**  If `t` is feasible for `(ρ, σ)`, then
`H_min(ρ|σ) ≥ −log₂ t`.  Stated in `ENNReal`, so the degenerate `λ* = 0` branch — where the
min-entropy is genuinely infinite — needs no side condition; and `t > 0` is not needed either,
since `isFeasible` already forces `0 ≤ t` and the boundary `t = 0` gives the trivial floor `0`. -/
lemma ofReal_neg_logb_le_conditionalMinEntropy {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ} (hfeas : isFeasible ρ σ t) :
    ENNReal.ofReal (-Real.logb 2 t) ≤ conditionalMinEntropy ρ σ := by
  have hlam_le : minFeasibleLambda ρ σ ≤ t :=
    csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeas
  rw [conditionalMinEntropy]
  by_cases hpos : 0 < minFeasibleLambda ρ σ
  · rw [if_pos hpos]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmono : Real.logb 2 (minFeasibleLambda ρ σ) ≤ Real.logb 2 t :=
      Real.logb_le_logb_of_le one_lt_two hpos hlam_le
    have hval : conditionalMinEntropyReal ρ σ = -Real.logb 2 (minFeasibleLambda ρ σ) := by
      rw [conditionalMinEntropyReal, Real.logb, neg_div]
    rw [hval]
    linarith
  · simp [hpos, show hasFeasibleLambda ρ σ from ⟨t, hfeas⟩]

/-! ## The superposition/mixture pair -/

/-- **A Bouman–Fehr superposition/dephased-mixture pair.**

`vec w i` is the Eve-side component of branch `i` conditioned on the measurement outcome `w`;
`support` is the branch index set `J`.  The two CQ states are the coherent (superposition) and
the dephased (mixture) hybrid states, identified by their blocks:

  `superposition(w) = |∑_{i ∈ J} vec w i⟩⟨∑_{i ∈ J} vec w i|`,
  `mixture(w)       = ∑_{i ∈ J} |vec w i⟩⟨vec w i|`.

The states are fields rather than definitions so that the results below apply to any CQ states
presented in this form; `ofVectors` shows the data is never vacuous. -/
structure SuperpositionMixture (W : Type*) [Fintype W] (dE : ℕ) (ι : Type*) where
  /-- The branch index set `J`. -/
  support : Finset ι
  /-- The Eve-side branch vectors `vᵢ(w)`. -/
  vec : W → ι → Fin dE → ℂ
  /-- The coherent hybrid state. -/
  superposition : CQState W dE
  /-- The dephased hybrid state. -/
  mixture : CQState W dE
  /-- The coherent blocks are the rank-one operators of the branch sums. -/
  superposition_stateMap : ∀ w, (superposition.stateMap w).toOp =
    Matrix.vecMulVec (∑ i ∈ support, vec w i) (star (∑ i ∈ support, vec w i))
  /-- The dephased blocks are the sums of the branch rank-one operators. -/
  mixture_stateMap : ∀ w, (mixture.stateMap w).toOp =
    ∑ i ∈ support, Matrix.vecMulVec (vec w i) (star (vec w i))

namespace SuperpositionMixture

/-- **Construction from branch vectors.**  Both CQ states are built explicitly, so the two
normalization hypotheses are the honest ones: the coherent and the dephased total weights are
each at most one.  Neither bound implies the other in general, and in the Bouman–Fehr
instantiation `vᵢ(w) = αᵢ⟨w|i⟩φⁱ_E` both equal `∑_{i ∈ J} |αᵢ|² = 1`. -/
def ofVectors (J : Finset ι) (v : W → ι → Fin dE → ℂ)
    (hsup : ∑ w : W, ∑ j, Complex.normSq ((∑ i ∈ J, v w i) j) ≤ 1)
    (hmix : ∑ w : W, ∑ i ∈ J, ∑ j, Complex.normSq (v w i j) ≤ 1) :
    SuperpositionMixture W dE ι where
  support := J
  vec := v
  superposition := CQState.ofBlockVectors (fun w => ∑ i ∈ J, v w i) hsup
  mixture := CQState.ofBlockVectorFamily J v hmix
  superposition_stateMap _ := rfl
  mixture_stateMap _ := rfl

variable (D : SuperpositionMixture W dE ι) (σ : SubDensityOp dE)

/-! ## Feasibility scaling (the Löwner step) -/

/-- **Feasibility scaling.**  Every scalar feasible for the dephased mixture against a reference
`σ` rescales by the branch count to a feasible scalar for the superposition against the *same*
`σ`.  This is the blockwise Cauchy–Schwarz step `ρ_WE ⪯ |J| · ρ^mix_WE` of Bouman–Fehr,
Appendix C. -/
theorem isFeasible_superposition_of_isFeasible_mixture {t : ℝ}
    (ht : isFeasible D.mixture σ t) :
    isFeasible D.superposition σ ((D.support.card : ℝ) * t) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) ht.1, fun w => ?_⟩
  rw [D.superposition_stateMap w]
  refine vecMulVec_sum_opLe_smul_of_sum_opLe_smul D.support (D.vec w) σ.toOp ?_
  rw [← D.mixture_stateMap w]
  exact ht.2 w

/-- Feasibility of the dephased mixture transfers to the superposition. -/
theorem hasFeasibleLambda_superposition_of_mixture (hfeas : hasFeasibleLambda D.mixture σ) :
    hasFeasibleLambda D.superposition σ :=
  let ⟨_, ht⟩ := hfeas
  ⟨_, D.isFeasible_superposition_of_isFeasible_mixture σ ht⟩

/-- **The optimum scales by at most the branch count:** `λ*_sup ≤ |J| · λ*_mix`.

This is the sharpest hypothesis-free form of the lemma: no positivity of the optima, no
`0 < |J|`, and no normalization of the branch vectors is used. -/
theorem minFeasibleLambda_superposition_le_card_mul_mixture
    (hfeas : hasFeasibleLambda D.mixture σ) :
    minFeasibleLambda D.superposition σ ≤
      (D.support.card : ℝ) * minFeasibleLambda D.mixture σ :=
  minFeasibleLambda_le_mul_of_isFeasible_scaling D.mixture σ D.superposition σ
    (Nat.cast_nonneg _) hfeas fun ht => D.isFeasible_superposition_of_isFeasible_mixture σ ht

/-! ## The min-entropy penalty -/

/-- **Bouman–Fehr Lemma 1, fixed reference, real-valued form.**

`H_min(ρ^mix|σ) − log₂|J| ≤ H_min(ρ_sup|σ)` for a *fixed* subnormalized reference `σ`.

The three side conditions are exactly the nondegenerate branch of `conditionalMinEntropyReal`
(see the module docstring for why `0 < λ*_sup` cannot be dropped from the real-valued form).
The `ENNReal` statements below need none of them. -/
theorem conditionalMinEntropyReal_superposition_ge_mixture_sub_logb_card
    (hJ : 0 < D.support.card) (hfeas : hasFeasibleLambda D.mixture σ)
    (hmixPos : 0 < minFeasibleLambda D.mixture σ)
    (hsupPos : 0 < minFeasibleLambda D.superposition σ) :
    conditionalMinEntropyReal D.mixture σ - Real.logb 2 (D.support.card : ℝ) ≤
      conditionalMinEntropyReal D.superposition σ := by
  have hc : (0 : ℝ) < (D.support.card : ℝ) := by exact_mod_cast hJ
  have h := conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling D.mixture σ
    D.superposition σ hc hfeas hmixPos hsupPos
    (fun ht => D.isFeasible_superposition_of_isFeasible_mixture σ ht)
  rwa [← Real.log_div_log]

/-- **Bouman–Fehr Lemma 1, fixed reference, boundary-correct form.**

`H_min(ρ^mix|σ) ≤ H_min(ρ_sup|σ) + log₂|J|` in `ENNReal`, where `⊤` is the honest value of the
min-entropy at a vanishing optimum.  The only hypothesis is that `σ` is a feasible reference for
the dephased mixture, which is what makes `λ*_mix` an infimum over a nonempty set. -/
theorem conditionalMinEntropy_mixture_le_superposition_add_logb_card
    (hfeas : hasFeasibleLambda D.mixture σ) :
    conditionalMinEntropy D.mixture σ ≤
      conditionalMinEntropy D.superposition σ +
        ENNReal.ofReal (Real.logb 2 (D.support.card : ℝ)) := by
  have hsupFeas : hasFeasibleLambda D.superposition σ := by
    obtain ⟨t, ht⟩ := hfeas
    exact ⟨_, D.isFeasible_superposition_of_isFeasible_mixture σ ht⟩
  by_cases hsupPos : 0 < minFeasibleLambda D.superposition σ
  · -- A positive superposition optimum forces `0 < |J|` and a positive mixture optimum.
    have hscale := D.minFeasibleLambda_superposition_le_card_mul_mixture σ hfeas
    have hmixNonneg : 0 ≤ minFeasibleLambda D.mixture σ := minFeasibleLambda_nonneg _ _
    have hprodPos : 0 < (D.support.card : ℝ) * minFeasibleLambda D.mixture σ :=
      lt_of_lt_of_le hsupPos hscale
    have hmixPos : 0 < minFeasibleLambda D.mixture σ := by
      rcases hmixNonneg.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hprodPos; exact absurd hprodPos (lt_irrefl 0)
    have hJ : 0 < D.support.card := by
      by_contra hJ0
      rw [Nat.eq_zero_of_not_pos hJ0] at hprodPos
      simp at hprodPos
    have hreal := D.conditionalMinEntropyReal_superposition_ge_mixture_sub_logb_card σ hJ hfeas
      hmixPos hsupPos
    have hlogNonneg : 0 ≤ Real.logb 2 (D.support.card : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast hJ)
    rw [conditionalMinEntropy, conditionalMinEntropy, if_pos hmixPos, if_pos hsupPos]
    calc ENNReal.ofReal (conditionalMinEntropyReal D.mixture σ)
        ≤ ENNReal.ofReal (conditionalMinEntropyReal D.superposition σ +
            Real.logb 2 (D.support.card : ℝ)) := by
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (conditionalMinEntropyReal D.superposition σ) +
            ENNReal.ofReal (Real.logb 2 (D.support.card : ℝ)) := ENNReal.ofReal_add_le
  · have htop : conditionalMinEntropy D.superposition σ = ⊤ := by
      simp [conditionalMinEntropy, hsupPos, hsupFeas]
    rw [htop]
    simp

/-- **Bouman–Fehr Lemma 1** in the paper's form: for the *optimized* conditional min-entropy
`H_min(·|E) = sup_σ H_min(·|σ)`,

  `H_min(ρ^mix_WE | E) ≤ H_min(ρ_WE | E) + log₂ |J|`,

i.e. `H_min(ρ_WE|E) ≥ H_min(ρ^mix_WE|E) − log₂|J|`.

The supremum form follows from the fixed-reference form because the Löwner step holds for one
and the same reference on both sides, and because feasibility transfers from the mixture to the
superposition — so every reference contributing to the left-hand supremum also contributes to the
right-hand one.  No positivity, normalization or nonemptiness hypothesis is needed.

`conditionalMinEntropyOpt` is the supremum over the *feasible* references, which is the reading
of the paper's `sup_{σ_E}` that the library adopts (the unrestricted supremum would be forced to
`⊤` by `σ = 0`; see the `MinEntropy` module docstring). -/
theorem conditionalMinEntropyOpt_mixture_le_superposition_add_logb_card :
    conditionalMinEntropyOpt D.mixture ≤
      conditionalMinEntropyOpt D.superposition +
        ENNReal.ofReal (Real.logb 2 (D.support.card : ℝ)) := by
  unfold conditionalMinEntropyOpt
  apply sSup_le
  rintro h ⟨σ, hfeas, rfl⟩
  refine le_trans (D.conditionalMinEntropy_mixture_le_superposition_add_logb_card σ hfeas) ?_
  exact add_le_add
    (conditionalMinEntropy_le_conditionalMinEntropyOpt D.superposition σ
      (D.hasFeasibleLambda_superposition_of_mixture σ hfeas)) (le_refl _)

end SuperpositionMixture

/-! ## The constructed instance -/

/-- The superposition penalty at the explicitly constructed pair of CQ states: nothing is assumed
to exist.  `ofVectors` builds both states from the branch vectors alone, and the optimized
penalty holds for them. -/
theorem conditionalMinEntropyOpt_ofVectors_le (J : Finset ι) (v : W → ι → Fin dE → ℂ)
    (hsup : ∑ w : W, ∑ j, Complex.normSq ((∑ i ∈ J, v w i) j) ≤ 1)
    (hmix : ∑ w : W, ∑ i ∈ J, ∑ j, Complex.normSq (v w i j) ≤ 1) :
    conditionalMinEntropyOpt (CQState.ofBlockVectorFamily J v hmix) ≤
      conditionalMinEntropyOpt (CQState.ofBlockVectors (fun w => ∑ i ∈ J, v w i) hsup) +
        ENNReal.ofReal (Real.logb 2 (J.card : ℝ)) :=
  (SuperpositionMixture.ofVectors J v hsup hmix
    ).conditionalMinEntropyOpt_mixture_le_superposition_add_logb_card

end InfoTheory.SmoothMinEntropy

end
