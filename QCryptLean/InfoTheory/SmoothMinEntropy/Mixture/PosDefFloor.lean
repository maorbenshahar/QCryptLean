import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth

/-!
# Signed smooth min-entropy — pointwise floor against a positive-definite reference

A positive-definite reference operator makes `smoothMinEntropyReal`
bounded below by an explicit, state-independent constant (Tomamichel 2016, §6.1
style crude floor: `H_min(X|A)_{ρ|σ} ≥ -log₂ C` for any scalar `C` with
`C · σ ≥ 1`, uniformly feasible over all CQ states by
`exists_uniform_isFeasible_of_posDef`).

No normalization hypothesis on the CQ state is required: the bound is clamped
at `0` via `min 0 (·)`, which absorbs both junk conventions of the underlying
real-valued definitions:
* `minFeasibleLambda ρ σ = 0` (degenerate/zero state) makes
  `conditionalMinEntropyReal` unfold to `-Real.log 0 / Real.log 2 = 0`;
* a non-`BddAbove` smoothing set makes `smoothMinEntropyReal` collapse to
  `sSup = 0` by `Real.sSup_of_not_bddAbove`.
Both junk branches return exactly `0`, so a floor `≤ 0` survives them.

## Main statements
- `smoothMinEntropyReal_ge_of_posDef_ref_aux`: the explicit floor
  `min 0 (-Real.log C / Real.log 2) ≤ smoothMinEntropyReal ε ρ σref` from a
  uniform feasibility witness `C`.
- `smoothMinEntropyReal_ge_of_posDef_ref`: existence form for a positive-definite
  reference (the witness `k` satisfies `k ≤ 0`, so it is junk-proof).
- `bddBelow_smoothMinEntropyReal_family`: any family of CQ states has smooth
  min-entropies bounded below against a positive-definite reference — the
  shape `ciInf_le` consumes.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A uniform feasible coefficient `C` gives the signed smooth floor `min 0 (-log C / log 2)`
for every CQ state and nonnegative radius, including totalized zero values. -/
theorem smoothMinEntropyReal_ge_of_posDef_ref_aux
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (σref : SubDensityOp n) {C : ℝ} (hC : ∀ ρ' : CQState X n, isFeasible ρ' σref C)
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X n) :
    min 0 (-Real.log C / Real.log 2) ≤ smoothMinEntropyReal ε ρ σref := by
  have hk_nonpos : min 0 (-Real.log C / Real.log 2) ≤ 0 := min_le_left _ _
  -- Pointwise: every CQ state has real min-entropy at least the clamped floor.
  have hpt : ∀ ρ' : CQState X n,
      min 0 (-Real.log C / Real.log 2) ≤ conditionalMinEntropyReal ρ' σref := by
    intro ρ'
    have hlam_le : minFeasibleLambda ρ' σref ≤ C :=
      minFeasibleLambda_le_of_isFeasible ρ' σref (hC ρ')
    have hlam_nn : 0 ≤ minFeasibleLambda ρ' σref := minFeasibleLambda_nonneg ρ' σref
    unfold conditionalMinEntropyReal
    by_cases hpos : 0 < minFeasibleLambda ρ' σref
    · -- Honest branch: `log` is monotone on the positive optimum.
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog_le : Real.log (minFeasibleLambda ρ' σref) ≤ Real.log C :=
        Real.log_le_log hpos hlam_le
      exact le_trans (min_le_right _ _)
        (div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le)
    · -- Junk branch: zero optimum, `Real.log_zero` collapses the entropy to `0`.
      push Not at hpos
      have hzero : minFeasibleLambda ρ' σref = 0 := le_antisymm hpos hlam_nn
      rw [hzero, Real.log_zero, neg_zero, zero_div]
      exact hk_nonpos
  by_cases hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σref))
  · -- Honest branch: the center state witnesses membership in the smoothing set.
    have hmem : conditionalMinEntropyReal ρ σref ∈ setOf (isInSmoothedSetReal ε ρ σref) :=
      ⟨ρ, rfl, by rw [CQState.purifiedDistance_self_zero]; exact hε⟩
    exact le_trans (hpt ρ) (le_csSup hbdd hmem)
  · -- Junk branch: the `sSup` of a non-`BddAbove` set is `0`.
    unfold smoothMinEntropyReal
    rw [Real.sSup_of_not_bddAbove hbdd]
    exact hk_nonpos

/-- Against a positive-definite reference, every CQ state has a finite nonpositive lower bound
on its signed smooth min-entropy at a nonnegative radius. -/
theorem smoothMinEntropyReal_ge_of_posDef_ref
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X n) (σref : SubDensityOp n)
    (hσ : σref.toOp.PosDef) :
    ∃ k : ℝ, k ≤ 0 ∧ k ≤ smoothMinEntropyReal ε ρ σref := by
  obtain ⟨C, -, hC⟩ := exists_uniform_isFeasible_of_posDef (X := X) σref hσ
  exact ⟨min 0 (-Real.log C / Real.log 2), min_le_left _ _,
    smoothMinEntropyReal_ge_of_posDef_ref_aux σref hC ε hε ρ⟩

/-- Every family of CQ states has signed smooth min-entropies bounded below against a fixed
positive-definite reference at a nonnegative radius. -/
theorem bddBelow_smoothMinEntropyReal_family
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {ι : Type*} (F : ι → CQState X n) {σref : SubDensityOp n}
    (hσ : σref.toOp.PosDef) (ε : ℝ) (hε : 0 ≤ ε) :
    BddBelow (Set.range fun i : ι => smoothMinEntropyReal ε (F i) σref) := by
  obtain ⟨C, -, hC⟩ := exists_uniform_isFeasible_of_posDef (X := X) σref hσ
  refine ⟨min 0 (-Real.log C / Real.log 2), ?_⟩
  rintro y ⟨i, rfl⟩
  exact smoothMinEntropyReal_ge_of_posDef_ref_aux σref hC ε hε (F i)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
