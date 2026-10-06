import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy

/-!
# Conditional Min-Entropy under Classical Extension — Renner `lem:classnn`

Adding a classical register to a CQ state only increases the conditional
min-entropy: if `ρ_{XBC}` is classical on `H_X` and `σ_C ∈ N(H_C)`, then
`Hmin(ρ_{XBC} | σ_C) ≥ Hmin(ρ_{BC} | σ_C)`.

This is Renner's thesis lemma `lem:classnn` (Renner 2005, §`sec:smin`,
line 3052), cited in the proof of Renner `thm:Renyisym` (smooth Hmin of
symmetric states), which is the textbook smoothing-radius bound the BB84
finite-size chain needs in place of the Tomamichel-style `extensionRadius`
step.

## Translation to project framework

The project's `CQState X n` (Tomamichel §2.4.4) is exactly Renner's
classical-on-X state, with the X register classical and the BC register
combined into a single quantum dim n. `CQState.quantumMarginal` (the
sum-of-blocks `∑_x ρ.stateMap x`) gives Renner's `ρ_{BC}` as a
`SubDensityOp n`. The reference σ is `SubDensityOp n` throughout (Renner's
`σ_C` lifted to BC via `id_B ⊗ σ_C` is just a particular choice of σ).

## Proof strategy

Following Renner thesis lines 3060–3083 (~15 lines of math):

1. Each block `ρ.stateMap x` is dominated in PSD order by the quantum
   marginal `quantumMarginalOp ρ = ∑_x ρ.stateMap x`. (Each block is PSD,
   so removing positive contributions leaves a positive operator.)
2. Therefore feasibility of t for the marginal (`marginal ≤ t·σ`) implies
   feasibility of t for the full ρ (`each block ≤ t·σ`).
3. Hence the feasibility set for the marginal is a subset of the
   feasibility set for ρ; infimum is monotone in the opposite direction;
   negating the log flips the inequality back.

## Main definitions

- `CQState.fromSubDensityOp`: trivial-classical (`Unit`) CQ state built
  from a `SubDensityOp`, used to wrap the quantum marginal as a CQ state
  for direct comparison.

## Main statements

- `stateMap_opLe_quantumMarginalOp`: each block of a CQ state is dominated
  by its quantum marginal in PSD order.
- `isFeasible_of_quantumMarginalOp_dominated`,
  `isFeasible_of_marginal_isFeasible`,
  `isFeasible_marginal_of_isFeasible_card_smul`: SDP-feasibility transfer
  between a CQ state and the trivial-classical wrapping of its quantum
  marginal.
- `conditionalMinEntropyReal_classical_extension`: Renner `lem:classnn`,
  conditional min-entropy is monotone under extension by a classical
  register.
-/

open Quantum.Operators

namespace InfoTheory.SmoothMinEntropy

/-- Wrap a `SubDensityOp` as a trivial-classical (`Unit`) `CQState`. The
    sole classical block is the original sub-density operator. -/
def CQState.fromSubDensityOp {n : ℕ} (ρ : SubDensityOp n) : CQState Unit n where
  stateMap _ := ρ
  weight_le_one := by
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    exact ρ.trace_le_one

/-- Each block of a CQ state is dominated by the quantum marginal in PSD order.
    `(ρ.stateMap x).toOp ≤_PSD ρ.quantumMarginalOp` for every `x`. -/
lemma stateMap_opLe_quantumMarginalOp
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) :
    opLe (ρ.stateMap x).toOp ρ.quantumMarginalOp := by
  intro v
  unfold CQState.quantumMarginalOp quadraticForm
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.single_le_sum (f := fun y => (star v ⬝ᵥ (ρ.stateMap y).toOp.mulVec v).re)
    (fun y _ => ?_) (Finset.mem_univ x)
  exact (ρ.stateMap y).pos_semidef v

/-- Feasibility transfer (Renner `lem:classnn` at the SDP level): if `t` is
    feasible for the quantum marginal of `ρ` (treated as a trivial-X CQ
    state), then `t` is feasible for `ρ` itself. -/
lemma isFeasible_of_quantumMarginalOp_dominated
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ} (ht : 0 ≤ t)
    (h : opLe ρ.quantumMarginalOp (Complex.ofReal t • σ.toOp)) :
    isFeasible ρ σ t := by
  refine ⟨ht, fun x => ?_⟩
  exact opLe_trans (stateMap_opLe_quantumMarginalOp ρ x) h

/-- **Helper A.** If `t` is feasible for the trivial-classical wrapping of the
    quantum marginal, then `t` is feasible for the original CQ state. -/
lemma isFeasible_of_marginal_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ}
    (h : isFeasible (CQState.fromSubDensityOp ρ.quantumMarginal) σ t) :
    isFeasible ρ σ t := by
  apply isFeasible_of_quantumMarginalOp_dominated ρ σ h.1
  -- `((fromSubDensityOp ρ.quantumMarginal).stateMap default).toOp` is definitionally
  -- equal to `ρ.quantumMarginal.toOp = ρ.quantumMarginalOp`.
  exact h.2 ()

/-- **Helper B.** Feasibility scales with the size of the classical register: if
    `t` is feasible for the original CQ state, then `|X| * t` is feasible for the
    trivial-classical wrapping of the quantum marginal. -/
lemma isFeasible_marginal_of_isFeasible_card_smul
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ}
    (h : isFeasible ρ σ t) :
    isFeasible (CQState.fromSubDensityOp ρ.quantumMarginal) σ (Fintype.card X * t) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) h.1, ?_⟩
  intro u v
  -- LHS quadratic form is over `ρ.quantumMarginalOp = ∑ x, (ρ.stateMap x).toOp`.
  change (quadraticForm ρ.quantumMarginalOp v).re ≤
    (quadraticForm (Complex.ofReal (Fintype.card X * t) • σ.toOp) v).re
  -- Unfold the RHS to a real coefficient times the quadratic form of σ.
  rw [quadraticForm_ofReal_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- Unfold the LHS as a sum of per-block quadratic forms.
  unfold CQState.quantumMarginalOp quadraticForm
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  -- Per-block bound from the hypothesis on each `ρ.stateMap x`.
  have hbound : ∀ x : X,
      (star v ⬝ᵥ (ρ.stateMap x).toOp.mulVec v).re ≤
        t * (quadraticForm σ.toOp v).re := by
    intro x
    have hx := h.2 x v
    rw [quadraticForm_ofReal_smul, Complex.mul_re] at hx
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx
    exact hx
  calc ∑ x : X, (star v ⬝ᵥ (ρ.stateMap x).toOp.mulVec v).re
      ≤ ∑ _x : X, t * (quadraticForm σ.toOp v).re :=
        Finset.sum_le_sum (fun x _ => hbound x)
    _ = (Fintype.card X : ℝ) * t * (quadraticForm σ.toOp v).re := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **Renner `lem:classnn` (textbook form).** Conditional min-entropy is
    monotone under extension by a classical register:
    `Hmin(ρ_{XBC} | σ) ≥ Hmin(ρ_{BC} | σ)`.

    In project terms: `conditionalMinEntropyReal` of the full CQ state is at
    least the same quantity for the trivial-classical wrapping of its
    quantum marginal. -/
theorem conditionalMinEntropyReal_classical_extension
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    conditionalMinEntropyReal (CQState.fromSubDensityOp ρ.quantumMarginal) σ ≤
      conditionalMinEntropyReal ρ σ := by
  set ρ' : CQState Unit n := CQState.fromSubDensityOp ρ.quantumMarginal with hρ'
  set lFull : ℝ := minFeasibleLambda ρ σ with hlFull
  set lMarg : ℝ := minFeasibleLambda ρ' σ with hlMarg
  have hlFull_nn : 0 ≤ lFull := minFeasibleLambda_nonneg ρ σ
  have hlMarg_nn : 0 ≤ lMarg := minFeasibleLambda_nonneg ρ' σ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Subset relation from Helper A: feasible(ρ') ⊆ feasible(ρ).
  have hsub : Set.ofPred (isFeasible ρ' σ) ⊆ Set.ofPred (isFeasible ρ σ) :=
    fun _ ht => isFeasible_of_marginal_isFeasible ρ σ ht
  -- Helper B as a set membership map.
  have hmap : ∀ t ∈ Set.ofPred (isFeasible ρ σ),
      (Fintype.card X : ℝ) * t ∈ Set.ofPred (isFeasible ρ' σ) :=
    fun t ht => isFeasible_marginal_of_isFeasible_card_smul ρ σ ht
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card X : ℝ) := Nat.cast_nonneg _
  by_cases hne : (Set.ofPred (isFeasible ρ' σ)).Nonempty
  · -- ρ' has feasible witnesses, so ρ does too, and `lFull ≤ lMarg`.
    have hle : lFull ≤ lMarg :=
      csInf_le_csInf (minFeasibleLambda_bddBelow ρ σ) hne hsub
    by_cases hpos : 0 < lFull
    · -- Standard log-monotone case.
      have hlog_le : Real.log lFull ≤ Real.log lMarg :=
        Real.log_le_log hpos hle
      unfold conditionalMinEntropyReal
      exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le
    · -- `lFull = 0`. Use Helper B to force `lMarg = 0` as well.
      push Not at hpos
      have hzero : lFull = 0 := le_antisymm hpos hlFull_nn
      obtain ⟨t', ht'⟩ := hne
      have ht_full : (Set.ofPred (isFeasible ρ σ)).Nonempty := ⟨t', hsub ht'⟩
      -- Show `lMarg ≤ 0` via an ε-argument.
      have h_marg_le : lMarg ≤ 0 := by
        rcases eq_or_lt_of_le hcard_nn with hc0 | hc_pos
        · -- |X| = 0 case: pick any t ∈ feasible(ρ); |X|*t = 0 ∈ feasible(ρ').
          obtain ⟨t₀, ht₀⟩ := ht_full
          have h0 : (Fintype.card X : ℝ) * t₀ ∈ Set.ofPred (isFeasible ρ' σ) := hmap t₀ ht₀
          rw [← hc0, zero_mul] at h0
          exact csInf_le (minFeasibleLambda_bddBelow ρ' σ) h0
        · -- |X| > 0 case: ε-argument.
          refine le_of_forall_pos_le_add (fun δ hδ => ?_)
          have hε_pos : 0 < δ / (Fintype.card X : ℝ) := div_pos hδ hc_pos
          -- From lFull = 0 < δ/|X|, find a feasible t < δ/|X|.
          have hlt : lFull < δ / (Fintype.card X : ℝ) := by rw [hzero]; exact hε_pos
          obtain ⟨t, ht, htlt⟩ :=
            exists_lt_of_csInf_lt ht_full hlt
          have hmem : (Fintype.card X : ℝ) * t ∈ Set.ofPred (isFeasible ρ' σ) := hmap t ht
          have hbd : lMarg ≤ (Fintype.card X : ℝ) * t :=
            csInf_le (minFeasibleLambda_bddBelow ρ' σ) hmem
          have hcard_eq : (Fintype.card X : ℝ) * (δ / (Fintype.card X : ℝ)) = δ := by
            field_simp
          have hbd2 : (Fintype.card X : ℝ) * t < δ := by
            have := mul_lt_mul_of_pos_left htlt hc_pos
            rw [hcard_eq] at this
            exact this
          linarith
      have hzero_marg : lMarg = 0 := le_antisymm h_marg_le hlMarg_nn
      -- Both H values are -log 0 / log 2 = 0.
      unfold conditionalMinEntropyReal
      rw [show minFeasibleLambda ρ' σ = 0 from hzero_marg]
      rw [show minFeasibleLambda ρ σ = 0 from hzero]
  · -- feasible(ρ') = ∅. By Helper B, feasible(ρ) = ∅ too. Both H = 0.
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : Set.ofPred (isFeasible ρ σ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro t ht
      have hmem : (Fintype.card X : ℝ) * t ∈ Set.ofPred (isFeasible ρ' σ) := hmap t ht
      rw [hne] at hmem
      exact hmem
    have hzero_full : lFull = 0 := by
      change minFeasibleLambda ρ σ = 0
      unfold minFeasibleLambda
      rw [hempty, Real.sInf_empty]
    have hzero_marg : lMarg = 0 := by
      change minFeasibleLambda ρ' σ = 0
      unfold minFeasibleLambda
      rw [hne, Real.sInf_empty]
    unfold conditionalMinEntropyReal
    rw [show minFeasibleLambda ρ' σ = 0 from hzero_marg]
    rw [show minFeasibleLambda ρ σ = 0 from hzero_full]

end InfoTheory.SmoothMinEntropy
