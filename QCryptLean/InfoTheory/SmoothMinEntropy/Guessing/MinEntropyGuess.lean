import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.PGMReference

/-!
# POVM Guessing Probability Equivalence — weak and strong duality, PGM reference, edge cases

Proof of the strong-duality identity

    `conditionalMinEntropyOptReal ρ = -log₂ (povmGuessingProb ρ)`

for CQ states (Tomamichel 2016, eq. 6.30).  The argument splits into:

* **Step A** — the weak-duality direction
  `conditionalMinEntropyOptReal ρ ≤ -log₂ (povmGuessingProb ρ)`,
  proved as `conditionalMinEntropyOptReal_le_neg_log_povmGuessingProb`.

* **Step B** — the strong-duality direction
  `-log₂ (povmGuessingProb ρ) ≤ conditionalMinEntropyOptReal ρ`,
  obtained by exhibiting the Pretty-Good-Measurement reference operator `σ*`
  (lemma `conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos`).
  The key PGM feasibility step `pgm_sigma_feasible` is reduced here to the
  Koenig–Renner–Schaffner optimality lemma
  in `PGMReference.lean`, which remains the sole `sorry` in this flow.

The companion edge-case lemmas `stateMap_eq_zero_of_povmGuessingProb_eq_zero`
and `minFeasibleLambda_eq_zero_of_stateMap_zero` handle the degenerate cases
(`povmGuessingProb ρ = 0` or `IsEmpty X`) uniformly, and the main theorem
`conditionalMinEntropyReal_cq_guess_eq` combines the three cases.

## Main statements

- `conditionalMinEntropyOptReal_le_neg_log_povmGuessingProb`: weak-duality
  direction (Step A).
- `conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos`:
  strong-duality direction for the positive-probability branch (Step B).
- `pgm_sigma_feasible`: PGM-reference feasibility witness (delegates to the
  KRS lemma in `PGMReference.lean`).
- `conditionalMinEntropyReal_cq_guess_eq`: the full equivalence
  `H_min(X|A)_ρ = -log₂(Pg(X|A)_ρ)`.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Edge-case helpers -/

/-- If the outcome set `X` is empty but the underlying Hilbert space is
nontrivial (`NeZero n`), the sSup-set defining `povmGuessingProb` is empty
(no family `M` can sum to `1 ≠ 0` in `Op n`), so `povmGuessingProb ρ = 0`. -/
lemma povmGuessingProb_eq_zero_of_isEmpty
    {X : Type*} [Fintype X] [IsEmpty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) : povmGuessingProb ρ = 0 := by
  have h_one_ne_zero : (1 : Op n) ≠ 0 := by
    intro h
    have h00 : ((1 : Op n) (0 : Fin n) (0 : Fin n)) =
        ((0 : Op n) (0 : Fin n) (0 : Fin n)) := by rw [h]
    simp at h00
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      p = ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re}
  have h_empty : S = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨M, _, hM_sum, _⟩
    rw [Fintype.sum_empty] at hM_sum
    exact h_one_ne_zero hM_sum.symm
  change sSup S = 0
  rw [h_empty, Real.sSup_empty]

/-- If `minFeasibleLambda ρ σ = 0` for every reference σ, then the optimized
real conditional min-entropy of ρ vanishes. -/
lemma conditionalMinEntropyOptReal_eq_zero_of_minFeasibleLambda_eq_zero
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n)
    (hlam : ∀ σ : SubDensityOp n, minFeasibleLambda ρ σ = 0) :
    conditionalMinEntropyOptReal ρ = 0 := by
  have hcond : ∀ σ : SubDensityOp n, conditionalMinEntropyReal ρ σ = 0 := by
    intro σ
    unfold conditionalMinEntropyReal
    rw [hlam σ, Real.log_zero, neg_zero, zero_div]
  unfold conditionalMinEntropyOptReal
  have hset : {h | ∃ σ : SubDensityOp n, h = conditionalMinEntropyReal ρ σ} =
      ({0} : Set ℝ) := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨σ, rfl⟩; exact hcond σ
    · rintro rfl; exact ⟨(0 : SubDensityOp n), (hcond 0).symm⟩
  rw [hset]
  exact csSup_singleton 0

/-- If the outcome set `X` is empty, every `t ≥ 0` is feasible for every
reference `σ` (the dominance condition is vacuous), so
`minFeasibleLambda ρ σ = 0` for all `σ` and the optimized real conditional
min-entropy is `sSup {0} = 0`. -/
lemma conditionalMinEntropyOptReal_eq_zero_of_isEmpty
    {X : Type*} [Fintype X] [IsEmpty X] {n : ℕ}
    (ρ : CQState X n) : conditionalMinEntropyOptReal ρ = 0 := by
  refine conditionalMinEntropyOptReal_eq_zero_of_minFeasibleLambda_eq_zero ρ ?_
  intro σ
  apply le_antisymm _ (minFeasibleLambda_nonneg ρ σ)
  have hfeas : isFeasible ρ σ 0 := ⟨le_refl 0, fun x => isEmptyElim x⟩
  unfold minFeasibleLambda
  exact csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeas

/-- If the POVM guessing probability vanishes (with a nonempty outcome set),
every classical component of the CQ state is the zero operator.

The proof plugs the one-hot POVM at each `x` into the sSup bound, showing
`(ρ.stateMap x).toOp.trace.re ≤ povmGuessingProb ρ = 0`; PSD then forces
`(ρ.stateMap x).toOp = 0` via `Matrix.PosSemidef.trace_eq_zero_iff`. -/
lemma stateMap_eq_zero_of_povmGuessingProb_eq_zero
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (h : povmGuessingProb ρ = 0) (x : X) :
    (ρ.stateMap x).toOp = 0 := by
  classical
  -- Introduce the sSup-set S defining povmGuessingProb.
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ y : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M y) v).re) ∧
      (∑ y : X, M y = 1) ∧
      p = ∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re}
  -- The one-hot POVM at `x` yields `(ρ.stateMap x).toOp.trace.re ∈ S`.
  have hmem : ((ρ.stateMap x).toOp).trace.re ∈ S :=
    ⟨oneHotPovm x, oneHotPovm_quadraticForm_re_nonneg x,
      oneHotPovm_sum x, (oneHotPovm_trace_sum ρ x).symm⟩
  have hBdd : BddAbove S := by
    refine ⟨1, fun p hp => ?_⟩
    obtain ⟨M, hM_pos, hM_sum, rfl⟩ := hp
    exact povmLike_traceSum_le_one ρ M hM_pos hM_sum
  have h_le : ((ρ.stateMap x).toOp).trace.re ≤ povmGuessingProb ρ := le_csSup hBdd hmem
  rw [h] at h_le
  have h_nn : 0 ≤ ((ρ.stateMap x).toOp).trace.re := (ρ.stateMap x).trace_nonneg
  have h_re_zero : ((ρ.stateMap x).toOp).trace.re = 0 := le_antisymm h_le h_nn
  have hpsd : Matrix.PosSemidef (ρ.stateMap x).toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have h_im : ((ρ.stateMap x).toOp).trace.im = 0 :=
    (hpsd.trace_nonneg.2).symm
  have h_trace_eq : ((ρ.stateMap x).toOp).trace = 0 := by
    apply Complex.ext
    · simpa using h_re_zero
    · simpa using h_im
  exact hpsd.trace_eq_zero_iff.mp h_trace_eq

/-- A positive POVM guessing probability forces the outcome set to be
nonempty: if `X` were empty, `povmGuessingProb ρ` would be `0`. -/
lemma nonempty_of_povmGuessingProb_pos
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    {ρ : CQState X n} (hp : 0 < povmGuessingProb ρ) : Nonempty X := by
  rw [← not_isEmpty_iff]
  intro hne
  have h0 : povmGuessingProb ρ = 0 := povmGuessingProb_eq_zero_of_isEmpty ρ
  linarith

/-- If every classical component of a CQ state vanishes, the minimum feasible
λ is `0` for every reference operator σ: `t = 0` is then trivially feasible. -/
lemma minFeasibleLambda_eq_zero_of_stateMap_zero
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (h : ∀ x : X, (ρ.stateMap x).toOp = 0)
    (σ : SubDensityOp n) : minFeasibleLambda ρ σ = 0 := by
  apply le_antisymm _ (minFeasibleLambda_nonneg ρ σ)
  have hfeas : isFeasible ρ σ 0 := by
    refine ⟨le_refl 0, fun x v => ?_⟩
    rw [h x]
    have hlhs : (quadraticForm (0 : Op n) v).re = 0 := by
      unfold quadraticForm; simp [Matrix.zero_mulVec]
    have hrhs : (quadraticForm ((Complex.ofReal 0 : ℂ) • σ.toOp) v).re = 0 := by
      unfold quadraticForm
      simp [Complex.ofReal_zero, zero_smul, Matrix.zero_mulVec]
    rw [hlhs, hrhs]
  unfold minFeasibleLambda
  exact csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeas

/-! ## Step A — weak-duality direction -/

/-- Per-σ weak-duality inequality: for every reference σ,
    `conditionalMinEntropyReal ρ σ ≤ -log₂ (povmGuessingProb ρ)`.

Proof: split on `povmGuessingProb ρ = 0` (edge case handled via
`stateMap_eq_zero_of_povmGuessingProb_eq_zero` and
`minFeasibleLambda_eq_zero_of_stateMap_zero`), and otherwise on whether the
feasible set is nonempty. When `povmGuessingProb ρ > 0` and the feasible
set is nonempty, weak duality gives `povmGuessingProb ρ ≤ minFeasibleLambda`,
so `Real.log_le_log` and positivity of `Real.log 2` close it. When empty or
genuinely `0`, the `Real.log 0 = 0` sentinel collapses the LHS to `0`, which
is bounded by the nonneg RHS. -/
lemma conditionalMinEntropyReal_le_neg_log_povmGuessingProb
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    conditionalMinEntropyReal ρ σ ≤ -Real.log (povmGuessingProb ρ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  by_cases hp : povmGuessingProb ρ = 0
  · have hsm : ∀ x : X, (ρ.stateMap x).toOp = 0 :=
      fun x => stateMap_eq_zero_of_povmGuessingProb_eq_zero ρ hp x
    have hlam : minFeasibleLambda ρ σ = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρ hsm σ
    rw [hlam, hp, Real.log_zero, neg_zero, zero_div]
  · have hp_pos : 0 < povmGuessingProb ρ :=
      lt_of_le_of_ne (povmGuessingProb_nonneg ρ) (Ne.symm hp)
    by_cases hfeas : hasFeasibleLambda ρ σ
    · have hlam_ge_p : povmGuessingProb ρ ≤ minFeasibleLambda ρ σ :=
        povmGuessingProb_le_minFeasibleLambda ρ σ hfeas
      have hlog_le : Real.log (povmGuessingProb ρ) ≤ Real.log (minFeasibleLambda ρ σ) :=
        Real.log_le_log hp_pos hlam_ge_p
      exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le
    · have hempty : Set.ofPred (isFeasible ρ σ) = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨t, ht⟩
        exact hfeas ⟨t, ht⟩
      have hlam : minFeasibleLambda ρ σ = 0 := by
        unfold minFeasibleLambda
        rw [hempty]
        exact Real.sInf_empty
      rw [hlam, Real.log_zero, neg_zero, zero_div]
      apply div_nonneg _ hlog2.le
      rw [neg_nonneg]
      exact Real.log_nonpos (le_of_lt hp_pos) (povmGuessingProb_le_one ρ)

/-- The sSup-set defining `conditionalMinEntropyOptReal` is bounded above by
`-log₂ (povmGuessingProb ρ)`. Immediate corollary of
`conditionalMinEntropyReal_le_neg_log_povmGuessingProb`. -/
lemma conditionalMinEntropyOptReal_bddAbove
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) :
    BddAbove {h | ∃ σ : SubDensityOp n, h = conditionalMinEntropyReal ρ σ} := by
  rcases isEmpty_or_nonempty X with hX | hX
  · -- Empty case: every feasible set trivially contains 0, so
    -- `minFeasibleLambda ρ σ = 0` for every σ, hence every element of the set is 0.
    refine ⟨0, ?_⟩
    rintro _ ⟨σ, rfl⟩
    have hfeas : isFeasible ρ σ 0 := ⟨le_refl 0, fun x => isEmptyElim x⟩
    have hlam : minFeasibleLambda ρ σ = 0 := by
      apply le_antisymm _ (minFeasibleLambda_nonneg ρ σ)
      exact csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeas
    unfold conditionalMinEntropyReal
    rw [hlam, Real.log_zero, neg_zero, zero_div]
  · refine ⟨-Real.log (povmGuessingProb ρ) / Real.log 2, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact conditionalMinEntropyReal_le_neg_log_povmGuessingProb ρ σ

/-- **Step A (weak-duality direction)**: for any CQ state with a nonempty
outcome register, the optimized real conditional min-entropy is bounded above
by `-log₂ (povmGuessingProb ρ)`. Immediate from the per-σ bound. -/
lemma conditionalMinEntropyOptReal_le_neg_log_povmGuessingProb
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) :
    conditionalMinEntropyOptReal ρ ≤ -Real.log (povmGuessingProb ρ) / Real.log 2 := by
  unfold conditionalMinEntropyOptReal
  apply csSup_le
  · exact ⟨_, (0 : SubDensityOp n), rfl⟩
  rintro _ ⟨σ, rfl⟩
  exact conditionalMinEntropyReal_le_neg_log_povmGuessingProb ρ σ

/-! ## Step B — strong-duality direction

These lemmas implement the PGM (Pretty-Good-Measurement) construction and
its SDP feasibility analysis, following Tomamichel 2016, §6.2 (eq. 6.30)
and Koenig–Renner–Schaffner 2009.  The optimality hypothesis
`p = povmGuessingProb ρ` in `pgm_sigma_feasible` is essential: without it
the conclusion is false (e.g. for `n = 2`, `X = {1,2}`,
`ρ_A(1) = |0⟩⟨0|/2`, `ρ_A(2) = |1⟩⟨1|/2`, and the uniform POVM
`M_1 = M_2 = I/2`, we have `p = 1/2` but any σ dominating both
`|0⟩⟨0|` and `|1⟩⟨1|` must satisfy `Tr σ ≥ 2 > 1`). -/

/-- For any `ε > 0`, the sSup definition of `povmGuessingProb` furnishes a
valid POVM whose expected trace-sum is within `ε` of `povmGuessingProb ρ`.

This is the standard "approximate sSup witness" extraction applied to the
`povmGuessingProb` set (see its definition in `MinEntropy.lean`). -/
lemma exists_epsilon_optimal_povm
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      povmGuessingProb ρ - ε <
        ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ y : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M y) v).re) ∧
      (∑ y : X, M y = 1) ∧
      p = ∑ y : X, ((M y) * (ρ.stateMap y).toOp).trace.re}
  have hS_ne : S.Nonempty :=
    ⟨_, oneHotPovm x₀, oneHotPovm_quadraticForm_re_nonneg x₀,
      oneHotPovm_sum x₀, rfl⟩
  have h_lt : povmGuessingProb ρ - ε < sSup S := by
    change povmGuessingProb ρ - ε < povmGuessingProb ρ
    linarith
  obtain ⟨p, hp_mem, hp_lt⟩ := exists_lt_of_lt_csSup hS_ne h_lt
  obtain ⟨M, hM_pos, hM_sum, hp_eq⟩ := hp_mem
  refine ⟨M, hM_pos, hM_sum, ?_⟩
  rw [← hp_eq]
  exact hp_lt

/-- **Finite-dimensional attainment of the POVM guessing supremum.**

For a CQ state `ρ` with nonempty outcome register, there exists a POVM
`M : X → Op n` whose expected trace-sum exactly equals `povmGuessingProb ρ`
(the supremum defining `povmGuessingProb` is attained).  Wraps
`exists_optimal_povm_hermitian` from `PovmCompactness.lean`, which proves
attainment via compactness of the POVM feasible set and continuity of the
trace-sum objective. -/
lemma exists_optimal_povm
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) :
    ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      povmGuessingProb ρ =
        ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re := by
  obtain ⟨M, ⟨hM_prop, hM_sum⟩, hM_eq⟩ := exists_optimal_povm_hermitian ρ
  refine ⟨M, fun x v => ?_, hM_sum, ?_⟩
  · exact posSemidef_re_quadraticForm_nonneg (hM_prop x) v
  · simpa [povmObjective] using hM_eq

/-- **PGM feasibility** (strong-duality direction).  If `M : X → Op n` is an
*optimal* POVM for `ρ` — one whose expected trace-sum attains
`povmGuessingProb ρ` — with positive value `p`, then the
Pretty-Good-Measurement reference
  `σ* := (1/p) • ∑ x, (M_x)^{1/2} · ρ_A(x) · (M_x)^{1/2}`
is sub-normalized and `p` is feasible for `(ρ, σ*)`, i.e.
`isFeasible ρ σ* p`.

The optimality hypothesis `p = povmGuessingProb ρ` is essential: without it
the conclusion is *false* (see the section note above).  The concrete
construction is delegated to `pgm_sigma_feasible_of_hermitian_povm` in
`PGMReference.lean`. -/
lemma pgm_sigma_feasible
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n)
    (M : X → Op n)
    (_hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (_hM_sum : ∑ x : X, M x = 1)
    (_hp_pos : 0 < povmGuessingProb ρ)
    (_hp_eq : ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    ∃ σ : SubDensityOp n, isFeasible ρ σ (povmGuessingProb ρ) := by
  classical
  -- The given `M` is not assumed Hermitian, so we discard it and rebuild σ
  -- from the Hermitian optimal POVM produced by `exists_optimal_povm_hermitian`.
  have : Nonempty X := nonempty_of_povmGuessingProb_pos _hp_pos
  obtain ⟨N, ⟨hN_psd, hN_sum⟩, hN_eq⟩ := exists_optimal_povm_hermitian ρ
  have hN_eq' :
      ∑ x : X, ((N x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ := by
    simpa [povmObjective] using hN_eq.symm
  exact pgm_sigma_feasible_of_hermitian_povm ρ N hN_psd hN_sum _hp_pos hN_eq'

/-- **Step B (strong-duality direction, positive case)**: for a CQ state
with `povmGuessingProb ρ > 0`, the optimized real conditional min-entropy
is bounded below by `-log₂ (povmGuessingProb ρ)`.

Proof: `exists_optimal_povm` produces a POVM `M` with
`p := ∑ Tr(M_x ρ(x)).re = povmGuessingProb ρ > 0`.  `pgm_sigma_feasible`
then produces σ with `isFeasible ρ σ p`, so `minFeasibleLambda ρ σ ≤ p = Pg`.
Combined with the weak-duality inequality `Pg ≤ minFeasibleLambda ρ σ`
(`povmGuessingProb_le_minFeasibleLambda`) we get
`minFeasibleLambda ρ σ = Pg`, so `conditionalMinEntropyReal ρ σ` equals
the target value exactly and the sSup is ≥ the target. -/
lemma conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hp : 0 < povmGuessingProb ρ) :
    -Real.log (povmGuessingProb ρ) / Real.log 2 ≤ conditionalMinEntropyOptReal ρ := by
  classical
  have : Nonempty X := nonempty_of_povmGuessingProb_pos hp
  obtain ⟨M, hM_pos, hM_sum, hp_eq_Pg⟩ := exists_optimal_povm ρ
  obtain ⟨σ, hfeas⟩ :=
    pgm_sigma_feasible ρ M hM_pos hM_sum hp hp_eq_Pg.symm
  have hlam_le : minFeasibleLambda ρ σ ≤ povmGuessingProb ρ :=
    csInf_le (minFeasibleLambda_bddBelow ρ σ) hfeas
  have hhf : hasFeasibleLambda ρ σ := ⟨povmGuessingProb ρ, hfeas⟩
  have hlam_ge : povmGuessingProb ρ ≤ minFeasibleLambda ρ σ :=
    povmGuessingProb_le_minFeasibleLambda ρ σ hhf
  have hlam_eq : minFeasibleLambda ρ σ = povmGuessingProb ρ :=
    le_antisymm hlam_le hlam_ge
  have hcond_eq : conditionalMinEntropyReal ρ σ =
      -Real.log (povmGuessingProb ρ) / Real.log 2 := by
    unfold conditionalMinEntropyReal
    rw [hlam_eq]
  unfold conditionalMinEntropyOptReal
  rw [← hcond_eq]
  exact le_csSup (conditionalMinEntropyOptReal_bddAbove ρ) ⟨σ, rfl⟩

/-- A normalized CQ state on a nonempty classical register has strictly
positive POVM guessing probability. -/
lemma povmGuessingProb_pos_of_normalizedCQState
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : NormalizedCQState X n) :
    0 < povmGuessingProb (ρ : CQState X n) := by
  classical
  have hsum_pos : 0 < ∑ x : X, ((ρ : CQState X n).stateMap x).trace := by
    have hsum_eq : (∑ x : X, ((ρ : CQState X n).stateMap x).trace) = 1 := by
      simpa using ρ.weight_eq_one
    rw [hsum_eq]
    norm_num
  have hnonneg :
      ∀ x ∈ (Finset.univ : Finset X), 0 ≤ ((ρ : CQState X n).stateMap x).trace := by
    intro x _
    exact ((ρ : CQState X n).stateMap x).trace_nonneg
  obtain ⟨x₀, _, hx₀_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum_pos
  set S : Set ℝ := {p | ∃ (M : X → Op n),
      (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧
      (∑ x : X, M x = 1) ∧
      p = ∑ x : X, ((M x) * (((ρ : CQState X n).stateMap x).toOp)).trace.re}
  have hmem : ((((ρ : CQState X n).stateMap x₀).toOp).trace.re) ∈ S :=
    ⟨oneHotPovm x₀, oneHotPovm_quadraticForm_re_nonneg x₀,
      oneHotPovm_sum x₀, (oneHotPovm_trace_sum (ρ : CQState X n) x₀).symm⟩
  have hBdd : BddAbove S := by
    refine ⟨1, fun p hp => ?_⟩
    obtain ⟨M, hM_pos, hM_sum, rfl⟩ := hp
    exact povmLike_traceSum_le_one (ρ : CQState X n) M hM_pos hM_sum
  have hle :
      (((ρ : CQState X n).stateMap x₀).toOp).trace.re ≤
        povmGuessingProb (ρ : CQState X n) :=
    le_csSup hBdd hmem
  exact lt_of_lt_of_le (by simpa [SubDensityOp.trace] using hx₀_pos) hle

/-- Convert an operational guessing-probability upper bound into an optimized
conditional min-entropy lower bound.  The exponent is in bits: a bound
`Pg ≤ exp (-k * log 2)` yields `k ≤ Hmin`. -/
lemma conditionalMinEntropyOptReal_ge_of_povmGuessingProb_le_exp_neg_mul_log_two
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (k : ℝ)
    (hp : 0 < povmGuessingProb ρ)
    (hPg : povmGuessingProb ρ ≤ Real.exp (-k * Real.log 2)) :
    k ≤ conditionalMinEntropyOptReal ρ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log (povmGuessingProb ρ) ≤ -k * Real.log 2 :=
    (Real.log_le_iff_le_exp hp).mpr hPg
  have hk_log_le : k * Real.log 2 ≤ -Real.log (povmGuessingProb ρ) := by
    linarith
  have hk_le_neglog :
      k ≤ -Real.log (povmGuessingProb ρ) / Real.log 2 := by
    calc
      k = (k * Real.log 2) / Real.log 2 := by
        field_simp [hlog2.ne']
      _ ≤ -Real.log (povmGuessingProb ρ) / Real.log 2 :=
        div_le_div_of_nonneg_right hk_log_le hlog2.le
  exact hk_le_neglog.trans
    (conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos ρ hp)

/-- If the POVM guessing probability of a CQ state (with nonempty outcome
set) vanishes, the optimized real conditional min-entropy also vanishes.

Proof: `povmGuessingProb ρ = 0` forces `(ρ.stateMap x).toOp = 0` for every
`x` (via `stateMap_eq_zero_of_povmGuessingProb_eq_zero`), which makes
`minFeasibleLambda ρ σ = 0` for every σ (via
`minFeasibleLambda_eq_zero_of_stateMap_zero`). Hence every value in the
sSup set defining `conditionalMinEntropyOptReal` is `0`. -/
lemma conditionalMinEntropyOptReal_eq_zero_of_povmGuessingProb_eq_zero
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hp : povmGuessingProb ρ = 0) :
    conditionalMinEntropyOptReal ρ = 0 := by
  have hsm : ∀ x : X, (ρ.stateMap x).toOp = 0 :=
    fun x => stateMap_eq_zero_of_povmGuessingProb_eq_zero ρ hp x
  refine conditionalMinEntropyOptReal_eq_zero_of_minFeasibleLambda_eq_zero ρ
    (fun σ => minFeasibleLambda_eq_zero_of_stateMap_zero ρ hsm σ)

/-! ## Main theorem: POVM guessing equivalence -/

/-- Equivalence of min-entropy and POVM guessing probability for CQ states.

    Tomamichel 2016, eq. 6.30:
      exp(-H_min(X|A)_ρ) = max_{POVM} Σ_x Tr(M_x ρ_A(x))

    Equivalently: H_min(X|A)_ρ = -log₂(Pg(X|A)_ρ).

    Proof:
    * `IsEmpty X` case: both sides are `0` (see
      `povmGuessingProb_eq_zero_of_isEmpty` and
      `conditionalMinEntropyOptReal_eq_zero_of_isEmpty`).
    * `Nonempty X` case with `povmGuessingProb ρ = 0`: both sides are `0`
      (see `conditionalMinEntropyOptReal_eq_zero_of_povmGuessingProb_eq_zero`).
    * `Nonempty X` case with `povmGuessingProb ρ > 0`: antisymmetry from
      `conditionalMinEntropyOptReal_le_neg_log_povmGuessingProb` (weak
      duality, Step A) and
      `conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos`
      (strong duality, Step B). -/
theorem conditionalMinEntropyReal_cq_guess_eq {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) :
    conditionalMinEntropyOptReal ρ = -Real.log (povmGuessingProb ρ) / Real.log 2 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [povmGuessingProb_eq_zero_of_isEmpty ρ,
        conditionalMinEntropyOptReal_eq_zero_of_isEmpty ρ,
        Real.log_zero, neg_zero, zero_div]
  · by_cases hp : povmGuessingProb ρ = 0
    · rw [conditionalMinEntropyOptReal_eq_zero_of_povmGuessingProb_eq_zero ρ hp,
          hp, Real.log_zero, neg_zero, zero_div]
    · have hp_pos : 0 < povmGuessingProb ρ :=
        lt_of_le_of_ne (povmGuessingProb_nonneg ρ) (Ne.symm hp)
      exact le_antisymm
        (conditionalMinEntropyOptReal_le_neg_log_povmGuessingProb ρ)
        (conditionalMinEntropyOptReal_ge_neg_log_povmGuessingProb_of_pos ρ hp_pos)

/-- A normalized CQ state on a nonempty classical register has nonnegative
optimized real conditional min-entropy. -/
lemma conditionalMinEntropyOptReal_nonneg_of_normalizedCQState
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : NormalizedCQState X n) :
    0 ≤ conditionalMinEntropyOptReal (ρ : CQState X n) := by
  rw [conditionalMinEntropyReal_cq_guess_eq]
  exact div_nonneg
    (neg_nonneg.mpr
      (Real.log_nonpos
        (le_of_lt (povmGuessingProb_pos_of_normalizedCQState ρ))
        (povmGuessingProb_le_one _)))
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

end InfoTheory.SmoothMinEntropy

end
