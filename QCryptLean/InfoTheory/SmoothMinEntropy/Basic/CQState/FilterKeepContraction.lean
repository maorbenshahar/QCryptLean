import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth

/-!
# Block-keep filter contraction of CQ purified distance / generalized fidelity

A *block-keep filter* on a classical-quantum state keeps the quantum block at every
classical outcome `x` satisfying a state-independent predicate `keep x` and zeros every
failing block.  Because the kept outcome set is the same for both arguments, this is the
classical-register Lüders projection onto the passing sub-algebra — a trace-non-increasing
completely positive data-processing channel on the CQ joint state.

The generalized fidelity `F*` of Tomamichel (2016, §3.3.1) is monotone-nondecreasing under
any trace-non-increasing CP map, so the block-keep filter **raises** generalized fidelity and
**contracts** purified distance.  Here this is proved elementarily, with no appeal to a general
CP-map DPI: the ordinary fidelity sum drops by the failing-block fidelities, while the
sub-normalization correction `√((1-trρ)(1-trσ))` rises, and the net sign is settled by a
Cauchy–Schwarz bound on the dropped fidelities plus the AM–GM identity
`√(αβ) ≥ √((α-u)(β-v)) + √(uv)`.

This is the same-radius robustness used by the BB84 privacy-amplification smooth-min-entropy
tolerance lemmas: the PE-pass filter on the honest IID reference does not lower its
`εTensor`-smooth conditional min-entropy.

**Textbook reference**: Tomamichel, M. (2016). *Quantum Information Processing with Finite
Resources*. Springer. §3.3.1 (generalized fidelity), §3.4 (purified distance), and the
data-processing inequality for `F*` under trace-non-increasing CP maps; Renner, R. (2005).
*Security of Quantum Key Distribution*. arXiv:quant-ph/0512258v2, §6.5.

The scalar core `Real.sqrt_sub_mul_add_sqrt_mul_le` is in `QCryptLean.Math.Analysis.AMGM`.

## Main statements
- `CQState.sum_fidelity_le_sqrt_sum_trace_mul_sum_trace`: Cauchy–Schwarz on a block fidelity
  sum, `∑ F(ρₓ,σₓ) ≤ √((∑ trρₓ)(∑ trσₓ))`.
- `CQState.fidelityGen_filterKeep_ge`: generalized fidelity of CQ joint densities is
  nondecreasing under a common block-keep filter.
- `CQState.purifiedDistance_filterKeep_le`: CQ purified distance is contracted by a common
  block-keep filter.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Cauchy–Schwarz on a block fidelity sum.**  The sum of per-block Uhlmann fidelities over
any subset `s` of classical outcomes is at most the geometric mean of the two block-weight
sums on `s`:
`∑_{x∈s} F(ρₓ, σₓ) ≤ √((∑_{x∈s} trρₓ)(∑_{x∈s} trσₓ))`. -/
lemma CQState.sum_fidelity_le_sqrt_sum_trace_mul_sum_trace
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ σ : CQState X n) (s : Finset X) :
    ∑ x ∈ s, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
        (σ.stateMap x).toPosSemidefOp ≤
      Real.sqrt ((∑ x ∈ s, (ρ.stateMap x).trace) * (∑ x ∈ s, (σ.stateMap x).trace)) := by
  classical
  -- termwise: F(ρₓ,σₓ) ≤ √(trρₓ · trσₓ) = √(trρₓ)·√(trσₓ)
  have hterm : ∀ x ∈ s,
      Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp (σ.stateMap x).toPosSemidefOp ≤
        Real.sqrt ((ρ.stateMap x).trace) * Real.sqrt ((σ.stateMap x).trace) := by
    intro x _
    have hsq := fidelity_sq_le_trace_mul_trace (ρ.stateMap x) (σ.stateMap x)
    have hF_nn := Quantum.Metrics.fidelity_nonneg_posSemidefOp
      (ρ.stateMap x).toPosSemidefOp (σ.stateMap x).toPosSemidefOp
    have hstep := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hF_nn,
      Real.sqrt_mul (ρ.stateMap x).trace_nonneg] at hstep
    exact hstep
  -- sum bound, then Cauchy–Schwarz on the sqrt products
  have hsum_le :
      ∑ x ∈ s, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
          (σ.stateMap x).toPosSemidefOp ≤
        ∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) * Real.sqrt ((σ.stateMap x).trace) :=
    Finset.sum_le_sum hterm
  have hCS :
      (∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) * Real.sqrt ((σ.stateMap x).trace)) ≤
        Real.sqrt ((∑ x ∈ s, (ρ.stateMap x).trace) * (∑ x ∈ s, (σ.stateMap x).trace)) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun x => Real.sqrt ((ρ.stateMap x).trace))
      (fun x => Real.sqrt ((σ.stateMap x).trace))
    -- key : (∑ √trρ · √trσ)² ≤ (∑ (√trρ)²)·(∑ (√trσ)²)
    have h2 : (∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) ^ 2) =
        ∑ x ∈ s, (ρ.stateMap x).trace := by
      apply Finset.sum_congr rfl; intro x _; exact Real.sq_sqrt (ρ.stateMap x).trace_nonneg
    have h3 : (∑ x ∈ s, Real.sqrt ((σ.stateMap x).trace) ^ 2) =
        ∑ x ∈ s, (σ.stateMap x).trace := by
      apply Finset.sum_congr rfl; intro x _; exact Real.sq_sqrt (σ.stateMap x).trace_nonneg
    rw [h2, h3] at key
    have hlhs_nn :
        0 ≤ ∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) * Real.sqrt ((σ.stateMap x).trace) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hrhs_nn :
        0 ≤ (∑ x ∈ s, (ρ.stateMap x).trace) * (∑ x ∈ s, (σ.stateMap x).trace) :=
      mul_nonneg (Finset.sum_nonneg fun x _ => (ρ.stateMap x).trace_nonneg)
        (Finset.sum_nonneg fun x _ => (σ.stateMap x).trace_nonneg)
    rw [show
        (∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) * Real.sqrt ((σ.stateMap x).trace)) =
          Real.sqrt ((∑ x ∈ s, Real.sqrt ((ρ.stateMap x).trace) *
            Real.sqrt ((σ.stateMap x).trace)) ^ 2) from
        (Real.sqrt_sq hlhs_nn).symm]
    exact Real.sqrt_le_sqrt (le_trans key (le_of_eq rfl))
  exact le_trans hsum_le hCS

/-- **Block-keep filter raises generalized fidelity.**

Let `Fρ`, `Fρ'` be the block-keep filters of `ρ`, `ρ'` for a common state-independent predicate
`keep` (kept block = input block when `keep x`, zero block otherwise).  Then the generalized
fidelity of the filtered joint densities is at least that of the originals.

The kept-block fidelity sum is the same on both sides; the failing-block fidelities that drop out
are reabsorbed into the (larger) sub-normalization correction by the Cauchy–Schwarz bound
`CQState.sum_fidelity_le_sqrt_sum_trace_mul_sum_trace` and the AM–GM core
`Real.sqrt_sub_mul_add_sqrt_mul_le`. -/
theorem CQState.fidelityGen_filterKeep_ge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ ρ' Fρ Fρ' : CQState X n) (keep : X → Bool)
    (hFρ : ∀ x, Fρ.stateMap x = if keep x then ρ.stateMap x else 0)
    (hFρ' : ∀ x, Fρ'.stateMap x = if keep x then ρ'.stateMap x else 0) :
    fidelityGen ρ.toJointDensity ρ'.toJointDensity ≤
      fidelityGen Fρ.toJointDensity Fρ'.toJointDensity := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  classical
  set s : Finset X := Finset.univ.filter (fun x => keep x = true) with hs_def
  -- Block-sum form of the four scalars.
  have hmem : ∀ x, x ∈ s ↔ keep x = true := by
    intro x; simp [hs_def]
  -- traces
  have htrace_zero : ((0 : SubDensityOp n).trace) = 0 := by
    simp [SubDensityOp.trace, show (0 : SubDensityOp n).toOp = 0 from rfl]
  have hp : ρ.toJointDensity.trace = ∑ x : X, (ρ.stateMap x).trace :=
    ρ.toJointDensity_trace_eq_sum
  have hq : ρ'.toJointDensity.trace = ∑ x : X, (ρ'.stateMap x).trace :=
    ρ'.toJointDensity_trace_eq_sum
  have hpS : Fρ.toJointDensity.trace = ∑ x ∈ s, (ρ.stateMap x).trace := by
    rw [Fρ.toJointDensity_trace_eq_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true), (Fρ.stateMap x).trace = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hFρ x, ite_eq_right hx, htrace_zero]
    have heq : ∑ x ∈ Finset.univ.filter (fun x => keep x = true), (Fρ.stateMap x).trace =
        ∑ x ∈ s, (ρ.stateMap x).trace := by
      apply Finset.sum_congr rfl; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hFρ x, ite_eq_left hx]
    rw [heq, h0, add_zero]
  have hqS : Fρ'.toJointDensity.trace = ∑ x ∈ s, (ρ'.stateMap x).trace := by
    rw [Fρ'.toJointDensity_trace_eq_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true), (Fρ'.stateMap x).trace = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hFρ' x, ite_eq_right hx, htrace_zero]
    have heq : ∑ x ∈ Finset.univ.filter (fun x => keep x = true), (Fρ'.stateMap x).trace =
        ∑ x ∈ s, (ρ'.stateMap x).trace := by
      apply Finset.sum_congr rfl; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hFρ' x, ite_eq_left hx]
    rw [heq, h0, add_zero]
  -- fidelity sums
  have hF_full :
      Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp ρ'.toJointDensity.toPosSemidefOp =
        ∑ x : X, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
          (ρ'.stateMap x).toPosSemidefOp :=
    CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity ρ ρ'
  have hF_filt :
      Quantum.Metrics.fidelity Fρ.toJointDensity.toPosSemidefOp Fρ'.toJointDensity.toPosSemidefOp =
        ∑ x ∈ s, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
          (ρ'.stateMap x).toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity Fρ Fρ']
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true),
        Quantum.Metrics.fidelity (Fρ.stateMap x).toPosSemidefOp
          (Fρ'.stateMap x).toPosSemidefOp = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      apply Quantum.Metrics.fidelity_eq_zero_of_left_toOp_eq_zero
      rw [hFρ x, ite_eq_right hx]; rfl
    have heq : ∑ x ∈ Finset.univ.filter (fun x => keep x = true),
        Quantum.Metrics.fidelity (Fρ.stateMap x).toPosSemidefOp
          (Fρ'.stateMap x).toPosSemidefOp =
        ∑ x ∈ s, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
          (ρ'.stateMap x).toPosSemidefOp := by
      apply Finset.sum_congr rfl; intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      congr 1 <;> · first
        | (rw [hFρ x, ite_eq_left hx]) | (rw [hFρ' x, ite_eq_left hx])
    rw [heq, h0, add_zero]
  -- abbreviations
  set A : ℝ := ∑ x ∈ s, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
    (ρ'.stateMap x).toPosSemidefOp with hA_def
  set B : ℝ := ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true),
    Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp (ρ'.stateMap x).toPosSemidefOp
    with hB_def
  have hAB : (∑ x : X, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
      (ρ'.stateMap x).toPosSemidefOp) = A + B := by
    rw [hA_def, hB_def, hs_def]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true) _).symm
  set p : ℝ := ∑ x : X, (ρ.stateMap x).trace with hp_def
  set q : ℝ := ∑ x : X, (ρ'.stateMap x).trace with hq_def
  set pS : ℝ := ∑ x ∈ s, (ρ.stateMap x).trace with hpS_def
  set qS : ℝ := ∑ x ∈ s, (ρ'.stateMap x).trace with hqS_def
  set dp : ℝ := ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true), (ρ.stateMap x).trace
    with hdp_def
  set dq : ℝ := ∑ x ∈ Finset.univ.filter (fun x => ¬ keep x = true), (ρ'.stateMap x).trace
    with hdq_def
  have hp_split : p = pS + dp := by
    rw [hp_def, hpS_def, hdp_def, hs_def]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true) _).symm
  have hq_split : q = qS + dq := by
    rw [hq_def, hqS_def, hdq_def, hs_def]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => keep x = true) _).symm
  -- nonnegativities and weight bounds
  have hB_nn : 0 ≤ B :=
    Finset.sum_nonneg fun x _ => Quantum.Metrics.fidelity_nonneg_posSemidefOp _ _
  have hdp_nn : 0 ≤ dp :=
    Finset.sum_nonneg fun x _ => (ρ.stateMap x).trace_nonneg
  have hdq_nn : 0 ≤ dq :=
    Finset.sum_nonneg fun x _ => (ρ'.stateMap x).trace_nonneg
  have hp_le_one : p ≤ 1 := by
    rw [hp_def, ← ρ.toJointDensity_trace_eq_sum]; exact ρ.toJointDensity.trace_le_one
  have hq_le_one : q ≤ 1 := by
    rw [hq_def, ← ρ'.toJointDensity_trace_eq_sum]; exact ρ'.toJointDensity.trace_le_one
  -- Cauchy–Schwarz: B ≤ √(dp·dq)
  have hB_le : B ≤ Real.sqrt (dp * dq) := by
    rw [hB_def, hdp_def, hdq_def]
    exact CQState.sum_fidelity_le_sqrt_sum_trace_mul_sum_trace ρ ρ'
      (Finset.univ.filter (fun x => ¬ keep x = true))
  -- AM–GM core: √((1-pS-dp)(1-qS-dq)) + √(dp·dq) ≤ √((1-pS)(1-qS))
  have hcore :
      Real.sqrt ((1 - pS - dp) * (1 - qS - dq)) + Real.sqrt (dp * dq) ≤
        Real.sqrt ((1 - pS) * (1 - qS)) := by
    have h1 : (1 - pS) - dp = 1 - pS - dp := by ring
    have h2 : (1 - qS) - dq = 1 - qS - dq := by ring
    have := Real.sqrt_sub_mul_add_sqrt_mul_le (α := 1 - pS) (β := 1 - qS)
      (u := dp) (v := dq) hdp_nn hdq_nn (by linarith [hp_split, hp_le_one])
      (by linarith [hq_split, hq_le_one])
    rw [h1, h2] at this
    exact this
  -- Assemble.
  unfold fidelityGen
  rw [hF_full, hF_filt, hp, hq, hpS, hqS, hAB]
  have hsub_full : (1 - p) = (1 - pS - dp) := by rw [hp_split]; ring
  have hsub_q : (1 - q) = (1 - qS - dq) := by rw [hq_split]; ring
  rw [hsub_full, hsub_q]
  -- goal: A + B + √((1-pS-dp)(1-qS-dq)) ≤ A + √((1-pS)(1-qS))
  have hchain : B + Real.sqrt ((1 - pS - dp) * (1 - qS - dq)) ≤
      Real.sqrt ((1 - pS) * (1 - qS)) := by
    calc B + Real.sqrt ((1 - pS - dp) * (1 - qS - dq))
        ≤ Real.sqrt (dp * dq) + Real.sqrt ((1 - pS - dp) * (1 - qS - dq)) := by linarith [hB_le]
      _ = Real.sqrt ((1 - pS - dp) * (1 - qS - dq)) + Real.sqrt (dp * dq) := by ring
      _ ≤ Real.sqrt ((1 - pS) * (1 - qS)) := hcore
  linarith [hchain]

/-- **Block-keep filter contracts CQ purified distance.**

The CQ purified distance between the block-keep filters of `ρ`, `ρ'` (for a common
state-independent predicate `keep`) is at most the purified distance between `ρ`, `ρ'`. -/
theorem CQState.purifiedDistance_filterKeep_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ ρ' Fρ Fρ' : CQState X n) (keep : X → Bool)
    (hFρ : ∀ x, Fρ.stateMap x = if keep x then ρ.stateMap x else 0)
    (hFρ' : ∀ x, Fρ'.stateMap x = if keep x then ρ'.stateMap x else 0) :
    CQState.purifiedDistance Fρ Fρ' ≤ CQState.purifiedDistance ρ ρ' := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  exact purifiedDistance_le_of_fidelityGen_ge Fρ.toJointDensity Fρ'.toJointDensity
    ρ.toJointDensity ρ'.toJointDensity
    (CQState.fidelityGen_filterKeep_ge ρ ρ' Fρ Fρ' keep hFρ hFρ')

/-- The block-keep filter of a CQ state: keep the quantum block at every kept outcome, zero the
rest.  The total weight only drops, so `weight_le_one` is inherited from the kept sub-sum. -/
noncomputable def CQState.filterKeep {X : Type*} [Fintype X] {n : ℕ}
    (keep : X → Bool) (ρ : CQState X n) : CQState X n where
  stateMap := fun x => if keep x then ρ.stateMap x else 0
  weight_le_one := by
    classical
    refine le_trans (Finset.sum_le_sum ?_) ρ.weight_le_one
    intro x _
    by_cases hx : keep x
    · simp [hx]
    · simp only [hx, Bool.false_eq_true, ite_false]
      have : ((0 : SubDensityOp n).trace) = 0 := by
        simp [SubDensityOp.trace, show (0 : SubDensityOp n).toOp = 0 from rfl]
      rw [this]; exact (ρ.stateMap x).trace_nonneg

@[simp] lemma CQState.filterKeep_stateMap {X : Type*} [Fintype X] {n : ℕ}
    (keep : X → Bool) (ρ : CQState X n) (x : X) :
    (CQState.filterKeep keep ρ).stateMap x = if keep x then ρ.stateMap x else 0 :=
  rfl

/-- Blockwise Löwner domination of a keep-filter by its argument: each filtered block
`(filterKeep keep ρ').stateMap x` is `≼` the unfiltered block `ρ'.stateMap x`.  Kept blocks are
equal (`le_refl`); dropped blocks are `0 ≼ (ρ'.stateMap x)` from the PSD nonnegativity of the
quadratic form. -/
lemma CQState.filterKeep_stateMap_opLe {X : Type*} [Fintype X] {n : ℕ}
    (keep : X → Bool) (ρ' : CQState X n) (x : X) :
    opLe ((CQState.filterKeep keep ρ').stateMap x).toOp (ρ'.stateMap x).toOp := by
  classical
  rw [CQState.filterKeep_stateMap]
  by_cases hx : keep x
  · simp only [hx, ite_true]
    intro v
    exact le_refl _
  · simp only [hx, Bool.false_eq_true, ite_false]
    intro v
    have h0 : ((0 : SubDensityOp n).toOp) = 0 := rfl
    rw [h0]
    have hz : (quadraticForm (0 : Op n) v).re = 0 := by
      simp [quadraticForm, Matrix.zero_mulVec]
    rw [hz]
    exact (ρ'.stateMap x).pos_semidef v

/-- Keeping classical blocks increases extended smooth min-entropy at every radius. -/
theorem smoothMinEntropy_filterKeep_ge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (ρ Fρ : CQState X n) (σ : SubDensityOp n) (keep : X → Bool)
    (hFρ : ∀ x, Fρ.stateMap x = if keep x then ρ.stateMap x else 0) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε Fρ σ := by
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨CQState.filterKeep keep τ, ?_, ?_⟩
  · exact (CQState.purifiedDistance_filterKeep_le ρ τ Fρ (CQState.filterKeep keep τ)
      keep hFρ (fun _ => rfl)).trans hd
  · intro t ht
    exact ⟨ht.1, fun x => opLe_trans (CQState.filterKeep_stateMap_opLe keep τ x) (ht.2 x)⟩


/-- Keeping classical outcomes does not decrease signed smooth min-entropy when the kept weight
exceeds `2 * ε` and the reference is positive definite. -/
theorem smoothMinEntropyReal_filterKeep_ge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (ρ Fρ : CQState X n) (σ : SubDensityOp n) (keep : X → Bool)
    (hε : 0 ≤ ε)
    (hσ_pd : σ.toOp.PosDef)
    (hFρ : ∀ x, Fρ.stateMap x = if keep x then ρ.stateMap x else 0)
    (hkeep : 2 * ε < ∑ x : X, (Fρ.stateMap x).trace) :
    smoothMinEntropyReal ε ρ σ ≤ smoothMinEntropyReal ε Fρ σ := by
  classical
  set η : ℝ := (∑ x : X, (Fρ.stateMap x).trace) - 2 * ε with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have hfloor_Fρ : ∀ τ : CQState X n,
      CQState.purifiedDistance Fρ τ ≤ ε → η ≤ ∑ x : X, (τ.stateMap x).trace := by
    intro τ hτ
    refine CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower (η := η) ?_ hτ
    rw [hη_def]; ring_nf; rfl
  have hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε Fρ σ)) :=
    smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη_pos Fρ σ hfloor_Fρ
  unfold smoothMinEntropyReal
  apply csSup_le (smoothedSetReal_nonempty hε ρ σ)
  rintro a ⟨ρ', rfl, hd⟩
  set Fρ' : CQState X n := CQState.filterKeep keep ρ' with hFρ'_def
  have hFρ'_stateMap : ∀ x, Fρ'.stateMap x = if keep x then ρ'.stateMap x else 0 := fun x => rfl
  have hd' : CQState.purifiedDistance Fρ Fρ' ≤ ε :=
    le_trans (CQState.purifiedDistance_filterKeep_le ρ ρ' Fρ Fρ' keep hFρ hFρ'_stateMap) hd
  have hweight_Fρ' : η ≤ ∑ x : X, (Fρ'.stateMap x).trace := hfloor_Fρ Fρ' hd'
  have hweight_pos : 0 < ∑ x : X, (Fρ'.stateMap x).trace := lt_of_lt_of_le hη_pos hweight_Fρ'
  have hpos : 0 < minFeasibleLambda Fρ' σ :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos Fρ' σ hσ_pd hweight_pos
  have hmono : conditionalMinEntropyReal ρ' σ ≤ conditionalMinEntropyReal Fρ' σ :=
    conditionalMinEntropyReal_mono_stateMap_of_opLe Fρ' ρ' σ
      (fun x => CQState.filterKeep_stateMap_opLe keep ρ' x)
      (hasFeasibleLambda_of_posDef ρ' σ hσ_pd) hpos
  exact le_trans hmono (le_csSup hbdd ⟨Fρ', rfl, hd'⟩)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
