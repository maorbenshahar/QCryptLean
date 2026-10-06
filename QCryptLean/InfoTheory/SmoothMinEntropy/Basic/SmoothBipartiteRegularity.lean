import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ConditioningIsometryInvariance

/-!
# Regularity of the smooth bipartite min-entropy optimization set

`smoothBipartiteMinEntropyOptReal ε ρ = sSup {H_min(A|C)_{ρ'} : P(ρ, ρ') ≤ ε}`
(`SmoothBipartite.lean`) is an ℝ-valued supremum, so every statement about it needs to know
whether the optimization set is bounded above — otherwise Lean's `sSup` of an unbounded set is a
junk value and the inequality being proved is not the intended one.  `SmoothBipartite.lean`
therefore carries `BddAbove` as an explicit hypothesis.

This file discharges that hypothesis in the regime where it is true, and explains why it cannot be
discharged in general.

## What is proved

* `bipartiteMinEntropyOptReal_le_of_trace_le` — a *uniform* upper bound
  `H_min(A|C)_ρ ≤ log₂(dA / t)` for any positive lower bound `t ≤ Tr ρ`, from the
  reference-independent estimate `Tr ρ / dA ≤ dmaxFeasibleLambda`
  (`trace_div_dim_le_dmaxFeasibleLambda`).
* `smoothBipartiteMinSet_bddAbove_of_normalized` — for a **normalized** centre `ρ` and a radius
  `ε < 1`, the smooth optimization set is bounded above by `log₂(dA / (1 − ε²))`.  The ball members
  cannot have vanishing trace: `1 − ε² ≤ Tr ρ'` (`trace_ge_of_purifiedDistance_of_normalized`).
* `ne_zero_of_purifiedDistance_of_normalized` — the same estimate in the form used to
  exclude the `Real.log 0 = 0` sentinel: every ball member of a normalized centre at radius
  `ε < 1` is a nonzero operator.
* two corollaries of `SmoothBipartite.lean` with the boundedness premise derived from normalization
  and `0 ≤ ε < 1`:
  `smoothBipartiteMinEntropyOptReal_ge_of_mem_ball_of_normalized` and
  `smoothBipartiteMinEntropyOptReal_monotone_eps_of_normalized`.

## The endpoint `ε = 1`

The mathematical reason for excluding this endpoint is the family `t·ρ`, `t ↓ 0`: its
purified distance from normalized `ρ` is at most one, while
`H_min(A|C)_{t·ρ} = H_min(A|C)_ρ + log₂(1/t)` grows without bound. Thus the optimization set is
unbounded at `ε ≥ 1`. This scaling argument is explanatory mathematics, not a formalized theorem
in this file; the proved boundedness result below is for `0 ≤ ε < 1`.
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Uniform upper bound on the reference-optimized min-entropy from a trace lower bound.**
If `0 < t ≤ Tr ρ`, then `H_min(A|C)_ρ ≤ log₂(dA / t)`.

The bound is reference-independent: for every feasible `σ` the estimate
`Tr ρ / dA ≤ dmaxFeasibleLambda ρ (1_A ⊗ σ)` (`trace_div_dim_le_dmaxFeasibleLambda`) gives
`H_min(A|C)_{ρ|σ} = −log₂ dmax ≤ −log₂(t/dA)`, and the supremum inherits it. -/
theorem bipartiteMinEntropyOptReal_le_of_trace_le {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) {t : ℝ} (ht : 0 < t) (htr : t ≤ ρ.trace) :
    bipartiteMinEntropyOptReal ρ ≤ -Real.log (t / (dA : ℝ)) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  have htdA : (0 : ℝ) < t / (dA : ℝ) := div_pos ht hdA
  rw [bipartiteMinEntropyOptReal_eq_sSup]
  refine csSup_le (bipartiteMinEntropyOptSet_nonempty ρ) ?_
  rintro h ⟨σ, hfeas, rfl⟩
  have htr' : t ≤ ρ.toOp.trace.re := htr
  have hbound : t / (dA : ℝ) ≤ dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) :=
    le_trans (by gcongr) (trace_div_dim_le_dmaxFeasibleLambda ρ σ hfeas)
  unfold bipartiteMinEntropyReal
  rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
  exact Real.log_le_log htdA hbound

/-- **Ball members of a normalized centre are nonzero** at radius `ε < 1`: the purified distance
controls the trace, `1 − ε² ≤ Tr ρ'` (`trace_ge_of_purifiedDistance_of_normalized`), and
`ε < 1` makes that positive. This is what excludes the `Real.log 0 = 0` sentinel on a smoothing
ball. -/
theorem ne_zero_of_purifiedDistance_of_normalized {n : ℕ} [NeZero n]
    (ρ ρ' : SubDensityOp n) (hρ : ρ.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hd : purifiedDistance ρ ρ' ≤ ε) : ρ'.toOp ≠ 0 := by
  have hsq : ε ^ 2 < 1 := by nlinarith
  have htr : 1 - ε ^ 2 ≤ ρ'.trace :=
    SubDensityOp.trace_ge_of_purifiedDistance_of_normalized ρ ρ' hρ hε hd
  intro h0
  rw [SubDensityOp.trace, h0, Matrix.trace_zero, Complex.zero_re] at htr
  linarith

/-- **The smooth optimization set of a normalized centre is bounded above for `ε < 1`.**
Uniform bound `log₂(dA / (1 − ε²))`: every ball member has trace at least `1 − ε² > 0`
(`trace_ge_of_purifiedDistance_of_normalized`), and `bipartiteMinEntropyOptReal_le_of_trace_le`
turns that into the stated bound. See the module docstring for why `ε < 1` cannot be dropped. -/
theorem smoothBipartiteMinSet_bddAbove_of_normalized {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) (hρ : ρ.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    BddAbove (setOf (isInSmoothBipartiteMinSet ε ρ)) := by
  have hsq : ε ^ 2 < 1 := by nlinarith
  refine ⟨-Real.log ((1 - ε ^ 2) / (dA : ℝ)) / Real.log 2, ?_⟩
  rintro h ⟨ρ', hd, rfl⟩
  exact bipartiteMinEntropyOptReal_le_of_trace_le ρ' (by linarith)
    (SubDensityOp.trace_ge_of_purifiedDistance_of_normalized ρ ρ' hρ hε hd)

/-- Hypothesis-free form of `smoothBipartiteMinEntropyOptReal_ge_of_mem_ball` for a normalized
centre and a radius below one. -/
theorem smoothBipartiteMinEntropyOptReal_ge_of_mem_ball_of_normalized {dA dC : ℕ}
    [NeZero dA] [NeZero dC] (ρ ρ' : SubDensityOp (dA * dC)) (hρ : ρ.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hd : purifiedDistance ρ ρ' ≤ ε) :
    bipartiteMinEntropyOptReal ρ' ≤ smoothBipartiteMinEntropyOptReal ε ρ :=
  smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε ρ ρ'
    (smoothBipartiteMinSet_bddAbove_of_normalized ρ hρ hε hε1) hd

/-- Hypothesis-free form of `smoothBipartiteMinEntropyOptReal_monotone_eps` for a normalized centre
and radii below one. -/
theorem smoothBipartiteMinEntropyOptReal_monotone_eps_of_normalized {dA dC : ℕ}
    [NeZero dA] [NeZero dC] (ρ : SubDensityOp (dA * dC)) (hρ : ρ.trace = 1)
    {ε ε' : ℝ} (hε : 0 ≤ ε) (h : ε ≤ ε') (hε1 : ε' < 1) :
    smoothBipartiteMinEntropyOptReal ε ρ ≤ smoothBipartiteMinEntropyOptReal ε' ρ :=
  smoothBipartiteMinEntropyOptReal_monotone_eps hε h ρ
    (smoothBipartiteMinSet_bddAbove_of_normalized ρ hρ (hε.trans h) hε1)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
