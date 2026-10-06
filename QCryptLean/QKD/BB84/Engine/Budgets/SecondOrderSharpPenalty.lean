/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Cor IV.2 finite-size AEP penalty at a variance cap, in closed form

Dupuis–Fawzi's Corollary IV.2 finite-size AEP penalty for the smooth min-entropy of an IID tensor
power, charged at a variance cap `V` on `V(X|B)`.  The improved BB84 row instantiates `V` at the
cap `bb84SharpVarianceCap = log₂²(1+√2) ≈ 1.6168`, the bound
`condDivergenceVariance_le_logb_one_add_sqrt_two` gives at `d_A = 2`.  This module is pure real
arithmetic: the scalar penalty, its clamped Rényi-order offset, and their elementary properties,
with no quantum content.  The AEP lift that pays this penalty
(`bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharp`) stays in
`Engine/PerRound/SecondOrderSharpPenalty.lean`, which imports this module.

With `B := log₂(2/ε²)`, `β := secondOrderSharpBeta V m ε` and `α := 1 + β`, the chain is

```
Hmin^ε(ρ^{⊗m} ‖ ρ_B^{⊗m})
  ≥ m·H'_α(X|B)_ρ − B/(α−1)
  ≥ m·(H − ((α−1)·log 2/2)·V − (α−1)²·K) − B/β
  ≥ m·H − (V/2)·log 2·m·β − K_β·m·β² − B/β
  = m·H − finiteSizePenaltySecondOrderSharp V m ε.
```

At a variance cap `V` the first summand is `(V/2)·log 2·m·β`, the optimiser of the first plus
third summand is `β = √(2B/(V·log 2·m))`. The fixed choice retains the clamp `β ≤ 1/16`,
inactive exactly on `B ≤ V·log 2·m/512` (`secondOrderSharpRegime`). The clamp guarantees
`β < 1` for the fixed security theorems without a regime assumption: the square-root choice can
exceed `1` for small blocks. The free-offset penalty allows every `0 < β < 1` and uses the
mathematical remainder `K_β = binarySecondOrderRemainderBound β`.


## Main definitions

- `QKD.BB84.Engine.bb84SharpVarianceCap`: the cap `log₂²(1+√2)`, the variance bound
  `condDivergenceVariance_le_logb_one_add_sqrt_two` gives at `d_A = 2`.
- `QKD.BB84.Engine.secondOrderSharpRegime`: the regime `B ≤ V·log 2·m/512` on which the clamp
  is inactive and the penalty has a closed form.
- `QKD.BB84.Engine.secondOrderSharpBeta`, `QKD.BB84.Engine.bb84SecondOrderSharpAlpha`: the clamped
  `α`-offset and the Rényi order it selects.
- `QKD.BB84.Engine.finiteSizePenaltySecondOrderSharp`: the penalty.

## Main results

- `QKD.BB84.Engine.finiteSizePenaltySecondOrderSharp_nonneg`: nonnegative for `V ≥ 0`, with no
  hypotheses on `m`, `ε`.
- `QKD.BB84.Engine.finiteSizePenaltySecondOrderSharp_eq_closedForm`: on `secondOrderSharpRegime V`,
  the closed form `√(2·V·log 2·m·log₂(2/ε²)) + 2·K_β·log₂(2/ε²)/(V·log 2)`.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `K(α)` (`:789`), `\label{eq_eatblock}` (`:1047`),
`\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`); the variance bound improved by this cap is
`\label{lem:divergence-variance-general-bounds}` (`:394`) with `\label{eq:bound_dalpha}`
(`:398`–`:399`); Tomamichel 2015 (`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`
`\label{pr:min-renyi}`).
-/

noncomputable section

namespace QKD.BB84.Engine

open InfoTheory.Renyi

/-- `log₂(2/ε²) > 1` for `0 < ε < 1`: the argument exceeds `2`. -/
lemma one_lt_logb_two_div_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 < Real.logb 2 (2 / ε ^ 2) := by
  have hsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hsq1 : ε ^ 2 < 1 := by nlinarith
  have h2 : (2 : ℝ) < 2 / ε ^ 2 := by
    rw [lt_div_iff₀ hsq]
    nlinarith
  have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at this

/-- The variance cap `log₂²(1 + √2) ≈ 1.6168`: the bound
`condDivergenceVariance_le_logb_one_add_sqrt_two` gives for `V(X|B)` at `d_A = 2`.  This is the
variance cap the improved BB84 row charges its Cor IV.2 penalty at. It improves
Dupuis–Fawzi's classical-register cap `log₂²(2 d_A + 1)`; no attainment is asserted. -/
noncomputable def bb84SharpVarianceCap : ℝ := Real.logb 2 (1 + Real.sqrt 2) ^ 2

/-- The variance cap is positive: `log₂(2) = 1 < log₂(1+√2)` since `2 < 1+√2`. -/
lemma bb84SharpVarianceCap_pos : 0 < bb84SharpVarianceCap := by
  have h2 : (2 : ℝ) < 1 + Real.sqrt 2 := by linarith [Real.one_lt_sqrt_two]
  have h1 : (1 : ℝ) < Real.logb 2 (1 + Real.sqrt 2) := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) h2
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  rw [bb84SharpVarianceCap]
  exact pow_pos (lt_trans (by norm_num) h1) 2

/-- **The cap times `log 2` is bracketed: `1.1195 ≤ V·log 2 ≤ 1.122`** (true
`1.1207135`).  `V·log 2 = Δ²/log 2` with `Δ = log(1+√2)` bracketed by
`Real.log_one_add_sqrt_two_mem_Icc` and `log 2` by the decimal `log 2` lemmas. -/
lemma bb84SharpVarianceCap_mul_log_two_mem_Icc :
    bb84SharpVarianceCap * Real.log 2 ∈ Set.Icc (1.1195 : ℝ) 1.122 := by
  obtain ⟨hLlo, hLhi⟩ := Real.log_one_add_sqrt_two_mem_Icc
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hform : bb84SharpVarianceCap * Real.log 2
      = Real.log (1 + Real.sqrt 2) ^ 2 / Real.log 2 := by
    rw [bb84SharpVarianceCap, Real.logb, div_pow, div_mul_eq_mul_div, pow_two (Real.log 2),
      mul_comm (Real.log (1 + Real.sqrt 2) ^ 2) (Real.log 2),
      mul_div_mul_left _ _ (ne_of_gt hl2pos)]
  rw [hform]
  have key1 : (1.1195 : ℝ) * Real.log 2
      ≤ Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) := by
    calc (1.1195 : ℝ) * Real.log 2 ≤ 1.1195 * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hlog2hi.le (by norm_num)
      _ ≤ 0.88093 * 0.88093 := by norm_num
      _ ≤ Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) :=
        mul_self_le_mul_self (by norm_num) hLlo
  have key2 : Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2) ≤ 1.122 * Real.log 2 := by
    calc Real.log (1 + Real.sqrt 2) * Real.log (1 + Real.sqrt 2)
        ≤ 0.88184 * 0.88184 := mul_self_le_mul_self (le_trans (by norm_num) hLlo) hLhi
      _ ≤ 1.122 * 0.6931471803 := by norm_num
      _ ≤ 1.122 * Real.log 2 := mul_le_mul_of_nonneg_left hlog2lo.le (by norm_num)
  refine ⟨?_, ?_⟩
  · -- `1.1195·log 2 ≤ 1.1195·0.6931471808 ≤ 0.88093² ≤ Δ²`
    rw [le_div_iff₀ hl2pos, pow_two (Real.log (1 + Real.sqrt 2))]
    exact key1
  · -- `Δ² ≤ 0.88184² ≤ 1.122·0.6931471803 ≤ 1.122·log 2`
    rw [div_le_iff₀ hl2pos, pow_two (Real.log (1 + Real.sqrt 2))]
    exact key2

/-- **The Cor IV.2 regime at variance cap `V`**: `B ≤ V·log 2·m/512`, with `B = log₂(2/ε²)`.

Equivalently `√(2·B/(V·log 2·m)) ≤ 1/16`, i.e. the clamp inside `secondOrderSharpBeta V` is
inactive.  It is the band on which `finiteSizePenaltySecondOrderSharp V` equals the closed form of
DF `:1053` at `V(X|B) ≤ V`.  It is empty for small `m`: `0 < ε < 1` forces `B > 1`, while
`V·log 2·m/512` grows linearly in `m` from `0`. -/
def secondOrderSharpRegime (V : ℝ) (m : ℕ) (ε : ℝ) : Prop :=
  Real.logb 2 (2 / ε ^ 2) ≤ V * Real.log 2 * (m : ℝ) / 512

/-- **The clamped Dupuis–Fawzi `α`-offset at variance cap `V`**,
`β⋆ = min(1/16, √(2·B/(V·log 2·m)))`.

The unclamped branch is DF's optimiser `:1061` `\label{eq_alphachoiceext}` evaluated at
`ρ[Ω] = 1` and variance cap `V`. The clamp makes this fixed choice admissible (`β⋆ < 1`)
without a block-size or smoothing regime assumption; the raw square root can exceed `1`. -/
noncomputable def secondOrderSharpBeta (V : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  min (1 / 16) (Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))))

/-- The Rényi order the Cor IV.2 penalty is charged at (variance cap `V`),
`α = 1 + β⋆ ≤ 1 + 1/16`, with `1 < α` when `0 < V`, `m ≥ 1` and `0 < ε < 1`. -/
noncomputable def bb84SecondOrderSharpAlpha (V : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  1 + secondOrderSharpBeta V m ε

/-- **The Cor IV.2 finite-size AEP penalty at variance cap `V`.**

`(V/2)·log 2·m·β + K_β·m·β² + log₂(2/ε²)/β` at `β = secondOrderSharpBeta V m ε`.  The first
summand is `((α−1)·log 2/2)·V·m` at a state with `V(X|B) ≤ V`.

On `secondOrderSharpRegime V m ε` it equals
`√(2·V·log 2·m·log₂(2/ε²)) + 2·K_β·log₂(2/ε²)/(V·log 2)`
(`finiteSizePenaltySecondOrderSharp_eq_closedForm`). -/
noncomputable def finiteSizePenaltySecondOrderSharp (V : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  V / 2 * Real.log 2 * (m : ℝ) * secondOrderSharpBeta V m ε
    + binarySecondOrderRemainderBound (secondOrderSharpBeta V m ε) * (m : ℝ)
        * secondOrderSharpBeta V m ε ^ 2
    + Real.logb 2 (2 / ε ^ 2) / secondOrderSharpBeta V m ε

/-- **The Cor IV.2 finite-size AEP penalty at variance cap `V`, charged at a free Rényi offset
`β`.**

`(V/2)·log 2·m·β + K_β·m·β² + log₂(2/ε²)/β` — the Dupuis–Fawzi Cor. IV.2 bound's finite-size
penalty at an arbitrary `β ∈ (0, 1)`, not only at the clamped optimiser `secondOrderSharpBeta`
(which ignores the `K_β·m·β²` remainder).  The free-β version lets the improved BB84 row pick any
admissible offset. -/
noncomputable def finiteSizePenaltySecondOrderSharpAt (V : ℝ) (m : ℕ) (ε β : ℝ) : ℝ :=
  V / 2 * Real.log 2 * (m : ℝ) * β
    + binarySecondOrderRemainderBound β * (m : ℝ) * β ^ 2
    + Real.logb 2 (2 / ε ^ 2) / β

/-- The fixed-β⋆ penalty is the free-β penalty at `β = secondOrderSharpBeta V m ε`. -/
lemma finiteSizePenaltySecondOrderSharp_eq (V : ℝ) (m : ℕ) (ε : ℝ) :
    finiteSizePenaltySecondOrderSharp V m ε
      = finiteSizePenaltySecondOrderSharpAt V m ε (secondOrderSharpBeta V m ε) :=
  rfl

/-! ## Elementary facts about `β⋆` -/

/-- `0 ≤ β⋆`. -/
lemma secondOrderSharpBeta_nonneg (V : ℝ) (m : ℕ) (ε : ℝ) : 0 ≤ secondOrderSharpBeta V m ε :=
  le_min (by norm_num) (Real.sqrt_nonneg _)

/-- The fixed offset satisfies `β⋆ ≤ 1/16` unconditionally. -/
lemma secondOrderSharpBeta_le_one_sixteenth (V : ℝ) (m : ℕ) (ε : ℝ) :
    secondOrderSharpBeta V m ε ≤ 1 / 16 :=
  min_le_left _ _

/-- `0 < β⋆` whenever `0 < V`, `0 < ε < 1` and `m ≥ 1`. -/
lemma secondOrderSharpBeta_pos (V : ℝ) (hV : 0 < V) (m : ℕ) [NeZero m] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) : 0 < secondOrderSharpBeta V m ε := by
  have hB : 1 < Real.logb 2 (2 / ε ^ 2) := one_lt_logb_two_div_sq ε hε hε1
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hden : (0 : ℝ) < V * Real.log 2 * (m : ℝ) := mul_pos (mul_pos hV hl2) hm
  refine lt_min (by norm_num) (Real.sqrt_pos.mpr ?_)
  exact div_pos (by linarith) hden

/-- `1 < α` whenever `0 < V`, `0 < ε < 1` and `m ≥ 1`. -/
lemma one_lt_bb84SecondOrderSharpAlpha (V : ℝ) (hV : 0 < V) (m : ℕ) [NeZero m] (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) : 1 < bb84SecondOrderSharpAlpha V m ε := by
  have := secondOrderSharpBeta_pos V hV m ε hε hε1
  rw [bb84SecondOrderSharpAlpha]; linarith

/-- The fixed Rényi order satisfies `α ≤ 1 + 1/16` unconditionally. -/
lemma bb84SecondOrderSharpAlpha_le (V : ℝ) (m : ℕ) (ε : ℝ) :
    bb84SecondOrderSharpAlpha V m ε ≤ 1 + 1 / 16 := by
  have := secondOrderSharpBeta_le_one_sixteenth V m ε
  rw [bb84SecondOrderSharpAlpha]; linarith

/-! ## Nonnegativity and the closed form -/

/-- The Cor IV.2 penalty at variance cap `V` is nonnegative for `V ≥ 0`, with no hypotheses on
`m`, `ε`.  Under Lean's junk-value conventions the degenerate inputs collapse the whole expression
to `0`: at `m = 0`, at `ε = 0` and at `ε ≥ √2` the `√` argument is non-positive, so `β⋆ = 0` and
the third summand is `B/0 = 0`. -/
lemma finiteSizePenaltySecondOrderSharp_nonneg (V : ℝ) (hV : 0 ≤ V) (m : ℕ) (ε : ℝ) :
    0 ≤ finiteSizePenaltySecondOrderSharp V m ε := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hβnn : 0 ≤ secondOrderSharpBeta V m ε := secondOrderSharpBeta_nonneg V m ε
  rcases eq_or_lt_of_le hβnn with h0 | hpos
  · rw [finiteSizePenaltySecondOrderSharp, ← h0]
    simp
  · -- β⋆ > 0 forces a positive square-root branch, hence `B > 0`.
    have hsq : 0 < Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))) :=
      lt_of_lt_of_le hpos (min_le_right _ _)
    have harg : 0 < 2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)) := by
      by_contra hc
      push_neg at hc
      rw [Real.sqrt_eq_zero_of_nonpos hc] at hsq
      exact lt_irrefl _ hsq
    have hB : 0 < Real.logb 2 (2 / ε ^ 2) := by
      by_contra hc
      push_neg at hc
      have hnum : 2 * Real.logb 2 (2 / ε ^ 2) ≤ 0 := by linarith
      have hden : (0 : ℝ) ≤ V * Real.log 2 * (m : ℝ) :=
        mul_nonneg (mul_nonneg hV hl2) (Nat.cast_nonneg _)
      have hquot : 2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)) ≤ 0 := by
        rcases eq_or_lt_of_le hden with hd | hd
        · rw [← hd, div_zero]
        · exact div_nonpos_of_nonpos_of_nonneg hnum hd.le
      linarith
    have t1 : (0 : ℝ) ≤ V / 2 * Real.log 2 * (m : ℝ) * secondOrderSharpBeta V m ε := by
      have h1 : (0 : ℝ) ≤ V / 2 := div_nonneg hV (by norm_num)
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 hl2) (Nat.cast_nonneg _)) hβnn
    have hK := binarySecondOrderRemainderBound_nonneg
      ((secondOrderSharpBeta_le_one_sixteenth V m ε).trans (by norm_num))
    have t2 : 0 ≤ binarySecondOrderRemainderBound (secondOrderSharpBeta V m ε) * (m : ℝ)
        * secondOrderSharpBeta V m ε ^ 2 := by positivity
    have t3 : 0 ≤ Real.logb 2 (2 / ε ^ 2) / secondOrderSharpBeta V m ε := (div_pos hB hpos).le
    rw [finiteSizePenaltySecondOrderSharp]
    linarith

/-- The free-offset Cor IV.2 penalty is nonnegative for `V ≥ 0`, `0 < ε ≤ 1` and
`0 ≤ β ≤ 1`. -/
lemma finiteSizePenaltySecondOrderSharpAt_nonneg (V : ℝ) (hV : 0 ≤ V) (m : ℕ)
    (ε β : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    0 ≤ finiteSizePenaltySecondOrderSharpAt V m ε β := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : ε ^ 2 ≤ 1 := by nlinarith
  have harg : (1 : ℝ) ≤ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < ε ^ 2)]
    linarith
  have hB : 0 ≤ Real.logb 2 (2 / ε ^ 2) :=
    Real.logb_nonneg (by norm_num) harg
  have hK := binarySecondOrderRemainderBound_nonneg hβ1
  unfold finiteSizePenaltySecondOrderSharpAt
  positivity

/-- **The regime at variance cap `V` forces `m ≥ 1`.**

`0 < ε < 1` gives `log₂(2/ε²) > 1`, and the regime caps that by `V·log 2·m/512`, which vanishes
at `m = 0`. -/
lemma one_le_of_secondOrderSharpRegime (V : ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hregime : secondOrderSharpRegime V m ε) : 1 ≤ (m : ℝ) := by
  by_contra hm
  have hm0 : (m : ℕ) = 0 := by
    have hm' : (m : ℕ) < 1 := by exact_mod_cast (not_le.mp hm)
    omega
  subst hm0
  have hB1 : 1 < Real.logb 2 (2 / ε ^ 2) := one_lt_logb_two_div_sq ε hε hε1
  rw [secondOrderSharpRegime] at hregime
  simp only [Nat.cast_zero, mul_zero, zero_div] at hregime
  linarith

/-- On the regime at variance cap `V` the clamp is inactive: `β⋆ = √(2·B/(V·log 2·m))`. -/
lemma secondOrderSharpBeta_eq_sqrt_of_regime (V : ℝ) (hV : 0 < V) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hregime : secondOrderSharpRegime V m ε) :
    secondOrderSharpBeta V m ε
      = Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hB : 1 < Real.logb 2 (2 / ε ^ 2) := one_lt_logb_two_div_sq ε hε hε1
  have hm : (0 : ℝ) < (m : ℝ) := by
    have := one_le_of_secondOrderSharpRegime V m ε hε hε1 hregime
    linarith
  have hden : (0 : ℝ) < V * Real.log 2 * (m : ℝ) := mul_pos (mul_pos hV hl2) hm
  rw [secondOrderSharpRegime] at hregime
  -- the regime `B ≤ D/512` is exactly `2B/D ≤ 1/256`, i.e. `√(2B/D) ≤ 1/16`
  have hle : 2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)) ≤ 1 / 256 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 256)]
    have hreg : Real.logb 2 (2 / ε ^ 2) * 512 ≤ V * Real.log 2 * (m : ℝ) :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 512)).mp hregime
    linarith
  have hsqrt : Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))) ≤ 1 / 16 := by
    calc Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ)))
             ≤ Real.sqrt (1 / 256) := Real.sqrt_le_sqrt hle
      _ = 1 / 16 := by
          rw [show (1 : ℝ) / 256 = ((1 : ℝ) / 16) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
  rw [secondOrderSharpBeta]
  exact min_eq_right hsqrt

/-- **The closed form of the penalty at variance cap `V`**, on the regime.

`finiteSizePenaltySecondOrderSharp V m ε
  = √(2·V·log 2·m·log₂(2/ε²)) + 2·K_β·log₂(2/ε²)/(V·log 2)`.

`hregime` is load-bearing: off the regime the `min (1/16)` clamp is active and the two sides
differ. -/
lemma finiteSizePenaltySecondOrderSharp_eq_closedForm (V : ℝ) (hV : 0 < V) (m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hregime : secondOrderSharpRegime V m ε) :
    finiteSizePenaltySecondOrderSharp V m ε
      = Real.sqrt (2 * V * Real.log 2 * (m : ℝ) * Real.logb 2 (2 / ε ^ 2))
        + 2 * binarySecondOrderRemainderBound (secondOrderSharpBeta V m ε)
          * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hB : 1 < Real.logb 2 (2 / ε ^ 2) := one_lt_logb_two_div_sq ε hε hε1
  have hm : (0 : ℝ) < (m : ℝ) := by
    have := one_le_of_secondOrderSharpRegime V m ε hε hε1 hregime
    linarith
  set B : ℝ := Real.logb 2 (2 / ε ^ 2) with hBdef
  set D : ℝ := V * Real.log 2 * (m : ℝ) with hDdef
  have hDpos : 0 < D := mul_pos (mul_pos hV hl2) hm
  have hBpos : 0 < B := by linarith
  have hβ : secondOrderSharpBeta V m ε = Real.sqrt (2 * B / D) :=
    secondOrderSharpBeta_eq_sqrt_of_regime V hV m ε hε hε1 hregime
  have hargnn : (0 : ℝ) ≤ 2 * B / D := div_nonneg (by linarith) hDpos.le
  have hsq : Real.sqrt (2 * B / D) ^ 2 = 2 * B / D := Real.sq_sqrt hargnn
  -- `(V/2)·log 2·m·β = (D/2)·β = √(D·B/2)` and `B/β = √(D·B/2)`; the two sum to `√(2·D·B)`
  have hterm1 : D / 2 * Real.sqrt (2 * B / D) = Real.sqrt (D * B / 2) := by
    have hid : D * B / 2 = (D / 2 * Real.sqrt (2 * B / D)) ^ 2 := by
      rw [mul_pow, hsq]; field_simp
    rw [hid, Real.sqrt_sq (by positivity)]
  have hterm3 : B / Real.sqrt (2 * B / D) = Real.sqrt (D * B / 2) := by
    have hid : D * B / 2 = (B / Real.sqrt (2 * B / D)) ^ 2 := by
      rw [div_pow, hsq]; field_simp
    rw [hid, Real.sqrt_sq (by positivity)]
  have hhalf : Real.sqrt (2 * D * B) = 2 * Real.sqrt (D * B / 2) := by
    rw [show 2 * D * B = 2 ^ 2 * (D * B / 2) from by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [finiteSizePenaltySecondOrderSharp, hβ, hsq,
    show V / 2 * Real.log 2 * (m : ℝ) * Real.sqrt (2 * B / D)
      = D / 2 * Real.sqrt (2 * B / D) from by rw [hDdef]; ring,
    hterm1, hterm3,
    show binarySecondOrderRemainderBound (Real.sqrt (2 * B / D)) * (m : ℝ) * (2 * B / D)
      = 2 * binarySecondOrderRemainderBound (Real.sqrt (2 * B / D)) * B / (V * Real.log 2)
      from by
      rw [hDdef]; field_simp,
    show 2 * V * Real.log 2 * (m : ℝ) * B = 2 * D * B from by rw [hDdef]; ring,
    hhalf, hDdef]
  have hVne : (V : ℝ) ≠ 0 := ne_of_gt hV
  have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hl2
  field_simp
  ring

end QKD.BB84.Engine

end -- noncomputable section
