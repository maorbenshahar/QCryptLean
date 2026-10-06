import QCryptLean.InfoTheory.Renyi.DivergenceVariance

/-!
# The binary classical Dupuis–Fawzi remainder

Dupuis–Fawzi's Corollary IV.2 bounds the second-order remainder for `α ∈ (1, 2)`. For a
normalized state with a binary classical register, both entropy differences in `secondOrderK`
are at most `1`. At `α = 1 + β`, this gives `K(1 + β) ≤ K_β` for `0 < β < 1`, where
`K_β = K_* · 2^β / (1 - β)^3` and `K_* = log³(2 + e²) / (6 log 2)`.

Reference: Dupuis–Fawzi 2018 (arXiv:1805.11652), Corollary IV.2
(`EAT-second-order-ieee-1col-r2.tex:784`, remainder at `:789`), with the classical-register
improvement following their variance bound (`:877`, `:450`).
-/

open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

/-- The binary classical Dupuis–Fawzi remainder base `K_* = log³(2 + e²) / (6 log 2)`. -/
def binarySecondOrderRemainderBase : ℝ :=
  Real.log (2 + Real.exp 2) ^ 3 / (6 * Real.log 2)

/-- The binary classical Dupuis–Fawzi remainder bound `K_β = K_* · 2^β / (1 - β)^3`,
valid for Rényi offsets `0 < β < 1`. -/
def binarySecondOrderRemainderBound (β : ℝ) : ℝ :=
  binarySecondOrderRemainderBase * (2 : ℝ) ^ β / (1 - β) ^ 3

/-- The binary remainder bound is nonnegative for `β ≤ 1`. -/
lemma binarySecondOrderRemainderBound_nonneg {β : ℝ} (hβ : β ≤ 1) :
    0 ≤ binarySecondOrderRemainderBound β := by
  have hlog : 0 ≤ Real.log (2 + Real.exp 2) := Real.log_nonneg (by
    have := Real.exp_pos (2 : ℝ)
    linarith)
  have hden : 0 ≤ 1 - β := sub_nonneg.mpr hβ
  unfold binarySecondOrderRemainderBound binarySecondOrderRemainderBase
  positivity

/-- `K(1 + β) ≤ K_β` for `0 < β < 1` at a normalized binary classical register.

The conditional von Neumann entropy is at most `log₂ 2 = 1`, and the conditional Petz-down
Rényi entropies at orders `1 + β` and `2` are nonnegative. Thus both entropy differences in
Dupuis–Fawzi's Corollary IV.2 remainder are at most `1`. -/
theorem secondOrderK_le_binarySecondOrderRemainderBound
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hcard : Fintype.card X = 2) :
    secondOrderK (1 + β) ρ ≤ binarySecondOrderRemainderBound β := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hα1 : 1 < 1 + β := by linarith
  have hα2 : 1 + β ≤ 2 := by linarith
  have hH1 : condVonNeumann ρ ≤ 1 := by
    have hHd := condVonNeumann_le_logb_card ρ hnorm
    simpa [hcard, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hHd
  have hRα : 0 ≤ condPetzRenyiDown (1 + β) ρ :=
    condRenyiPetz_nonneg_of_cq (1 + β) hα1 hα2 ρ hnorm
  have hR2 : 0 ≤ condPetzRenyiDown 2 ρ :=
    condRenyiPetz_nonneg_of_cq 2 (by norm_num) (by norm_num) ρ hnorm
  have hEα : condVonNeumann ρ - condPetzRenyiDown (1 + β) ρ ≤ 1 :=
    (sub_le_self _ hRα).trans hH1
  have hE2 : condVonNeumann ρ - condPetzRenyiDown 2 ρ ≤ 1 :=
    (sub_le_self _ hR2).trans hH1
  have hdenβ : 0 < 1 - β := sub_pos.mpr hβ1
  have hB2 : (2 : ℝ) ^ (β * (condVonNeumann ρ - condPetzRenyiDown (1 + β) ρ))
      ≤ (2 : ℝ) ^ β := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa using mul_le_mul_of_nonneg_left hEα hβpos.le
  have harg_pos : (0 : ℝ) < (2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ)
      + Real.exp 2 := by positivity
  have harg_le : (2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ) + Real.exp 2
      ≤ 2 + Real.exp 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hE2
    rw [Real.rpow_one] at h
    exact add_le_add h le_rfl
  have hlog_nn : 0 ≤ Real.log ((2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ)
      + Real.exp 2) :=
    Real.log_nonneg (le_add_of_nonneg_of_le (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.one_le_exp (by norm_num)))
  have hB3 : Real.log ((2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ) + Real.exp 2) ^ 3
      ≤ Real.log (2 + Real.exp 2) ^ 3 :=
    pow_le_pow_left₀ hlog_nn (Real.log_le_log harg_pos harg_le) 3
  rw [secondOrderK, show 1 + β - 1 = β by ring, show 2 - (1 + β) = 1 - β by ring]
  calc (1 / (6 * (1 - β) ^ 3 * Real.log 2))
        * (2 : ℝ) ^ (β * (condVonNeumann ρ - condPetzRenyiDown (1 + β) ρ))
        * Real.log ((2 : ℝ) ^ (condVonNeumann ρ - condPetzRenyiDown 2 ρ) + Real.exp 2) ^ 3
      ≤ (1 / (6 * (1 - β) ^ 3 * Real.log 2)) * (2 : ℝ) ^ β
          * Real.log (2 + Real.exp 2) ^ 3 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB2 (by positivity)) hB3
          (by positivity) (by positivity)
    _ = binarySecondOrderRemainderBound β := by
        unfold binarySecondOrderRemainderBound binarySecondOrderRemainderBase
        field_simp

end InfoTheory.Renyi

end
