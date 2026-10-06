import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy

/-!
# λ\*-bound — min-entropy ↔ λ\* conversion (sub-normalized side condition)

This file hosts the auxiliary conversion lemma
`minFeasibleLambda_le_pow_neg_k_subNorm`, which turns a conditional min-entropy
lower bound `k ≤ H_min(ρ|σ)` (together with the side condition `λ\* ≤ 1`) into
the operator inequality `λ\* ≤ 2^{-k}` driving the LHL bound.

This is the only declaration that does not belong to the squared-chain assembly;
the assembly itself (`joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm`
and its helpers) lives in `LambdaBoundCore.lean`, and the normalized counterpart
in `LambdaBound.lean`.

This conversion lemma is used by both
`InfoTheory.QuantumLHL.extractorDistance_le_of_minEntropy` (in `Main.lean`) and
`InfoTheory.QuantumLHL.quantum_LHL_subNormalized` (in
`SmoothingSideConditions.lean`).

## Main statements

- `minFeasibleLambda_le_pow_neg_k_subNorm`: under `λ\* ≤ 1` and
  `ENNReal.ofReal k ≤ H_min(ρ|σ)`, one has `λ\* ≤ 2^{-k}`.

Reference: Tomamichel 2016, Def 6.2 / Prop 7.1 hypothesis.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Min-entropy to λ conversion.**

If `minFeasibleLambda ρ σ ≤ 1` and the conditional min-entropy is at least `k`,
then `minFeasibleLambda ρ σ ≤ 2 ^ (-k)`.

Proof: split on whether `λ* = minFeasibleLambda ρ σ` is positive. If `λ* > 0`,
`conditionalMinEntropy ρ σ = ENNReal.ofReal (conditionalMinEntropyReal ρ σ)`
and `k ≤ conditionalMinEntropyReal ρ σ = −log₂(λ*)` gives `λ* ≤ 2^{−k}`. If
`λ* = 0`, the conclusion reduces to `0 ≤ 2^{−k}`, which is immediate. No
feasibility hypothesis is required; the `λ* = 0` branch is handled directly.

Used by both `InfoTheory.QuantumLHL.extractorDistance_le_of_minEntropy` (in `Main.lean`) and
`InfoTheory.QuantumLHL.quantum_LHL_subNormalized` (in
`SmoothingSideConditions.lean`).

Reference: Tomamichel 2016, Def 6.2 / Prop 7.1 hypothesis. -/
lemma minFeasibleLambda_le_pow_neg_k_subNorm
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hlam_le_one : minFeasibleLambda ρ σ ≤ 1)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    minFeasibleLambda ρ σ ≤ 2 ^ (-k) := by
  set lam := minFeasibleLambda ρ σ
  have hlam_nn : 0 ≤ lam := minFeasibleLambda_nonneg ρ σ
  by_cases hpos : 0 < lam
  · have hcme : conditionalMinEntropy ρ σ =
        ENNReal.ofReal (conditionalMinEntropyReal ρ σ) := by
      unfold conditionalMinEntropy
      rw [if_pos hpos]
    rw [hcme] at hk
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog_le : Real.log lam ≤ 0 := Real.log_nonpos hlam_nn hlam_le_one
    have hH_nn : 0 ≤ conditionalMinEntropyReal ρ σ := by
      unfold conditionalMinEntropyReal
      have : 0 ≤ -Real.log lam := by linarith
      exact div_nonneg this (le_of_lt hlog2)
    by_cases hk_sign : k ≤ 0
    · have h_neg_k : 0 ≤ -k := by linarith
      have h_one_le : (1 : ℝ) ≤ (2 : ℝ) ^ (-k) := by
        have := (Real.rpow_le_rpow_left_iff (x := (2:ℝ)) one_lt_two).mpr h_neg_k
        simpa [Real.rpow_zero] using this
      linarith
    · push Not at hk_sign
      have hk_le_H : k ≤ conditionalMinEntropyReal ρ σ :=
        (ENNReal.ofReal_le_ofReal_iff hH_nn).mp hk
      have hH_def : conditionalMinEntropyReal ρ σ =
          -Real.log lam / Real.log 2 := rfl
      rw [hH_def] at hk_le_H
      have hk_mul : k * Real.log 2 ≤ -Real.log lam :=
        (le_div_iff₀ hlog2).mp hk_le_H
      have hlog_le2 : Real.log lam ≤ -k * Real.log 2 := by linarith
      have hlog_rpow : Real.log ((2 : ℝ) ^ (-k)) = -k * Real.log 2 :=
        Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-k)
      have hrpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-k) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h_log_le : Real.log lam ≤ Real.log ((2 : ℝ) ^ (-k)) := by
        rw [hlog_rpow]; exact hlog_le2
      exact (Real.log_le_log_iff hpos hrpow_pos).mp h_log_le
  · push Not at hpos
    have hzero : lam = 0 := le_antisymm hpos hlam_nn
    rw [hzero]
    exact Real.rpow_nonneg (by norm_num) _

end InfoTheory.QuantumLHL

end -- noncomputable section
