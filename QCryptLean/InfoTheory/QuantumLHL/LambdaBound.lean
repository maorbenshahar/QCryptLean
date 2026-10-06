import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundCore

/-!
# λ\*-bound — normalized variant — Tomamichel Prop 7.1, eq. 7.37–7.41

This file hosts the normalized counterpart of the analytic λ\*-bound chain
(Tomamichel 2016, Prop 7.1, eq. 7.37–7.41). Each declaration is a thin
specialization of the sub-normalized assembly in `LambdaBoundCore.lean`
along the coercion `NormalizedCQState X n → CQState X n`.

The chain itself (α, δ, ε_subNorm, β) — together with the Cauchy–Schwarz,
2-universality, feasibility, and trace-norm helper lemmas — lives in
`LambdaBoundCore.lean`. The assembly uses the squared chain (`F := σ⁻¹/⁴`) whose δ-step
`sum_tr_SMzSsq_le_sum_tr_SrhoxSsq` is proved without sorry in
`LambdaBoundCore.lean`.

## Main statements

- `sum_tr_SrhoxsqS_le_lambda` (Step ε, normalized): for a normalized CQ state
  `ρ` and feasible `σ`, `∑_x Tr(σ⁻¹/² · ρ_A(x)² · σ⁻¹/²) ≤ λ\*`.
- `joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda` (Steps 2–6, normalized):
  the per-block trace-norm sum `∑_z ‖M_z − N_z‖₁ ≤ √(|Z| · λ\*)`.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37–7.41.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Step (ε): feasibility-to-operator-bound for the normalized CQ case.**

For a normalized CQ state `ρ` (so `Tr(ρ_A) = 1`), a positive-definite reference
`σ` with nonempty feasible set, and `S := σ⁻¹/²`,

  `∑_x Tr(S · ρ_A(x) · ρ_A(x) · S) ≤ minFeasibleLambda ρ σ`.

(Stated in the `S · ·² · S` sandwich form to chain with α/δ, where the running
quadratic is `Tr(σ⁻¹ · ·²)`.)

This is a thin specialization of the sub-normalized variant
`InfoTheory.QuantumLHL.sum_tr_SrhoxsqS_le_lambda_subNorm` (in
`LambdaBoundCore.lean`) along the coercion `NormalizedCQState X n → CQState X n`.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.41. -/
lemma sum_tr_SrhoxsqS_le_lambda
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : NormalizedCQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda (ρ : CQState X n) σ) :
    ∑ x : X,
        (hσ_pd.inverseSqrt * (ρ.toCQState.stateMap x).toOp *
            (ρ.toCQState.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re ≤
      minFeasibleLambda (ρ : CQState X n) σ :=
  sum_tr_SrhoxsqS_le_lambda_subNorm (ρ : CQState X n) σ hσ_pd hfeas

/-- **Steps 2–6 of Prop 7.1 packaged as a single assembly lemma.**

Starting from the per-block trace-norm factorization (Step 1, already proved in
Main.lean as `cqState_joint_traceNorm_eq_sum_blocks`), this lemma combines:
  · `traceNorm_sq_le_trsig_squared` (α-sq: per-block σ⁻¹/⁴ squared CS),
  · `Finset.sq_sum_le_card_mul_sum_sq` (β: outer discrete Jensen),
  · `sum_tr_SMzSsq_le_sum_tr_SrhoxSsq` (δ-sq: squared 2-universality expansion),
  · `sum_tr_SrhoxSsq_le_lambda_subNorm` (ε-sq: squared feasibility operator bound),
  · `SubDensityOp.trace_le_one`,
  · `Real.sqrt_le_sqrt` and `Real.sqrt_sq` (nonneg square-root monotonicity)
into the bound `∑_z ‖M_z − N_z‖₁ ≤ √(|Z| · λ*)`.

This is a thin specialization of the sub-normalized variant
`InfoTheory.QuantumLHL.joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm`
(in `LambdaBoundCore.lean`) along the coercion
`NormalizedCQState X n → CQState X n`.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37–7.41. -/
lemma joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda
    {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : NormalizedCQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda (ρ : CQState X n) σ) :
    ∑ z : Z, Quantum.Metrics.traceNorm
        (((extractorOutputState H (ρ : CQState X n)).stateMap z).toOp -
          ((uniformOutputState ρ.toCQState.quantumMarginal : CQState Z n).stateMap z).toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * minFeasibleLambda (ρ : CQState X n) σ) :=
  joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm
    H hH (ρ : CQState X n) σ hσ_pd hfeas

end InfoTheory.QuantumLHL

end -- noncomputable section
