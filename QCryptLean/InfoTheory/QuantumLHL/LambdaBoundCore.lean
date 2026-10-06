import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundFourthRoot
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSquaredCollision
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundTwoUniversal
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.UniformOutputBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.Quantum.Operators.InverseSqrt
import Mathlib.Algebra.Order.Chebyshev

/-!
# λ\*-bound core helpers (sub-normalized form) — squared chain and assembly

This file provides the analytic core of the squared-sandwich λ\*-bound chain
(Renner §5.4.3, Tomamichel 2016, Prop 7.1) used by both
`InfoTheory.QuantumLHL.joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda`
(the normalized variant in `LambdaBound.lean`) and
`InfoTheory.QuantumLHL.joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm`
(the sub-normalized variant, hosted here).

The active chain is the **squared chain** (sandwich operator `F := σ⁻¹/⁴`):

  (α-sq)  Per-block squared Cauchy–Schwarz:
           `‖D‖₁² ≤ Tr(σ) · Tr((F·D·F)²)` (`traceNorm_sq_le_trsig_squared`)

  (δ-sq)  Squared 2-universality expansion:
           `∑_z Tr((F·D_z·F)²) ≤ ∑_x Tr((F·ρ_x·F)²)` (`sum_tr_SMzSsq_le_sum_tr_SrhoxSsq`)

  (ε-sq)  Squared feasibility bound:
           `∑_x Tr((F·ρ_x·F)²) ≤ λ\*` (`sum_tr_SrhoxSsq_le_lambda_subNorm`)

  (β)     Outer discrete Jensen (Mathlib `sq_sum_le_card_mul_sum_sq`).

Also present for completeness: the outer chain's α-step
`traceNorm_sq_le_trsig_trSDsqS` and feasibility step
`sum_tr_SrhoxsqS_le_lambda_subNorm`, retained because they are exported by
`LambdaBound.lean`.

The normalized counterparts of the sub-normalized lemmas are obtained as thin
specializations in `LambdaBound.lean`.

## Main statements

Outer chain helpers (present; α and ε only):
- `traceNorm_sq_le_trsig_trSDsqS` (α): Hermitian σ-weighted Cauchy–Schwarz.
- `sum_tr_SrhoxsqS_le_lambda_subNorm` (ε, sub-normalized): feasibility ⇒
  operator bound.

Squared chain (sandwich operator `F := σ⁻¹/⁴`, Renner §5.4.3):
- `traceNorm_sq_le_trsig_squared` (α-sq): `‖D‖₁² ≤ Tr(σ) · Tr((F·D·F)²)`.
- `sum_tr_SMzSsq_le_sum_tr_SrhoxSsq` (δ-sq): `∑_z Tr((F·D_z·F)²) ≤ ∑_x Tr((F·ρ_x·F)²)`.
- `InfoTheory.QuantumLHL.tr_inverseFourthRoot_sandwich_sq_le_of_opLe` (ε-sq per-block):
`Tr((F·ρx·F)²) ≤ t · Tr(ρx)`.
- `sum_tr_SrhoxSsq_le_lambda_subNorm` (ε-sq): `∑_x Tr((F·ρ_x·F)²) ≤ λ\*`.

Assembly:
- `joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm`: full
  sub-normalized assembly delivering `∑_z ‖M_z − N_z‖₁ ≤ √(|Z| · λ\*)`.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Step (α): per-block σ⁻¹/² Cauchy–Schwarz (sandwich form).**

For any Hermitian `D : Op n` and positive-definite reference `σ`, with
`S := σ⁻¹/²`,

  `‖D‖₁² ≤ Tr(σ) · Tr(S · D · D · S)`.

This is the direct Hermitian specialization of
`traceNorm_sq_le_sandwich_trace`: substituting `D† = D` into the
general CS inequality `‖D‖₁² ≤ Tr(σ) · Tr(S · D · D† · S)` yields the RHS
`Tr(S · D · D · S) = Tr(σ⁻¹ · D²)` (by cyclicity).  This is the quadratic form
it is *not* the `Tr((S · D · S)²)` ("true `E²`") form — the two quantities differ
by an extra `σ⁻¹` sitting between the two `D` factors and are not universally
ordered.  This lemma is retained for API completeness; the active assembly uses
the squared chain (`traceNorm_sq_le_trsig_squared`).

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37 (Renner σ-weighted CS). -/
lemma traceNorm_sq_le_trsig_trSDsqS
    {n : ℕ} [NeZero n]
    {σ : Op n} (hσ : σ.PosDef) {D : Op n} (hD : D.IsHermitian) :
    (Quantum.Metrics.traceNorm D) ^ 2 ≤
      σ.trace.re *
        (hσ.inverseSqrt * D * D * hσ.inverseSqrt).trace.re := by
  have h := traceNorm_sq_le_sandwich_trace hσ D
  rwa [hD.eq] at h


/-- **Hermitianness of the per-block difference `M_z − (1/|Z|) • ρ_A`.**

The per-block extractor weighting `M_z := extractorWeightedOp H ρ z` is Hermitian
by construction (it is the `toOp` field of `extractorConditionedOp`, whose
`isHermitian` field closes the obligation). The uniform-output block
`(1/|Z|) • ρ.quantumMarginalOp` is a real scalar multiple of a Hermitian
operator (`ρ.quantumMarginalOp_isHermitian`), and a real scalar on ℂ is
self-adjoint. Combining via `Matrix.IsHermitian.sub` gives the result. -/
lemma extractorWeighted_sub_uniform_isHermitian
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : CQState X n) (z : Z) :
    (extractorWeightedOp H ρ z -
        (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp).IsHermitian := by
  have hM : (extractorWeightedOp H ρ z).IsHermitian :=
    (extractorConditionedOp H ρ z).isHermitian
  have hsa : IsSelfAdjoint ((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ)) :=
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hN : ((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp).IsHermitian := by
    change ((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp).conjTranspose =
      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp
    rw [Matrix.conjTranspose_smul, hsa, ρ.quantumMarginalOp_isHermitian]
  exact Matrix.IsHermitian.sub hM hN

-- ===== SQUARED-SANDWICH CHAIN (Renner §5.4.3) =====

/-- Hilbert-Schmidt bound for the polar-unitary factor in the squared-sandwich
Cauchy-Schwarz step.  If `F = σ^{-1/4}` and `P = F⁻¹`, then
`‖P U P‖₂² ≤ Tr(σ)` for every unitary `U`. -/
private lemma inverseFourthRoot_unitary_hs_trace_le
    {n : ℕ} [NeZero n]
    {σ : Op n} (hσ : σ.PosDef) (U : UnitaryOp n) :
    (((hσ.inverseFourthRoot)⁻¹ * U.toOp * (hσ.inverseFourthRoot)⁻¹) *
        (((hσ.inverseFourthRoot)⁻¹ * U.toOp *
          (hσ.inverseFourthRoot)⁻¹).conjTranspose)).trace.re ≤
      σ.trace.re := by
  set F : Op n := hσ.inverseFourthRoot
  set P : Op n := F⁻¹
  set C : Op n := P * P
  set Y : Op n := U.toOp * C * U.toOp.conjTranspose
  -- `F σ^{1/2} F = 1` exhibits the left inverse `F σ^{1/2}` of `F`
  have hF_unit : IsUnit F :=
    IsUnit.of_mul_eq_one_right _ hσ.inverseFourthRoot_sandwich_sigmaSqrt
  have hF_det : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF_unit
  have hFP : F * P = 1 := Matrix.mul_nonsing_inv F hF_det
  have hPF : P * F = 1 := Matrix.nonsing_inv_mul F hF_det
  have hP_herm : P.IsHermitian := hσ.inverseFourthRoot_isHermitian.inv
  -- `C = P P = P Pᴴ` is positive semidefinite
  have hC_psd : C.PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose P
    rwa [hP_herm.eq] at h
  have hC_herm : C.IsHermitian := hC_psd.isHermitian
  -- `C² = σ`: sandwich `F² σ F² = σ^{-1/2} σ σ^{-1/2} = 1` between two copies of `P² = F⁻²`
  have hC_sq : C * C = σ := by
    have hG : F * F * σ * (F * F) = 1 := by
      rw [hσ.inverseFourthRoot_sq]
      exact hσ.inverseSqrt_sandwich_eq_one
    calc C * C = (P * P) * (F * F * σ * (F * F)) * (P * P) := by rw [hG, Matrix.mul_one]
      _ = (P * (P * F) * F) * σ * (F * (F * P) * P) := by simp only [Matrix.mul_assoc]
      _ = σ := by
        rw [hPF, hFP, Matrix.mul_one, Matrix.mul_one, hPF, hFP, Matrix.one_mul, Matrix.mul_one]
  have hAA_trace :
      (((hσ.inverseFourthRoot)⁻¹ * U.toOp * (hσ.inverseFourthRoot)⁻¹) *
          (((hσ.inverseFourthRoot)⁻¹ * U.toOp *
            (hσ.inverseFourthRoot)⁻¹).conjTranspose)).trace =
        (C * Y).trace := by
    calc ((P * U.toOp * P) * (P * U.toOp * P).conjTranspose).trace
        = ((P * U.toOp * P) * (P * U.toOp.conjTranspose * P)).trace := by
            simp only [Matrix.conjTranspose_mul, hP_herm.eq, Matrix.mul_assoc]
      _ = (P * (U.toOp * C * U.toOp.conjTranspose) * P).trace := by
            simp only [C, Matrix.mul_assoc]
      _ = (C * Y).trace := by
            rw [Matrix.trace_mul_cycle P (U.toOp * C * U.toOp.conjTranspose) P]
  have hY_trace :
      (Y.conjTranspose * Y).trace.re = (C * C).trace.re := by
    have hY_conj : Y.conjTranspose = Y := by
      change (U.toOp * C * U.toOp.conjTranspose).conjTranspose = U.toOp * C * U.toOp.conjTranspose
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hC_herm.eq, ← Matrix.mul_assoc]
    rw [hY_conj]
    have htrace : (Y * Y).trace = (C * C).trace := by
      calc (Y * Y).trace
          = ((U.toOp * C * U.toOp.conjTranspose) *
              (U.toOp * C * U.toOp.conjTranspose)).trace := rfl
        _ = (U.toOp * C * (U.toOp.conjTranspose * U.toOp) *
              C * U.toOp.conjTranspose).trace := by
              simp only [Matrix.mul_assoc]
        _ = (U.toOp * C * 1 * C * U.toOp.conjTranspose).trace := by
              rw [U.unitary_left]
        _ = (U.toOp * (C * C) * U.toOp.conjTranspose).trace := by
              simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (U.toOp.conjTranspose * U.toOp * (C * C)).trace := by
              rw [Matrix.trace_mul_cycle U.toOp (C * C) U.toOp.conjTranspose]
        _ = (C * C).trace := by rw [U.unitary_left, Matrix.one_mul]
    exact congrArg Complex.re htrace
  have hHS := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose C Y
  have hHS' :
      ‖(C * Y).trace‖ ^ 2 ≤ (C * C).trace.re ^ 2 := by
    rwa [hC_herm.eq, hY_trace, ← sq] at hHS
  have hT_nn : 0 ≤ (C * C).trace.re := by
    rw [hC_sq]
    exact hσ.posSemidef.trace_re_nonneg
  have hnorm_le : ‖(C * Y).trace‖ ≤ (C * C).trace.re :=
    le_of_sq_le_sq hHS' hT_nn
  have hre_le_norm : (C * Y).trace.re ≤ ‖(C * Y).trace‖ :=
    (le_abs_self (C * Y).trace.re).trans (Complex.abs_re_le_norm (C * Y).trace)
  calc (((hσ.inverseFourthRoot)⁻¹ * U.toOp * (hσ.inverseFourthRoot)⁻¹) *
          (((hσ.inverseFourthRoot)⁻¹ * U.toOp *
            (hσ.inverseFourthRoot)⁻¹).conjTranspose)).trace.re
      = (C * Y).trace.re := congrArg Complex.re hAA_trace
    _ ≤ ‖(C * Y).trace‖ := hre_le_norm
    _ ≤ (C * C).trace.re := hnorm_le
    _ = σ.trace.re := by rw [hC_sq]

/-- **Step (α-sq): squared-sandwich Cauchy–Schwarz (Renner Lemma 5.1.3).**

For Hermitian `D : Op n` and positive-definite `σ`, with `F := hσ.inverseFourthRoot`:

  `‖D‖₁² ≤ Tr(σ) · ((F·D·F)·(F·D·F)).trace.re`.

Proof route (Renner thesis Lemma 5.1.3): Write D = σ^{1/4} · M · σ^{1/4} where
M := F · D · F (so M is Hermitian since D is). Polar decomposition: D = U · |D|.
Then `‖D‖₁ = Re Tr(U* · D) = Re Tr(σ^{1/4} · U* · σ^{1/4} · M)` (cyclicity).
HS Cauchy–Schwarz: `‖D‖₁ ≤ ‖σ^{1/4} · U* · σ^{1/4}‖_F · ‖M‖_F`.
Squared: `‖D‖₁² ≤ ‖σ^{1/4} · U* · σ^{1/4}‖²_F · ‖M‖²_F`.
- `‖M‖²_F = Tr(M*·M) = Tr(M²)` (M Hermitian).
- `‖σ^{1/4} · U* · σ^{1/4}‖²_F = Tr(σ^{1/2} · U · σ^{1/2} · U*)`. Since U is unitary,
  the singular values of `σ^{1/2}·U` equal those of `σ^{1/2}`, so
  `Tr(σ^{1/2} · U · σ^{1/2} · U*) ≤ Tr(σ)` (unitary invariance and PSD trace bounds).
Combining: `‖D‖₁² ≤ Tr(σ) · Tr(M²) = Tr(σ) · Tr((F·D·F)²)`.
Reference: Renner thesis §5.1, Lemma 5.1.3. -/
lemma traceNorm_sq_le_trsig_squared
    {n : ℕ} [NeZero n]
    {σ : Op n} (hσ : σ.PosDef) {D : Op n} (hD : D.IsHermitian) :
    (Quantum.Metrics.traceNorm D) ^ 2 ≤
      σ.trace.re *
        ((hσ.inverseFourthRoot * D * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * D * hσ.inverseFourthRoot)).trace.re := by
  classical
  set F : Op n := hσ.inverseFourthRoot with hF_def
  set P : Op n := F⁻¹ with hP_def
  have hF_herm : F.IsHermitian := hσ.inverseFourthRoot_isHermitian
  -- `F σ^{1/2} F = 1` exhibits the left inverse `F σ^{1/2}` of `F`
  have hF_unit : IsUnit F :=
    IsUnit.of_mul_eq_one_right _ hσ.inverseFourthRoot_sandwich_sigmaSqrt
  have hF_det : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF_unit
  have hFP : F * P = 1 := Matrix.mul_nonsing_inv F hF_det
  have hPF : P * F = 1 := Matrix.nonsing_inv_mul F hF_det
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose
      D.conjTranspose
  rw [show D.conjTranspose.conjTranspose = D from Matrix.conjTranspose_conjTranspose D] at hU
  have h_norm_eq : Quantum.Metrics.traceNorm D = (U.toOp * D.conjTranspose).trace.re := by
    rw [hU, ← Quantum.Metrics.traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul D]
  have h_norm_eqD : Quantum.Metrics.traceNorm D = (U.toOp * D).trace.re := by
    rwa [hD.eq] at h_norm_eq
  set A : Op n := P * U.toOp * P with hA_def
  set B : Op n := F * D * F with hB_def
  have h_trace_rewrite : (U.toOp * D).trace = (A * B).trace := by
    symm
    calc (A * B).trace
        = (P * U.toOp * P * (F * D * F)).trace := by rw [hA_def, hB_def]
      _ = (P * U.toOp * D * F).trace := by
            -- the inner `P F` cancels
            simp only [← Matrix.mul_assoc]
            rw [Matrix.mul_assoc (P * U.toOp) P F, hPF, Matrix.mul_one]
      _ = (F * (P * U.toOp) * D).trace := Matrix.trace_mul_cycle (P * U.toOp) D F
      _ = (U.toOp * D).trace := by
            rw [← Matrix.mul_assoc, hFP, Matrix.one_mul]
  have hB_herm : B.IsHermitian := by
    change (F * D * F).conjTranspose = F * D * F
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF_herm.eq, hD.eq, Matrix.mul_assoc]
  have hAA_le : (A * A.conjTranspose).trace.re ≤ σ.trace.re :=
    inverseFourthRoot_unitary_hs_trace_le hσ U
  have hBB_nonneg : 0 ≤ (B.conjTranspose * B).trace.re :=
    (Matrix.posSemidef_conjTranspose_mul_self B).trace_re_nonneg
  have hCS := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose A B
  have h_re_sq_le_norm_sq :
      ((U.toOp * D).trace.re) ^ 2 ≤ ‖(U.toOp * D).trace‖ ^ 2 := by
    have habs := Complex.abs_re_le_norm (U.toOp * D).trace
    have h_sq : ((U.toOp * D).trace.re) ^ 2 =
        |((U.toOp * D).trace.re)| ^ 2 := by rw [sq_abs]
    rw [h_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc Quantum.Metrics.traceNorm D ^ 2
      = ((U.toOp * D).trace.re) ^ 2 := by rw [h_norm_eqD]
    _ ≤ ‖(U.toOp * D).trace‖ ^ 2 := h_re_sq_le_norm_sq
    _ = ‖(A * B).trace‖ ^ 2 := by rw [h_trace_rewrite]
    _ ≤ (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re := hCS
    _ ≤ σ.trace.re * (B.conjTranspose * B).trace.re :=
        mul_le_mul_of_nonneg_right hAA_le hBB_nonneg
    _ = σ.trace.re * (B * B).trace.re := by rw [hB_herm.eq]
    _ = σ.trace.re *
          ((hσ.inverseFourthRoot * D * hσ.inverseFourthRoot) *
            (hσ.inverseFourthRoot * D * hσ.inverseFourthRoot)).trace.re := rfl

/-- **Squared centering identity.**

For operators `S`, `R`, and `M : Z → Op n` with `∑_z M z = R`, with `c = 1/|Z|`:

  `∑_z ((S·(M_z − c·R)·S) * (S·(M_z − c·R)·S)).trace.re
       = (∑_z ((S·M_z·S) * (S·M_z·S)).trace.re) − c · ((S·R·S)·(S·R·S)).trace.re`.

Pure algebra; squared-sandwich analogue of `sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_uniform`.
Proof: expand `S·(M_z − c·R)·S = (S·M_z·S) − c·(S·R·S)`, use bilinearity of trace,
and `∑_z (S·M_z·S) = S·R·S`. -/
lemma sum_tr_SMzSsq_centering
    {Z : Type*} [Fintype Z] {n : ℕ}
    (S R : Op n) (M : Z → Op n) (hSumM : ∑ z, M z = R) :
    ∑ z : Z, ((S * (M z - (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • R) * S) *
              (S * (M z - (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • R) * S)).trace.re =
    (∑ z : Z, ((S * M z * S) * (S * M z * S)).trace.re) -
      ((1 : ℝ) / (Fintype.card Z : ℝ)) * ((S * R * S) * (S * R * S)).trace.re := by
  classical
  let N : Z → Op n := fun z => S * M z * S
  let Q : Op n := S * R * S
  have hSumN : (∑ z : Z, N z) = Q := by
    dsimp [N, Q]
    calc
      (∑ z : Z, S * M z * S) = (∑ z : Z, S * M z) * S := by
        rw [Finset.sum_mul]
      _ = S * (∑ z : Z, M z) * S := by
        rw [← Matrix.mul_sum]
      _ = S * R * S := by
        rw [hSumM]
  have h := sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_uniform (1 : Op n) Q N hSumN
  simpa [N, Q, Matrix.one_mul, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul] using h

/-- **K_sq kernel non-negativity for PSD operators.**

For Hermitian `S` and PSD `A, B`:
`((S * A * S) * (S * B * S)).trace.re ≥ 0`.

Proof: `S·A·S` and `S·B·S` are PSD (Hermitian sandwich of PSD). Then the
conclusion is `tr_prod_sandwich_re_nonneg` instantiated at T = 1 with factors
`S·A·S` and `S·B·S`. -/
lemma tr_SMzSsq_nonneg_of_psd
    {n : ℕ} {S : Op n} (hS : S.IsHermitian)
    {A B : Op n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((S * A * S) * (S * B * S)).trace.re := by
  have hS_cT : S.conjTranspose = S := hS.eq
  have hSAS_psd : (S * A * S).PosSemidef := by
    rw [show S * A * S = S.conjTranspose * A * S from by rw [hS_cT]]
    exact hA.conjTranspose_mul_mul_same S
  have hSBS_psd : (S * B * S).PosSemidef := by
    rw [show S * B * S = S.conjTranspose * B * S from by rw [hS_cT]]
    exact hB.conjTranspose_mul_mul_same S
  have h1 : (1 : Op n).IsHermitian := Matrix.isHermitian_one
  -- Use tr_prod_sandwich_re_nonneg with T = 1: ((1·P·1)·(1·Q·1)).trace.re = (P·Q).trace.re
  have := tr_prod_sandwich_re_nonneg h1 hSAS_psd hSBS_psd
  simpa using this

/-- **Bilinearity of K_sq: full pair sum equals sandwiched marginal square.**

For operator `S` and family `R : X → Op n`:
`∑_x ∑_{x'} ((S·R_x·S) * (S·R_{x'}·S)).trace.re = ((S·(∑_x R_x)·S) * (S·(∑_x R_x)·S)).trace.re`.

Proof: expand sums using bilinearity of matrix multiplication and linearity of trace. -/
lemma sum_pair_tr_SMzSsq_eq_marginal_sq
    {X : Type*} [Fintype X] {n : ℕ} (S : Op n) (R : X → Op n) :
    ∑ x : X, ∑ x' : X, ((S * R x * S) * (S * R x' * S)).trace.re =
    ((S * (∑ x : X, R x) * S) * (S * (∑ x : X, R x) * S)).trace.re := by
  have h := sum_pair_tr_S_RR_S_eq_marginal_sq
    (1 : Op n) (fun x : X => S * R x * S)
  have hsum : (∑ x : X, S * R x * S) = S * (∑ x : X, R x) * S := by
    rw [← Finset.sum_mul, ← Matrix.mul_sum]
  simpa [hsum, Matrix.one_mul, Matrix.mul_one] using h

/-- **Step (δ-sq): squared-sandwich 2-universality expansion.**

With `M_z := extractorWeightedOp H ρ z`, `D_z := M_z − (1/|Z|)·ρ_A`,
`F := hσ.inverseFourthRoot`:

  `∑_z ((F·D_z·F)·(F·D_z·F)).trace.re ≤ ∑_x ((F·ρ_x·F)·(F·ρ_x·F)).trace.re`.

Proof chain:
1. `sum_tr_SMzSsq_centering`: `∑_z K_sq(D_z) = ∑_z K_sq(M_z) − c·K_sq(ρ_A)`.
2. Jensen via `tr_smul_avg_sq_re_le_avg_tr_sq_re` applied to `s ↦ F * E s z * F`:
   `∑_z K_sq(M_z) ≤ (1/|Seed|)·∑_s ∑_z K_sq(E_{s,z})`.
3. Per-seed collision identity `per_seed_collision_identity_single` + bilinearity of trace:
   `(1/|Seed|)·∑_s ∑_z K_sq(E_{s,z}) = ∑_{x,x'} τ(x,x')·K_sq(ρ_x, ρ_{x'})`.
4. Split diagonal/off-diagonal + 2-universality (`quantumHash_offdiag_weighted_sum_nonpos`)
   + non-negativity of K_sq for PSD ρ_x (`tr_SMzSsq_nonneg_of_psd`)
   + `sum_pair_tr_SMzSsq_eq_marginal_sq`:
   `∑_{x,x'} τ(x,x')·K_sq(ρ_x, ρ_{x'}) ≤ ∑_x K_sq(ρ_x) + c·K_sq(ρ_A)`.
5. Cancellation: `∑_z K_sq(D_z) ≤ ∑_x K_sq(ρ_x)`.

Reference: Renner §5.4.3, eq. (5.7). -/
lemma sum_tr_SMzSsq_le_sum_tr_SrhoxSsq
    {Seed X Z : Type*} [Fintype Seed] [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ}
    (H : QuantumHashFamily Seed X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    {σ : Op n} (hσ : σ.PosDef) :
    ∑ z : Z,
        ((hσ.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseFourthRoot)).trace.re ≤
    ∑ x : X,
        ((hσ.inverseFourthRoot * (ρ.stateMap x).toOp * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * (ρ.stateMap x).toOp * hσ.inverseFourthRoot)).trace.re := by
  classical
  have hSumM : ∑ z : Z, extractorWeightedOp H ρ z = ρ.quantumMarginalOp :=
    sum_extractorWeightedOp_eq_quantumMarginalOp H ρ
  have hExpand :
      (∑ z : Z,
        ((hσ.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseFourthRoot)).trace.re) =
      (∑ z : Z,
        ((hσ.inverseFourthRoot * extractorWeightedOp H ρ z * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * extractorWeightedOp H ρ z *
            hσ.inverseFourthRoot)).trace.re) -
      ((1 : ℝ) / (Fintype.card Z : ℝ)) *
        ((hσ.inverseFourthRoot * ρ.quantumMarginalOp * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * ρ.quantumMarginalOp *
            hσ.inverseFourthRoot)).trace.re :=
    sum_tr_SMzSsq_centering
      hσ.inverseFourthRoot ρ.quantumMarginalOp
      (fun z : Z => extractorWeightedOp H ρ z) hSumM
  have hF_herm : hσ.inverseFourthRoot.IsHermitian :=
    hσ.inverseFourthRoot_isHermitian
  have hJensen :=
    sum_tr_SMzSsq_le_seed_avg_collision_sum
      hσ.inverseFourthRoot hF_herm H ρ
  have hCombined :=
    InfoTheory.QuantumLHL.seed_avg_collision_sum_sq_le_diag_plus_c_marginalSq_algebra
      hσ.inverseFourthRoot hF_herm H hH ρ
  have hM_le :
      (∑ z : Z,
        ((hσ.inverseFourthRoot * extractorWeightedOp H ρ z * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * extractorWeightedOp H ρ z *
            hσ.inverseFourthRoot)).trace.re) ≤
      (∑ x : X,
        ((hσ.inverseFourthRoot * (ρ.stateMap x).toOp * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * (ρ.stateMap x).toOp *
            hσ.inverseFourthRoot)).trace.re) +
      ((1 : ℝ) / (Fintype.card Z : ℝ)) *
        ((hσ.inverseFourthRoot * ρ.quantumMarginalOp * hσ.inverseFourthRoot) *
          (hσ.inverseFourthRoot * ρ.quantumMarginalOp *
            hσ.inverseFourthRoot)).trace.re :=
    hJensen.trans hCombined
  rw [hExpand]
  linarith [hM_le]

/-- **Step (ε-sq, sub-normalized): squared-sandwich feasibility-to-trace bound.**

If `isFeasible ρ σ t`, then
`∑_x ((F·ρ_x·F)·(F·ρ_x·F)).trace.re ≤ t` where `F := hσ_pd.inverseFourthRoot`.
Follows from `InfoTheory.QuantumLHL.tr_inverseFourthRoot_sandwich_sq_le_of_opLe` + sub-normalization
`Tr(ρ_A) ≤ 1`. -/
lemma sum_tr_SrhoxSsq_le_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    {t : ℝ} (ht : isFeasible ρ σ t) :
    ∑ x : X,
        ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot) *
          (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot)).trace.re
      ≤ t := by
  obtain ⟨ht_nn, ht_dom⟩ := ht
  have h_per : ∀ x : X,
      ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot) *
        (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot)).trace.re ≤
        t * (ρ.stateMap x).toOp.trace.re := fun x =>
    InfoTheory.QuantumLHL.tr_inverseFourthRoot_sandwich_sq_le_of_opLe hσ_pd
      (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
      (ht_dom x)
  have h_marg : ∑ x : X, (ρ.stateMap x).toOp.trace.re = ρ.quantumMarginalOp.trace.re := by
    unfold CQState.quantumMarginalOp; rw [Matrix.trace_sum, Complex.re_sum]
  calc ∑ x : X,
          ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot) *
            (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot)).trace.re
      ≤ ∑ x : X, t * (ρ.stateMap x).toOp.trace.re :=
          Finset.sum_le_sum (fun x _ => h_per x)
    _ = t * ∑ x : X, (ρ.stateMap x).toOp.trace.re := by rw [← Finset.mul_sum]
    _ = t * ρ.quantumMarginalOp.trace.re := by rw [h_marg]
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left ρ.quantumMarginalOp_trace_le_one ht_nn
    _ = t := mul_one t

/-- **Step (ε-sq): squared-sandwich λ* bound (sub-normalized).**

`∑_x ((F·ρ_x·F)·(F·ρ_x·F)).trace.re ≤ minFeasibleLambda ρ σ` where
`F := hσ_pd.inverseFourthRoot`.
Squared-sandwich analogue of `sum_tr_SrhoxsqS_le_lambda_subNorm`. -/
lemma sum_tr_SrhoxSsq_le_lambda_subNorm
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda ρ σ) :
    ∑ x : X,
        ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot) *
          (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp * hσ_pd.inverseFourthRoot)).trace.re
      ≤ minFeasibleLambda ρ σ := by
  obtain ⟨t₀, ht₀⟩ := hfeas
  unfold minFeasibleLambda
  refine le_csInf ⟨t₀, ht₀⟩ ?_
  intro t ht
  exact sum_tr_SrhoxSsq_le_of_isFeasible ρ σ hσ_pd ht

/-- **Trace cyclicity helper**: `Tr(σ · (S · ρx · S)) = Tr(ρx)` when
`S := σ^(−1/2)` so that `S · σ · S = 1`. -/
lemma tr_sigma_SrhoS_eq_tr_rho
    {n : ℕ} {σ : Matrix (Fin n) (Fin n) ℂ} (hσ_pd : σ.PosDef)
    (ρx : Matrix (Fin n) (Fin n) ℂ) :
    (σ * (hσ_pd.inverseSqrt * ρx * hσ_pd.inverseSqrt)).trace = ρx.trace := by
  set S := hσ_pd.inverseSqrt
  have hSand : S * σ * S = 1 := hσ_pd.inverseSqrt_sandwich_eq_one
  have step1 : σ * (S * ρx * S) = (σ * S) * (ρx * S) := by noncomm_ring
  have step2 : (ρx * S) * (σ * S) = ρx * (S * σ * S) := by noncomm_ring
  calc (σ * (S * ρx * S)).trace
      = ((σ * S) * (ρx * S)).trace := by rw [step1]
    _ = ((ρx * S) * (σ * S)).trace := Matrix.trace_mul_comm _ _
    _ = (ρx * (S * σ * S)).trace := by rw [step2]
    _ = (ρx * 1).trace := by rw [hSand]
    _ = ρx.trace := by rw [Matrix.mul_one]

/-- **Trace cyclicity helper**: `Tr(σ · B · B) = Tr(S · ρx² · S)` when
`B = S · ρx · S` with `S := σ^(−1/2)`, using `S · σ · S = 1`. -/
lemma tr_sigma_SrhoS_SrhoS_eq_tr_SrhoxsqS
    {n : ℕ} {σ : Matrix (Fin n) (Fin n) ℂ} (hσ_pd : σ.PosDef)
    (ρx : Matrix (Fin n) (Fin n) ℂ) :
    (σ * ((hσ_pd.inverseSqrt * ρx * hσ_pd.inverseSqrt) *
          (hσ_pd.inverseSqrt * ρx * hσ_pd.inverseSqrt))).trace =
      (hσ_pd.inverseSqrt * ρx * ρx * hσ_pd.inverseSqrt).trace := by
  set S := hσ_pd.inverseSqrt
  have hSand : S * σ * S = 1 := hσ_pd.inverseSqrt_sandwich_eq_one
  -- Use trace cyclicity: Tr(σ * (S*ρx*S) * (S*ρx*S)) = Tr((S*ρx*S) * σ * (S*ρx*S))
  have step_cycle : (σ * ((S * ρx * S) * (S * ρx * S))).trace =
      ((S * ρx * S) * σ * (S * ρx * S)).trace := by
    rw [← Matrix.mul_assoc σ (S * ρx * S) (S * ρx * S)]
    exact Matrix.trace_mul_cycle σ (S * ρx * S) (S * ρx * S)
  -- Simplify (S*ρx*S) * σ * (S*ρx*S) = S * ρx * (S*σ*S) * ρx * S = S * ρx * ρx * S
  have step_simplify : (S * ρx * S) * σ * (S * ρx * S) = S * ρx * ρx * S := by
    have eq1 : (S * ρx * S) * σ * (S * ρx * S) =
        (S * ρx) * (S * σ * S) * (ρx * S) := by noncomm_ring
    rw [eq1, hSand]
    noncomm_ring
  rw [step_cycle, step_simplify]

/-- **Helper 1 — Per-block feasibility-to-trace bound.**

If `ρx` is PSD and `ρx ≤ t·σ` in the Löwner order, then
`Tr(σ⁻¹ · ρx²) = Tr(S · ρx² · S) ≤ t · Tr(ρx)`.

Proof strategy: set `B := S · ρx · S`. From the sandwich identity,
`opLe B (t · I)`, then `opLe (B·B) (t · B)`. Apply PSD-weighted trace
monotonicity with weight `σ` to get `Tr(σ · B²) ≤ Tr(σ · t·B)`, then convert
both sides using trace cyclicity. -/
lemma tr_SrhoxsqS_le_of_opLe
    {n : ℕ} {σ : Matrix (Fin n) (Fin n) ℂ} (hσ_pd : σ.PosDef)
    {ρx : Matrix (Fin n) (Fin n) ℂ} (hρx : ρx.PosSemidef)
    {t : ℝ} (h : opLe ρx (Complex.ofReal t • σ)) :
    (hσ_pd.inverseSqrt * ρx * ρx * hσ_pd.inverseSqrt).trace.re
      ≤ t * ρx.trace.re := by
  set S := hσ_pd.inverseSqrt
  set B : Matrix (Fin n) (Fin n) ℂ := S * ρx * S
  have hS_herm : S.IsHermitian := hσ_pd.inverseSqrt_isHermitian
  have hS_conj : S.conjTranspose = S := hS_herm.eq
  -- PSD of B
  have hB_psd : B.PosSemidef := by
    have h1 := hρx.conjTranspose_mul_mul_same S
    rw [hS_conj] at h1
    exact h1
  have hB_herm : B.IsHermitian := hB_psd.isHermitian
  -- Feasibility of sandwich: opLe B (t • 1)
  have hopLe_B_t1 : opLe B (Complex.ofReal t • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
    hσ_pd.inverseSqrt_sandwich_of_opLe h
  -- Squaring: opLe (B * B) (t • B)
  have hBB_opLe : opLe (B * B) (Complex.ofReal t • B) :=
    sq_opLe_smul_of_opLe_smul_one hB_psd hopLe_B_t1
  -- Hermitianity of B*B and t•B
  have hBB_herm : (B * B).IsHermitian := by
    change (B * B).conjTranspose = B * B
    rw [Matrix.conjTranspose_mul, hB_herm.eq]
  have ht_sa : IsSelfAdjoint (Complex.ofReal t : ℂ) := by
    change star (Complex.ofReal t) = Complex.ofReal t
    rw [Complex.star_def, Complex.conj_ofReal]
  have htB_herm : (Complex.ofReal t • B).IsHermitian := ht_sa.smul hB_herm
  -- Apply PSD-weighted trace monotonicity with weight σ
  have hσ_psd : σ.PosSemidef := hσ_pd.posSemidef
  have htrace : (σ * (B * B)).trace.re ≤ (σ * (Complex.ofReal t • B)).trace.re :=
    trace_mul_le_of_opLe hσ_psd hBB_herm htB_herm hBB_opLe
  -- Convert RHS: (σ * (t • B)).trace.re = t * ρx.trace.re
  have hRHS : (σ * (Complex.ofReal t • B)).trace.re = t * ρx.trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    change (σ * (S * ρx * S)).trace.re = ρx.trace.re
    rw [tr_sigma_SrhoS_eq_tr_rho hσ_pd ρx]
  -- Convert LHS: (σ * (B * B)).trace.re = (S * ρx * ρx * S).trace.re
  have hLHS : (σ * (B * B)).trace.re = (S * ρx * ρx * S).trace.re := by
    change (σ * ((S * ρx * S) * (S * ρx * S))).trace.re =
      (S * ρx * ρx * S).trace.re
    rw [tr_sigma_SrhoS_SrhoS_eq_tr_SrhoxsqS hσ_pd ρx]
  rw [hLHS, hRHS] at htrace
  exact htrace

/-- **Helper 2 — Summed feasibility-to-trace bound.**

For every feasible `t` (`isFeasible ρ σ t`), summing the per-block bound from
`tr_SrhoxsqS_le_of_opLe` and using sub-normalization `Tr(ρ_A) ≤ 1` with `t ≥ 0`
yields `∑_x Tr(S · ρ_A(x)² · S) ≤ t`. -/
lemma sum_tr_SrhoxsqS_le_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    {t : ℝ} (ht : isFeasible ρ σ t) :
    ∑ x : X,
        (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re ≤ t := by
  obtain ⟨ht_nn, ht_dom⟩ := ht
  -- Per-block bound via Helper 1.
  have h_per : ∀ x : X,
      (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
          (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re ≤
        t * (ρ.stateMap x).toOp.trace.re := by
    intro x
    have hρx_psd : ((ρ.stateMap x).toOp).PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
    exact tr_SrhoxsqS_le_of_opLe hσ_pd hρx_psd (ht_dom x)
  -- Trace of marginal equals the sum of block traces.
  have h_marg : ∑ x : X, (ρ.stateMap x).toOp.trace.re = ρ.quantumMarginalOp.trace.re := by
    unfold CQState.quantumMarginalOp
    rw [Matrix.trace_sum, Complex.re_sum]
  calc ∑ x : X,
          (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re
      ≤ ∑ x : X, t * (ρ.stateMap x).toOp.trace.re :=
        Finset.sum_le_sum (fun x _ => h_per x)
    _ = t * ∑ x : X, (ρ.stateMap x).toOp.trace.re := by rw [← Finset.mul_sum]
    _ = t * ρ.quantumMarginalOp.trace.re := by rw [h_marg]
    _ ≤ t * 1 :=
        mul_le_mul_of_nonneg_left ρ.quantumMarginalOp_trace_le_one ht_nn
    _ = t := mul_one t

/-- **Step (ε) — sub-normalized variant: feasibility-to-operator-bound.**

Sub-normalized counterpart of
`InfoTheory.QuantumLHL.sum_tr_SrhoxsqS_le_lambda` (in `LambdaBound.lean`), which
is stated for `NormalizedCQState`. The input `ρ` is an arbitrary `CQState X n`
(its marginal may have trace strictly less than `1`).

Proof sketch: feasibility gives `ρ_A(x) ≤ λ*·σ` in the Löwner order, hence
`Tr(σ⁻¹ ρ_A(x)²) ≤ λ* · Tr(ρ_A(x))`. Summing over `x` and using the
sub-normalization bound `∑_x Tr(ρ_A(x)) = Tr(ρ_A) ≤ 1` with `λ* ≥ 0` closes the
bound.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.41 (sub-normalized form). -/
lemma sum_tr_SrhoxsqS_le_lambda_subNorm
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda ρ σ) :
    ∑ x : X,
        (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re ≤
      minFeasibleLambda ρ σ := by
  obtain ⟨t₀, ht₀⟩ := hfeas
  unfold minFeasibleLambda
  refine le_csInf ⟨t₀, ht₀⟩ ?_
  intro t ht
  exact sum_tr_SrhoxsqS_le_of_isFeasible ρ σ hσ_pd ht

/-- **Sub-normalized assembly of the per-block trace norms (Prop 7.1, eq. 7.37–7.41).**

Sub-normalized counterpart of
`InfoTheory.QuantumLHL.joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda`
(which is stated for `NormalizedCQState`). Here the input `ρ` is an arbitrary
CQ state.

Starting from the per-block trace-norm factorization
(`cqState_joint_traceNorm_eq_sum_blocks`), combining the α/β/δ steps of the
σ⁻¹/² Cauchy–Schwarz + 2-universality + Jensen chain with the sub-normalized
feasibility operator bound yields:

  `∑_z ‖M_z − N_z‖₁ ≤ √(|Z| · minFeasibleLambda ρ σ)`

where `M_z = extractorWeightedOp H ρ z` and
`N_z = (1/|Z|) • ρ.quantumMarginalOp`.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37–7.41 (sub-normalized form). -/
lemma joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm
    {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda ρ σ) :
    ∑ z : Z, Quantum.Metrics.traceNorm
        (((extractorOutputState H ρ).stateMap z).toOp -
          ((uniformOutputState ρ.quantumMarginal : CQState Z n).stateMap z).toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * minFeasibleLambda ρ σ) := by
  -- Named real-arithmetic ingredients.
  set lam := minFeasibleLambda ρ σ
  have hlam_nn : 0 ≤ lam := minFeasibleLambda_nonneg ρ σ
  have hσtr_nn : (0 : ℝ) ≤ σ.toOp.trace.re := σ.trace_nonneg
  have hσtr_le : σ.toOp.trace.re ≤ 1 := σ.trace_le_one
  have hcardZ_nn : (0 : ℝ) ≤ (Fintype.card Z : ℝ) := Nat.cast_nonneg _
  -- Per-block trace-norm, exactly matching the goal's summand after the
  -- uniform-output rewrite.
  let a : Z → ℝ := fun z =>
    Quantum.Metrics.traceNorm
      (extractorWeightedOp H ρ z -
        (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp)
  -- Bridge the two cast forms of the uniform scalar `1 / |Z|` (as produced by
  -- `uniformOutput_stateMap_toOp` vs. the one used in `a` and the α/δ steps).
  have hsc : ((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ) =
      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) := by
    push_cast; ring
  have h_block_eq :
      ∑ z : Z, Quantum.Metrics.traceNorm
          (((extractorOutputState H ρ).stateMap z).toOp -
            ((uniformOutputState ρ.quantumMarginal : CQState Z n).stateMap z).toOp) =
        ∑ z : Z, a z := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    show Quantum.Metrics.traceNorm
        (((extractorOutputState H ρ).stateMap z).toOp -
          ((uniformOutputState ρ.quantumMarginal : CQState Z n).stateMap z).toOp) = a z
    rw [uniformOutput_stateMap_toOp, hsc]
    rfl
  rw [h_block_eq]
  -- Each per-block difference is Hermitian.
  have h_herm : ∀ z : Z, (extractorWeightedOp H ρ z -
      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp).IsHermitian :=
    fun z => extractorWeighted_sub_uniform_isHermitian H ρ z
  -- α-sq (per-block squared Cauchy–Schwarz).
  have h_alpha : ∀ z : Z, (a z) ^ 2 ≤
      σ.toOp.trace.re *
        ((hσ_pd.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ_pd.inverseFourthRoot) *
          (hσ_pd.inverseFourthRoot *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ_pd.inverseFourthRoot)).trace.re :=
    fun z => traceNorm_sq_le_trsig_squared hσ_pd (h_herm z)
  -- δ-sq (squared 2-universality expansion) and ε-sq (squared feasibility bound).
  have h_delta := sum_tr_SMzSsq_le_sum_tr_SrhoxSsq H hH ρ hσ_pd
  have h_epsilon := sum_tr_SrhoxSsq_le_lambda_subNorm ρ σ hσ_pd hfeas
  -- Chain α-sq + δ-sq + ε-sq + σ.trace.re ≤ 1 into ∑ a_z² ≤ λ*.
  have h_sum_sq_le_lam : (∑ z : Z, (a z) ^ 2) ≤ lam := by
    calc (∑ z : Z, (a z) ^ 2)
        ≤ ∑ z : Z, σ.toOp.trace.re *
            ((hσ_pd.inverseFourthRoot *
                (extractorWeightedOp H ρ z -
                  (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                hσ_pd.inverseFourthRoot) *
              (hσ_pd.inverseFourthRoot *
                (extractorWeightedOp H ρ z -
                  (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                hσ_pd.inverseFourthRoot)).trace.re :=
          Finset.sum_le_sum (fun z _ => h_alpha z)
      _ = σ.toOp.trace.re *
            ∑ z : Z,
              ((hσ_pd.inverseFourthRoot *
                  (extractorWeightedOp H ρ z -
                    (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                  hσ_pd.inverseFourthRoot) *
                (hσ_pd.inverseFourthRoot *
                  (extractorWeightedOp H ρ z -
                    (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                  hσ_pd.inverseFourthRoot)).trace.re := by
          rw [← Finset.mul_sum]
      _ ≤ σ.toOp.trace.re *
            ∑ x : X,
              ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp *
                    hσ_pd.inverseFourthRoot) *
                (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp *
                    hσ_pd.inverseFourthRoot)).trace.re :=
          mul_le_mul_of_nonneg_left h_delta hσtr_nn
      _ ≤ σ.toOp.trace.re * lam :=
          mul_le_mul_of_nonneg_left h_epsilon hσtr_nn
      _ ≤ 1 * lam := mul_le_mul_of_nonneg_right hσtr_le hlam_nn
      _ = lam := one_mul lam
  -- β (Jensen) and sqrt monotonicity.
  have h_card_sum_sq : (∑ z : Z, a z) ^ 2 ≤
      (Fintype.card Z : ℝ) * ∑ z : Z, (a z) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Z)) (f := a)
    simpa [Finset.card_univ] using h
  have h_sum_sq : (∑ z : Z, a z) ^ 2 ≤ (Fintype.card Z : ℝ) * lam :=
    h_card_sum_sq.trans (mul_le_mul_of_nonneg_left h_sum_sq_le_lam hcardZ_nn)
  exact Real.le_sqrt_of_sq_le h_sum_sq

end InfoTheory.QuantumLHL

end -- noncomputable section
