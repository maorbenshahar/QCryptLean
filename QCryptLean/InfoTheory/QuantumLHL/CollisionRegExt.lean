import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyDirect
import QCryptLean.InfoTheory.QuantumLHL.UniformOutputBlock
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarseningTraceDistance
import QCryptLean.InfoTheory.QuantumLHL.ExtractorContractivity
import QCryptLean.InfoTheory.QuantumLHL.GeneralRefLHL
import QCryptLean.Quantum.TensorProducts.Rpow
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct

/-!
# Register-extension collision identity and the seed-extractor trace-distance bridge

Two endpoints of the low-QBER kept-block collision leftover-hash route
(RT arXiv:2603.04493 Lemma 12 / Renner arXiv:quant-ph/0512258v2 §5.5).

## Definitions

`weightedFrobeniusSq` and `collisionQuantity` are the σ-weighted Hilbert–Schmidt
square and the collision quantity `Γ = 2^{-H₂(X|E)_{ρ|σ}}` (Renner §6.5); both are
imported from the InfoTheory.QuantumLHL.GeneralRefLHL module (the symmetric `4-2-4` form
`weightedFrobeniusSq σ A = ‖σ^{-1/4} A σ^{-1/4}‖_F²`, which for positive-definite `σ`
equals the one-sided sandwich `Re Tr(Aᴴ · σ^{-1/2} · A · σ^{-1/2})` by cyclicity of
the trace).  Using the single shared definition keeps the L1 general-reference LHL
bound (`GeneralRefLHL.lean`) and the (★) identity below on the same `collisionQuantity`.

## Main statements

* `collisionQuantity_regExt_pure_eq` (★): for the register-extended
  reference `σE ⊗ (I_V/dV)` and per-outcome **rank-≤1** blocks with `partialTraceB`
  marginals `ρE`, the EV-level collision quantity collapses to a sum over outcomes of
  squared traces of the **marginal** blocks against `σE^{-1/2}`, with the `V` register
  entering only through the scalar `dV`.  The ambient positive-semidefiniteness of each
  block (structural, from `CQState.stateMap : X → SubDensityOp`, `SubDensityOp` extends
  `PosSemidefOp`) combined with `hpure` (rank ≤ 1) is load-bearing: the identity is
  *false* for non-Hermitian rank-1 blocks.
* `seedKeyExtractor_traceDistanceGen_eq_half_offDiag`: the seed-visible
  extractor trace distance equals one-half the seed-averaged off-diagonal trace-norm LHS,
  by block-additivity of the trace norm over the `(s,z)` seed×key register.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan arXiv:2403.11851 Thm 3 (App. B, B13–B19); RT
arXiv:2603.04493 Lem 12;
Renner arXiv:quant-ph/0512258v2 §5.5–5.6.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Arithmetic collapse for a family with at most one nonzero entry:
`∑ᵢ f(i)² = (∑ᵢ f(i))²`.  The single (or zero) nonzero term makes the cross terms of the
square vanish.  Used with the eigenvalue family of a rank-≤1 operator. -/
theorem collisionRegExt_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h_supp : Fintype.card {i // f i ≠ 0} ≤ 1) :
    ∑ i, (f i) ^ 2 = (∑ i, f i) ^ 2 := by
  classical
  have hsub : Subsingleton {i // f i ≠ 0} :=
    Fintype.card_le_one_iff_subsingleton.mp h_supp
  by_cases hall : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hall
    have h_others : ∀ i, f i ≠ 0 → i = j := by
      intro i hi
      have heq : (⟨i, hi⟩ : {k // f k ≠ 0}) = ⟨j, hj⟩ := Subsingleton.elim _ _
      exact (Subtype.mk.injEq _ _ _ _).mp heq
    have h1 : ∑ i, (f i) ^ 2 = (f j) ^ 2 := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun h => absurd (Finset.mem_univ j) h)
      have hi0 : f i = 0 := by by_contra hfi; exact hij (h_others i hfi)
      rw [hi0]; ring
    have h2 : ∑ i, f i = f j := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun h => absurd (Finset.mem_univ j) h)
      by_contra hfi; exact hij (h_others i hfi)
    rw [h1, h2]
  · push Not at hall; simp [hall]

/-- **Rank-≤1 PSD trace-square collapse.** For a positive-semidefinite operator `B` of rank
≤ 1, `Re Tr(B²) = (Re Tr B)²`.  Proof: `B` has at most one nonzero eigenvalue, so its
eigenvalue power sums satisfy `∑ λᵢ² = (∑ λᵢ)²` (`collisionRegExt_sum_sq`), and both traces
are the corresponding power sums (`trace_pow_eq_sum_eigenvalues_pow`). -/
theorem collisionRegExt_trace_sq_of_rank_le_one {n : ℕ} (B : Op n)
    (hB : B.PosSemidef) (hrank : B.rank ≤ 1) :
    (B * B).trace.re = (B.trace.re) ^ 2 := by
  have hHerm := hB.isHermitian
  have hsupp : Fintype.card {i // hHerm.eigenvalues i ≠ 0} ≤ 1 := by
    rw [← Matrix.IsHermitian.rank_eq_card_non_zero_eigs hHerm]; exact hrank
  have h1 : B.trace.re = ∑ i, hHerm.eigenvalues i := by
    rw [hHerm.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => Complex.ofReal_re _)
  have h2 : (B * B).trace.re = ∑ i, (hHerm.eigenvalues i) ^ 2 := by
    rw [← pow_two, Math.SpectralTheory.trace_pow_eq_sum_eigenvalues_pow B hHerm 2,
      Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [h1, h2]
  exact collisionRegExt_sum_sq _ hsupp

/-- The `NNReal`-algebra map into `Op n` is the scalar-multiple-of-identity. -/
theorem collisionRegExt_algebraMapNNReal_eq_smul {n : ℕ} (t : NNReal) :
    algebraMap NNReal (Op n) t = ((t : ℝ) : ℂ) • (1 : Op n) := by
  rw [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, ← Complex.coe_smul]

/-- **Real power of a scalar-multiple of the identity.** For `0 ≤ c`,
`((c) • 1) ^ y = (c ^ y) • 1` (continuous functional calculus on a scalar operator). -/
theorem collisionRegExt_scalar_rpow {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (y : ℝ) :
    ((c : ℂ) • (1 : Op n)) ^ y = ((c ^ y : ℝ) : ℂ) • (1 : Op n) := by
  have hc' : ((c.toNNReal : ℝ) : ℂ) = (c : ℂ) := by rw [Real.coe_toNNReal c hc]
  rw [← hc', ← collisionRegExt_algebraMapNNReal_eq_smul, CFC.rpow_algebraMap,
    collisionRegExt_algebraMapNNReal_eq_smul, NNReal.coe_rpow, Real.coe_toNNReal c hc]

/-- **`σ^(−1/2)` is the CFC inverse square root.** For positive-definite `σ`,
`hσ.inverseSqrt = σ ^ (−1/2)` (bridge between the `PosDef.inverseSqrt` construction and the
`CFC.rpow` used by `weightedFrobeniusSq`). -/
theorem collisionRegExt_inverseSqrt_eq_rpow {n : ℕ} {σ : Op n} (hσ : σ.PosDef) :
    hσ.inverseSqrt = σ ^ (-1/2 : ℝ) := by
  obtain ⟨u, hu_eq⟩ := hσ.isUnit
  rw [Matrix.PosDef.inverseSqrt, CFC.sqrt_eq_rpow, ← hu_eq, ← Matrix.coe_units_inv u,
    ← CFC.rpow_neg u (1/2) (by rw [hu_eq]; exact hσ.posSemidef.nonneg)]
  norm_num

/-- **`(I_V/dV)^(−1/2) = √dV · I_V`.** The max-mixed reference on `V` raised to `−1/2`. -/
theorem collisionRegExt_maxMixed_rpow_neg_half {dV : ℕ} [NeZero dV] :
    ((1 / (dV : ℂ)) • (1 : Op dV)) ^ (-1/2 : ℝ)
      = (((dV : ℝ) ^ (1/2 : ℝ) : ℝ) : ℂ) • (1 : Op dV) := by
  have hcast : (1 / (dV : ℂ)) = (((1 / dV : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, collisionRegExt_scalar_rpow _ (by positivity)]
  have hval : ((1 / (dV : ℝ)) ^ (-1/2 : ℝ)) = (dV : ℝ) ^ (1/2 : ℝ) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    norm_num
  rw [hval]

/-- **Partial-trace adjoint against `X ⊗ 1`.** `Tr[(X ⊗ 1_V) · A] = Tr[X · Tr_V A]`, tracing
out the second (`V`) factor.  Follows from `partialTraceB_sandwich_tensor_one` with `B = 1`. -/
theorem collisionRegExt_trace_tensor_one_mul {dE dV : ℕ} (X : Op dE) (A : Op (dE * dV)) :
    ((X ⊗ (1 : Op dV)) * A).trace = (X * partialTraceB A).trace := by
  rw [← trace_partialTraceB ((X ⊗ (1 : Op dV)) * A)]
  congr 1
  calc partialTraceB ((X ⊗ (1 : Op dV)) * A)
      = partialTraceB ((X ⊗ (1 : Op dV)) * A * ((1 : Op dE) ⊗ (1 : Op dV))) := by
        rw [Op.tensor_one, Matrix.mul_one]
    _ = X * partialTraceB A * (1 : Op dE) :=
        partialTraceB_sandwich_tensor_one X 1 A
    _ = X * partialTraceB A := by rw [Matrix.mul_one]

/-- **Per-block register-extension collision reduction (the core of (★)).**  For a
positive-definite `σE` and a **positive-semidefinite rank-≤1** block `A` on `E ⊗ V`,
the `σE ⊗ (I_V/dV)`-weighted Hilbert–Schmidt square of `A` collapses to
`dV · (Re Tr[σE^{-1/2} · Tr_V A])²`, the `V` register entering only through the scalar `dV`.

The rank-≤1 + ambient-PSD hypotheses are load-bearing: they force
`Re Tr(B²) = (Re Tr B)²` for `B = σ^{-1/4} A σ^{-1/4}`
(`collisionRegExt_trace_sq_of_rank_le_one`); the tensor factorization of `σ^{-1/2}` and the
partial-trace adjoint (`collisionRegExt_trace_tensor_one_mul`) drop the `V` register to `dV`. -/
theorem weightedFrobeniusSq_regExt {dE dV : ℕ} [NeZero dV]
    (σE : Op dE) (hσE : σE.PosDef) (A : Op (dE * dV))
    (hA : A.PosSemidef) (hrank : A.rank ≤ 1) :
    weightedFrobeniusSq (σE ⊗ ((1 / (dV : ℂ)) • (1 : Op dV))) A
      = (dV : ℝ) * ((hσE.inverseSqrt * partialTraceB A).trace.re) ^ 2 := by
  set M : Op dV := (1 / (dV : ℂ)) • (1 : Op dV) with hM_def
  have hM : M.PosDef := (Matrix.PosDef.one).smul (a := 1 / ((dV : ℕ) : ℂ))
    (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero dV))))
  set σ : Op (dE * dV) := σE ⊗ M with hσ_def
  have hσ : σ.PosDef := by
    rw [hσ_def]; unfold Quantum.TensorProducts.Op.tensor
    rw [Matrix.reindex_apply]
    exact (Matrix.PosDef.kronecker hσE hM).submatrix_equiv finProdFinEquiv.symm
  have hσE_nn : (0 : Op dE) ≤ σE := Matrix.nonneg_iff_posSemidef.mpr hσE.posSemidef
  have hM_nn : (0 : Op dV) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  set F : Op (dE * dV) := σ ^ (-1/4 : ℝ) with hF_def
  have hF_psd : F.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hF_herm : Fᴴ = F := hF_psd.isHermitian.eq
  have hA_herm : Aᴴ = A := hA.isHermitian.eq
  set B : Op (dE * dV) := F * A * F with hB_def
  have hB_herm : Bᴴ = B := by
    rw [hB_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF_herm, hA_herm,
      Matrix.mul_assoc]
  have hB_psd : B.PosSemidef := by
    rw [hB_def]
    have h := hA.mul_mul_conjTranspose_same F
    rwa [hF_herm] at h
  have hB_rank : B.rank ≤ 1 := by
    rw [hB_def]
    calc ((F * A) * F).rank ≤ (F * A).rank :=
          le_trans (Matrix.rank_mul_le _ _) (min_le_left _ _)
      _ ≤ A.rank := le_trans (Matrix.rank_mul_le _ _) (min_le_right _ _)
      _ ≤ 1 := hrank
  have hWF : weightedFrobeniusSq σ A = (B * B).trace.re := by
    rw [weightedFrobeniusSq, ← hF_def, ← hB_def, hB_herm]
  have hFF : F * F = σ ^ (-1/2 : ℝ) := by
    rw [hF_def, ← CFC.rpow_add hσ.isUnit, show (-1/4 + -1/4 : ℝ) = -1/2 from by norm_num]
  set c : ℝ := (dV : ℝ) ^ (1/2 : ℝ) with hc_def
  have hBtr : B.trace = (c : ℂ) * (hσE.inverseSqrt * partialTraceB A).trace := by
    rw [hB_def, Matrix.trace_mul_comm (F * A) F, ← Matrix.mul_assoc, hFF, hσ_def,
      Op.tensor_rpow σE M hσE_nn hM_nn (-1/2), hM_def, collisionRegExt_maxMixed_rpow_neg_half,
      Op.tensor_smul_right, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul,
      collisionRegExt_trace_tensor_one_mul, ← collisionRegExt_inverseSqrt_eq_rpow hσE, hc_def]
  rw [hWF, collisionRegExt_trace_sq_of_rank_le_one B hB_psd hB_rank, hBtr,
    Complex.re_ofReal_mul, mul_pow]
  have hc_sq : c ^ 2 = (dV : ℝ) := by
    rw [hc_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  rw [hc_sq]

/-- **(★) — the register-extension collision identity.**

For a positive-definite reference `σE` on the `E` register, a CQ state `ρEV` on
`E ⊗ V` whose every per-outcome block is **rank ≤ 1** (`hpure`) with `partialTraceB`
marginal equal to the `E`-block `ρE` (`hmarg`), the EV-level collision quantity at the
register-extended reference `σE ⊗ (I_V / dV)` collapses to

  `collisionQuantity (σE ⊗ (1/dV)•I) (ρEV.stateMap ·).toOp
      = dV · ∑ x, (Re Tr(σE^{-1/2} · ρE.stateMap x))²`,

carrying **no** `E⊗V` operator on the right-hand side — the `V` register enters only
through the scalar `dV`.

The identity is *false* for non-Hermitian rank-1 blocks `|u⟩⟨v|`; it holds because each
block is ambient positive-semidefinite (structural, from
`CQState.stateMap : X → SubDensityOp`, `SubDensityOp` extends `PosSemidefOp`) *and* rank
≤ 1, which together force `c·|ψ⟩⟨ψ|` with `c ≥ 0`.  Tensor orientation: the `V = B`
factor is the second factor, traced by `partialTraceB : Op (dE * dV) → Op dE`, matching
the Nahar et al. B13 usage.

Nahar et al. arXiv:2403.11851 App. B; Watrous *TQI* §2.2 (sub-operators of a rank-1
projector). -/
theorem collisionQuantity_regExt_pure_eq {X : Type*} [Fintype X] {dE dV : ℕ}
    (σE : Op dE) (hσ : σE.PosDef) (ρEV : CQState X (dE * dV)) (ρE : CQState X dE)
    (hpure : ∀ x, ((ρEV.stateMap x).toOp).rank ≤ 1)
    (hmarg : ∀ x, Quantum.TensorProducts.partialTraceB (ρEV.stateMap x).toOp
      = (ρE.stateMap x).toOp) :
    collisionQuantity (σE ⊗ ((1 / (dV : ℂ)) • (1 : Op dV)))
        (fun x => (ρEV.stateMap x).toOp)
      = (dV : ℝ) * ∑ x, ((hσ.inverseSqrt * (ρE.stateMap x).toOp).trace.re) ^ 2 := by
  rcases Nat.eq_zero_or_pos dV with hdV | hdV
  · subst hdV
    have hzero : ∀ (Y : Op (dE * 0)), Y.trace = 0 := by
      intro Y
      simp only [Matrix.trace, Matrix.diag]
      apply Finset.sum_eq_zero
      intro i _
      exact absurd i.2 (by simp)
    rw [collisionQuantity]
    have hlhs : ∑ x, weightedFrobeniusSq (σE ⊗ ((1 / ((0 : ℕ) : ℂ)) • (1 : Op 0)))
        ((ρEV.stateMap x).toOp) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [weightedFrobeniusSq, hzero]
      simp
    rw [hlhs]
    simp
  · haveI : NeZero dV := ⟨hdV.ne'⟩
    rw [collisionQuantity, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [weightedFrobeniusSq_regExt σE hσ _
      (posSemidefOp_implies_mathlib (ρEV.stateMap x).toPosSemidefOp) (hpure x), hmarg x]

/-- **The seed-extractor trace-distance bridge.**

The seed-visible extractor output state and the seed-visible uniform target state are
both block-diagonal over the `(s, z)` seed×key classical register.  Hence their
generalized trace distance equals one-half the seed-averaged off-diagonal trace-norm
LHS of the leftover-hash lemma:

  `traceDistanceGen (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedUniformOutputState ρ.quantumMarginal).toJointDensity.toOp
    = ½ · (1/|S|) · ∑_{s,z} ‖ (∑_{x : hash s x = z} ρ.stateMap x)
                              − (1/|Z|) · ρ.quantumMarginalOp ‖₁`.

The `|Tr − Tr|` half of `traceDistanceGen` vanishes because the two joint densities have
equal trace (both marginals equal `ρ.quantumMarginalOp`); the trace-norm half factors
through `traceNorm_joint_diff_eq_sum` (block-additivity over `S × Z`).

The `[DecidableEq S]` instance is required for the `.toJointDensity` of the `S × Z`
classical register (`CQState.toJointDensity` needs `DecidableEq (S × Z)`); it is a
well-formedness instance present in every consumer and does not alter the content.

RT arXiv:2603.04493
Lem 12. -/
theorem seedKeyExtractor_traceDistanceGen_eq_half_offDiag {S X Z : Type*}
    [Fintype S] [Nonempty S] [DecidableEq S]
    [Fintype X] [DecidableEq X] [Fintype Z] [Nonempty Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) ρ.quantumMarginal).toJointDensity.toOp
      = (1 / 2) * (1 / (Fintype.card S : ℝ)) * ∑ s, ∑ z,
          Quantum.Metrics.traceNorm
            ((∑ x, if H.hash s x = z then (ρ.stateMap x).toOp else 0)
              - (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginalOp) := by
  -- The `|Tr − Tr|` half of the generalized trace distance vanishes: both joint
  -- densities have real trace equal to `ρ.quantumMarginal.trace`.
  have htrace :
      ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp.trace
          - (seedUniformOutputState (S := S) (Z := Z)
              ρ.quantumMarginal).toJointDensity.toOp.trace).re
        = 0 := by
    rw [Complex.sub_re,
      seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace H ρ,
      seedUniformOutputState_joint_trace_eq_quantumMarginal_trace (S := S) (Z := Z)
        ρ.quantumMarginal]
    ring
  -- Per-block factorization of the trace-norm difference.
  have hblock : ∀ sz : S × Z,
      Quantum.Metrics.traceNorm
          (((seedKeyExtractorOutputState H ρ).stateMap sz).toOp
            - ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp)
        = (1 / (Fintype.card S : ℝ)) *
            Quantum.Metrics.traceNorm
              ((∑ x, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0)
                - (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginalOp) := by
    intro sz
    have hcast : (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ)
        = ((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hconv : (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp
        = (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginalOp := by
      rw [hcast, Complex.coe_smul]
    rw [seed_visible_stateMap_sub_uniform_toOp_eq (S := S) (Z := Z) H ρ sz, hconv,
      traceNorm_real_smul, abs_of_nonneg (by positivity)]
  haveI : Nonempty (S × Z) := inferInstance
  rw [Quantum.Metrics.traceDistanceGen, htrace, abs_zero, mul_zero, add_zero]
  rw [traceNorm_joint_diff_eq_sum (seedKeyExtractorOutputState H ρ)
      (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal)]
  rw [Finset.sum_congr rfl (fun sz _ => hblock sz), ← Finset.mul_sum,
    Fintype.sum_prod_type]
  ring

/-- The collision quantity is nonnegative (a sum of `weightedFrobeniusSq`, each `≥ 0`). -/
theorem collisionQuantity_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (σ : Op n) (V : X → Op n) : 0 ≤ collisionQuantity σ V :=
  Finset.sum_nonneg fun x _ => weightedFrobeniusSq_nonneg σ (V x)

/-- **P1 net — the general-reference
collision leftover-hash bound at the extractor level.**

Composes the P1c bridge (`seedKeyExtractor_traceDistanceGen_eq_half_offDiag`) with the L1
general-reference off-diagonal bound
(`QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le_genRef`,
`GeneralRefLHL.lean`): the seed-visible extractor trace distance from the ideal
seed-uniform output is at most `½·√(Tr σ · |Z| · (1 − 1/|Z|) · Γ)`, `Γ = collisionQuantity
σ V`, carrying **no** `√dimE` max-mixed factor (RT arXiv:2603.04493 Lem 12 / Renner §5.5).

The two sums align because `CQState.quantumMarginalOp ρ = ∑ x, (ρ.stateMap x).toOp`
definitionally. -/
theorem seedKeyExtractor_traceDistanceGen_le_collisionRoot {S X Z : Type*}
    [Fintype S] [Nonempty S] [DecidableEq S]
    [Fintype X] [DecidableEq X] [Fintype Z] [Nonempty Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star)
    (ρ : CQState X n) (σ : Op n) (hσ : σ.PosDef) :
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) ρ.quantumMarginal).toJointDensity.toOp
      ≤ (1 / 2) * Real.sqrt (σ.trace.re * (Fintype.card Z : ℝ)
          * (1 - 1 / (Fintype.card Z : ℝ))
          * collisionQuantity σ (fun x => (ρ.stateMap x).toOp)) := by
  rw [seedKeyExtractor_traceDistanceGen_eq_half_offDiag H ρ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact h2.seedAvg_traceNorm_offDiag_le_genRef σ hσ (fun x => (ρ.stateMap x).toOp)

end InfoTheory.QuantumLHL

end -- noncomputable section
