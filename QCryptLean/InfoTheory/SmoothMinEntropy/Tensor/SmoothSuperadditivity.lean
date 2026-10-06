import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.JointDensityCoherence
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistanceTensor
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistanceReindex

/-!
# Smooth Min-Entropy Tensor Superadditivity — Renner `lem:Hminindaddsmooth`

This file develops Renner thesis Lemma `lem:Hminindaddsmooth` (Renner 2005,
§4.2.2, line 3624), generalizing the non-smooth `lem:HRindadd` (line 2819) to
the smooth conditional min-entropy.

**Statement.**

> Let `ρ_{A B} ∈ N(H_A ⊗ H_B)`, `σ_B ∈ N(H_B)`, similarly
> `ρ_{A' B'}, σ_{B'}`, and let `ε, ε' ≥ 0`. Then
> `Hmin^{ε+ε'}(ρ_{A B} ⊗ ρ_{A' B'} | σ_B ⊗ σ_{B'})
>   ≥ Hmin^ε(ρ_{A B} | σ_B) + Hmin^{ε'}(ρ_{A' B'} | σ_{B'})`.

i.e., smooth conditional min-entropy is **superadditive** under tensor
products of independent states.

## Main definitions
- `CQState.tensor`: the binary tensor product of CQ states, with classical
  register `X × X'` and quantum register of dimension `n * n'`.

## Main statements
- `isFeasible_tensor`: feasibility multiplicativity for the conditional
  min-entropy SDP under tensor products.
- `minFeasibleLambda_tensor_le`: the tensor SDP optimum is at most the product
  of the component optima.
- `conditionalMinEntropyReal_tensor_additivity_le`: Renner `lem:HRindadd`
  (non-smooth tensor additivity) at the level of `conditionalMinEntropyReal`.
- `smoothMinEntropyReal_tensor_superadditivity`: Renner `lem:Hminindaddsmooth`,
  the main smooth tensor superadditivity bound.

**Why we need it.** `lem:Hminindaddsmooth` is cited directly in the proof
of Renner `thm:Renyisym` (line 6118 — symmetric-subspace AEP) which the
BB84 finite-size chain needs in place of the Tomamichel-style
`extensionRadius` step.

**Translation to project framework.**

* The project's `CQState X n` has classical register `X` and quantum
  register of dimension `n`. Renner's `ρ_{A B}` corresponds to a
  CQ state where `A = X` is classical and `B = n` is quantum. The
  reference σ is `SubDensityOp n` on the conditioning register.
* `SubDensityOp.tensor` (`InfoTheory/SmoothMinEntropy/TensorProduct.lean`)
  already supplies the operator-level binary tensor product on `n * m`.
  We extend it to CQ states via `CQState.tensor`, putting the classical
  register product `X × X'` over the quantum register product `n * n'`.
* Each block of the tensor CQ state is the operator tensor of the
  corresponding component blocks: `(stateMap (x, x')) = (ρ.stateMap x) ⊗
  (ρ'.stateMap x')`. Trace multiplicativity (`SubDensityOp.tensor_trace`)
  delivers `weight_le_one` directly.

**Proof strategy** (Renner thesis lines 3639–3672, ~30 lines of math):

1. (Smoothing extraction) For any `ν > 0`, pick `ρ̄_{A B} ∈ B^ε(ρ_{A B})`
   and `ρ̄_{A' B'} ∈ B^{ε'}(ρ_{A' B'})` such that
   `Hmin(ρ̄_{A B}|σ_B) > Hmin^ε(ρ_{A B}|σ_B) - ν` and similarly for
   the primed pair (Tomamichel 6.5; project's `isInSmoothedSetReal`).
2. (Non-smooth additivity, `lem:HRindadd`)
   `Hmin(ρ̄_{A B} ⊗ ρ̄_{A' B'} | σ_B ⊗ σ_{B'})
      = Hmin(ρ̄_{A B}|σ_B) + Hmin(ρ̄_{A' B'}|σ_{B'})`.
   At the SDP level: feasibility of `t · t'` for the tensor follows from
   `(t · σ_B) ⊗ (t' · σ_{B'}) - ρ̄ ⊗ ρ̄'` being PSD whenever each factor's
   slack is PSD; conversely, the tensor optimum factors via partial
   trace.
3. (Triangle on tensor) `‖ρ̄ ⊗ ρ̄' - ρ ⊗ ρ'‖₁ ≤ tr(ρ̄')‖ρ̄ - ρ‖₁ +
   tr(ρ)‖ρ̄' - ρ'‖₁ ≤ tr(ρ ⊗ ρ')(ε + ε')`, so the tensor is in
   `B^{ε+ε'}(ρ ⊗ ρ')`. Project hook: same triangle bound holds at the
   purified-distance level by Tomamichel 3.16.
4. Conclude `Hmin^{ε+ε'}(ρ ⊗ ρ' | σ ⊗ σ') > LHS - 2ν` for every `ν > 0`,
   then take `ν → 0`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A real-scaled PSD operator stays PSD when the scalar is a nonneg real. -/
lemma posSemidef_ofReal_smul {n : ℕ} {A : Op n} (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) : (Complex.ofReal t • A).PosSemidef :=
  Matrix.PosSemidef.smul hA (RCLike.ofReal_nonneg.mpr ht)

/-- Any value strictly above `minFeasibleLambda` is itself feasible (by upward
    closure of the feasibility set, given that the optimum is attained from above). -/
lemma isFeasible_of_minFeasibleLambda_lt {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : SubDensityOp n}
    (hfeas : hasFeasibleLambda ρ σ)
    {α : ℝ} (hα : minFeasibleLambda ρ σ < α) :
    isFeasible ρ σ α := by
  obtain ⟨t, ht⟩ := hfeas
  unfold minFeasibleLambda at hα
  obtain ⟨β, hβ_mem, hβ_lt⟩ :=
    exists_lt_of_csInf_lt ⟨t, ht⟩ hα
  exact isFeasible_mono_t hβ_mem hβ_lt.le

/-- **Multiplicativity of feasible scalars under tensor.** If `t` is feasible for
`(ρ, σ)` and `t'` is feasible for `(ρ', σ')`, then the product `t * t'` is feasible
for the tensor pair `(CQState.tensor ρ ρ', SubDensityOp.tensor σ σ')`.

This is the SDP/feasibility content of Renner's `lem:HRindadd`, the non-smooth
tensor additivity of the min-entropy SDP. -/
lemma isFeasible_tensor {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} {ρ : CQState X n} {ρ' : CQState X' n'}
    {σ : SubDensityOp n} {σ' : SubDensityOp n'} {t t' : ℝ}
    (ht : isFeasible ρ σ t) (ht' : isFeasible ρ' σ' t') :
    isFeasible (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') (t * t') := by
  refine ⟨mul_nonneg ht.1 ht'.1, ?_⟩
  rintro ⟨x, x'⟩
  have hAh : (ρ.stateMap x).toOp.IsHermitian := (ρ.stateMap x).isHermitian
  have hCp : (ρ'.stateMap x').toOp.PosSemidef :=
    posSemidefOp_implies_mathlib (ρ'.stateMap x').toPosSemidefOp
  have hσp : σ.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hσ'p : σ'.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σ'.toPosSemidefOp
  have ht_c : (0 : ℂ) ≤ Complex.ofReal t := Complex.zero_le_real.mpr ht.1
  have ht'_c : (0 : ℂ) ≤ Complex.ofReal t' := Complex.zero_le_real.mpr ht'.1
  have hBp : (Complex.ofReal t • σ.toOp).PosSemidef := hσp.smul ht_c
  have hDp : (Complex.ofReal t' • σ'.toOp).PosSemidef := hσ'p.smul ht'_c
  have hAB : opLe (ρ.stateMap x).toOp (Complex.ofReal t • σ.toOp) := ht.2 x
  have hCD : opLe (ρ'.stateMap x').toOp (Complex.ofReal t' • σ'.toOp) := ht'.2 x'
  have h := opLe_tensor_psd hAh hBp hCp hDp.isHermitian hAB hCD
  rw [Quantum.TensorProducts.Op.smul_tensor_smul, ← Complex.ofReal_mul] at h
  exact h

/-- **Tensor optimum is dominated by the product of optima.** With nonempty
feasibility for both components, the tensor SDP optimum is at most the product
of the component optima. This is the easy direction of Renner's non-smooth
`lem:HRindadd`. -/
lemma minFeasibleLambda_tensor_le {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} (ρ : CQState X n) (ρ' : CQState X' n')
    (σ : SubDensityOp n) (σ' : SubDensityOp n')
    (hfeas : hasFeasibleLambda ρ σ) (hfeas' : hasFeasibleLambda ρ' σ') :
    minFeasibleLambda (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') ≤
      minFeasibleLambda ρ σ * minFeasibleLambda ρ' σ' := by
  set lam1 := minFeasibleLambda ρ σ with hlam1_def
  set lam2 := minFeasibleLambda ρ' σ' with hlam2_def
  have hlam1_nn : 0 ≤ lam1 := minFeasibleLambda_nonneg _ _
  have hlam2_nn : 0 ≤ lam2 := minFeasibleLambda_nonneg _ _
  have hS_ne : (setOf (isFeasible ρ σ)).Nonempty := hfeas
  have hS'_ne : (setOf (isFeasible ρ' σ')).Nonempty := hfeas'
  apply le_of_forall_pos_le_add
  intro ε hε
  -- Pick a small `d > 0` with `d * (lam1 + lam2 + 1) ≤ ε`.
  set d := ε / (lam1 + lam2 + ε + 1) with hd_def
  have hden_pos : 0 < lam1 + lam2 + ε + 1 := by positivity
  have hd_pos : 0 < d := div_pos hε hden_pos
  have hd_le_one : d ≤ 1 := by
    rw [hd_def, div_le_one hden_pos]
    linarith only [hlam1_nn, hlam2_nn]
  -- Get t close to lam1, t' close to lam2.
  have hlam1_lt : lam1 < lam1 + d := lt_add_of_pos_right lam1 hd_pos
  have hlam2_lt : lam2 < lam2 + d := lt_add_of_pos_right lam2 hd_pos
  obtain ⟨t, ht_mem, ht_lt⟩ :=
    exists_lt_of_csInf_lt hS_ne (show lam1 < lam1 + d from hlam1_lt)
  obtain ⟨t', ht'_mem, ht'_lt⟩ :=
    exists_lt_of_csInf_lt hS'_ne (show lam2 < lam2 + d from hlam2_lt)
  have ht_nn : 0 ≤ t := ht_mem.1
  have ht'_nn : 0 ≤ t' := ht'_mem.1
  have ht_feas : isFeasible ρ σ t := ht_mem
  have ht'_feas : isFeasible ρ' σ' t' := ht'_mem
  -- Helper 1: t * t' is feasible for the tensor; csInf bounds.
  have hfeas_tt' : isFeasible (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') (t * t') :=
    isFeasible_tensor ht_feas ht'_feas
  have h_ltensor_le :
      minFeasibleLambda (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') ≤ t * t' :=
    csInf_le (minFeasibleLambda_bddBelow _ _) hfeas_tt'
  -- Bound t * t' by (lam1 + d)(lam2 + d).
  have hlam1d_nn : 0 ≤ lam1 + d := add_nonneg hlam1_nn hd_pos.le
  have htt'_le : t * t' ≤ (lam1 + d) * (lam2 + d) :=
    mul_le_mul ht_lt.le ht'_lt.le ht'_nn hlam1d_nn
  -- Expand and bound the slack by ε.
  have h_slack : d * (lam1 + lam2) + d * d ≤ ε := by
    have hd_sq_le : d * d ≤ d := mul_le_of_le_one_left hd_pos.le hd_le_one
    -- `d·(λ₁+λ₂+1) = ε·(λ₁+λ₂+1)/(λ₁+λ₂+ε+1) ≤ ε`
    have h_step : d * (lam1 + lam2 + 1) ≤ ε := by
      rw [hd_def, div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      exact mul_le_mul_of_nonneg_left (by linarith only [hε]) hε.le
    linarith only [hd_sq_le, h_step]
  have h_expand : (lam1 + d) * (lam2 + d) = lam1 * lam2 + (d * (lam1 + lam2) + d * d) := by ring
  linarith only [h_ltensor_le, htt'_le, h_slack, h_expand]

/-- **Renner `lem:HRindadd` (non-smooth tensor additivity)**, Renner thesis
    line 2819. Conditional min-entropy is additive under the binary tensor
    product of independent states.

    The non-smooth inequality used in the proof of `lem:Hminindaddsmooth`.
    Renner's proof "follows immediately from the definition" — at the
    `conditionalMinEntropyReal` level this is the SDP fact
    `minFeasibleLambda (ρ.tensor ρ') (σ.tensor σ') ≤ minFeasibleLambda ρ σ ·
    minFeasibleLambda ρ' σ'` (`minFeasibleLambda_tensor_le`); the log-rescaling
    turns the product into a sum.

    The statement requires positivity of all three optima. The single-factor
    positivity hypotheses `hλ, hλ'` rule out the `Real.log 0 = 0` sentinel
    behaviour of `conditionalMinEntropyReal` at the boundaries; the tensor
    positivity hypothesis `hλ_tensor` similarly avoids the right-hand-side
    sentinel and lets us apply `Real.log_le_log`. -/
theorem conditionalMinEntropyReal_tensor_additivity_le
    {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ρ : CQState X n) (ρ' : CQState X' n')
    (σ : SubDensityOp n) (σ' : SubDensityOp n')
    (hfeas : hasFeasibleLambda ρ σ) (hfeas' : hasFeasibleLambda ρ' σ')
    (hlam : 0 < minFeasibleLambda ρ σ) (hlam' : 0 < minFeasibleLambda ρ' σ')
    (hlam_tensor :
      0 < minFeasibleLambda (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ')) :
    conditionalMinEntropyReal ρ σ + conditionalMinEntropyReal ρ' σ' ≤
      conditionalMinEntropyReal (CQState.tensor ρ ρ')
        (SubDensityOp.tensor σ σ') := by
  unfold conditionalMinEntropyReal
  set lam1 := minFeasibleLambda ρ σ
  set lam2 := minFeasibleLambda ρ' σ'
  set lamT := minFeasibleLambda (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ')
  have hT_le : lamT ≤ lam1 * lam2 :=
    minFeasibleLambda_tensor_le ρ ρ' σ σ' hfeas hfeas'
  have h12_pos : 0 < lam1 * lam2 := mul_pos hlam hlam'
  have hlog_le : Real.log lamT ≤ Real.log lam1 + Real.log lam2 := by
    have h1 : Real.log lamT ≤ Real.log (lam1 * lam2) :=
      Real.log_le_log hlam_tensor hT_le
    rwa [Real.log_mul hlam.ne' hlam'.ne'] at h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hineq : -(Real.log lam1 + Real.log lam2) ≤ -Real.log lamT := by linarith
  have h_div :
      (-(Real.log lam1 + Real.log lam2)) / Real.log 2 ≤ -Real.log lamT / Real.log 2 :=
    div_le_div_of_nonneg_right hineq hlog2_pos.le
  have hsum :
      -Real.log lam1 / Real.log 2 + -Real.log lam2 / Real.log 2 =
        (-(Real.log lam1 + Real.log lam2)) / Real.log 2 := by ring
  linarith

/-! ### Helpers for the smooth wrapper

Two pieces of analytic infrastructure used by
`smoothMinEntropyReal_tensor_superadditivity`: a tensor-coherence identity for
`toJointDensity` (so that the ε-ball on the tensor CQ-state can be related to
ε-balls on the factors) and the purified-distance triangle/tensor subadditivity
bound (Tomamichel 2016 eq. 3.41). -/

/-- **Purified-distance subadditivity under tensor products** (Tomamichel
    2016, eq. 3.41). The purified distance between operator tensor products
    is bounded above by the sum of factor purified distances. The analytic
    heart of `smoothMinEntropyReal_tensor_superadditivity`. -/
lemma purifiedDistance_tensor_subadditive
    {n n' : ℕ} [NeZero n] [NeZero n']
    (ρ τ : SubDensityOp n) (ρ' τ' : SubDensityOp n') :
    InfoTheory.SmoothMinEntropy.purifiedDistance
        (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') ≤
      InfoTheory.SmoothMinEntropy.purifiedDistance τ ρ +
      InfoTheory.SmoothMinEntropy.purifiedDistance τ' ρ' := by
  -- Mirror `purifiedDistance_triangle`: rewrite each purified distance as
  -- `sin` of the Bures angle, reduce to the Bures-angle subadditivity
  -- `fidelityAngle_tensor_subadditive`, and close with the elementary
  -- `Real.sin_le_sin_add_sin_of_le_add`.
  set α := Real.arccos (fidelityGen τ ρ)
  set β := Real.arccos (fidelityGen τ' ρ')
  set γ := Real.arccos
      (fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ'))
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _,
      Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg τ ρ)⟩
  have hβ_mem : β ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _,
      Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg τ' ρ')⟩
  have hγ_mem : γ ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _,
      Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg _ _)⟩
  have hangle : γ ≤ α + β :=
    fidelityAngle_tensor_subadditive ρ τ ρ' τ'
  have hsin := Real.sin_le_sin_add_sin_of_le_add hα_mem hβ_mem hγ_mem hangle
  rw [purifiedDistance_eq_sin_arccos
        (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ'),
      purifiedDistance_eq_sin_arccos τ ρ,
      purifiedDistance_eq_sin_arccos τ' ρ']
  exact hsin

/-! ### Step-3 helpers: tensor subadditivity at the CQ purified-distance level

The CQ-state purified distance between tensor CQ states is bounded by the sum
of factor distances. This packages two facts:

* the operator-level `purifiedDistance_tensor_subadditive` above (Tomamichel
  2016 eq. 3.41), and
* the unitary/permutation invariance of `purifiedDistance` along the
  reindexing `(n*n') * card(X×X') ↔ (n*card X) * (n'*card X')` that converts
  `(CQState.tensor ρ ρ').toJointDensity` (joint density of the tensor CQ
  state) into `SubDensityOp.tensor ρ.toJointDensity ρ'.toJointDensity` (the
  operator tensor of the joint densities).

The second fact is the *honest* mathematical content beyond the operator-level
statement: a permutation acting on the classical block index is a unitary,
and `purifiedDistance` is unitary-invariant. -/

/-- **Purified distance is invariant under dimension cast.** Pure dimension
    transport via `SubDensityOp.castDim` is reflexive at the level of the
    underlying matrix data, so it cannot change `purifiedDistance`. The proof
    is by `subst` on the dimension equality. -/
lemma purifiedDistance_castDim {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (ρ τ : SubDensityOp n) :
    InfoTheory.SmoothMinEntropy.purifiedDistance
        (SubDensityOp.castDim h ρ) (SubDensityOp.castDim h τ) =
      InfoTheory.SmoothMinEntropy.purifiedDistance ρ τ := by
  subst h
  rfl

/-- **Explicit-permutation coherence at the joint-density level.**

    There exists a permutation `e` of `Fin (n * n' * card (X × X'))` such
    that for *every* CQ state `ρ : CQState X n` and `ρ' : CQState X' n'`,
    the joint density of the CQ tensor product equals the operator tensor
    of the factor joint densities, dimension-cast and then reindexed by `e`.

    The permutation `e` is the relabelling between
    `Fintype.equivFin (X × X')` and the compositional product
    `(Fintype.equivFin X).prodCongr (Fintype.equivFin X') ∘ finProdFinEquiv`
    on the classical block index. This is the permutation-level coherence
    that the purified-distance form `tensor_toJointDensity_purifiedDistance_eq`
    needs. -/
lemma exists_tensor_toJointDensity_reindex_eq
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    (n n' : ℕ)
    (h_dim : n * Fintype.card X * (n' * Fintype.card X') =
             n * n' * Fintype.card (X × X')) :
    ∃ e : Fin (n * n' * Fintype.card (X × X')) ≃ Fin (n * n' * Fintype.card (X × X')),
      ∀ (ρ : CQState X n) (ρ' : CQState X' n'),
        (CQState.tensor ρ ρ').toJointDensity =
          InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e
            (SubDensityOp.castDim h_dim
              (SubDensityOp.tensor ρ.toJointDensity ρ'.toJointDensity)) := by
  refine ⟨InfoTheory.SmoothMinEntropy.tensorJointReindexEquiv X X' n n' h_dim, ?_⟩
  intro ρ ρ'
  apply InfoTheory.SmoothMinEntropy.SubDensityOp.ext
  exact InfoTheory.SmoothMinEntropy.CQState.tensor_toJointDensity_toOp_eq_reindex
    h_dim ρ ρ'

/-- **Purified-distance form of the CQ-tensor joint-density coherence.** The
    purified distance between joint densities of CQ tensor states equals the
    purified distance between operator tensors of the factor joint densities,
    after aligning dimensions via `SubDensityOp.castDim`.

    The mathematical content is unitary (permutation) invariance of
    `purifiedDistance` along the reindexing
    `Fintype.equivFin (X × X') ↔ Fintype.equivFin X × Fintype.equivFin X' ∘
    finProdFinEquiv` of the classical block index. Proved by composing
    `exists_tensor_toJointDensity_reindex_eq` with
    `InfoTheory.SmoothMinEntropy.purifiedDistance_reindex`. -/
lemma tensor_toJointDensity_purifiedDistance_eq
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X']
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ρ τ : CQState X n) (ρ' τ' : CQState X' n')
    (h_dim : n * Fintype.card X * (n' * Fintype.card X') =
             n * n' * Fintype.card (X × X')) :
    InfoTheory.SmoothMinEntropy.purifiedDistance
        (CQState.tensor ρ ρ').toJointDensity (CQState.tensor τ τ').toJointDensity =
      InfoTheory.SmoothMinEntropy.purifiedDistance
        (SubDensityOp.castDim h_dim
          (SubDensityOp.tensor ρ.toJointDensity ρ'.toJointDensity))
        (SubDensityOp.castDim h_dim
          (SubDensityOp.tensor τ.toJointDensity τ'.toJointDensity)) := by
  haveI : NeZero (n * n' * Fintype.card (X × X')) := by
    refine ⟨Nat.mul_ne_zero (NeZero.ne (n * n')) ?_⟩
    exact Fintype.card_ne_zero
  obtain ⟨e, h_eq⟩ := exists_tensor_toJointDensity_reindex_eq (X := X) (X' := X')
    n n' h_dim
  rw [h_eq ρ ρ', h_eq τ τ']
  exact InfoTheory.SmoothMinEntropy.purifiedDistance_reindex e _ _

/-- **Tensor subadditivity at the CQ-state purified-distance level.** Composes
    the operator-level `purifiedDistance_tensor_subadditive` with the
    purified-distance form `tensor_toJointDensity_purifiedDistance_eq` of the
    joint-density coherence and the dimension-cast invariance
    `purifiedDistance_castDim`. -/
lemma CQState.tensor_purifiedDistance_subadditive
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X']
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ρ τ : CQState X n) (ρ' τ' : CQState X' n') :
    CQState.purifiedDistance (CQState.tensor ρ ρ') (CQState.tensor τ τ') ≤
      CQState.purifiedDistance ρ τ + CQState.purifiedDistance ρ' τ' := by
  have h_dim :
      n * Fintype.card X * (n' * Fintype.card X') =
        n * n' * Fintype.card (X × X') := by
    rw [Fintype.card_prod]; ring
  unfold CQState.purifiedDistance
  rw [tensor_toJointDensity_purifiedDistance_eq ρ τ ρ' τ' h_dim,
      purifiedDistance_castDim]
  exact purifiedDistance_tensor_subadditive
    τ.toJointDensity ρ.toJointDensity τ'.toJointDensity ρ'.toJointDensity

/-- **Renner `lem:Hminindaddsmooth` — smooth Hmin tensor superadditivity.**
    Renner thesis line 3624. For independent states `ρ_{A B}, ρ_{A' B'}`
    and conditioning `σ_B, σ_{B'}`, with smoothing radii `ε, ε' ≥ 0`,
    `Hmin^{ε+ε'}(ρ ⊗ ρ' | σ ⊗ σ') ≥ Hmin^ε(ρ|σ) + Hmin^{ε'}(ρ'|σ')`.

    Routes through `conditionalMinEntropyReal_tensor_additivity_le` (the
    non-smooth additivity at the SDP level) plus the standard smoothing
    extraction (Tomamichel 6.5 ↔ project's `isInSmoothedSetReal`) plus
    `CQState.tensor_purifiedDistance_subadditive` (Tomamichel 3.41) for
    the ε-ball triangle on the tensor.

    Proof outline (Tomamichel 6.5; Renner thesis lines 3639–3672):

    1. fix `ν > 0` and reduce via `le_of_forall_pos_le_add`;
    2. extract approximators `ρ̄, ρ̄'` for each smooth-Hmin sSup with
       `smoothMinEntropyReal_exists_approx`;
    3. show `ρ̄ ⊗ ρ̄'` lies in the `(ε+ε')`-ball of `ρ ⊗ ρ'` via
       `CQState.tensor_purifiedDistance_subadditive`;
    4. apply `conditionalMinEntropyReal_tensor_additivity_le` on the
       approximators, with positivity of the relevant feasible-λ optima
       supplied by `minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos`;
    5. realise the resulting bound as a member of the smoothed sSup using
       `smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove`;
    6. conclude with `linarith` and let `ν → 0⁺` (handled implicitly by the
       outer `le_of_forall_pos_le_add`). -/
theorem smoothMinEntropyReal_tensor_superadditivity
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X']
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ε ε' : ℝ) (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hε_lt : ε + ε' < 1)
    (ρ : CQState X n) (ρ' : CQState X' n')
    (σ : SubDensityOp n) (σ' : SubDensityOp n')
    (hρnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hρ'norm : ∑ x' : X', (ρ'.stateMap x').trace = 1)
    (hσ_pd : σ.toOp.PosDef) (hσ'_pd : σ'.toOp.PosDef) :
    smoothMinEntropyReal ε ρ σ + smoothMinEntropyReal ε' ρ' σ' ≤
      smoothMinEntropyReal (ε + ε') (CQState.tensor ρ ρ')
        (SubDensityOp.tensor σ σ') := by
  -- Step 1: reduce to "≤ RHS + ν" for arbitrary ν > 0.
  apply le_of_forall_pos_le_add
  intro ν hν
  have hν2_pos : 0 < ν / 2 := half_pos hν
  -- Step 2: extract approximators ρ̄ ∈ B^ε(ρ), ρ̄' ∈ B^{ε'}(ρ') whose
  -- conditionalMinEntropyReal lies within ν/2 of the corresponding sSup.
  have h_lt1 : smoothMinEntropyReal ε ρ σ - ν / 2 < smoothMinEntropyReal ε ρ σ :=
    sub_lt_self _ hν2_pos
  have h_lt2 : smoothMinEntropyReal ε' ρ' σ' - ν / 2 < smoothMinEntropyReal ε' ρ' σ' :=
    sub_lt_self _ hν2_pos
  obtain ⟨ρhat, hd1, hh1⟩ :=
    smoothMinEntropyReal_exists_approx ε hε ρ σ (smoothMinEntropyReal ε ρ σ - ν / 2) h_lt1
  obtain ⟨ρhat', hd2, hh2⟩ :=
    smoothMinEntropyReal_exists_approx ε' hε' ρ' σ' (smoothMinEntropyReal ε' ρ' σ' - ν / 2) h_lt2
  -- Step 3: ρhat ⊗ ρhat' is in the (ε+ε')-ball of ρ ⊗ ρ'.
  have hd_tensor :
      CQState.purifiedDistance (CQState.tensor ρ ρ') (CQState.tensor ρhat ρhat') ≤
        ε + ε' := by
    have h_sub :=
      CQState.tensor_purifiedDistance_subadditive
        (X := X) (X' := X') ρ ρhat ρ' ρhat'
    linarith only [h_sub, hd1, hd2]
  -- Step 4: non-smooth tensor additivity on the approximators. PosDef of the
  -- references gives feasibility; positive total weight on each approximator
  -- gives positivity of the corresponding optimum.
  have hε_sq_lt : ε ^ 2 < 1 := pow_lt_one₀ hε (by linarith only [hε_lt, hε']) two_ne_zero
  have hε'_sq_lt : ε' ^ 2 < 1 := pow_lt_one₀ hε' (by linarith only [hε_lt, hε]) two_ne_zero
  have hweight1 : 0 < ∑ x : X, (ρhat.stateMap x).trace := by
    have h_ge : 1 - ε ^ 2 ≤ ∑ x : X, (ρhat.stateMap x).trace :=
      CQState.sum_stateMap_trace_ge_of_purifiedDistance hε hρnorm hd1
    linarith only [h_ge, hε_sq_lt]
  have hweight2 : 0 < ∑ x' : X', (ρhat'.stateMap x').trace := by
    have h_ge : 1 - ε' ^ 2 ≤ ∑ x' : X', (ρhat'.stateMap x').trace :=
      CQState.sum_stateMap_trace_ge_of_purifiedDistance hε' hρ'norm hd2
    linarith only [h_ge, hε'_sq_lt]
  have hfeas1 : hasFeasibleLambda ρhat σ :=
    hasFeasibleLambda_of_posDef ρhat σ hσ_pd
  have hfeas2 : hasFeasibleLambda ρhat' σ' :=
    hasFeasibleLambda_of_posDef ρhat' σ' hσ'_pd
  have hlam1 : 0 < minFeasibleLambda ρhat σ :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
      ρhat σ hweight1 hfeas1
  have hlam2 : 0 < minFeasibleLambda ρhat' σ' :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
      ρhat' σ' hweight2 hfeas2
  -- Tensor feasibility / positivity at the joint level.
  have hσσ'_pd : (SubDensityOp.tensor σ σ').toOp.PosDef :=
    SubDensityOp.tensor_posDef σ σ' hσ_pd hσ'_pd
  have hfeasT :
      hasFeasibleLambda (CQState.tensor ρhat ρhat')
        (SubDensityOp.tensor σ σ') :=
    hasFeasibleLambda_of_posDef _ _ hσσ'_pd
  have hweightT :
      0 < ∑ p : X × X', ((CQState.tensor ρhat ρhat').stateMap p).trace := by
    rw [CQState.tensor_sum_trace]
    exact mul_pos hweight1 hweight2
  have hlamT :
      0 < minFeasibleLambda (CQState.tensor ρhat ρhat')
        (SubDensityOp.tensor σ σ') :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
      (CQState.tensor ρhat ρhat') (SubDensityOp.tensor σ σ')
      hweightT hfeasT
  have hAdd :=
    conditionalMinEntropyReal_tensor_additivity_le ρhat ρhat' σ σ'
      hfeas1 hfeas2 hlam1 hlam2 hlamT
  -- Step 5: realise the bound on the approximator tensor as a member of the
  -- smoothed sSup at radius ε+ε'. Uses _of_bddAbove, supplying boundedness
  -- of the smoothed set from `smoothMinEntropyReal_bddAbove` (now available
  -- under the strengthened signature).
  have hρρ'_norm :
      ∑ p : X × X', ((CQState.tensor ρ ρ').stateMap p).trace = 1 := by
    rw [CQState.tensor_sum_trace, hρnorm, hρ'norm]; ring
  have hbdd_tensor :
      BddAbove (setOf (isInSmoothedSetReal (ε + ε') (CQState.tensor ρ ρ')
        (SubDensityOp.tensor σ σ'))) :=
    smoothMinEntropyReal_bddAbove (ε + ε') hε_lt
      (CQState.tensor ρ ρ') hρρ'_norm (SubDensityOp.tensor σ σ')
  have hsmooth_le :
      conditionalMinEntropyReal (CQState.tensor ρhat ρhat') (SubDensityOp.tensor σ σ') ≤
        smoothMinEntropyReal (ε + ε') (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove (ε + ε')
      (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ')
      (conditionalMinEntropyReal (CQState.tensor ρhat ρhat') (SubDensityOp.tensor σ σ'))
      (CQState.tensor ρhat ρhat') hbdd_tensor hd_tensor le_rfl
  -- Step 6: chain everything.
  linarith only [hh1, hh2, hAdd, hsmooth_le]

/-- Signed entropy floors add under tensoring when each floor is certified by a feasible
exponential coefficient. Negative floors remain signed until the final ENNReal conversion. -/
theorem smoothMinEntropy_tensor_superadditivity_of_isFeasible
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X'] {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    {ε ε' k k' : ℝ} (ρ τ : CQState X n) (ρ' τ' : CQState X' n')
    (σ : SubDensityOp n) (σ' : SubDensityOp n')
    (hd : CQState.purifiedDistance ρ τ ≤ ε)
    (hd' : CQState.purifiedDistance ρ' τ' ≤ ε')
    (hk : isFeasible τ σ (2 ^ (-k))) (hk' : isFeasible τ' σ' (2 ^ (-k'))) :
    ENNReal.ofReal (k + k') ≤
      smoothMinEntropy (ε + ε') (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') := by
  apply smoothMinEntropy_ge_of_isFeasible _ (CQState.tensor τ τ')
  · exact (CQState.tensor_purifiedDistance_subadditive ρ τ ρ' τ').trans (add_le_add hd hd')
  · have hpow : (2 : ℝ) ^ (-(k + k')) = 2 ^ (-k) * 2 ^ (-k') := by
      rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [hpow]
    exact isFeasible_tensor hk hk'

/-- Extended smooth entropies are superadditive under tensor products when each ball has
a coefficient-one feasible witness. These certificates protect the zero floor from clipping. -/
theorem smoothMinEntropy_tensor_superadditivity
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X'] {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ε ε' : ℝ) (ρ : CQState X n) (ρ' : CQState X' n')
    (σ : SubDensityOp n) (σ' : SubDensityOp n')
    (hzero : ∃ τ, CQState.purifiedDistance ρ τ ≤ ε ∧ isFeasible τ σ 1)
    (hzero' : ∃ τ', CQState.purifiedDistance ρ' τ' ≤ ε' ∧ isFeasible τ' σ' 1) :
    smoothMinEntropy ε ρ σ + smoothMinEntropy ε' ρ' σ' ≤
      smoothMinEntropy (ε + ε') (CQState.tensor ρ ρ') (SubDensityOp.tensor σ σ') := by
  rw [smoothMinEntropy_eq_iSup_feasibleFloor ε ρ σ,
    smoothMinEntropy_eq_iSup_feasibleFloor ε' ρ' σ']
  have hz : ∃ k : NNReal, ∃ τ, CQState.purifiedDistance ρ τ ≤ ε ∧
      isFeasible τ σ (2 ^ (-(k : ℝ))) := by
    refine ⟨0, ?_⟩
    simpa only [NNReal.coe_zero, neg_zero, Real.rpow_zero] using hzero
  have hz' : ∃ k : NNReal, ∃ τ', CQState.purifiedDistance ρ' τ' ≤ ε' ∧
      isFeasible τ' σ' (2 ^ (-(k : ℝ))) := by
    refine ⟨0, ?_⟩
    simpa only [NNReal.coe_zero, neg_zero, Real.rpow_zero] using hzero'
  apply ENNReal.biSup_add_biSup_le' hz hz'
  intro k hk k' hk'
  obtain ⟨τ, hd, hfeas⟩ := hk
  obtain ⟨τ', hd', hfeas'⟩ := hk'
  have h := smoothMinEntropy_tensor_superadditivity_of_isFeasible
    ρ τ ρ' τ' σ σ' hd hd' hfeas hfeas'
  simpa only [ENNReal.ofReal_add k.coe_nonneg k'.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using h

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
