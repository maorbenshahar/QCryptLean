import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ConditioningIsometryInvariance
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Conditioning-side partial-trace data processing for the bipartite min-entropy

Discarding part of the **conditioning** register can only increase the conditional min-entropy:

`H_min(A | C₁C₂)_ρ ≤ H_min(A | C₁)_{Tr_{C₂} ρ}`, and likewise for the ε-smooth entropy.

This is Tomamichel (2016), Theorem 6.2 (`th:data-proc`) in the special case where the `A`-side map
is the identity (which is unital, hence sub-unital) and the `B`-side map is the partial trace over a
subregister. It is a *general bipartite, reference-optimized* statement: the reference is optimized
over all `D_max`-feasible `σ` on the conditioning register, not fixed and not restricted to the
maximally mixed or CQ case.

## The two transports

* **Value transport (ε = 0).** A `D_max`-feasible reference `σ` on `C₁ ⊗ C₂`, that is
  `ρ ≤ t·(1_A ⊗ σ)`, pushes forward to `Tr_{C₂} σ` at the *same* scalar `t`: the partial trace is
  Löwner
  monotone (`partialTraceB_opLe_of_opLe`) and fixes the `A`-side identity factor
  (`partialTraceB_castDim_one_tensor`). Feasible sets therefore only grow, `D_max` only drops, and
  `H_min` only rises. Lifted over the reference optimization this gives
  `bipartiteMinEntropyOptReal_partialTrace_conditioning_le`.
* **Metric transport (smooth lift).** The conditioning-side partial trace is CPTP, hence CP
  trace-non-increasing, so the purified distance contracts under it
  (`SubDensityOp.fidelityGen_le_fidelityGen_cp_tni`). Every element of the ε-ball of `ρ` maps into
  the ε-ball of `Tr_{C₂} ρ`, so the smoothed supremum transports:
  `smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le`.

## The boundedness hypothesis

The smooth statement is an inequality between two `sSup`s of real-valued optimization sets. The
target set must be bounded above for `csSup` reasoning to be meaningful, and this is **not**
automatic: as `ρ'` ranges over the ε-ball its trace can shrink, and a nearly-zero sub-normalized
state has a very large conditional min-entropy. Tomamichel's Theorem 6.2 restricts the smoothing
radius by `ε < √(tr ρ)` for exactly this reason. The hypothesis `hbdd` is therefore carried
explicitly here rather than advertised away;
`smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le_of_normalized` discharges it for a
normalized state and `0 ≤ ε < 1`, which is the `tr ρ = 1` case of Tomamichel's range.

## Main statements

* `SubDensityOp.partialTrace_of_conditioning` — the explicit conditioning-side partial trace.
* `partialTraceB_castDim_one_tensor` — `Tr_{C₂}(1_A ⊗ σ) = 1_A ⊗ Tr_{C₂} σ`.
* `dmaxFeasibleLambda_partialTrace_conditioning_le` — the `D_max` scalar does not increase.
* `bipartiteMinEntropyOptReal_partialTrace_conditioning_le` — the nonsmooth DPI.
* `purifiedDistance_partialTrace_conditioning_le` — metric contraction.
* `smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le` — the smooth DPI.
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Local cast glue -/

/-! ## The conditioning-side partial trace -/

/-- **Discard the trailing conditioning subregister.** For a bipartite sub-normalized state on
`A ⊗ (C₁ ⊗ C₂)`, reindex to `(A ⊗ C₁) ⊗ C₂` by associativity of the row-major flattening and trace
out the trailing `C₂` factor, landing on `A ⊗ C₁`. -/
def SubDensityOp.partialTrace_of_conditioning {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) : SubDensityOp (dA * dC1) :=
  (SubDensityOp.castDim (Nat.mul_assoc dA dC1 dC2).symm ρ).partialTraceB

@[simp]
lemma SubDensityOp.partialTrace_of_conditioning_toOp {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) :
    (SubDensityOp.partialTrace_of_conditioning ρ).toOp =
      Quantum.TensorProducts.partialTraceB
        (Op.castDim (Nat.mul_assoc dA dC1 dC2).symm ρ.toOp) := by
  unfold SubDensityOp.partialTrace_of_conditioning
  rw [SubDensityOp.partialTraceB_toOp, SubDensityOp.castDim_toOp]

/-- **The conditioning-side partial trace preserves the trace.** Both the associativity relabelling
and the partial trace do. -/
@[simp]
lemma SubDensityOp.trace_partialTrace_of_conditioning {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) :
    (SubDensityOp.partialTrace_of_conditioning ρ).trace = ρ.trace := by
  rw [SubDensityOp.partialTrace_of_conditioning, SubDensityOp.trace_partialTraceB,
    SubDensityOp.castDim_trace]

/-! ## The tensor identity `Tr_{C₂}(1_A ⊗ σ) = 1_A ⊗ Tr_{C₂} σ` -/

/-- **Conditioning-side partial trace of a tensored identity.** Tracing out the trailing `C₂` factor
of `1_A ⊗ σ` — after the `A ⊗ (C₁ ⊗ C₂) ≃ (A ⊗ C₁) ⊗ C₂` reindexing — leaves `1_A` untouched and
traces `C₂` out of `σ`. -/
lemma partialTraceB_castDim_one_tensor {dA dC1 dC2 : ℕ} (σ : Op (dC1 * dC2)) :
    partialTraceB
        (Op.castDim (Nat.mul_assoc dA dC1 dC2).symm (Op.tensor (1 : Op dA) σ)) =
      Op.tensor (1 : Op dA) (partialTraceB σ) := by
  ext i j
  rw [Op_tensor_apply_finProd]
  simp only [partialTraceB, Matrix.of_apply, Op.castDim, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [matrix_eqRec_apply, Op_tensor_apply_finProd, finProdFinEquiv_symm_cast_assoc,
    finProdFinEquiv_symm_cast_assoc]
  have hi1 : (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1 = i := by
    rw [Equiv.symm_apply_apply]
  have hj1 : (finProdFinEquiv.symm (finProdFinEquiv (j, k))).1 = j := by
    rw [Equiv.symm_apply_apply]
  have hi2 : (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 = k := by
    rw [Equiv.symm_apply_apply]
  have hj2 : (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 = k := by
    rw [Equiv.symm_apply_apply]
  simp only [hi1, hj1, hi2, hj2, Matrix.one_apply]

/-! ## Feasibility pushforward -/

/-- **Feasibility pushforward at the same scalar.** If `σ` on `C₁ ⊗ C₂` is `D_max`-feasible for `ρ`
at scalar `t`, then `Tr_{C₂} σ` is `D_max`-feasible for the discarded state at the *same* `t`. -/
lemma dmaxIsFeasible_partialTrace_conditioning_of_feasible {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) (σ : SubDensityOp (dC1 * dC2)) {t : ℝ}
    (ht : dmaxIsFeasible ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) t) :
    dmaxIsFeasible (SubDensityOp.partialTrace_of_conditioning ρ).toOp
      (Op.tensor (1 : Op dA) σ.partialTraceB.toOp) t := by
  obtain ⟨htn, htle⟩ := ht
  refine ⟨htn, ?_⟩
  have hmono := partialTraceB_opLe_of_opLe
    (opLe_castDim (Nat.mul_assoc dA dC1 dC2).symm htle)
  rw [Op.castDim_smul, partialTraceB_smul, partialTraceB_castDim_one_tensor,
    ← SubDensityOp.partialTrace_of_conditioning_toOp, ← SubDensityOp.partialTraceB_toOp] at hmono
  exact hmono

/-- The `D_max`-feasible family transports: a feasible reference for `ρ` yields a feasible reference
for the discarded state. -/
lemma hasDmaxFeasibleLambda_partialTrace_conditioning {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) (σ : SubDensityOp (dC1 * dC2))
    (hfeas : hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    hasDmaxFeasibleLambda (SubDensityOp.partialTrace_of_conditioning ρ).toOp
      (Op.tensor (1 : Op dA) σ.partialTraceB.toOp) := by
  obtain ⟨t, ht⟩ := hfeas
  exact ⟨t, dmaxIsFeasible_partialTrace_conditioning_of_feasible ρ σ ht⟩

/-- **`D_max`-scalar contraction.** Discarding `C₂` cannot increase the `D_max` feasible scalar:
`D_max(Tr_{C₂} ρ ‖ 1_A ⊗ Tr_{C₂} σ) ≤ D_max(ρ ‖ 1_A ⊗ σ)`, because the feasible set only grows. -/
lemma dmaxFeasibleLambda_partialTrace_conditioning_le {dA dC1 dC2 : ℕ}
    (ρ : SubDensityOp (dA * (dC1 * dC2))) (σ : SubDensityOp (dC1 * dC2))
    (hfeas : hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    dmaxFeasibleLambda (SubDensityOp.partialTrace_of_conditioning ρ).toOp
        (Op.tensor (1 : Op dA) σ.partialTraceB.toOp) ≤
      dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) :=
  csInf_le_csInf (dmaxFeasibleLambda_bddBelow _ _) hfeas
    (fun _ ht => dmaxIsFeasible_partialTrace_conditioning_of_feasible ρ σ ht)

/-! ## Value transport (the ε = 0 core) -/

/-- The `D_max` feasible scalar of the zero state against any reference is `0`. -/
private lemma dmaxFeasibleLambda_zero_left {d : ℕ} (Q : Op d) :
    dmaxFeasibleLambda (0 : Op d) Q = 0 := by
  refine le_antisymm ?_ (dmaxFeasibleLambda_nonneg _ _)
  refine dmaxFeasibleLambda_le_of_feasible _ _ ⟨le_refl 0, ?_⟩
  rw [Complex.ofReal_zero, zero_smul]
  intro v
  simp

/-- **Per-reference value transport.** Against a `D_max`-feasible reference `σ`, discarding `C₂`
does not decrease the conditional min-entropy measured with the pushforward reference `Tr_{C₂} σ`.

The `D_max = 0` sentinel (which encodes `H_min = +∞`) is excluded on the nonzero branch: the
conditioning partial trace preserves the trace, so a nonzero state stays nonzero. -/
lemma bipartiteMinEntropyReal_partialTrace_conditioning_ge {dA dC1 dC2 : ℕ}
    [NeZero dA] [NeZero dC1] [NeZero dC2]
    (ρ : SubDensityOp (dA * (dC1 * dC2))) (σ : SubDensityOp (dC1 * dC2))
    (hfeas : hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    bipartiteMinEntropyReal ρ σ ≤
      bipartiteMinEntropyReal (SubDensityOp.partialTrace_of_conditioning ρ) σ.partialTraceB := by
  have hfeas' := hasDmaxFeasibleLambda_partialTrace_conditioning ρ σ hfeas
  have hcmp := dmaxFeasibleLambda_partialTrace_conditioning_le ρ σ hfeas
  unfold bipartiteMinEntropyReal
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hρ0 : ρ.toOp = 0
  · have hlam_orig : dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) = 0 := by
      rw [hρ0]; exact dmaxFeasibleLambda_zero_left _
    have hpt0 : (SubDensityOp.partialTrace_of_conditioning ρ).toOp = 0 := by
      rw [SubDensityOp.partialTrace_of_conditioning_toOp, hρ0, Op.castDim_zero]
      exact (Quantum.Channels.isCPTP_partialTraceB.1).map_zero
    have hlam_push : dmaxFeasibleLambda (SubDensityOp.partialTrace_of_conditioning ρ).toOp
        (Op.tensor (1 : Op dA) σ.partialTraceB.toOp) = 0 := by
      rw [hpt0]; exact dmaxFeasibleLambda_zero_left _
    rw [hlam_orig, hlam_push]
  · have hpt0 : (SubDensityOp.partialTrace_of_conditioning ρ).toOp ≠ 0 := by
      intro hz
      have hz' : (SubDensityOp.partialTrace_of_conditioning ρ).trace = 0 := by
        unfold SubDensityOp.trace
        rw [hz, Matrix.trace_zero, Complex.zero_re]
      rw [SubDensityOp.trace_partialTrace_of_conditioning] at hz'
      exact (ne_of_gt (subDensity_trace_re_pos ρ hρ0)) hz'
    have hpushpos : 0 < dmaxFeasibleLambda (SubDensityOp.partialTrace_of_conditioning ρ).toOp
        (Op.tensor (1 : Op dA) σ.partialTraceB.toOp) :=
      dmaxFeasibleLambda_pos_of_ne_zero _ hpt0 σ.partialTraceB hfeas'
    have hlog := Real.log_le_log hpushpos hcmp
    rw [div_le_div_iff_of_pos_right h2] at *
    linarith [hlog]

/-- **Conditioning-side data processing, ε = 0.** On the reference-optimized bipartite conditional
min-entropy, discarding the conditioning subregister `C₂` does not decrease `H_min`:
`H_min(A | C₁C₂)_ρ ≤ H_min(A | C₁)_{Tr_{C₂} ρ}`. -/
theorem bipartiteMinEntropyOptReal_partialTrace_conditioning_le {dA dC1 dC2 : ℕ}
    [NeZero dA] [NeZero dC1] [NeZero dC2]
    (ρ : SubDensityOp (dA * (dC1 * dC2))) :
    bipartiteMinEntropyOptReal ρ ≤
      bipartiteMinEntropyOptReal (SubDensityOp.partialTrace_of_conditioning ρ) := by
  have : NeZero (dC1 * dC2) := ⟨Nat.mul_ne_zero (NeZero.ne dC1) (NeZero.ne dC2)⟩
  rw [bipartiteMinEntropyOptReal_eq_sSup, bipartiteMinEntropyOptReal_eq_sSup]
  apply csSup_le (bipartiteMinEntropyOptSet_nonempty ρ)
  rintro v ⟨σ, hfeas, rfl⟩
  have hfeas' := hasDmaxFeasibleLambda_partialTrace_conditioning ρ σ hfeas
  have hmem :
      bipartiteMinEntropyReal (SubDensityOp.partialTrace_of_conditioning ρ) σ.partialTraceB ∈
        bipartiteMinEntropyOptSet (SubDensityOp.partialTrace_of_conditioning ρ) :=
    ⟨σ.partialTraceB, hfeas', rfl⟩
  calc bipartiteMinEntropyReal ρ σ
      ≤ bipartiteMinEntropyReal (SubDensityOp.partialTrace_of_conditioning ρ) σ.partialTraceB :=
        bipartiteMinEntropyReal_partialTrace_conditioning_ge ρ σ hfeas
    _ ≤ sSup (bipartiteMinEntropyOptSet (SubDensityOp.partialTrace_of_conditioning ρ)) :=
        le_csSup (bipartiteMinEntropyOptSet_bddAbove _) hmem

/-! ## Metric transport -/

/-- **The conditioning-side partial trace contracts the purified distance.** It is CPTP, hence CP
trace-non-increasing, and the generalized fidelity is non-decreasing under such maps. -/
theorem purifiedDistance_partialTrace_conditioning_le {dA dC1 dC2 : ℕ}
    [NeZero dA] [NeZero dC1] [NeZero dC2]
    (ρ τ : SubDensityOp (dA * (dC1 * dC2))) :
    purifiedDistance (SubDensityOp.partialTrace_of_conditioning ρ)
        (SubDensityOp.partialTrace_of_conditioning τ) ≤
      purifiedDistance ρ τ := by
  have : NeZero (dA * dC1) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dC1)⟩
  have : NeZero (dA * (dC1 * dC2)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (Nat.mul_ne_zero (NeZero.ne dC1) (NeZero.ne dC2))⟩
  have : NeZero (dA * dC1 * dC2) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dC1)) (NeZero.ne dC2)⟩
  set h : dA * (dC1 * dC2) = dA * dC1 * dC2 := (Nat.mul_assoc dA dC1 dC2).symm
  set Φ : Op (dA * (dC1 * dC2)) → Op (dA * dC1) := fun A => partialTraceB (Op.castDim h A) with hΦ
  have hΦlin : IsLinearMap ℂ Φ := by
    refine ⟨fun A B => ?_, fun c A => ?_⟩
    · simp only [hΦ, Op.castDim_add]
      exact (Quantum.Channels.isCPTP_partialTraceB.1).map_add _ _
    · simp only [hΦ, Op.castDim_smul]
      exact (Quantum.Channels.isCPTP_partialTraceB.1).map_smul _ _
  have hΦcp : Quantum.Channels.IsCompletelyPositive Φ :=
    Quantum.Channels.isCompletelyPositive_comp partialTraceB (Op.castDim h)
      Quantum.Channels.isCPTP_partialTraceB.2.1 (Quantum.Channels.castDimLinear_isCPTP h).2.1
      Quantum.Channels.isCPTP_partialTraceB.1
  have hΦtni : ∀ A : Op (dA * (dC1 * dC2)), A.PosSemidef → (Φ A).trace.re ≤ A.trace.re := by
    intro A _
    have hΦtr : (Φ A).trace = A.trace := by
      simp only [hΦ]
      rw [Quantum.TensorProducts.trace_partialTraceB, Op.castDim_trace]
    rw [hΦtr]
  have hρ' : (SubDensityOp.partialTrace_of_conditioning ρ).toOp = Φ ρ.toOp := by
    rw [SubDensityOp.partialTrace_of_conditioning_toOp]
  have hτ' : (SubDensityOp.partialTrace_of_conditioning τ).toOp = Φ τ.toOp := by
    rw [SubDensityOp.partialTrace_of_conditioning_toOp]
  exact purifiedDistance_le_of_fidelityGen_ge _ _ _ _
    (SubDensityOp.fidelityGen_le_fidelityGen_cp_tni Φ hΦlin hΦcp hΦtni ρ τ
      (SubDensityOp.partialTrace_of_conditioning ρ)
      (SubDensityOp.partialTrace_of_conditioning τ) hρ' hτ')

/-! ## The smooth conditioning-side data-processing inequality -/

/-- **Conditioning-side partial-trace data processing for the smooth bipartite min-entropy**
(Tomamichel 2016, Theorem 6.2 `th:data-proc`, with the identity map on `A` and the partial trace on
the conditioning side). Discarding the conditioning subregister `C₂` does not decrease the ε-smooth
reference-optimized conditional min-entropy:

`H_min^ε(A | C₁C₂)_ρ ≤ H_min^ε(A | C₁)_{Tr_{C₂} ρ}`.

Each ε-ball element `τ` of `ρ` maps to an ε-ball element `Tr_{C₂} τ` of `Tr_{C₂} ρ` at the same
radius (metric transport), whose min-entropy transports by the ε = 0 core.

The hypothesis `hbdd` — the target smooth optimization set is bounded above — is genuinely needed
for the real-valued `sSup` encoding and is *not* an unconditional fact: see the module docstring and
`…_of_normalized` below for the normalized case of Tomamichel's smoothing range `ε < √(tr ρ)`. -/
theorem smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le {dA dC1 dC2 : ℕ}
    [NeZero dA] [NeZero dC1] [NeZero dC2]
    [NeZero (dA * (dC1 * dC2))] [NeZero (dA * dC1)]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : SubDensityOp (dA * (dC1 * dC2)))
    (hbdd : BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε
      (SubDensityOp.partialTrace_of_conditioning ρ)))) :
    smoothBipartiteMinEntropyOptReal ε ρ ≤
      smoothBipartiteMinEntropyOptReal ε (SubDensityOp.partialTrace_of_conditioning ρ) := by
  rw [show smoothBipartiteMinEntropyOptReal ε ρ
        = sSup (Set.ofPred (isInSmoothBipartiteMinSet ε ρ)) from rfl]
  apply csSup_le (smoothBipartiteMinSet_nonempty hε ρ)
  rintro v ⟨τ, hdist, rfl⟩
  have hval : bipartiteMinEntropyOptReal τ ≤
      bipartiteMinEntropyOptReal (SubDensityOp.partialTrace_of_conditioning τ) :=
    bipartiteMinEntropyOptReal_partialTrace_conditioning_le τ
  have hmetric : purifiedDistance (SubDensityOp.partialTrace_of_conditioning ρ)
      (SubDensityOp.partialTrace_of_conditioning τ) ≤ ε :=
    le_trans (purifiedDistance_partialTrace_conditioning_le ρ τ) hdist
  have hball : bipartiteMinEntropyOptReal (SubDensityOp.partialTrace_of_conditioning τ) ≤
      smoothBipartiteMinEntropyOptReal ε (SubDensityOp.partialTrace_of_conditioning ρ) :=
    smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε
      (SubDensityOp.partialTrace_of_conditioning ρ)
      (SubDensityOp.partialTrace_of_conditioning τ) hbdd hmetric
  linarith [hval, hball]

/-- **Smooth conditioning-side data processing for a normalized state.** For a normalized bipartite
state and a smoothing radius `0 ≤ ε < 1` — the `tr ρ = 1` case of Tomamichel's range
`0 ≤ ε < √(tr ρ)` in Theorem 6.2 — the boundedness hypothesis is discharged by
`isInSmoothBipartiteMinSet_bddAbove_of_normalized`, using that the conditioning-side partial trace
preserves the trace. -/
theorem smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le_of_normalized
    {dA dC1 dC2 : ℕ} [NeZero dA] [NeZero dC1] [NeZero dC2]
    [NeZero (dA * (dC1 * dC2))] [NeZero (dA * dC1)]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (ρ : SubDensityOp (dA * (dC1 * dC2)))
    (hρ : ρ.trace = 1) :
    smoothBipartiteMinEntropyOptReal ε ρ ≤
      smoothBipartiteMinEntropyOptReal ε (SubDensityOp.partialTrace_of_conditioning ρ) :=
  smoothBipartiteMinEntropyOptReal_partialTrace_conditioning_le hε ρ
    (isInSmoothBipartiteMinSet_bddAbove_of_normalized hε hε1
      (SubDensityOp.partialTrace_of_conditioning ρ)
      (by rw [SubDensityOp.trace_partialTrace_of_conditioning, hρ]))

end InfoTheory.SmoothMinEntropy

end
