import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.CoarsenLift

/-!
# Coarsening states with fiber support

Orthogonal fiber support controls feasible coefficients after classical coarsening. Purified-
distance witnesses give the associated extended smooth entropy lower bound.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The fibre slice -/

/-- The `f₀`-fibre slice of a CQ state with product classical register `Y × F`: keep the block at
`(y, f₀)` and index it by `y`.  The total weight only drops, so `weight_le_one` is inherited. -/
noncomputable def CQState.fiberSlice {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (f₀ : F) (ρ : CQState (Y × F) d) : CQState Y d where
  stateMap y := ρ.stateMap (y, f₀)
  weight_le_one := by
    refine le_trans ?_ ρ.weight_le_one
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun y _ => ?_
    exact Finset.single_le_sum (f := fun f : F => (ρ.stateMap (y, f)).trace)
      (fun f _ => (ρ.stateMap (y, f)).trace_nonneg) (Finset.mem_univ f₀)

@[simp] lemma CQState.fiberSlice_stateMap {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (f₀ : F) (ρ : CQState (Y × F) d) (y : Y) :
    (CQState.fiberSlice f₀ ρ).stateMap y = ρ.stateMap (y, f₀) := rfl

/-- On a state supported on the single fibre `F = {f₀}`, the product-projection coarsening is the
`f₀`-fibre slice: every fibre sum has exactly one nonzero summand. -/
lemma coarsen_prodFst_eq_fiberSlice_of_fiberSupport
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Fintype F] {d : ℕ}
    (ρ : CQState (Y × F) d) (f₀ : F)
    (hsupp : ∀ p : Y × F, p.2 ≠ f₀ → ρ.stateMap p = 0) :
    CQState.coarsen (Prod.fst : Y × F → Y) ρ = CQState.fiberSlice f₀ ρ := by
  apply CQState.ext_stateMap
  funext y
  apply SubDensityOp.ext
  rw [coarsen_prodFst_stateMap_toOp]
  rw [Finset.sum_eq_single f₀]
  · rfl
  · intro f _ hf
    rw [hsupp (y, f) hf]
    rfl
  · intro h
    exact absurd (Finset.mem_univ f₀) h

/-! ## The distance step -/

/-- The Uhlmann fidelity of a zero block against any block vanishes. -/
private lemma fidelity_zero_left_subDensityOp {d : ℕ} [NeZero d] (τ : SubDensityOp d) :
    Quantum.Metrics.fidelity (0 : SubDensityOp d).toPosSemidefOp τ.toPosSemidefOp = 0 := by
  have hsq := fidelity_sq_le_trace_mul_trace (0 : SubDensityOp d) τ
  have hz : ((0 : SubDensityOp d).trace) = 0 := by
    simp [SubDensityOp.trace, show (0 : SubDensityOp d).toOp = 0 from rfl]
  rw [hz, zero_mul] at hsq
  have hnn := Quantum.Metrics.fidelity_nonneg_posSemidefOp
    (0 : SubDensityOp d).toPosSemidefOp τ.toPosSemidefOp
  nlinarith

/-- **Slicing does not lower generalized fidelity against a fibre-supported state.**

The off-fibre blocks of `ρ` are `0`, so they contribute nothing to the block-fidelity sum and the
Uhlmann fidelities of the sliced and unsliced pairs are *equal*.  Slicing preserves the weight of
`ρ` and can only lower the weight of `ρ'`, so the sub-normalization correction
`√((1 - tr)(1 - tr))` only grows. -/
lemma fidelityGen_fiberSlice_ge_of_fiberSupport
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ρ ρ' : CQState (Y × F) d) (f₀ : F)
    (hsupp : ∀ p : Y × F, p.2 ≠ f₀ → ρ.stateMap p = 0) :
    fidelityGen ρ.toJointDensity ρ'.toJointDensity ≤
      fidelityGen (CQState.fiberSlice f₀ ρ).toJointDensity
        (CQState.fiberSlice f₀ ρ').toJointDensity := by
  have : NeZero (Fintype.card (Y × F)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (d * Fintype.card (Y × F)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (d * Fintype.card Y) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  -- The Uhlmann fidelities agree exactly.
  have hfid : Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        ρ'.toJointDensity.toPosSemidefOp =
      Quantum.Metrics.fidelity (CQState.fiberSlice f₀ ρ).toJointDensity.toPosSemidefOp
        (CQState.fiberSlice f₀ ρ').toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single f₀]
    · rfl
    · intro f _ hf
      rw [hsupp (y, f) hf]
      exact fidelity_zero_left_subDensityOp _
    · intro h
      exact absurd (Finset.mem_univ f₀) h
  -- Slicing preserves the weight of the fibre-supported `ρ`.
  have htr : (CQState.fiberSlice f₀ ρ).toJointDensity.trace = ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine (Finset.sum_eq_single (f := fun f : F => (ρ.stateMap (y, f)).trace) f₀
      (fun f _ hf => ?_) (fun h => ?_)).symm
    · change (ρ.stateMap (y, f)).trace = 0
      rw [hsupp (y, f) hf]
      simp [SubDensityOp.trace, show (0 : SubDensityOp d).toOp = 0 from rfl]
    · exact absurd (Finset.mem_univ f₀) h
  -- Slicing can only lower the weight of `ρ'`.
  have htr' : (CQState.fiberSlice f₀ ρ').toJointDensity.trace ≤ ρ'.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun y _ => ?_
    exact Finset.single_le_sum (f := fun f : F => (ρ'.stateMap (y, f)).trace)
      (fun f _ => (ρ'.stateMap (y, f)).trace_nonneg) (Finset.mem_univ f₀)
  unfold fidelityGen
  rw [hfid]
  refine add_le_add le_rfl (Real.sqrt_le_sqrt ?_)
  rw [htr]
  have h1 : (0 : ℝ) ≤ 1 - ρ.toJointDensity.trace := ρ.toJointDensity.one_sub_trace_nonneg
  nlinarith [h1, htr']

/-- **Slicing contracts CQ purified distance against a fibre-supported centre.** -/
lemma purifiedDistance_fiberSlice_le_of_fiberSupport
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ρ ρ' : CQState (Y × F) d) (f₀ : F)
    (hsupp : ∀ p : Y × F, p.2 ≠ f₀ → ρ.stateMap p = 0) :
    CQState.purifiedDistance (CQState.fiberSlice f₀ ρ) (CQState.fiberSlice f₀ ρ') ≤
      CQState.purifiedDistance ρ ρ' := by
  have : NeZero (Fintype.card (Y × F)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (d * Fintype.card (Y × F)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (d * Fintype.card Y) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  exact purifiedDistance_le_of_fidelityGen_ge _ _ _ _
    (fidelityGen_fiberSlice_ge_of_fiberSupport ρ ρ' f₀ hsupp)

/-! ## The entropy step -/

/-- The blocks of the `f₀`-fibre slice are a subfamily of the blocks of `ρ`, so every feasible `λ`
for `ρ` is feasible for the slice; the feasible infimum therefore drops. -/
lemma minFeasibleLambda_fiberSlice_le {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (f₀ : F) (ρ : CQState (Y × F) d) (σ : SubDensityOp d)
    (hfeas : hasFeasibleLambda ρ σ) :
    minFeasibleLambda (CQState.fiberSlice f₀ ρ) σ ≤ minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  refine csInf_le_csInf ⟨0, fun t ht => ht.1⟩ ⟨hfeas.choose, hfeas.choose_spec⟩ ?_
  intro t ht
  exact ⟨ht.1, fun y => ht.2 (y, f₀)⟩

/-- Slicing does not lower the real conditional min-entropy, given that the slice has a strictly
positive feasible optimum (needed for the `-log₂` comparison). -/
lemma conditionalMinEntropyReal_fiberSlice_ge {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (f₀ : F) (ρ : CQState (Y × F) d) (σ : SubDensityOp d)
    (hfeas : hasFeasibleLambda ρ σ)
    (hpos : 0 < minFeasibleLambda (CQState.fiberSlice f₀ ρ) σ) :
    conditionalMinEntropyReal ρ σ ≤ conditionalMinEntropyReal (CQState.fiberSlice f₀ ρ) σ := by
  have hle := minFeasibleLambda_fiberSlice_le f₀ ρ σ hfeas
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log (minFeasibleLambda (CQState.fiberSlice f₀ ρ) σ) ≤
      Real.log (minFeasibleLambda ρ σ) := Real.log_le_log hpos hle
  unfold conditionalMinEntropyReal
  exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le

/-! ## The main result -/

/-- A centre supported on one fibre can be coarsened without decreasing its extended
smooth entropy; slicing witnesses preserves feasible coefficients and contracts distance. -/
theorem smoothMinEntropy_coarsen_prodFst_ge_of_fiberSupport
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState (Y × F) d) (σ : SubDensityOp d) (f₀ : F)
    (hsupp : ∀ p : Y × F, p.2 ≠ f₀ → ρ.stateMap p = 0) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (CQState.coarsen (Prod.fst : Y × F → Y) ρ) σ := by
  rw [coarsen_prodFst_eq_fiberSlice_of_fiberSupport ρ f₀ hsupp]
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨CQState.fiberSlice f₀ τ,
    (purifiedDistance_fiberSlice_le_of_fiberSupport ρ τ f₀ hsupp).trans hd, ?_⟩
  intro t ht
  exact ⟨ht.1, fun y => ht.2 (y, f₀)⟩


/-- Removing a classical factor supported at one value does not decrease signed smooth
min-entropy below the stated weight threshold. -/
theorem smoothMinEntropyReal_coarsen_prodFst_ge_of_fiberSupport
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState (Y × F) d) (σ : SubDensityOp d)
    (hσ_pd : σ.toOp.PosDef) (f₀ : F)
    (hsupp : ∀ p : Y × F, p.2 ≠ f₀ → ρ.stateMap p = 0)
    (hkeep : 2 * ε < ∑ p : Y × F, (ρ.stateMap p).trace) :
    smoothMinEntropyReal ε ρ σ ≤
      smoothMinEntropyReal ε (CQState.coarsen (Prod.fst : Y × F → Y) ρ) σ := by
  classical
  rw [coarsen_prodFst_eq_fiberSlice_of_fiberSupport ρ f₀ hsupp]
  set η : ℝ := (∑ p : Y × F, (ρ.stateMap p).trace) - 2 * ε with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have hslice_weight : ∑ y : Y, ((CQState.fiberSlice f₀ ρ).stateMap y).trace =
      ∑ p : Y × F, (ρ.stateMap p).trace := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine (Finset.sum_eq_single (f := fun f : F => (ρ.stateMap (y, f)).trace) f₀
      (fun f _ hf => ?_) (fun h => ?_)).symm
    · change (ρ.stateMap (y, f)).trace = 0
      rw [hsupp (y, f) hf]
      simp [SubDensityOp.trace, show (0 : SubDensityOp d).toOp = 0 from rfl]
    · exact absurd (Finset.mem_univ f₀) h
  have hρ_lower : η + 2 * ε ≤ ∑ y : Y, ((CQState.fiberSlice f₀ ρ).stateMap y).trace := by
    rw [hslice_weight, hη_def]
    linarith
  have hfloor : ∀ τ : CQState Y d,
      CQState.purifiedDistance (CQState.fiberSlice f₀ ρ) τ ≤ ε →
        η ≤ ∑ y : Y, (τ.stateMap y).trace := fun τ hτ =>
    CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ_lower hτ
  have hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε (CQState.fiberSlice f₀ ρ) σ)) :=
    smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη_pos
      (CQState.fiberSlice f₀ ρ) σ hfloor
  unfold smoothMinEntropyReal
  apply csSup_le (smoothedSetReal_nonempty hε ρ σ)
  rintro a ⟨ρ', rfl, hd⟩
  have hd' : CQState.purifiedDistance (CQState.fiberSlice f₀ ρ) (CQState.fiberSlice f₀ ρ') ≤ ε :=
    le_trans (purifiedDistance_fiberSlice_le_of_fiberSupport ρ ρ' f₀ hsupp) hd
  have hw : η ≤ ∑ y : Y, ((CQState.fiberSlice f₀ ρ').stateMap y).trace :=
    hfloor (CQState.fiberSlice f₀ ρ') hd'
  have hpos : 0 < minFeasibleLambda (CQState.fiberSlice f₀ ρ') σ :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos (CQState.fiberSlice f₀ ρ') σ hσ_pd
      (lt_of_lt_of_le hη_pos hw)
  have hmono : conditionalMinEntropyReal ρ' σ ≤
      conditionalMinEntropyReal (CQState.fiberSlice f₀ ρ') σ :=
    conditionalMinEntropyReal_fiberSlice_ge f₀ ρ' σ
      (hasFeasibleLambda_of_posDef ρ' σ hσ_pd) hpos
  exact le_trans hmono (le_csSup hbdd ⟨CQState.fiberSlice f₀ ρ', rfl, hd'⟩)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
