import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.CoarsenFiberSupport
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.FilterKeepContraction
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.AnnounceCoarsenCommute

/-!
# Filtering and coarsening smooth entropy

Feasible ball witnesses survive classical filtering and coarsening. The canonical smooth entropy
comparison includes zero filtered states and requires no real-supremum boundedness condition.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Classical algebra of coarsenings and filters -/

/-- **Classical coarsening composes**: coarsening by `f` and then by `g` is coarsening by `g ∘ f`.
The general-API home of the private copies used inside the BB84 floor chains, e.g.
`coarsen_coarsen` in `AnnouncePEFloorChain.lean`. -/
lemma CQState.coarsen_coarsen {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] {d : ℕ} (f : X → Y) (g : Y → Z) (ρ : CQState X d) :
    CQState.coarsen g (CQState.coarsen f ρ) = CQState.coarsen (g ∘ f) ρ := by
  classical
  refine CQState.ext_stateMap (funext fun z => SubDensityOp.ext ?_)
  rw [CQState.coarsen_stateMap_toOp, CQState.coarsen_stateMap_toOp]
  have hinner : ∀ y : Y, (if g y = z then ((CQState.coarsen f ρ).stateMap y).toOp else 0) =
      ∑ x : X, (if g y = z then (if f x = y then (ρ.stateMap x).toOp else 0) else 0) := by
    intro y
    by_cases hy : g y = z
    · rw [ite_eq_left hy, CQState.coarsen_stateMap_toOp]
      exact Finset.sum_congr rfl fun x _ => (ite_eq_left hy).symm
    · rw [ite_eq_right hy, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => ite_eq_right hy),
        Finset.sum_const, smul_zero]
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hinner y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (f x)]
  · rw [ite_eq_left rfl]
    rfl
  · intro y _ hy
    by_cases hgy : g y = z
    · rw [ite_eq_left hgy, ite_eq_right (Ne.symm hy)]
    · rw [ite_eq_right hgy]
  · intro h
    exact absurd (Finset.mem_univ (f x)) h

/-- **Filters compose**: filtering by `k₂` and then by `k₁` keeps exactly the outcomes both
predicates accept. -/
lemma CQState.filterKeep_filterKeep {X : Type*} [Fintype X] {d : ℕ}
    (k₁ k₂ : X → Bool) (ρ : CQState X d) :
    CQState.filterKeep k₁ (CQState.filterKeep k₂ ρ) =
      CQState.filterKeep (fun x => k₂ x && k₁ x) ρ := by
  refine CQState.ext_stateMap (funext fun x => ?_)
  simp only [CQState.filterKeep_stateMap, Bool.and_eq_true]
  by_cases h₁ : k₁ x <;> by_cases h₂ : k₂ x <;> simp [h₁, h₂]

/-- **A left announce kernel commutes with a block-keep filter.**  Dropped blocks stay dropped
because `K x ⊗ 0 = 0`, and kept blocks are untouched. -/
lemma CQState.tensorLeftKernel_filterKeep {X : Type*} [Fintype X] {dE dC : ℕ}
    (keep : X → Bool) (ρ : CQState X dE) (K : X → SubDensityOp dC) :
    (CQState.filterKeep keep ρ).tensorLeftKernel K =
      CQState.filterKeep keep (ρ.tensorLeftKernel K) := by
  refine CQState.ext_stateMap (funext fun x => SubDensityOp.ext ?_)
  simp only [CQState.tensorLeftKernel_stateMap, CQState.filterKeep_stateMap]
  by_cases hx : keep x
  · simp [hx]
  · simp only [hx, Bool.false_eq_true, ite_false]
    change Op.tensor (K x).toOp ((0 : SubDensityOp dE)).toOp = (0 : Op (dC * dE))
    rw [show ((0 : SubDensityOp dE)).toOp = (0 : Op dE) from rfl]
    exact tensor_zero_op (K x).toOp

/-- **A classical filter can only remove weight.**

The total classical weight of the filtered state is at most that of the unfiltered one: a kept block
is unchanged and a dropped block contributes `0` in place of a nonnegative trace. -/
lemma CQState.sum_filterKeep_stateMap_trace_le {X : Type*} [Fintype X] {d : ℕ}
    (keep : X → Bool) (A : CQState X d) :
    ∑ x : X, ((CQState.filterKeep keep A).stateMap x).trace ≤ ∑ x : X, (A.stateMap x).trace := by
  refine Finset.sum_le_sum fun x _ => ?_
  rw [CQState.filterKeep_stateMap]
  by_cases hx : keep x
  · rw [ite_eq_left hx]
  · rw [ite_eq_right (by simpa using hx)]
    rw [show ((0 : SubDensityOp d)).trace = 0 from by
      simp [SubDensityOp.trace, show (0 : SubDensityOp d).toOp = 0 from rfl]]
    exact (A.stateMap x).trace_nonneg

/-- **The filter becomes a `Prod.snd` block-keep on the refined register.**

With `p x = (g x, keep x)`, coarsening the filtered state along `p` gives the `Prod.snd`-filter of
the coarsened unfiltered state: a fibre of `p` over `(y, b)` is entirely inside `keep⁻¹(b)`, so the
filter either keeps all of it (`b = true`) or drops all of it (`b = false`). -/
lemma CQState.coarsen_pair_filterKeep {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {d : ℕ} (g : X → Y) (keep : X → Bool) (A : CQState X d) :
    CQState.coarsen (fun x => (g x, keep x)) (CQState.filterKeep keep A) =
      CQState.filterKeep (Prod.snd : Y × Bool → Bool)
        (CQState.coarsen (fun x => (g x, keep x)) A) := by
  classical
  refine CQState.ext_stateMap (funext fun q => SubDensityOp.ext ?_)
  rw [CQState.coarsen_stateMap_toOp]
  by_cases hq : q.2 = true
  · rw [CQState.filterKeep_stateMap, ite_eq_left hq, CQState.coarsen_stateMap_toOp]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : (g x, keep x) = q
    · rw [ite_eq_left hx, ite_eq_left hx, CQState.filterKeep_stateMap, ite_eq_left]
      rw [← hx] at hq
      exact hq
    · rw [ite_eq_right hx, ite_eq_right hx]
  · rw [CQState.filterKeep_stateMap, ite_eq_right hq]
    rw [show ((0 : SubDensityOp d)).toOp = (0 : Op d) from rfl]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : (g x, keep x) = q
    · rw [ite_eq_left hx, CQState.filterKeep_stateMap, ite_eq_right]
      · rfl
      · rw [← hx] at hq
        exact hq
    · rw [ite_eq_right hx]

/-! ## The entropy transfer -/

/-- Filtering before an arbitrary classical coarsening increases extended smooth
min-entropy, with no kept-weight or reference regularity restriction. -/
theorem smoothMinEntropy_coarsen_filterKeep_ge
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {d : ℕ} [NeZero d] (ε : ℝ) (g : X → Y) (keep : X → Bool) (A : CQState X d)
    (σ : SubDensityOp d) :
    smoothMinEntropy ε (CQState.coarsen g A) σ ≤
      smoothMinEntropy ε (CQState.coarsen g (CQState.filterKeep keep A)) σ := by
  classical
  let p : X → Y × Bool := fun x => (g x, keep x)
  let FA := CQState.filterKeep keep A
  have hpair : CQState.coarsen p FA =
      CQState.filterKeep (Prod.snd : Y × Bool → Bool) (CQState.coarsen p A) :=
    CQState.coarsen_pair_filterKeep g keep A
  have hfstA : CQState.coarsen (Prod.fst : Y × Bool → Y) (CQState.coarsen p A) =
      CQState.coarsen g A := CQState.coarsen_coarsen p Prod.fst A
  have hfstFA : CQState.coarsen (Prod.fst : Y × Bool → Y) (CQState.coarsen p FA) =
      CQState.coarsen g FA := CQState.coarsen_coarsen p Prod.fst FA
  have hsupp : ∀ q : Y × Bool, q.2 ≠ true → (CQState.coarsen p FA).stateMap q = 0 := by
    intro q hq
    rw [hpair]
    simp [CQState.filterKeep_stateMap, hq]
  calc
    smoothMinEntropy ε (CQState.coarsen g A) σ ≤
        smoothMinEntropy ε (CQState.coarsen p A) σ := by
      rw [← hfstA]
      exact smoothMinEntropy_coarsen_le _ σ ε
    _ ≤ smoothMinEntropy ε (CQState.coarsen p FA) σ := by
      apply smoothMinEntropy_filterKeep_ge ε _ _ σ Prod.snd
      intro q
      rw [hpair, CQState.filterKeep_stateMap]
    _ ≤ smoothMinEntropy ε (CQState.coarsen g FA) σ := by
      rw [← hfstFA]
      exact smoothMinEntropy_coarsen_prodFst_ge_of_fiberSupport ε _ σ true hsupp


/-- Filtering classical outcomes before coarsening does not decrease signed smooth min-entropy
below the kept-weight threshold. -/
theorem smoothMinEntropyReal_coarsen_filterKeep_ge
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε : 0 ≤ ε) (g : X → Y) (keep : X → Bool) (A : CQState X d)
    (σ : SubDensityOp d) (hσ_pd : σ.toOp.PosDef)
    (hkeep : 2 * ε < ∑ x : X, ((CQState.filterKeep keep A).stateMap x).trace) :
    smoothMinEntropyReal ε (CQState.coarsen g A) σ ≤
      smoothMinEntropyReal ε (CQState.coarsen g (CQState.filterKeep keep A)) σ := by
  classical
  set p : X → Y × Bool := fun x => (g x, keep x) with hp
  set FA : CQState X d := CQState.filterKeep keep A with hFA
  have hpair : CQState.coarsen p FA =
      CQState.filterKeep (Prod.snd : Y × Bool → Bool) (CQState.coarsen p A) :=
    CQState.coarsen_pair_filterKeep g keep A
  have hfstA : CQState.coarsen (Prod.fst : Y × Bool → Y) (CQState.coarsen p A) =
      CQState.coarsen g A := CQState.coarsen_coarsen p Prod.fst A
  have hfstFA : CQState.coarsen (Prod.fst : Y × Bool → Y) (CQState.coarsen p FA) =
      CQState.coarsen g FA := CQState.coarsen_coarsen p Prod.fst FA
  have hwFA : ∑ q : Y × Bool, ((CQState.coarsen p FA).stateMap q).trace =
      ∑ x : X, (FA.stateMap x).trace :=
    InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq p FA
  have hkeepPair : 2 * ε < ∑ q : Y × Bool, ((CQState.coarsen p FA).stateMap q).trace := by
    rw [hwFA]; exact hkeep
  have hsupp : ∀ q : Y × Bool, q.2 ≠ true → (CQState.coarsen p FA).stateMap q = 0 := by
    intro q hq
    rw [hpair]
    simpa [CQState.filterKeep_stateMap] using
      (ite_eq_right hq : (if q.2 then ((CQState.coarsen p A).stateMap q) else 0) =
        (0 : SubDensityOp d))
  set η : ℝ := (∑ x : X, (FA.stateMap x).trace) - 2 * ε with hη
  have hη_pos : 0 < η := by rw [hη]; linarith
  have hAweight : ∑ x : X, (FA.stateMap x).trace ≤
      ∑ q : Y × Bool, ((CQState.coarsen p A).stateMap q).trace := by
    rw [InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq p A, hFA]
    exact CQState.sum_filterKeep_stateMap_trace_le keep A
  have hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε (CQState.coarsen p A) σ)) := by
    refine smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη_pos
      (CQState.coarsen p A) σ ?_
    intro τ hτ
    refine CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower (η := η) ?_ hτ
    rw [hη]; linarith [hAweight]
  have h2 : smoothMinEntropyReal ε (CQState.coarsen g A) σ ≤
      smoothMinEntropyReal ε (CQState.coarsen p A) σ := by
    rw [← hfstA]
    exact smoothMinEntropyReal_coarsen_le (CQState.coarsen p A) σ hσ_pd ε hε hbdd
  have h3 : smoothMinEntropyReal ε (CQState.coarsen p A) σ ≤
      smoothMinEntropyReal ε (CQState.coarsen p FA) σ := by
    refine smoothMinEntropyReal_filterKeep_ge ε (CQState.coarsen p A) (CQState.coarsen p FA) σ
      (Prod.snd : Y × Bool → Bool) hε hσ_pd (fun q => ?_) hkeepPair
    rw [hpair, CQState.filterKeep_stateMap]
  have h4 : smoothMinEntropyReal ε (CQState.coarsen p FA) σ ≤
      smoothMinEntropyReal ε (CQState.coarsen g FA) σ := by
    rw [← hfstFA]
    exact smoothMinEntropyReal_coarsen_prodFst_ge_of_fiberSupport ε hε (CQState.coarsen p FA) σ
      hσ_pd true hsupp hkeepPair
  exact le_trans h2 (le_trans h3 h4)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
