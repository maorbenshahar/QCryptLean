import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.MinEntropyGuess

/-!
# Classical Coarsening for Optimized CQ Min-Entropy

This file records the operational data-processing step for finite classical
coarsening.  The proof is phrased through POVM guessing probability: a POVM for
the fine register can be pushed forward to a POVM for the coarsened register,
and the coarsened objective contains the fine objective plus nonnegative
PSD trace cross-terms.

## Main definitions
- `povmCoarsen`: push a fine-register POVM forward along a classical map.

## Main statements
- `povmCoarsen_mem_povmFeasibleHerm`: POVM feasibility is preserved by coarsening.
- `povmGuessingProb_le_povmGuessingProb_coarsen`: guessing probability is monotone
  under finite classical coarsening.
- `conditionalMinEntropyOptReal_coarsen_le`: optimized CQ min-entropy data-processing
  inequality for classical coarsening.
-/

open Quantum.Operators Matrix Real
open InfoTheory.QuantumLHL
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Push a POVM indexed by a fine finite type forward along a classical map. -/
def povmCoarsen {X Y : Type*} [Fintype X] [DecidableEq Y] {n : ℕ}
    (g : X → Y) (M : X → Op n) : Y → Op n :=
  fun y => ∑ x : X, if g x = y then M x else 0

/-- Each pushed-forward POVM element is PSD when the fine POVM elements are PSD. -/
lemma povmCoarsen_posSemidef {X Y : Type*} [Fintype X] [DecidableEq Y] {n : ℕ}
    (g : X → Y) {M : X → Op n}
    (hM : ∀ x : X, (M x).PosSemidef) (y : Y) :
    (povmCoarsen g M y).PosSemidef := by
  unfold povmCoarsen
  exact Matrix.posSemidef_sum (s := (Finset.univ : Finset X))
    (x := fun x : X => if g x = y then M x else 0)
    (by
      intro x _
      by_cases hx : g x = y
      · simpa only [hx, if_true] using hM x
      · simpa only [hx, if_false] using (Matrix.PosSemidef.zero : (0 : Op n).PosSemidef))

/-- Pushing a Hermitian feasible POVM along a finite classical map preserves feasibility. -/
lemma povmCoarsen_mem_povmFeasibleHerm
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {n : ℕ}
    (g : X → Y) {M : X → Op n} (hM : M ∈ povmFeasibleHerm) :
    povmCoarsen g M ∈ (povmFeasibleHerm : Set (Y → Op n)) := by
  refine ⟨fun y => povmCoarsen_posSemidef g hM.1 y, ?_⟩
  calc
    ∑ y : Y, povmCoarsen g M y =
        ∑ y : Y, ∑ x : X, if g x = y then M x else 0 := by
      rfl
    _ = ∑ x : X, M x := sum_fiber_indicator_eq_sum g M
    _ = 1 := hM.2

/-- The fine POVM element at `x` is dominated by the pushed-forward element at
the fiber label `g x`. -/
lemma povmCoarsen_self_opLe
    {X Y : Type*} [Fintype X] [DecidableEq Y] {n : ℕ}
    (g : X → Y) {M : X → Op n}
    (hM : ∀ x : X, (M x).PosSemidef) (x₀ : X) :
    opLe (M x₀) (povmCoarsen g M (g x₀)) := by
  intro v
  unfold povmCoarsen
  have hsum :
      (quadraticForm (∑ x : X, if g x = g x₀ then M x else 0) v).re =
        ∑ x : X, (quadraticForm (if g x = g x₀ then M x else 0) v).re := by
    unfold quadraticForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [hsum]
  have hterm :
      (quadraticForm (if g x₀ = g x₀ then M x₀ else 0) v).re =
        (quadraticForm (M x₀) v).re := by
    simp only [if_true]
  rw [← hterm]
  exact Finset.single_le_sum
    (s := (Finset.univ : Finset X))
    (f := fun x : X => (quadraticForm (if g x = g x₀ then M x else 0) v).re)
    (fun x _ => by
      by_cases hx : g x = g x₀
      · simpa only [hx, if_true] using posSemidef_re_quadraticForm_nonneg (hM x) v
      · change 0 ≤ (quadraticForm (if g x = g x₀ then M x else 0) v).re
        rw [if_neg hx]
        unfold quadraticForm
        simp only [Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
        exact le_rfl)
    (Finset.mem_univ x₀)

/-- Tracing a coarse CQ block against a coarse POVM element is the sum of the
trace contributions over the corresponding fiber. -/
lemma trace_mul_coarsen_stateMap_toOp_eq_sum
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {n : ℕ}
    (g : X → Y) (ρ : CQState X n) (N : Y → Op n) (y : Y) :
    ((N y) * ((CQState.coarsen g ρ).stateMap y).toOp).trace.re =
      ∑ x : X, if g x = y then ((N (g x)) * (ρ.stateMap x).toOp).trace.re else 0 := by
  rw [CQState.coarsen_stateMap_toOp, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : g x = y
  · simp only [hx, if_true]
  · simp only [hx, if_false, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- Objective against a coarsened CQ state can be evaluated by pulling the
coarse POVM family back along the classical map. -/
lemma povmObjective_coarsen_eq_sum_comp
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {n : ℕ}
    (g : X → Y) (ρ : CQState X n) (N : Y → Op n) :
    povmObjective (CQState.coarsen g ρ) N =
      ∑ x : X, ((N (g x)) * (ρ.stateMap x).toOp).trace.re := by
  unfold povmObjective
  calc
    ∑ y : Y, ((N y) * ((CQState.coarsen g ρ).stateMap y).toOp).trace.re =
        ∑ y : Y,
          ∑ x : X, if g x = y then ((N (g x)) * (ρ.stateMap x).toOp).trace.re else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [trace_mul_coarsen_stateMap_toOp_eq_sum]
    _ = ∑ x : X, ((N (g x)) * (ρ.stateMap x).toOp).trace.re :=
      sum_fiber_indicator_eq_sum g
        (fun x : X => ((N (g x)) * (ρ.stateMap x).toOp).trace.re)

/-- Each fine-label trace contribution is bounded by the contribution of the
pushed-forward POVM element at its fiber label. -/
lemma trace_mul_le_trace_mul_povmCoarsen_self
    {X Y : Type*} [Fintype X] [DecidableEq Y] {n : ℕ}
    (g : X → Y) (ρ : CQState X n) {M : X → Op n}
    (hM : ∀ x : X, (M x).PosSemidef) (x : X) :
    ((M x) * (ρ.stateMap x).toOp).trace.re ≤
      ((povmCoarsen g M (g x)) * (ρ.stateMap x).toOp).trace.re := by
  have hρ_psd : ((ρ.stateMap x).toOp).PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have htrace :=
    trace_mul_le_of_opLe hρ_psd (hM x).isHermitian
      (povmCoarsen_posSemidef g hM (g x)).isHermitian
      (povmCoarsen_self_opLe g hM x)
  rw [Matrix.trace_mul_comm (ρ.stateMap x).toOp (M x),
    Matrix.trace_mul_comm (ρ.stateMap x).toOp (povmCoarsen g M (g x))] at htrace
  exact htrace

/-- A fine POVM's objective is bounded by the objective of its pushforward on
the coarsened CQ state. -/
lemma povmObjective_le_povmObjective_coarsen
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {n : ℕ}
    (g : X → Y) (ρ : CQState X n) {M : X → Op n}
    (hM : ∀ x : X, (M x).PosSemidef) :
    povmObjective ρ M ≤
      povmObjective (CQState.coarsen g ρ) (povmCoarsen g M) := by
  unfold povmObjective
  calc
    ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re ≤
        ∑ x : X, ((povmCoarsen g M (g x)) * (ρ.stateMap x).toOp).trace.re := by
      apply Finset.sum_le_sum
      intro x _
      exact trace_mul_le_trace_mul_povmCoarsen_self g ρ hM x
    _ = povmObjective (CQState.coarsen g ρ) (povmCoarsen g M) := by
      rw [povmObjective_coarsen_eq_sum_comp]

/-- Classical coarsening can only increase the optimal POVM guessing probability. -/
theorem povmGuessingProb_le_povmGuessingProb_coarsen
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} [NeZero n] (g : X → Y) (ρ : CQState X n)
    (hp : 0 < povmGuessingProb ρ) :
    povmGuessingProb ρ ≤ povmGuessingProb (CQState.coarsen g ρ) := by
  classical
  haveI : Nonempty X := nonempty_of_povmGuessingProb_pos hp
  obtain ⟨M, hM, hM_eq⟩ := exists_optimal_povm_hermitian ρ
  have hN : povmCoarsen g M ∈
      (povmFeasibleHerm : Set (Y → Op n)) :=
    povmCoarsen_mem_povmFeasibleHerm g hM
  calc
    povmGuessingProb ρ = povmObjective ρ M := hM_eq
    _ ≤ povmObjective (CQState.coarsen g ρ) (povmCoarsen g M) :=
      povmObjective_le_povmObjective_coarsen g ρ hM.1
    _ ≤ povmGuessingProb (CQState.coarsen g ρ) :=
      povmObjective_le_povmGuessingProb_of_mem (CQState.coarsen g ρ)
        (povmFeasibleHerm_subset_povmFeasible hN)

/-- Finite classical coarsening cannot increase optimized CQ min-entropy. -/
theorem conditionalMinEntropyOptReal_coarsen_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} [NeZero n] (g : X → Y) (ρ : CQState X n)
    (hp : 0 < povmGuessingProb ρ) :
    conditionalMinEntropyOptReal (CQState.coarsen g ρ) ≤
      conditionalMinEntropyOptReal ρ := by
  have hPg : povmGuessingProb ρ ≤ povmGuessingProb (CQState.coarsen g ρ) :=
    povmGuessingProb_le_povmGuessingProb_coarsen g ρ hp
  rw [conditionalMinEntropyReal_cq_guess_eq (CQState.coarsen g ρ),
    conditionalMinEntropyReal_cq_guess_eq ρ]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog :
      Real.log (povmGuessingProb ρ) ≤
        Real.log (povmGuessingProb (CQState.coarsen g ρ)) :=
    Real.log_le_log hp hPg
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) hlog2.le

end InfoTheory.SmoothMinEntropy

end
