import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor

/-!
# Classical Coarsening — CQ pushforwards, trace preservation, extractor regrouping

This file packages the finite pushforward of a CQ state along a classical map
and the corresponding regrouping identity for extractor output states.

## Main definitions
- `CQState.coarsenBlock`: the summed block over one fiber of a classical map.
- `CQState.coarsen`: finite classical pushforward of a CQ state.
- `QuantumHashFamily.precomp`: precomposition of a hash family by a classical map.

## Main statements
- `CQState.coarsen_quantumMarginalOp`: coarsening preserves the quantum marginal.
- `CQState.coarsen_joint_trace_re_eq`: coarsening preserves the joint real trace.
- `extractorOutputState_coarsen_eq_precomp`: extractor output commutes with
  classical coarsening after precomposing the hash family.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.QuantumLHL

/-- Summing a function over all finite fibers of a map recovers the original total sum. -/
lemma sum_fiber_indicator_eq_sum
    {X Y M : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [AddCommMonoid M]
    (g : X → Y) (f : X → M) :
    (∑ y : Y, ∑ x : X, if g x = y then f x else 0) = ∑ x : X, f x := by
  simpa only [Finset.mem_univ, Finset.sum_filter, true_and, eq_comm] using
    (Finset.sum_fiberwise (s := Finset.univ) g f)

end InfoTheory.QuantumLHL

namespace InfoTheory.SmoothMinEntropy

/-- Extensionality for CQ states by their block map. -/
theorem CQState.ext_stateMap {X : Type*} [Fintype X] {n : ℕ}
    {ρ σ : CQState X n} (h : ρ.stateMap = σ.stateMap) : ρ = σ := by
  cases ρ with
  | mk ρMap ρWeight =>
    cases σ with
    | mk σMap σWeight =>
      dsimp at h
      subst σMap
      congr

/-- The `y` block of the classical pushforward of a CQ state along `g : X → Y`.

It is the finite sum of all input blocks in the fiber of `y`. -/
noncomputable def CQState.coarsenBlock {X Y : Type*} [Fintype X] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) : SubDensityOp n where
  toOp := ∑ x : X, if g x = y then (ρ.stateMap x).toOp else 0
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : g x = y
    · rw [ite_eq_left hx]
      exact (ρ.stateMap x).isHermitian
    · simp [hx]
  pos_semidef := by
    intro v
    unfold quadraticForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : g x = y
    · simpa [hx, quadraticForm] using (ρ.stateMap x).pos_semidef v
    · simp [hx]
  trace_le_one := by
    have htrace :
        (∑ x : X, (if g x = y then (ρ.stateMap x).toOp else 0)).trace.re =
          ∑ x : X, if g x = y then (ρ.stateMap x).trace else 0 := by
      rw [Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : g x = y
      · simp [hx, SubDensityOp.trace]
      · simp [hx]
    rw [htrace]
    calc
      ∑ x : X, (if g x = y then (ρ.stateMap x).trace else 0) ≤
          ∑ x : X, (ρ.stateMap x).trace := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : g x = y
        · simp [hx]
        · simp [hx, (ρ.stateMap x).trace_nonneg]
      _ ≤ 1 := ρ.weight_le_one

@[simp]
lemma CQState.coarsenBlock_toOp {X Y : Type*} [Fintype X] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) :
    (CQState.coarsenBlock g ρ y).toOp =
      ∑ x : X, if g x = y then (ρ.stateMap x).toOp else 0 :=
  rfl

lemma CQState.coarsenBlock_trace {X Y : Type*} [Fintype X] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) :
    (CQState.coarsenBlock g ρ y).trace =
      ∑ x : X, if g x = y then (ρ.stateMap x).trace else 0 := by
  unfold CQState.coarsenBlock SubDensityOp.trace
  rw [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : g x = y
  · simp [hx]
  · simp [hx]

/-- Classical pushforward of a finite CQ state along `g : X → Y`.

The coarsened `Y` block is the finite sum of all `X` blocks in the fiber of `g`. -/
noncomputable def CQState.coarsen {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) : CQState Y n where
  stateMap := CQState.coarsenBlock g ρ
  weight_le_one := by
    calc
      ∑ y : Y, (CQState.coarsenBlock g ρ y).trace =
          ∑ y : Y, ∑ x : X, if g x = y then (ρ.stateMap x).trace else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        rw [CQState.coarsenBlock_trace]
      _ = ∑ x : X, ∑ y : Y, if g x = y then (ρ.stateMap x).trace else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x : X, (ρ.stateMap x).trace := by
        apply Finset.sum_congr rfl
        intro x _
        have hsum := Finset.sum_ite_eq (Finset.univ : Finset Y) (g x)
          (fun _ => (ρ.stateMap x).trace)
        simp
      _ ≤ 1 := ρ.weight_le_one

@[simp]
lemma CQState.coarsen_stateMap {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) :
    (CQState.coarsen g ρ).stateMap y = CQState.coarsenBlock g ρ y :=
  rfl

@[simp]
lemma CQState.coarsen_stateMap_toOp {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) :
    ((CQState.coarsen g ρ).stateMap y).toOp =
      ∑ x : X, if g x = y then (ρ.stateMap x).toOp else 0 :=
  rfl

lemma CQState.coarsen_stateMap_trace {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {n : ℕ} (g : X → Y) (ρ : CQState X n) (y : Y) :
    ((CQState.coarsen g ρ).stateMap y).trace =
      ∑ x : X, if g x = y then (ρ.stateMap x).trace else 0 :=
  CQState.coarsenBlock_trace g ρ y

/-- Classical coarsening preserves the quantum marginal operator. -/
theorem CQState.coarsen_quantumMarginalOp {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {n : ℕ} (g : X → Y) (ρ : CQState X n) :
    (CQState.coarsen g ρ).quantumMarginalOp = ρ.quantumMarginalOp := by
  unfold CQState.quantumMarginalOp
  calc
    ∑ y : Y, ((CQState.coarsen g ρ).stateMap y).toOp =
        ∑ y : Y, ∑ x : X, if g x = y then (ρ.stateMap x).toOp else 0 := by
      rfl
    _ = ∑ x : X, ∑ y : Y, if g x = y then (ρ.stateMap x).toOp else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : X, (ρ.stateMap x).toOp := by
      apply Finset.sum_congr rfl
      intro x _
      have hsum := Finset.sum_ite_eq (Finset.univ : Finset Y) (g x)
        (fun _ => (ρ.stateMap x).toOp)
      simp

/-- Classical coarsening preserves the quantum marginal wrapper. -/
theorem CQState.coarsen_quantumMarginal {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {n : ℕ} (g : X → Y) (ρ : CQState X n) :
    (CQState.coarsen g ρ).quantumMarginal = ρ.quantumMarginal := by
  apply SubDensityOp.ext
  exact CQState.coarsen_quantumMarginalOp g ρ

end InfoTheory.SmoothMinEntropy

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- The difference of two coarsened blocks is the fiberwise sum of block differences. -/
lemma CQState.coarsen_stateMap_toOp_sub_eq_sum
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ ρ' : CQState X n) (y : Y) :
    ((CQState.coarsen g ρ).stateMap y).toOp -
        ((CQState.coarsen g ρ').stateMap y).toOp =
      ∑ x : X, if g x = y then
        (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0 := by
  rw [CQState.coarsen_stateMap_toOp, CQState.coarsen_stateMap_toOp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : g x = y <;> simp [hx]

/-- The total trace of the CQ blocks is preserved by finite classical coarsening. -/
lemma CQState.sum_coarsen_stateMap_trace_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) :
    ∑ y : Y, ((CQState.coarsen g ρ).stateMap y).trace =
      ∑ x : X, (ρ.stateMap x).trace := by
  calc
    ∑ y : Y, ((CQState.coarsen g ρ).stateMap y).trace =
        ∑ y : Y, ∑ x : X, if g x = y then (ρ.stateMap x).trace else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [CQState.coarsen_stateMap_trace]
    _ = ∑ x : X, (ρ.stateMap x).trace := by
      exact sum_fiber_indicator_eq_sum g (fun x : X => (ρ.stateMap x).trace)

/-- Classical coarsening preserves the real trace of the CQ joint density. -/
lemma CQState.coarsen_joint_trace_re_eq
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (g : X → Y) (ρ : CQState X n) :
    (CQState.coarsen g ρ).toJointDensity.toOp.trace.re =
      ρ.toJointDensity.toOp.trace.re := by
  have hLHS :
      (CQState.coarsen g ρ).toJointDensity.toOp.trace.re =
        ∑ y : Y, ((CQState.coarsen g ρ).stateMap y).trace := by
    change (CQState.coarsen g ρ).toJointDensity.trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
  have hRHS :
      ρ.toJointDensity.toOp.trace.re =
        ∑ x : X, (ρ.stateMap x).trace := by
    change ρ.toJointDensity.trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
  rw [hLHS, hRHS]
  exact CQState.sum_coarsen_stateMap_trace_eq g ρ

/-- Precompose the domain of a quantum hash family by a finite classical map. -/
def QuantumHashFamily.precomp {S X Y Z : Type*} (H : QuantumHashFamily S Y Z)
    (g : X → Y) : QuantumHashFamily S X Z where
  hash := fun s x => H.hash s (g x)
  seedFintype := H.seedFintype
  seedNonempty := H.seedNonempty
  outputFintype := H.outputFintype
  outputNonempty := H.outputNonempty

@[simp]
lemma QuantumHashFamily.precomp_hash {S X Y Z : Type*} (H : QuantumHashFamily S Y Z)
    (g : X → Y) (s : S) (x : X) :
    (H.precomp g).hash s x = H.hash s (g x) :=
  rfl

/-- Extractor weighted blocks regroup over a classical coarsening. -/
theorem extractorWeightedOp_coarsen_eq_precomp
    {S X Y Z : Type*} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S Y Z) (g : X → Y) (ρ : CQState X n) (z : Z) :
    extractorWeightedOp H (CQState.coarsen g ρ) z =
      extractorWeightedOp (H.precomp g) ρ z := by
  unfold extractorWeightedOp
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  calc
    ∑ y : Y, (if H.hash s y = z then ((CQState.coarsen g ρ).stateMap y).toOp else 0) =
        ∑ y : Y, ∑ x : X,
          if H.hash s y = z then (if g x = y then (ρ.stateMap x).toOp else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : H.hash s y = z
      · simp [hy]
      · simp [hy]
    _ = ∑ x : X, ∑ y : Y,
          if H.hash s y = z then (if g x = y then (ρ.stateMap x).toOp else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : X, if H.hash s (g x) = z then (ρ.stateMap x).toOp else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have hswap :
          (∑ y : Y,
            if H.hash s y = z then (if g x = y then (ρ.stateMap x).toOp else 0) else 0) =
            ∑ y : Y, if g x = y then
              (if H.hash s y = z then (ρ.stateMap x).toOp else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hgy : g x = y <;> by_cases hhy : H.hash s y = z <;> simp [hgy, hhy]
      rw [hswap]
      have hsum := Finset.sum_ite_eq (Finset.univ : Finset Y) (g x)
        (fun y => if H.hash s y = z then (ρ.stateMap x).toOp else 0)
      simp

/-- Extractor conditioned operators regroup over a classical coarsening. -/
theorem extractorConditionedOp_coarsen_eq_precomp
    {S X Y Z : Type*} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S Y Z) (g : X → Y) (ρ : CQState X n) (z : Z) :
    extractorConditionedOp H (CQState.coarsen g ρ) z =
      extractorConditionedOp (H.precomp g) ρ z := by
  apply SubDensityOp.ext
  exact extractorWeightedOp_coarsen_eq_precomp H g ρ z

/-- Applying a hash family to a coarsened CQ state is the same extractor output
as applying the precomposed hash family to the raw CQ state. -/
theorem extractorOutputState_coarsen_eq_precomp
    {S X Y Z : Type*} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S Y Z) (g : X → Y) (ρ : CQState X n) :
    extractorOutputState H (CQState.coarsen g ρ) =
      extractorOutputState (H.precomp g) ρ := by
  apply CQState.ext_stateMap
  funext z
  exact extractorConditionedOp_coarsen_eq_precomp H g ρ z

end InfoTheory.QuantumLHL

end -- noncomputable section
