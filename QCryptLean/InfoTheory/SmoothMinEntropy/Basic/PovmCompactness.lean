import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.Quantum.Operators.DensityOpTopology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# POVM Compactness — feasible sets, objective bounds, and supremum attainment

This file isolates the feasible-set and topological content needed to show that
the supremum defining `povmGuessingProb` is attained.  It also records the
basic objective rewrites and sSup upper bound used by downstream optimality
arguments.

## Strategy

The raw feasible set

    K = { M : X → Op n | (∀ x v, 0 ≤ (quadraticForm (M x) v).re) ∧ ∑ x, M x = 1 }

is **not bounded** in the norm topology (one can add a skew-Hermitian piece
to one entry and subtract it from another, leaving both conditions intact
while the Frobenius norm blows up).  Instead, we pass to the Hermitian
feasible subset

    K_H = { M : X → Op n | (∀ x, (M x).IsHermitian ∧ (M x).PosSemidef)
                             ∧ ∑ x, M x = 1 }

and reduce along the symmetrization `symmFamily M`.

The main compactness lemma is `exists_optimal_povm_hermitian`:

    ∃ M ∈ K_H, povmGuessingProb ρ = ∑ x, ((M x) * (ρ.stateMap x).toOp).trace.re

from which `InfoTheory.SmoothMinEntropy.exists_optimal_povm` is a short
unpack (PSD ⇒ `0 ≤ (quadraticForm (M x) v).re`).

## Main definitions

- `povmFeasible`: raw POVM-like feasible families.
- `povmFeasibleHerm`: Hermitian PSD feasible POVM families.
- `povmObjective`: the POVM guessing objective as a function on families.

## Main statements

- `povmObjective_eq_sum_state_mul`: cyclic trace rewrite of the objective.
- `povmObjective_le_povmGuessingProb_of_mem`: every feasible family is bounded
  by the guessing supremum.
- `exists_optimal_povm_hermitian`: the Hermitian feasible set attains the
  guessing supremum.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Feasible sets -/

/-- Raw POVM-like feasible set: each `M x` is a matrix with nonnegative real
quadratic form (the weak positivity condition appearing in the definition
of `povmGuessingProb`), and `∑_x M x = 1`. -/
def povmFeasible {X : Type*} [Fintype X] {n : ℕ} : Set (X → Op n) :=
  { M | (∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re) ∧ ∑ x : X, M x = 1 }

/-- Hermitian POVM feasible set: each `M x` is PSD (and hence Hermitian), and
`∑_x M x = 1`. -/
def povmFeasibleHerm {X : Type*} [Fintype X] {n : ℕ} : Set (X → Op n) :=
  { M | (∀ x : X, (M x).PosSemidef) ∧ ∑ x : X, M x = 1 }

/-! ## `oneHotPovm` lies in `povmFeasibleHerm` -/

lemma oneHotPovm_isHermitian {X : Type*} [DecidableEq X] {n : ℕ}
    (x₀ : X) (x : X) : ((oneHotPovm x₀ x : Op n)).IsHermitian := by
  unfold oneHotPovm
  by_cases hx : x = x₀
  · rw [if_pos hx]
    change (1 : Op n)ᴴ = 1
    exact Matrix.conjTranspose_one
  · rw [if_neg hx]
    change (0 : Op n)ᴴ = 0
    exact Matrix.conjTranspose_zero

lemma oneHotPovm_posSemidef {X : Type*} [DecidableEq X] {n : ℕ}
    (x₀ : X) (x : X) : ((oneHotPovm x₀ x : Op n)).PosSemidef := by
  unfold oneHotPovm
  by_cases hx : x = x₀
  · rw [if_pos hx]; exact Matrix.PosSemidef.one
  · rw [if_neg hx]; exact Matrix.PosSemidef.zero

/-- The one-hot family witnesses nonemptiness of `povmFeasibleHerm`. -/
lemma oneHotPovm_mem_povmFeasibleHerm
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (x₀ : X) :
    (oneHotPovm x₀ : X → Op n) ∈ povmFeasibleHerm := by
  refine ⟨fun x => oneHotPovm_posSemidef x₀ x, ?_⟩
  exact oneHotPovm_sum x₀

lemma povmFeasibleHerm_nonempty
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} :
    (povmFeasibleHerm : Set (X → Op n)).Nonempty := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  exact ⟨oneHotPovm x₀, oneHotPovm_mem_povmFeasibleHerm x₀⟩

/-- Inclusion `K_H ⊆ K`. -/
lemma povmFeasibleHerm_subset_povmFeasible
    {X : Type*} [Fintype X] {n : ℕ} :
    (povmFeasibleHerm : Set (X → Op n)) ⊆ povmFeasible := by
  rintro M ⟨hM_prop, hM_sum⟩
  refine ⟨fun x v => ?_, hM_sum⟩
  exact posSemidef_re_quadraticForm_nonneg (hM_prop x) v

/-! ## Symmetrization preserves feasibility and the objective -/

/-- `symmFamily M` is PSD entrywise when `M` has nonneg re quadratic form. -/
lemma symmFamily_posSemidef {X : Type*} {n : ℕ}
    (M : X → Op n)
    (hM_pos : ∀ x : X, ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (M x) v).re)
    (x : X) : (symmFamily M x).PosSemidef :=
  Quantum.Operators.posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
    (symmFamily_isHermitian M x)
    (symmFamily_quadraticForm_re_nonneg M hM_pos x)

/-- Symmetrization sends the raw feasible set into the Hermitian feasible set. -/
lemma symmFamily_mem_povmFeasibleHerm
    {X : Type*} [Fintype X] {n : ℕ}
    {M : X → Op n} (hM : M ∈ povmFeasible) :
    (symmFamily M) ∈ povmFeasibleHerm := by
  obtain ⟨hM_pos, hM_sum⟩ := hM
  refine ⟨fun x => ?_, ?_⟩
  · exact symmFamily_posSemidef M hM_pos x
  · exact symmFamily_sum_eq_one M hM_sum

/-! ## Objective -/

/-- POVM guessing objective as a function of the family `M`. -/
def povmObjective {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : (X → Op n) → ℝ :=
  fun M => ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re

/-- Symmetrization preserves the objective when the target is Hermitian. -/
lemma povmObjective_symmFamily_eq
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) :
    povmObjective ρ (symmFamily M) = povmObjective ρ M := by
  unfold povmObjective
  exact symmFamily_trace_sum_re_eq M (fun x => (ρ.stateMap x).toOp)
    (fun x => (ρ.stateMap x).isHermitian)

/-- The POVM objective can be written with the state factor on the left. -/
lemma povmObjective_eq_sum_state_mul
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) :
    povmObjective ρ M =
      ∑ x : X, (((ρ.stateMap x).toOp * M x).trace.re) := by
  unfold povmObjective
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.trace_mul_comm]

/-! ## Fixed-POVM trace budgets -/

/-- Every component of a Hermitian feasible POVM is dominated by the identity
in the PSD order. -/
lemma povmFeasibleHerm_opLe_one
    {X : Type*} [Fintype X] {n : ℕ}
    {M : X → Op n} (hM : M ∈ (povmFeasibleHerm : Set (X → Op n))) (x : X) :
    opLe (M x) 1 := by
  exact opLe_one_of_sum_eq_one M
    (fun y v => posSemidef_re_quadraticForm_nonneg (hM.1 y) v) hM.2 x

/-- A Hermitian feasible POVM has total trace budget `1` against any density
operator. -/
lemma povmFeasibleHerm_trace_mul_density_sum_eq_one
    {X : Type*} [Fintype X] {n : ℕ}
    (σ : DensityOp n) {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n))) :
    ∑ x : X, ((M x) * σ.toOp).trace.re = 1 := by
  calc
    ∑ x : X, ((M x) * σ.toOp).trace.re =
        ((∑ x : X, (M x) * σ.toOp).trace).re := by
      rw [Matrix.trace_sum, Complex.re_sum]
    _ = (((∑ x : X, M x) * σ.toOp).trace).re := by
      rw [Finset.sum_mul]
    _ = ((1 : Op n) * σ.toOp).trace.re := by
      rw [hM.2]
    _ = 1 := by
      simpa using congrArg Complex.re σ.trace_one

/-- The fixed-POVM objective is nonnegative for Hermitian feasible POVMs. -/
lemma povmObjective_nonneg_of_povmFeasibleHerm
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n))) :
    0 ≤ povmObjective ρ M := by
  unfold povmObjective
  refine Finset.sum_nonneg (fun x _ => ?_)
  have hρ : ((ρ.stateMap x).toOp).PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib
      (ρ.stateMap x).toPosSemidefOp
  exact Quantum.Operators.trace_mul_psd_nonneg (M x)
    (ρ.stateMap x).toOp (hM.1 x) hρ

/-- The fixed-POVM objective is bounded by the total CQ weight. -/
lemma povmObjective_le_weight_sum_of_povmFeasibleHerm
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n))) :
    povmObjective ρ M ≤ ∑ x : X, (ρ.stateMap x).trace := by
  unfold povmObjective
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hρ_psd : ((ρ.stateMap x).toOp).PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib
      (ρ.stateMap x).toPosSemidefOp
  have h_le := trace_mul_le_of_opLe hρ_psd
    (hM.1 x).isHermitian Matrix.isHermitian_one
    (povmFeasibleHerm_opLe_one hM x)
  rw [mul_one, Matrix.trace_mul_comm] at h_le
  simpa [SubDensityOp.trace] using h_le

/-- Real aggregation step for the fixed-POVM KRS argument.

If every block obeys a pointwise squared Cauchy-Schwarz estimate with collision
term `C x`, then the POVM objective is bounded by the square root of the total
collision.  The POVM-specific input is only the trace budget
`∑_x Tr(M_x σ) = 1`. -/
lemma povmObjective_le_sqrt_sum_of_sq_le_trace_mul
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n)))
    (C : X → ℝ)
    (hC_nonneg : ∀ x : X, 0 ≤ C x)
    (h_sq : ∀ x : X,
      (((M x) * (ρ.stateMap x).toOp).trace.re) ^ 2 ≤
        ((M x) * σ.toOp).trace.re * C x) :
    povmObjective ρ M ≤ Real.sqrt (∑ x : X, C x) := by
  let a : X → ℝ := fun x => ((M x) * (ρ.stateMap x).toOp).trace.re
  let b : X → ℝ := fun x => ((M x) * σ.toOp).trace.re
  have hb_nonneg : ∀ x : X, 0 ≤ b x := by
    intro x
    have hσ : σ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
    exact Quantum.Operators.trace_mul_psd_nonneg (M x) σ.toOp
      (hM.1 x) hσ
  have hsum_b : ∑ x : X, b x = 1 := by
    simpa [b] using povmFeasibleHerm_trace_mul_density_sum_eq_one σ hM
  have h_obj : povmObjective ρ M = ∑ x : X, a x := by
    rfl
  rw [h_obj]
  calc
    ∑ x : X, a x ≤ ∑ x : X, Real.sqrt (b x * C x) := by
      refine Finset.sum_le_sum (fun x _ => ?_)
      exact Real.le_sqrt_of_sq_le (by simpa [a, b] using h_sq x)
    _ = ∑ x : X, Real.sqrt (b x) * Real.sqrt (C x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Real.sqrt_mul (hb_nonneg x)]
    _ ≤ Real.sqrt (∑ x : X, b x) * Real.sqrt (∑ x : X, C x) := by
      simpa using
        Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset X) hb_nonneg hC_nonneg
    _ = Real.sqrt (∑ x : X, C x) := by
      rw [hsum_b, Real.sqrt_one, one_mul]

/-! ## Sup equality: `sSup` over `K` equals `sSup` over `K_H` -/

/-- The `sSup`-set appearing in the definition of `povmGuessingProb`, in the
form `povmObjective ρ '' povmFeasible`. -/
lemma povmGuessingProb_eq_sSup_image_povmFeasible
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    povmGuessingProb ρ = sSup (povmObjective ρ '' povmFeasible) := by
  unfold povmGuessingProb povmObjective povmFeasible
  congr 1
  ext p
  constructor
  · rintro ⟨M, hM_pos, hM_sum, rfl⟩
    exact ⟨M, ⟨hM_pos, hM_sum⟩, rfl⟩
  · rintro ⟨M, ⟨hM_pos, hM_sum⟩, rfl⟩
    exact ⟨M, hM_pos, hM_sum, rfl⟩

/-- Any raw feasible POVM family has objective bounded by `povmGuessingProb`. -/
lemma povmObjective_le_povmGuessingProb_of_mem
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) {M : X → Op n} (hM : M ∈ povmFeasible) :
    povmObjective ρ M ≤ povmGuessingProb ρ := by
  rw [povmGuessingProb_eq_sSup_image_povmFeasible ρ]
  refine le_csSup ?_ ⟨M, hM, rfl⟩
  refine ⟨1, ?_⟩
  rintro p ⟨M', ⟨hM'_pos, hM'_sum⟩, rfl⟩
  exact povmLike_traceSum_le_one ρ M' hM'_pos hM'_sum

/-- Image of the objective on `povmFeasibleHerm` equals the image on
`povmFeasible`: symmetrization gives `⊆` and the inclusion
`povmFeasibleHerm ⊆ povmFeasible` gives `⊇`. -/
lemma povmObjective_image_povmFeasible_eq_image_povmFeasibleHerm
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    povmObjective ρ '' povmFeasible = povmObjective ρ '' povmFeasibleHerm := by
  apply Set.Subset.antisymm
  · rintro p ⟨M, hM, rfl⟩
    refine ⟨symmFamily M, symmFamily_mem_povmFeasibleHerm hM, ?_⟩
    exact povmObjective_symmFamily_eq ρ M
  · rintro p ⟨M, hM, rfl⟩
    exact ⟨M, povmFeasibleHerm_subset_povmFeasible hM, rfl⟩

/-- `povmGuessingProb ρ` is the `sSup` of the objective on the Hermitian
feasible set. -/
lemma povmGuessingProb_eq_sSup_image_povmFeasibleHerm
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    povmGuessingProb ρ = sSup (povmObjective ρ '' povmFeasibleHerm) := by
  rw [povmGuessingProb_eq_sSup_image_povmFeasible ρ,
      povmObjective_image_povmFeasible_eq_image_povmFeasibleHerm ρ]

/-- To bound the POVM guessing probability it suffices to bound the objective
on every Hermitian feasible POVM family.

This isolates the final optimization step from fixed-POVM estimates: downstream
arguments can prove `povmObjective ρ M ≤ B` for an arbitrary
`M ∈ povmFeasibleHerm`, then invoke this lemma to pass to
`povmGuessingProb ρ`. -/
lemma povmGuessingProb_le_of_forall_povmFeasibleHerm_objective_le
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) {B : ℝ}
    (hB : ∀ M : X → Op n,
      M ∈ (povmFeasibleHerm : Set (X → Op n)) → povmObjective ρ M ≤ B) :
    povmGuessingProb ρ ≤ B := by
  rw [povmGuessingProb_eq_sSup_image_povmFeasibleHerm ρ]
  refine csSup_le ?_ ?_
  · obtain ⟨M, hM⟩ :=
      (povmFeasibleHerm_nonempty : (povmFeasibleHerm : Set (X → Op n)).Nonempty)
    exact ⟨povmObjective ρ M, M, hM, rfl⟩
  · rintro p ⟨M, hM, rfl⟩
    exact hB M hM

/-! ## Topology of `povmFeasibleHerm`

`Op n = Matrix (Fin n) (Fin n) ℂ` carries only the Pi product topology by
default.  The lemmas below are phrased purely in terms of `IsClosed` and
`IsCompact` on that topological-space instance.
-/

/-- The Hermitian feasible set is closed.  (Each conjunct is closed: the
sum-equals-1 condition is the preimage of `{1}` under `M ↦ ∑ x, M x`;
positive semidefiniteness is closed by `isClosed_setOf_posSemidef`.) -/
lemma povmFeasibleHerm_isClosed
    {X : Type*} [Fintype X] {n : ℕ} :
    IsClosed (povmFeasibleHerm : Set (X → Op n)) := by
  have h_sum : IsClosed (setOf (fun M : X → Op n => ∑ x, M x = 1)) :=
    isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const
  have h_psd : ∀ x : X,
      IsClosed (setOf (fun M : X → Op n => (M x).PosSemidef)) := by
    intro x
    simpa only [Set.preimage, Set.mem_setOf_eq] using
      IsClosed.preimage (f := fun M : X → Op n => M x)
        (continuous_apply x) (isClosed_setOf_posSemidef (n := n))
  have hEq : (povmFeasibleHerm : Set (X → Op n)) =
      (⋂ x, setOf (fun M : X → Op n => (M x).PosSemidef)) ∩
        (setOf (fun M : X → Op n => ∑ x, M x = 1)) := by
    ext M
    simp only [povmFeasibleHerm, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hEq]
  exact (isClosed_iInter h_psd).inter h_sum

/-- Entry-wise bound for PSD operators dominated by the identity.
If `A` is PSD and `opLe A 1` (i.e. `(1 - A)` has nonneg real quadratic form),
then every entry has norm at most `1`.

This is the entry bound needed to package the Hermitian POVM feasible set inside
a compact box.  The proof combines the PSD entry Cauchy-Schwarz bound with
the diagonal estimate coming from `opLe A 1`. -/
lemma posSemidef_le_one_entry_abs_le_one {n : ℕ} {A : Op n}
    (hA_psd : A.PosSemidef) (hA_le : opLe A 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have h_diag_c : ∀ k : Fin n, (0 : ℂ) ≤ A k k :=
    fun k => hA_psd.diag_nonneg (i := k)
  have h_diag_re : ∀ k : Fin n, 0 ≤ (A k k).re :=
    fun k => (Complex.nonneg_iff.mp (h_diag_c k)).1
  have h_diag_le : ∀ k : Fin n, (A k k).re ≤ 1 := by
    intro k
    have h := opLe_re_diag_le hA_le k
    have h1 : ((1 : Op n) k k) = 1 := by simp
    rw [h1] at h
    simpa using h
  have h_bound : (A i i).re * (A j j).re ≤ 1 := by
    calc (A i i).re * (A j j).re
        ≤ 1 * 1 := by
          exact mul_le_mul (h_diag_le i) (h_diag_le j) (h_diag_re j) (by linarith)
      _ = 1 := by ring
  have h_sq_le : ‖A i j‖ ^ 2 ≤ 1 :=
    le_trans (posSemidef_entry_norm_sq_le_diag_mul hA_psd i j) h_bound
  have h_abs : |‖A i j‖| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    exact h_sq_le
  rw [abs_of_nonneg (norm_nonneg (A i j))] at h_abs
  exact h_abs

/-- Every matrix entry of a Hermitian feasible POVM effect has norm at most `1`. -/
lemma povmFeasibleHerm_entry_norm_le_one
    {X : Type*} [Fintype X] {n : ℕ}
    {M : X → Op n} (hM : M ∈ (povmFeasibleHerm : Set (X → Op n)))
    (x : X) (i j : Fin n) :
    ‖M x i j‖ ≤ 1 :=
  posSemidef_le_one_entry_abs_le_one (hM.1 x) (povmFeasibleHerm_opLe_one hM x) i j

/-- The Hermitian feasible set is compact.  Each entry is bounded by `1`
in PSD order (via `opLe_one_of_sum_eq_one` plus
`posSemidef_re_quadraticForm_nonneg`), hence in operator and Frobenius norm;
the full family `X → Op n` is therefore bounded in the finite-dimensional
real vector space `X → Op n`.  Combined with closedness
(`povmFeasibleHerm_isClosed`) and finite-dimensionality this gives
compactness. -/
lemma povmFeasibleHerm_isCompact
    {X : Type*} [Fintype X] {n : ℕ} :
    IsCompact (povmFeasibleHerm : Set (X → Op n)) := by
  classical
  -- Entry-wise closed bounding box B = {M | ∀ x i j, ‖M x i j‖ ≤ 1}.
  set B : Set (X → Op n) :=
    Set.univ.pi (fun _ : X =>
      Set.univ.pi (fun _ : Fin n =>
        Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)))
  have hB_cpt : IsCompact B := by
    refine isCompact_univ_pi (fun _ => ?_)
    refine isCompact_univ_pi (fun _ => ?_)
    refine isCompact_univ_pi (fun _ => ?_)
    exact ProperSpace.isCompact_closedBall (0 : ℂ) 1
  -- Containment via entry bound.
  have hSubset : (povmFeasibleHerm : Set (X → Op n)) ⊆ B := by
    intro M hM x _ i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact povmFeasibleHerm_entry_norm_le_one hM x i j
  exact hB_cpt.of_isClosed_subset povmFeasibleHerm_isClosed hSubset

/-- The POVM guessing objective is continuous.  Pointwise it is a finite
sum of polynomials in the matrix entries of `M`. -/
lemma continuous_povm_objective
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    Continuous (povmObjective ρ : (X → Op n) → ℝ) := by
  unfold povmObjective
  apply continuous_finset_sum
  intro x _
  fun_prop

/-! ## Attainment -/

/-- **Attainment of the POVM guessing supremum on the Hermitian feasible set.**

Combines compactness, nonemptyness, and continuity via
`IsCompact.exists_sSup_image_eq`. -/
lemma exists_optimal_povm_hermitian
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) :
    ∃ M ∈ (povmFeasibleHerm : Set (X → Op n)),
      povmGuessingProb ρ = povmObjective ρ M := by
  classical
  have hK_cpt : IsCompact (povmFeasibleHerm : Set (X → Op n)) :=
    povmFeasibleHerm_isCompact
  have hK_ne : (povmFeasibleHerm : Set (X → Op n)).Nonempty :=
    povmFeasibleHerm_nonempty
  have hcont : ContinuousOn (povmObjective ρ) (povmFeasibleHerm : Set (X → Op n)) :=
    (continuous_povm_objective ρ).continuousOn
  obtain ⟨M, hM, hMeq⟩ :=
    hK_cpt.exists_sSup_image_eq hK_ne hcont
  refine ⟨M, hM, ?_⟩
  rw [povmGuessingProb_eq_sSup_image_povmFeasibleHerm ρ, hMeq]

end InfoTheory.SmoothMinEntropy

end
