import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.AnnounceCoarsenCommute
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernelBlockRef

/-!
# Fiber references for coarsened announcements

Fiberwise operator domination supplies block-diagonal reference certificates after classical
coarsening. Fine or coarse purified-distance witnesses yield the stated extended smooth entropy
floors.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Block-diagonal operators on the announced register -/

/-- `Σ_p |p⟩⟨p| ⊗ A_p` on `C ⊗ E`, for an arbitrary family `A` of operators on `E`.

`blockDiagRefOp` is this construction at a sub-density family; the two agree definitionally
(`blockDiagRefOp_eq_blockDiagOp`).  `Op.tensor` places its left argument in the high digit, so the
announced register `C` sits in the high digits. -/
def blockDiagOp {dE dC : ℕ} (A : Fin dC → Op dE) : Op (dC * dE) :=
  ∑ p : Fin dC, Op.tensor (stdKet dC p * (stdKet dC p).dag) (A p)

lemma blockDiagRefOp_eq_blockDiagOp {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) :
    blockDiagRefOp ν = blockDiagOp (fun p => (ν p).toOp) := rfl

/-- The `(k, ·), (k, ·)` block of `Σ_p |p⟩⟨p| ⊗ A_p` is `A_k`: the off-diagonal announcement blocks
contribute nothing, by orthogonality of the `|p⟩`. -/
lemma blockDiagOp_apply_diagBlock {dE dC : ℕ} (A : Fin dC → Op dE) (k : Fin dC) (i j : Fin dE) :
    blockDiagOp A (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) = A k i j := by
  rw [blockDiagOp, Matrix.sum_apply, Finset.sum_eq_single k]
  · exact stdKetProj_tensor_apply_diagBlock (A k) k i j
  · intro p _ hp
    rw [Op_tensor_apply_finProd]
    simp [ket_mul_bra_apply, Ket.dag_vec, hp]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The quadratic form written out as a double sum over matrix entries. -/
private lemma quadraticForm_eq_double_sum_fibre {n : ℕ} (M : Op n) (v : Fin n → ℂ) :
    quadraticForm M v = ∑ i : Fin n, ∑ j : Fin n, star (v i) * M i j * v j := by
  simp only [quadraticForm, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, ← mul_assoc]

/-- **Renner's classical-conditioning equivalence at a block-diagonal left argument** —
arXiv:quant-ph/0512258v2 `main.tex:2936`, `\label{eq:classcondeq}`.

  `Σ_p |p⟩⟨p| ⊗ A_p ≼ t · Σ_p |p⟩⟨p| ⊗ ν_p   ⟺   ∀ p, A_p ≼ t · ν_p`.

Forward: test on vectors supported in block `p`, where every other announcement block drops out.
Backward: the difference splits as `Σ_p |p⟩⟨p| ⊗ (t·ν_p − A_p)`, a sum of positive semidefinite
terms.  No dimension factor enters in either direction.

`opLe_stdKetProj_tensor_blockDiagRefOp_iff` (`ClassicalAnnounceKernelBlockRef.lean`) is the case
where a single `A_p` is nonzero. -/
theorem opLe_blockDiagOp_blockDiagRefOp_iff {dE dC : ℕ}
    (ν : Fin dC → SubDensityOp dE) {A : Fin dC → Op dE} (hA : ∀ p, (A p).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) :
    opLe (blockDiagOp A) (Complex.ofReal t • blockDiagRefOp ν)
      ↔ ∀ p : Fin dC, opLe (A p) (Complex.ofReal t • (ν p).toOp) := by
  constructor
  · intro h p v
    have h1 := h (leftBlockVector p v)
    rw [quadraticForm_leftBlockVector_eq_sum, quadraticForm_leftBlockVector_eq_sum] at h1
    have hL : ∀ i j : Fin dE,
        blockDiagOp A (finProdFinEquiv (p, i)) (finProdFinEquiv (p, j)) = A p i j :=
      fun i j => blockDiagOp_apply_diagBlock A p i j
    have hR : ∀ i j : Fin dE,
        (Complex.ofReal t • blockDiagRefOp ν)
            (finProdFinEquiv (p, i)) (finProdFinEquiv (p, j))
          = (Complex.ofReal t • (ν p).toOp) i j := by
      intro i j
      rw [Matrix.smul_apply, Matrix.smul_apply, blockDiagRefOp_apply_diagBlock]
    simp only [hL, hR] at h1
    rw [quadraticForm_eq_double_sum_fibre, quadraticForm_eq_double_sum_fibre]
    exact h1
  · intro h
    apply opLe_of_posSemidef_sub
    have hsplit : (Complex.ofReal t • blockDiagRefOp ν) - blockDiagOp A
        = ∑ p : Fin dC, Op.tensor (stdKet dC p * (stdKet dC p).dag)
            ((Complex.ofReal t • (ν p).toOp) - A p) := by
      rw [blockDiagRefOp, blockDiagOp, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Quantum.TensorProducts.Op.tensor_sub_right,
        Quantum.TensorProducts.Op.tensor_smul_right]
    rw [hsplit]
    refine Matrix.posSemidef_sum _ (fun p _ => ?_)
    have hνp : ((Complex.ofReal t • (ν p).toOp)).PosSemidef :=
      (posSemidefOp_implies_mathlib (ν p).toPosSemidefOp).smul (Complex.zero_le_real.mpr ht)
    exact Op.tensor_posSemidef_mathlib (ketbra_posSemidef _)
      (opLe.posSemidef_sub (hA p) hνp.isHermitian (h p))

/-! ## The fibre blocks of the refined classical register -/

/-- The `(y, p)` block of the coarsening along the **refined** map `x ↦ (g x, ann x)` is the fibre
sum `Σ_{x : g x = y ∧ ann x = p} ρ_x`.

This exhibits the fibre sums below as the blocks of an honest CQ state on `Y × Fin dC`, which is
where their Hermiticity and positivity come from. -/
lemma coarsenBlock_pairMap_toOp {X Y : Type*} [Fintype X] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ann : X → Fin dC) (ρ : CQState X dE) (y : Y) (p : Fin dC) :
    (CQState.coarsenBlock (fun x => (g x, ann x)) ρ (y, p)).toOp
      = ∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0 := by
  rw [CQState.coarsenBlock_toOp]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : g x = y ∧ ann x = p
  · rw [ite_eq_left (Prod.ext hx.1 hx.2), ite_eq_left hx]
  · rw [ite_eq_right (fun h => hx ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩), ite_eq_right hx]

/-- The fibre sums are Hermitian, being the blocks of a CQ state. -/
lemma fibreSum_isHermitian {X Y : Type*} [Fintype X] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ann : X → Fin dC) (ρ : CQState X dE) (y : Y) (p : Fin dC) :
    (∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0).IsHermitian := by
  rw [← coarsenBlock_pairMap_toOp g ann ρ y p]
  exact (CQState.coarsenBlock (fun x => (g x, ann x)) ρ (y, p)).isHermitian

/-- **The coarsened announced state is block diagonal in the announced register, with the fibre sums
in its blocks.**

`Σ_{x : g x = y} |ann x⟩⟨ann x| ⊗ ρ_x = Σ_p |p⟩⟨p| ⊗ (Σ_{x : g x = y ∧ ann x = p} ρ_x)`.

Block twin of `bb84AnnounceCoarsenCQ_stateMap`, which states the
left-hand side for the BB84 announce-then-coarsen construction. -/
lemma coarsen_tensorLeftKernel_stateMap_toOp_eq_blockDiagOp
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag) (y : Y) :
    ((CQState.coarsen g (ρ.tensorLeftKernel K)).stateMap y).toOp
      = blockDiagOp
          (fun p => ∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0) := by
  have hpull : ∀ p : Fin dC,
      Op.tensor (stdKet dC p * (stdKet dC p).dag)
          (∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0)
        = ∑ x : X, if g x = y ∧ ann x = p then
            Op.tensor (stdKet dC p * (stdKet dC p).dag) (ρ.stateMap x).toOp else 0 := by
    intro p
    rw [tensor_sum_op]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : g x = y ∧ ann x = p
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, tensor_zero_op]
  calc ((CQState.coarsen g (ρ.tensorLeftKernel K)).stateMap y).toOp
      = ∑ x : X, if g x = y then
          Op.tensor (stdKet dC (ann x) * (stdKet dC (ann x)).dag) (ρ.stateMap x).toOp else 0 := by
        rw [CQState.coarsen_stateMap_toOp]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : g x = y
        · rw [ite_eq_left hx, ite_eq_left hx, CQState.tensorLeftKernel_stateMap,
            show ((K x).tensor (ρ.stateMap x)).toOp
                = Op.tensor (K x).toOp (ρ.stateMap x).toOp from rfl, hK x]
        · rw [ite_eq_right hx, ite_eq_right hx]
    _ = ∑ x : X, ∑ p : Fin dC, if g x = y ∧ ann x = p then
          Op.tensor (stdKet dC p * (stdKet dC p).dag) (ρ.stateMap x).toOp else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : g x = y
        · rw [ite_eq_left hx,
            show (∑ p : Fin dC, if g x = y ∧ ann x = p then
                  Op.tensor (stdKet dC p * (stdKet dC p).dag) (ρ.stateMap x).toOp else 0)
                = ∑ p : Fin dC, if ann x = p then
                  Op.tensor (stdKet dC p * (stdKet dC p).dag) (ρ.stateMap x).toOp else 0 from
              Finset.sum_congr rfl fun p _ => by simp [hx]]
          simp
        · rw [ite_eq_right hx]
          refine (Finset.sum_eq_zero fun p _ => ?_).symm
          exact ite_eq_right (fun h => hx h.1)
    _ = ∑ p : Fin dC, ∑ x : X, if g x = y ∧ ann x = p then
          Op.tensor (stdKet dC p * (stdKet dC p).dag) (ρ.stateMap x).toOp else 0 :=
        Finset.sum_comm
    _ = blockDiagOp
          (fun p => ∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0) :=
        (Finset.sum_congr rfl fun p _ => hpull p).symm

/-! ## The fibre-sum feasibility equivalence -/

/-- **The announcement costs nothing, at the level of the min-entropy SDP, even when it is not
constant on the fibres of the coarsening.**

The coarsened announced pair
`(coarsen g (ρ ⊗ K), Σ_p |p⟩⟨p| ⊗ ν_p)` and the family of **fibre-sum** conditions

  `Σ_{x : g x = y ∧ ann x = p} ρ_x ≼ t · ν_p`,

one for each pair `(y, p)` of a coarse classical value and an announcement value, have literally
the same set of feasible scalars `t`.  Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:2936`,
`\label{eq:classcondeq}` in the CQ encoding, with the `z`-block of that lemma read as the whole
fibre `{x : g x = y ∧ ann x = p}` rather than a single classical value.

`isFeasible_tensorLeftKernel_blockDiagRef_iff` (`ClassicalAnnounceKernelBlockRef.lean`) is the case
`g = id`, where each fibre is a single `x`.

`K` is an arbitrary announce kernel that happens to be the deterministic classical announcement
`|ann x⟩⟨ann x|`; the hypothesis is stated on `toOp` so any library carrier of that projector
discharges it.  The only hypothesis on the reference family is the sub-normalisation
`Σ_p tr ν_p ≤ 1` that `blockDiagRef` demands. -/
theorem isFeasible_coarsen_tensorLeftKernel_blockDiagRef_iff
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (t : ℝ) :
    isFeasible (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν) t
      ↔ 0 ≤ t ∧ ∀ (y : Y) (p : Fin dC),
          opLe (∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0)
            (Complex.ofReal t • (ν p).toOp) := by
  constructor
  · rintro ⟨ht, hy⟩
    refine ⟨ht, fun y p => ?_⟩
    have h := hy y
    rw [coarsen_tensorLeftKernel_stateMap_toOp_eq_blockDiagOp g ρ ann K hK y,
      blockDiagRef_toOp] at h
    exact (opLe_blockDiagOp_blockDiagRefOp_iff ν
      (fun q => fibreSum_isHermitian g ann ρ y q) ht).mp h p
  · rintro ⟨ht, hyp⟩
    refine ⟨ht, fun y => ?_⟩
    rw [coarsen_tensorLeftKernel_stateMap_toOp_eq_blockDiagOp g ρ ann K hK y, blockDiagRef_toOp]
    exact (opLe_blockDiagOp_blockDiagRefOp_iff ν
      (fun q => fibreSum_isHermitian g ann ρ y q) ht).mpr (hyp y)

/-- **The charge is exactly zero**, for the coarsened announced state as well.

The optimum of the coarsened announced min-entropy SDP equals the optimum of the fibre-sum problem,
so no constant — in particular no `log₂ d_C` — separates them. -/
theorem minFeasibleLambda_coarsen_tensorLeftKernel_blockDiagRef_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    minFeasibleLambda (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν)
      = sInf (Set.ofPred (fun t : ℝ => 0 ≤ t ∧ ∀ (y : Y) (p : Fin dC),
          opLe (∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0)
            (Complex.ofReal t • (ν p).toOp))) := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_coarsen_tensorLeftKernel_blockDiagRef_iff g ρ ann K hK ν hν t

/-! ## The entropy bounds -/

/-- Announcing then coarsening preserves the total classical weight: the announce blocks are
normalised and the coarsening is a classical pushforward. -/
lemma sum_coarsen_tensorLeftKernel_trace_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (K : X → SubDensityOp dC) (hKtr : ∀ x, (K x).trace = 1) :
    ∑ y : Y, ((CQState.coarsen g (ρ.tensorLeftKernel K)).stateMap y).trace
      = ∑ x : X, (ρ.stateMap x).trace := by
  rw [InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq g (ρ.tensorLeftKernel K)]
  exact CQState.tensorLeftKernel_weight ρ K hKtr

/-- **The unsmoothed zero-charge announce bound at a coarsened classical register** — Renner 2005
(arXiv:quant-ph/0512258v2) `main.tex:2917`, `\label{lem:Hminclasscondr}`.

A fibre-sum domination `Σ_{x : g x = y ∧ ann x = p} ρ_x ≼ 2^(−k) · ν_p` at a single scalar gives
`k ≤ H_min(Y | C E)` for the coarsened announced state against `Σ_p |p⟩⟨p| ⊗ ν_p`, with **nothing
subtracted**.

`hweight` rules out the `minFeasibleLambda = 0` sentinel of `conditionalMinEntropyReal`; no
positive-definiteness of the reference is needed because feasibility is supplied by `hfibre`
rather than derived. -/
theorem conditionalMinEntropyReal_coarsen_tensorLeftKernel_blockDiagRef_ge
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hweight : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (hfibre : ∀ (y : Y) (p : Fin dC),
      opLe (∑ x : X, if g x = y ∧ ann x = p then (ρ.stateMap x).toOp else 0)
        (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν p).toOp)) :
    k ≤ conditionalMinEntropyReal (CQState.coarsen g (ρ.tensorLeftKernel K))
      (blockDiagRef ν hν) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-k) := Real.rpow_pos_of_pos (by norm_num) _
  have hfeas : isFeasible (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν)
      ((2 : ℝ) ^ (-k)) :=
    (isFeasible_coarsen_tensorLeftKernel_blockDiagRef_iff g ρ ann K hK ν hν _).mpr
      ⟨hpow.le, hfibre⟩
  have hlam_le := minFeasibleLambda_le_of_isFeasible _ _ hfeas
  have hw : 0 < ∑ y : Y, ((CQState.coarsen g (ρ.tensorLeftKernel K)).stateMap y).trace := by
    rw [sum_coarsen_tensorLeftKernel_trace_eq g ρ K
      (fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x))]
    exact hweight
  have hpos := minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hw ⟨_, hfeas⟩
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k _ _ k hpos hlam_le

/-! ## The metric input: a classical coarsening contracts the CQ purified distance -/

/-- An off-fibre index contributes no fidelity: both blocks are the zero operator there. -/
private lemma fidelity_ite_fibre {n : ℕ} [NeZero n] {P : Prop} [Decidable P]
    (A B : SubDensityOp n) :
    Quantum.Metrics.fidelity (if P then A.toPosSemidefOp else 0)
        (if P then B.toPosSemidefOp else 0)
      = if P then Quantum.Metrics.fidelity A.toPosSemidefOp B.toPosSemidefOp else 0 := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
    exact Quantum.Metrics.fidelity_eq_zero_of_left_toOp_eq_zero _ _ rfl

/-- **A classical coarsening does not decrease the CQ Uhlmann fidelity.**

The fidelity of CQ joint densities is the sum of blockwise fidelities
(`CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity`), and merging the blocks of a fibre can
only increase it, by fidelity super-additivity `Quantum.Metrics.fidelity_sum_le_fidelity_sum`. -/
lemma CQState.fidelity_toJointDensity_le_coarsen
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} [NeZero n] [NeZero (n * Fintype.card X)] [NeZero (n * Fintype.card Y)]
    (g : X → Y) (ρ τ : CQState X n) :
    Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp τ.toJointDensity.toPosSemidefOp
      ≤ Quantum.Metrics.fidelity (CQState.coarsen g ρ).toJointDensity.toPosSemidefOp
          (CQState.coarsen g τ).toJointDensity.toPosSemidefOp := by
  rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
    CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
  have hsum : ∀ (υ : CQState X n) (y : Y),
      ((CQState.coarsen g υ).stateMap y).toPosSemidefOp.toOp
        = (∑ x : X, if g x = y then (υ.stateMap x).toPosSemidefOp else 0).toOp := by
    intro υ y
    rw [Quantum.Operators.PosSemidefOp.sum_toOp, CQState.coarsen_stateMap_toOp]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : g x = y
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx]
      rfl
  have hkey : ∀ y : Y,
      (∑ x : X, if g x = y then
          Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp (τ.stateMap x).toPosSemidefOp
        else 0)
      ≤ Quantum.Metrics.fidelity ((CQState.coarsen g ρ).stateMap y).toPosSemidefOp
          ((CQState.coarsen g τ).stateMap y).toPosSemidefOp := by
    intro y
    rw [Quantum.Metrics.fidelity_congr (hsum ρ y) (hsum τ y)]
    refine le_trans (le_of_eq ?_) (Quantum.Metrics.fidelity_sum_le_fidelity_sum
      (fun x => if g x = y then (ρ.stateMap x).toPosSemidefOp else 0)
      (fun x => if g x = y then (τ.stateMap x).toPosSemidefOp else 0))
    exact (Finset.sum_congr rfl fun x _ =>
      fidelity_ite_fibre (ρ.stateMap x) (τ.stateMap x)).symm
  calc ∑ x : X, Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp
          (τ.stateMap x).toPosSemidefOp
      = ∑ y : Y, ∑ x : X, if g x = y then
          Quantum.Metrics.fidelity (ρ.stateMap x).toPosSemidefOp (τ.stateMap x).toPosSemidefOp
        else 0 := (InfoTheory.QuantumLHL.sum_fiber_indicator_eq_sum g _).symm
    _ ≤ ∑ y : Y, Quantum.Metrics.fidelity ((CQState.coarsen g ρ).stateMap y).toPosSemidefOp
          ((CQState.coarsen g τ).stateMap y).toPosSemidefOp :=
        Finset.sum_le_sum fun y _ => hkey y

/-- **A classical coarsening contracts the CQ purified distance.**

The CQ specialisation of monotonicity of the purified distance under a CPTP map, for the classical
pushforward `CQState.coarsen g` along an arbitrary map `g : X → Y`.  Sibling of
`CQState.purifiedDistance_partialTraceB_contract`; it strictly generalises the injective-map
equality case.

Both ingredients are blockwise: coarsening preserves the total weight, so the sub-normalisation
correction of `fidelityGen` is unchanged, and it does not decrease the Uhlmann fidelity. -/
theorem CQState.purifiedDistance_coarsen_le
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {n : ℕ} [NeZero n]
    (g : X → Y) (ρ τ : CQState X n) :
    CQState.purifiedDistance (CQState.coarsen g ρ) (CQState.coarsen g τ) ≤
      CQState.purifiedDistance ρ τ := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have : NeZero (n * Fintype.card Y) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_fidelityGen_ge
  have htr : ∀ υ : CQState X n,
      (CQState.coarsen g υ).toJointDensity.trace = υ.toJointDensity.trace := by
    intro υ
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq g υ
  unfold fidelityGen
  refine add_le_add (CQState.fidelity_toJointDensity_le_coarsen g ρ τ) (le_of_eq ?_)
  rw [htr ρ, htr τ]

/-- A coarse-register ball witness with fibre domination certifies an extended smooth
floor against the coarsened announced reference. -/
theorem smoothMinEntropy_coarsen_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    {X Y : Type*} [Fintype X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (g : X → Y) (ρ ρbar : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (hball : CQState.purifiedDistance (CQState.coarsen g (ρ.tensorLeftKernel K))
      (CQState.coarsen g (ρbar.tensorLeftKernel K)) ≤ ε)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hfibre : ∀ (y : Y) (p : Fin dC),
      opLe (∑ x : X, if g x = y ∧ ann x = p then (ρbar.stateMap x).toOp else 0)
        (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν p).toOp)) :
    ENNReal.ofReal k ≤
      smoothMinEntropy ε (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν) := by
  apply smoothMinEntropy_ge_of_isFeasible _
    (CQState.coarsen g (ρbar.tensorLeftKernel K)) _ k hball
  exact (isFeasible_coarsen_tensorLeftKernel_blockDiagRef_iff g ρbar ann K hK ν hν _).mpr
    ⟨Real.rpow_nonneg (by norm_num) _, hfibre⟩

/-- A fine-register ball witness with fibre domination certifies an extended smooth
floor against the coarsened announced reference. -/
theorem smoothMinEntropy_coarsen_tensorLeftKernel_blockDiagRef_ge_of_fineBallWitness
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (g : X → Y) (ρ ρbar : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (hball : CQState.purifiedDistance ρ ρbar ≤ ε)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hfibre : ∀ (y : Y) (p : Fin dC),
      opLe (∑ x : X, if g x = y ∧ ann x = p then (ρbar.stateMap x).toOp else 0)
        (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν p).toOp)) :
    ENNReal.ofReal k ≤
      smoothMinEntropy ε (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν) := by
  apply smoothMinEntropy_coarsen_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    ε g ρ ρbar ann K hK _ ν hν k hfibre
  exact (CQState.purifiedDistance_coarsen_le g _ _).trans
    ((CQState.purifiedDistance_tensorLeftKernel_le ρ ρbar K
      (fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x))).trans hball)


/-- A positive-weight witness in the coarsened ball with fibrewise block domination gives the
signed smooth floor `k`. -/
theorem smoothMinEntropyReal_coarsen_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (g : X → Y) (ρ ρbar : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (hball : CQState.purifiedDistance (CQState.coarsen g (ρ.tensorLeftKernel K))
      (CQState.coarsen g (ρbar.tensorLeftKernel K)) ≤ ε)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hweight : 0 < ∑ x : X, (ρbar.stateMap x).trace)
    (hfibre : ∀ (y : Y) (p : Fin dC),
      opLe (∑ x : X, if g x = y ∧ ann x = p then (ρbar.stateMap x).toOp else 0)
        (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν p).toOp))
    (hbdd : BddAbove
      (Set.ofPred (isInSmoothedSetReal ε (CQState.coarsen g (ρ.tensorLeftKernel K))
        (blockDiagRef ν hν)))) :
    k ≤ smoothMinEntropyReal ε (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν) := by
  have hmem : isInSmoothedSetReal ε (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν)
      (conditionalMinEntropyReal (CQState.coarsen g (ρbar.tensorLeftKernel K))
        (blockDiagRef ν hν)) :=
    ⟨CQState.coarsen g (ρbar.tensorLeftKernel K), rfl, hball⟩
  refine le_trans ?_ (le_csSup hbdd hmem)
  exact conditionalMinEntropyReal_coarsen_tensorLeftKernel_blockDiagRef_ge g ρbar ann K hK ν hν k
    hweight hfibre

/-- A positive-weight witness in the original ball with fibrewise block domination gives the
coarsened signed smooth floor `k`. -/
theorem smoothMinEntropyReal_coarsen_tensorLeftKernel_blockDiagRef_ge_of_fineBallWitness
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (g : X → Y) (ρ ρbar : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (hball : CQState.purifiedDistance ρ ρbar ≤ ε)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hweight : 0 < ∑ x : X, (ρbar.stateMap x).trace)
    (hfibre : ∀ (y : Y) (p : Fin dC),
      opLe (∑ x : X, if g x = y ∧ ann x = p then (ρbar.stateMap x).toOp else 0)
        (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν p).toOp))
    (hbdd : BddAbove
      (Set.ofPred (isInSmoothedSetReal ε (CQState.coarsen g (ρ.tensorLeftKernel K))
        (blockDiagRef ν hν)))) :
    k ≤ smoothMinEntropyReal ε (CQState.coarsen g (ρ.tensorLeftKernel K)) (blockDiagRef ν hν) := by
  refine smoothMinEntropyReal_coarsen_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    ε g ρ ρbar ann K hK ?_ ν hν k hweight hfibre hbdd
  refine le_trans (CQState.purifiedDistance_coarsen_le g _ _) ?_
  exact le_trans (CQState.purifiedDistance_tensorLeftKernel_le ρ ρbar K
    (fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x))) hball

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
