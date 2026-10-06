import QCryptLean.InfoTheory.SmoothMinEntropy.ChainRule.SmoothEntropyBridgeLemmas
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.CQExtensionFiber
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.Operators.PrincipalSubmatrix

/-!
# Lifting classical coarsening

A coarse CQ state can be lifted to nearby fine states. Feasible coefficients transfer through this
lift, proving that classical coarsening cannot increase smooth min-entropy.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Metrics

/-- **(S1) Block-diagonal Uhlmann-fidelity additivity.**

The Uhlmann fidelity of two CQ block-diagonal PSD operators is the sum of the
blockwise Uhlmann fidelities. This is the equality content extracted from
`Quantum.Metrics.fidelity_sum_le_fidelity_sum`. -/
theorem fidelity_cqBlockPosSemidefOp_eq_sum
    {X : Type*} [Fintype X] [DecidableEq X]
    {d : ℕ} [NeZero d] [NeZero (d * Fintype.card X)]
    (A B : X → PosSemidefOp d) :
    Quantum.Metrics.fidelity (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B) =
      ∑ x : X, Quantum.Metrics.fidelity (A x) (B x) := by
  rw [Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
    Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum]
  exact Finset.sum_congr rfl
    (fun x _ => (Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct (A x) (B x)).symm)

/-! ## S2: the `F`-dephasing pinch as a CPTP map -/

/-- The cq reindexing equivalence: the `Fin d × F` block layout for the quantum
register `Fin (d * card F)`, matching `cqBlockPosSemidefOp`. -/
def fiberEquiv (F : Type*) [Fintype F] (d : ℕ) :
    Fin d × F ≃ Fin (d * Fintype.card F) :=
  (Equiv.prodCongr (Equiv.refl (Fin d)) (Fintype.equivFin F)).trans finProdFinEquiv

lemma fiberEquiv_apply {F : Type*} [Fintype F] {d : ℕ} (i : Fin d) (f : F) :
    fiberEquiv F d (i, f) = finProdFinEquiv (i, Fintype.equivFin F f) := rfl

/-- The orthogonal projector onto the `f`-th fiber block, as a diagonal `0/1`
operator on the quantum register `Fin (d * card F)`. -/
def blockProjDiag {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ} (f : F) :
    Op (d * Fintype.card F) :=
  Matrix.diagonal (fun p => if ((fiberEquiv F d).symm p).2 = f then (1 : ℂ) else 0)

@[simp] lemma blockProjDiag_conjTranspose {F : Type*} [Fintype F] [DecidableEq F]
    {d : ℕ} (f : F) :
    (blockProjDiag (d := d) f)ᴴ = blockProjDiag (d := d) f := by
  unfold blockProjDiag
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  rw [Pi.star_apply]
  split_ifs <;> simp

/-- Completeness relation for the fiber projectors: `∑_f Πf† Πf = 1`. -/
lemma blockProjDiag_completeness {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ} :
    ∑ f : F, (blockProjDiag (d := d) f)ᴴ * blockProjDiag (d := d) f = 1 := by
  have hidem : ∀ f : F, (blockProjDiag (d := d) f)ᴴ * blockProjDiag (d := d) f =
      blockProjDiag (d := d) f := by
    intro f
    rw [blockProjDiag_conjTranspose]
    unfold blockProjDiag
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    split_ifs <;> simp
  simp_rw [hidem]
  unfold blockProjDiag
  ext p q
  rw [Matrix.sum_apply]
  simp_rw [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, Matrix.one_apply_eq]
    rw [Finset.sum_ite_eq Finset.univ ((fiberEquiv F d).symm p).2 (fun _ => (1 : ℂ))]
    simp
  · simp only [if_neg hpq, Finset.sum_const_zero, Matrix.one_apply_ne hpq]

/-- The `F`-dephasing pinch channel on the quantum register `Fin (d * card F)`:
`M ↦ ∑_f Πf · M · Πf`, where `Πf` projects onto the `f`-th fiber block. -/
def fDephasingMap (F : Type*) [Fintype F] [DecidableEq F] (d : ℕ) :
    Op (d * Fintype.card F) →ₗ[ℂ] Op (d * Fintype.card F) :=
  Quantum.Channels.krausMapFintype (fun f : F => blockProjDiag (d := d) f)

lemma fDephasingMap_apply {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (M : Op (d * Fintype.card F)) :
    fDephasingMap F d M =
      ∑ f : F, blockProjDiag (d := d) f * M * (blockProjDiag (d := d) f)ᴴ := rfl

/-- The dephasing pinch is a CPTP quantum channel. -/
lemma fDephasingMap_isCPTP {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    [NeZero (d * Fintype.card F)] :
    Quantum.Channels.IsCPTP ⇑(fDephasingMap F d) :=
  Quantum.Channels.krausMapFintype_isCPTP _ blockProjDiag_completeness

/-- Entrywise action of the dephasing pinch: it keeps the entry `(p, q)` exactly
when `p` and `q` lie in the same fiber block, and zeros it otherwise. -/
lemma fDephasingMap_apply_entry {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (M : Op (d * Fintype.card F)) (p q : Fin (d * Fintype.card F)) :
    fDephasingMap F d M p q =
      if ((fiberEquiv F d).symm p).2 = ((fiberEquiv F d).symm q).2 then M p q else 0 := by
  rw [fDephasingMap_apply]
  simp_rw [blockProjDiag_conjTranspose]
  rw [Matrix.sum_apply]
  have hterm : ∀ f : F,
      (blockProjDiag (d := d) f * M * blockProjDiag (d := d) f) p q =
        (if ((fiberEquiv F d).symm p).2 = f then (1:ℂ) else 0) * M p q *
        (if ((fiberEquiv F d).symm q).2 = f then (1:ℂ) else 0) := by
    intro f
    unfold blockProjDiag
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp_rw [hterm]
  by_cases hab : ((fiberEquiv F d).symm p).2 = ((fiberEquiv F d).symm q).2
  · rw [if_pos hab]
    rw [Finset.sum_eq_single ((fiberEquiv F d).symm p).2]
    · rw [if_pos rfl, if_pos hab.symm]; ring
    · intro f _ hf
      rw [if_neg (Ne.symm hf), zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro f _
    by_cases haf : ((fiberEquiv F d).symm p).2 = f
    · have hbf : ((fiberEquiv F d).symm q).2 ≠ f := fun h => hab (haf.trans h.symm)
      rw [if_neg hbf, mul_zero]
    · rw [if_neg haf, zero_mul, zero_mul]

/-- The `f`-th fiber diagonal block of an operator on the quantum register:
the principal submatrix indexed by the `f`-fiber. -/
def blockExtract {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : Op (d * Fintype.card F)) : Op d :=
  M.submatrix (fun i => fiberEquiv F d (i, f)) (fun j => fiberEquiv F d (j, f))

@[simp] lemma blockExtract_apply {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : Op (d * Fintype.card F)) (i j : Fin d) :
    blockExtract f M i j = M (fiberEquiv F d (i, f)) (fiberEquiv F d (j, f)) := rfl

/-- **Action of the dephasing pinch.** The pinch sends `M` to the block-diagonal
operator (in the fiber layout) whose blocks are the fiber diagonal blocks of `M`.
This is the operator form connecting the pinch to `cqBlockPosSemidefOp`. -/
lemma fDephasingMap_eq_reindex_blockDiagonal {F : Type*} [Fintype F] [DecidableEq F]
    {d : ℕ} (M : Op (d * Fintype.card F)) :
    fDephasingMap F d M =
      Matrix.reindex (fiberEquiv F d) (fiberEquiv F d)
        (Matrix.blockDiagonal (fun f => blockExtract f M)) := by
  ext p q
  rw [fDephasingMap_apply_entry, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal_apply]
  by_cases h : ((fiberEquiv F d).symm p).2 = ((fiberEquiv F d).symm q).2
  · rw [if_pos h, if_pos h]
    have hp : (fiberEquiv F d)
        (((fiberEquiv F d).symm p).1, ((fiberEquiv F d).symm p).2) = p := by
      rw [Prod.mk.eta]; exact Equiv.apply_symm_apply _ _
    have hq : (fiberEquiv F d)
        (((fiberEquiv F d).symm q).1, ((fiberEquiv F d).symm p).2) = q := by
      rw [h, Prod.mk.eta]; exact Equiv.apply_symm_apply _ _
    rw [blockExtract_apply, hp, hq]
  · rw [if_neg h, if_neg h]

/-! ## S3: bundle / extract plumbing -/

/-- The fiber diagonal blocks sum to the partial trace over the fiber register. -/
lemma sum_blockExtract_eq_partialTraceB {F : Type*} [Fintype F] {d : ℕ}
    (M : Op (d * Fintype.card F)) :
    ∑ f : F, blockExtract f M = Quantum.TensorProducts.partialTraceB M := by
  ext i j
  rw [Matrix.sum_apply]
  simp_rw [blockExtract_apply, fiberEquiv_apply]
  rw [Equiv.sum_comp (Fintype.equivFin F)
    (fun k => M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)))]
  rfl

/-- Trace of a CQ block-diagonal PSD operator is the sum of blockwise traces. -/
lemma cqBlockPosSemidefOp_trace {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}
    (A : X → PosSemidefOp d) :
    (cqBlockPosSemidefOp A).toOp.trace = ∑ x : X, (A x).toOp.trace := by
  rw [cqBlockPosSemidefOp_toOp, Matrix.trace_reindex_self, Matrix.trace_blockDiagonal]

/-- Build a `PosSemidefOp` from a Mathlib positive-semidefinite matrix. -/
def posSemidefOpOfMathlib {n : ℕ} {B : Op n} (hB : B.PosSemidef) : PosSemidefOp n :=
  ⟨⟨B, hB.1⟩, posSemidef_re_quadraticForm_nonneg hB⟩

@[simp] lemma posSemidefOpOfMathlib_toOp {n : ℕ} {B : Op n} (hB : B.PosSemidef) :
    (posSemidefOpOfMathlib hB).toOp = B := rfl

/-- The fiber diagonal block of a `PosSemidefOp`, as a `PosSemidefOp`. -/
def blockExtractPSD {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : PosSemidefOp (d * Fintype.card F)) : PosSemidefOp d :=
  posSemidefOpOfMathlib
    ((posSemidefOp_implies_mathlib M).submatrix (fun i => fiberEquiv F d (i, f)))

@[simp] lemma blockExtractPSD_toOp {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : PosSemidefOp (d * Fintype.card F)) :
    (blockExtractPSD f M).toOp = blockExtract f M.toOp := rfl

/-- The pinch image of a PSD operator, repackaged as a CQ block-diagonal operator. -/
lemma cqBlock_blockExtractPSD_toOp_eq_fDephasing {F : Type*} [Fintype F] [DecidableEq F]
    {d : ℕ} (M : PosSemidefOp (d * Fintype.card F)) :
    (cqBlockPosSemidefOp (fun f => blockExtractPSD f M)).toOp = fDephasingMap F d M.toOp := by
  rw [fDephasingMap_eq_reindex_blockDiagonal, cqBlockPosSemidefOp_toOp]
  rfl

/-- The fiber diagonal block of a `SubDensityOp`, as a `SubDensityOp`: the
principal submatrix's trace is bounded by the ambient diagonal sum. -/
def blockExtractSub {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : SubDensityOp (d * Fintype.card F)) : SubDensityOp d where
  toPosSemidefOp := blockExtractPSD f M.toPosSemidefOp
  trace_le_one := by
    have hinj : Function.Injective (fun i : Fin d => fiberEquiv F d (i, f)) :=
      fun a b h => (Prod.ext_iff.mp ((fiberEquiv F d).injective h)).1
    have hle := Quantum.Operators.posSemidef_submatrix_trace_re_le_sum_diag_re
      (posSemidefOp_implies_mathlib M.toPosSemidefOp)
      (fun i : Fin d => fiberEquiv F d (i, f)) hinj
    change (blockExtractPSD f M.toPosSemidefOp).toOp.trace.re ≤ 1
    rw [blockExtractPSD_toOp]
    refine le_trans hle (le_trans (le_of_eq ?_) M.trace_le_one)
    simp [Matrix.trace, Matrix.diag, Complex.re_sum]

@[simp] lemma blockExtractSub_toOp {F : Type*} [Fintype F] {d : ℕ} (f : F)
    (M : SubDensityOp (d * Fintype.card F)) :
    (blockExtractSub f M).toOp = blockExtract f M.toOp := rfl

/-- The CQ block-diagonal bundle of a fiber family of sub-density operators. -/
def bundleSub {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → SubDensityOp d) (h : ∑ f : F, (A f).trace ≤ 1) :
    SubDensityOp (d * Fintype.card F) where
  toPosSemidefOp := cqBlockPosSemidefOp (fun f => (A f).toPosSemidefOp)
  trace_le_one := by
    show (cqBlockPosSemidefOp (fun f => (A f).toPosSemidefOp)).toOp.trace.re ≤ 1
    rw [cqBlockPosSemidefOp_trace, Complex.re_sum]
    exact h

@[simp] lemma bundleSub_toOp {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → SubDensityOp d) (h : ∑ f : F, (A f).trace ≤ 1) :
    (bundleSub A h).toOp = (cqBlockPosSemidefOp (fun f => (A f).toPosSemidefOp)).toOp := rfl

lemma bundleSub_trace {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → SubDensityOp d) (h : ∑ f : F, (A f).trace ≤ 1) :
    (bundleSub A h).trace = ∑ f : F, (A f).trace := by
  change (cqBlockPosSemidefOp (fun f => (A f).toPosSemidefOp)).toOp.trace.re = _
  rw [cqBlockPosSemidefOp_trace, Complex.re_sum]
  rfl

/-- Per-fiber weight bound: each `y`-fiber has total weight at most one. -/
lemma bundle_perY {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (ρ : CQState (Y × F) d) (y : Y) :
    ∑ f : F, (ρ.stateMap (y, f)).trace ≤ 1 := by
  calc ∑ f : F, (ρ.stateMap (y, f)).trace
      ≤ ∑ y' : Y, ∑ f : F, (ρ.stateMap (y', f)).trace :=
        Finset.single_le_sum
          (fun y' _ => Finset.sum_nonneg fun f _ => (ρ.stateMap (y', f)).trace_nonneg)
          (Finset.mem_univ y)
    _ = ∑ x : Y × F, (ρ.stateMap x).trace :=
        (Fintype.sum_prod_type (fun x => (ρ.stateMap x).trace)).symm
    _ ≤ 1 := ρ.weight_le_one

/-- Move the fiber `F` of a CQ state into the quantum register (block-diagonal). -/
def bundle {Y F : Type*} [Fintype Y] [Fintype F] [DecidableEq F] {d : ℕ}
    (ρ : CQState (Y × F) d) : CQState Y (d * Fintype.card F) where
  stateMap y := bundleSub (fun f => ρ.stateMap (y, f)) (bundle_perY ρ y)
  weight_le_one := by
    have heach : ∀ y : Y,
        (bundleSub (fun f => ρ.stateMap (y, f)) (bundle_perY ρ y)).trace =
          ∑ f : F, (ρ.stateMap (y, f)).trace :=
      fun y => bundleSub_trace _ _
    simp_rw [heach]
    calc ∑ y : Y, ∑ f : F, (ρ.stateMap (y, f)).trace
        = ∑ x : Y × F, (ρ.stateMap x).trace :=
          (Fintype.sum_prod_type (fun x => (ρ.stateMap x).trace)).symm
      _ ≤ 1 := ρ.weight_le_one

@[simp] lemma bundle_stateMap {Y F : Type*} [Fintype Y] [Fintype F] [DecidableEq F]
    {d : ℕ} (ρ : CQState (Y × F) d) (y : Y) :
    (bundle ρ).stateMap y = bundleSub (fun f => ρ.stateMap (y, f)) (bundle_perY ρ y) := rfl

/-- The product-projection coarsening sums each fiber. -/
lemma coarsen_prodFst_stateMap_toOp {Y F : Type*} [Fintype Y] [Fintype F] [DecidableEq Y]
    {d : ℕ} (ρ : CQState (Y × F) d) (y : Y) :
    ((CQState.coarsen (Prod.fst : Y × F → Y) ρ).stateMap y).toOp =
      ∑ f : F, (ρ.stateMap (y, f)).toOp := by
  rw [CQState.coarsen_stateMap_toOp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single y]
  · apply Finset.sum_congr rfl; intro f _; rw [if_pos rfl]
  · intro y' _ hy'
    apply Finset.sum_eq_zero; intro f _; rw [if_neg hy']
  · intro h; exact absurd (Finset.mem_univ y) h

/-- `partialTraceB` of the bundle recovers the product-projection coarsening:
the bundle is a blockwise extension of the coarse state. -/
lemma partialTraceB_bundle_eq_coarsen {Y F : Type*} [Fintype Y] [Fintype F]
    [DecidableEq Y] [DecidableEq F] {d : ℕ} (ρ : CQState (Y × F) d) :
    (bundle ρ).partialTraceB = CQState.coarsen (Prod.fst : Y × F → Y) ρ := by
  apply CQState.partialTraceB_eq_of_stateMap_toOp
  intro y
  rw [coarsen_prodFst_stateMap_toOp]
  have h := congrArg (fun A : PosSemidefOp d => A.toOp)
    (cqBlockPosSemidefOp_partialTraceB_eq_sum
      (fun f => (ρ.stateMap (y, f)).toPosSemidefOp))
  simp only [] at h
  rw [Quantum.Operators.PosSemidefOp.sum_toOp] at h
  exact h

/-- The fiber diagonal blocks sum to the trace of the original sub-density. -/
lemma sum_blockExtractSub_trace {F : Type*} [Fintype F] {d : ℕ}
    (M : SubDensityOp (d * Fintype.card F)) :
    ∑ f : F, (blockExtractSub f M).trace = M.trace := by
  calc ∑ f : F, (blockExtractSub f M).trace
      = ∑ f : F, ((blockExtract f M.toOp).trace).re := rfl
    _ = ((∑ f : F, blockExtract f M.toOp).trace).re := by
        rw [Matrix.trace_sum, Complex.re_sum]
    _ = (Quantum.TensorProducts.partialTraceB M.toOp).trace.re := by
        rw [sum_blockExtract_eq_partialTraceB]
    _ = M.toOp.trace.re := by rw [Quantum.TensorProducts.trace_partialTraceB]
    _ = M.trace := rfl

/-- `cqBlockPosSemidefOp` restated with the `fiberEquiv` reindexing. -/
lemma cqBlock_toOp_fiberEquiv {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → PosSemidefOp d) :
    (cqBlockPosSemidefOp A).toOp =
      Matrix.reindex (fiberEquiv F d) (fiberEquiv F d)
        (Matrix.blockDiagonal (fun f => (A f).toOp)) := rfl

/-- The fiber diagonal block of a CQ block-diagonal operator is the corresponding block. -/
lemma blockExtract_cqBlock {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → PosSemidefOp d) (f : F) :
    blockExtract f (cqBlockPosSemidefOp A).toOp = (A f).toOp := by
  ext i j
  rw [blockExtract_apply, cqBlock_toOp_fiberEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  rw [Matrix.blockDiagonal_apply, if_pos rfl]

/-- The pinch fixes a CQ block-diagonal operator. -/
lemma fDephasingMap_cqBlock {F : Type*} [Fintype F] [DecidableEq F] {d : ℕ}
    (A : F → PosSemidefOp d) :
    fDephasingMap F d (cqBlockPosSemidefOp A).toOp = (cqBlockPosSemidefOp A).toOp := by
  have hPQ : (fun f => blockExtract f (cqBlockPosSemidefOp A).toOp) =
      (fun x => (A x).toOp) := by
    funext f; exact blockExtract_cqBlock A f
  rw [fDephasingMap_eq_reindex_blockDiagonal, hPQ, ← cqBlock_toOp_fiberEquiv]

/-- **The fiber classical↔quantum move preserves generalized fidelity.** Bundling
the fiber `F` into the quantum register leaves the CQ generalized fidelity
unchanged: ordinary fidelity is block-additive and traces are preserved. -/
lemma fidelityGen_bundle_eq {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (μ ν : CQState (Y × F) d) :
    fidelityGen (bundle μ).toJointDensity (bundle ν).toJointDensity =
      fidelityGen μ.toJointDensity ν.toJointDensity := by
  haveI : NeZero (Fintype.card F) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (d * Fintype.card F) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  haveI : NeZero ((d * Fintype.card F) * Fintype.card Y) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI : NeZero (Fintype.card (Y × F)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (d * Fintype.card (Y × F)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  have hfid : Quantum.Metrics.fidelity (bundle μ).toJointDensity.toPosSemidefOp
        (bundle ν).toJointDensity.toPosSemidefOp =
      Quantum.Metrics.fidelity μ.toJointDensity.toPosSemidefOp
        ν.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
        CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
    have hblock : ∀ y : Y,
        Quantum.Metrics.fidelity ((bundle μ).stateMap y).toPosSemidefOp
            ((bundle ν).stateMap y).toPosSemidefOp =
          ∑ f : F, Quantum.Metrics.fidelity (μ.stateMap (y, f)).toPosSemidefOp
            (ν.stateMap (y, f)).toPosSemidefOp :=
      fun y => fidelity_cqBlockPosSemidefOp_eq_sum
        (fun f => (μ.stateMap (y, f)).toPosSemidefOp)
        (fun f => (ν.stateMap (y, f)).toPosSemidefOp)
    simp_rw [hblock]
    rw [← Fintype.sum_prod_type (fun p : Y × F =>
      Quantum.Metrics.fidelity (μ.stateMap p).toPosSemidefOp (ν.stateMap p).toPosSemidefOp)]
  have htrμ : (bundle μ).toJointDensity.trace = μ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    simp_rw [bundle_stateMap, bundleSub_trace]
    rw [← Fintype.sum_prod_type (fun p : Y × F => (μ.stateMap p).trace)]
  have htrν : (bundle ν).toJointDensity.trace = ν.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    simp_rw [bundle_stateMap, bundleSub_trace]
    rw [← Fintype.sum_prod_type (fun p : Y × F => (ν.stateMap p).trace)]
  unfold fidelityGen
  rw [hfid, htrμ, htrν]

/-- The fine witness produced by the lift: extract each fiber diagonal block of the
extension back into the classical register. -/
def coarsenLiftWitness {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (τhat : CQState Y (d * Fintype.card F)) : CQState (Y × F) d where
  stateMap x := blockExtractSub x.2 (τhat.stateMap x.1)
  weight_le_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [sum_blockExtractSub_trace]
    exact τhat.weight_le_one

@[simp] lemma coarsenLiftWitness_stateMap {Y F : Type*} [Fintype Y] [Fintype F] {d : ℕ}
    (τhat : CQState Y (d * Fintype.card F)) (x : Y × F) :
    (coarsenLiftWitness τhat).stateMap x = blockExtractSub x.2 (τhat.stateMap x.1) := rfl

/-! ## d2: the smooth coarsening lift, and the smooth coarsening DPI -/

/-- **(d2) The smooth coarsening lift (product-projection case).**

For the product projection `g = Prod.fst : Y × F → Y`, every coarse witness `τ` in
the `ε`-ball of `CQState.coarsen g ρ` lifts to a fine witness `τ'` in the `ε`-ball
of `ρ` with `CQState.coarsen g τ' = τ`.  This is Uhlmann's theorem for the
coarsening channel: bundle `F` into the quantum register, apply the
partial-trace Uhlmann extension, and pinch the extension to its `F`-block-diagonal
part (the distance is preserved by the data-processing inequality for the pinch). -/
theorem exists_coarsen_preimage_in_ball
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ρ : CQState (Y × F) d) (ε : ℝ) (τ : CQState Y d)
    (hτ : CQState.purifiedDistance (CQState.coarsen (Prod.fst : Y × F → Y) ρ) τ ≤ ε) :
    ∃ τ' : CQState (Y × F) d,
      CQState.purifiedDistance ρ τ' ≤ ε ∧
      CQState.coarsen (Prod.fst : Y × F → Y) τ' = τ := by
  haveI : NeZero (Fintype.card F) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (d * Fintype.card F) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  -- 1. Uhlmann extension of the coarse witness through the bundle.
  have hdist : CQState.purifiedDistance (bundle ρ).partialTraceB τ ≤ ε := by
    rw [partialTraceB_bundle_eq_coarsen]; exact hτ
  obtain ⟨τhat, hτhat_dist, hτhat_pt⟩ :=
    CQState.exists_extension_of_partialTraceB_purifiedDistance (bundle ρ) τ ε hdist
  refine ⟨coarsenLiftWitness τhat, ?_, ?_⟩
  · -- distance bound: pinch DPI + the fiber classical↔quantum move
    have hA : fidelityGen (bundle ρ).toJointDensity τhat.toJointDensity ≤
        fidelityGen (bundle ρ).toJointDensity
          (bundle (coarsenLiftWitness τhat)).toJointDensity := by
      refine CQState.fidelityGen_le_fidelityGen_blockwise_cptp
        (bundle ρ) τhat (bundle ρ) (bundle (coarsenLiftWitness τhat))
        (fun _ => fDephasingMap F d) (fun _ => fDephasingMap_isCPTP) ?_ ?_
      · intro y
        rw [bundle_stateMap, bundleSub_toOp]
        exact (fDephasingMap_cqBlock (fun f => (ρ.stateMap (y, f)).toPosSemidefOp)).symm
      · intro y
        rw [bundle_stateMap, bundleSub_toOp]
        exact cqBlock_blockExtractPSD_toOp_eq_fDephasing (τhat.stateMap y).toPosSemidefOp
    rw [fidelityGen_bundle_eq] at hA
    have hstep := purifiedDistance_le_of_fidelityGen_ge ρ.toJointDensity
      (coarsenLiftWitness τhat).toJointDensity (bundle ρ).toJointDensity
      τhat.toJointDensity hA
    exact le_trans hstep hτhat_dist
  · -- coarsen of the witness recovers `τ`
    apply CQState.ext_stateMap
    funext y
    apply SubDensityOp.ext
    rw [coarsen_prodFst_stateMap_toOp]
    change (∑ f : F, (blockExtractSub f (τhat.stateMap y)).toOp) = (τ.stateMap y).toOp
    simp_rw [blockExtractSub_toOp]
    rw [sum_blockExtract_eq_partialTraceB, ← CQState.partialTraceB_stateMap_toOp, hτhat_pt]

/-! ## General-map coarsening via the uniform-fiber relabel reduction -/

/-- **Uniform-fiber relabel of a general classical coarsening.**

A general classical map `g : X → Z` that factors through an equivalence
`e : X ≃ Z × F` (with `(e x).1 = g x`, i.e. the first coordinate of `e` is `g`)
coarsens exactly like the product projection `Prod.fst` applied to the relabel of
`ρ` along `e.symm`.  This reduces a general-map coarsening to the
product-projection coarsening handled by `smoothMinEntropy_coarsen_le`. -/
lemma coarsen_eq_coarsen_prodFst_relabel
    {X Z F : Type*} [Fintype X] [Fintype Z] [Fintype F] [DecidableEq Z]
    {d : ℕ} (g : X → Z) (e : X ≃ Z × F) (he : ∀ x, (e x).1 = g x) (ρ : CQState X d) :
    CQState.coarsen g ρ =
      CQState.coarsen (Prod.fst : Z × F → Z) (CQState.relabel e.symm ρ) := by
  apply CQState.ext_stateMap
  funext z
  apply SubDensityOp.ext
  rw [CQState.coarsen_stateMap_toOp, CQState.coarsen_stateMap_toOp,
    ← Equiv.sum_comp e (fun p : Z × F =>
      if p.1 = z then ((CQState.relabel e.symm ρ).stateMap p).toOp else 0)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [CQState.relabel_stateMap, Equiv.symm_apply_apply, he x]

/-- Product-projection coarsening cannot increase extended smooth min-entropy.
Uhlmann lifting preserves every feasible coefficient, including at zero witnesses. -/
theorem smoothMinEntropy_coarsen_le
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ρ : CQState (Y × F) d) (σ : SubDensityOp d) (ε : ℝ) :
    smoothMinEntropy ε (CQState.coarsen (Prod.fst : Y × F → Y) ρ) σ ≤
      smoothMinEntropy ε ρ σ := by
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  obtain ⟨τ', hd', heq⟩ := exists_coarsen_preimage_in_ball ρ ε τ hd
  refine ⟨τ', hd', fun t ht => ?_⟩
  exact isFeasible_of_isFeasible_coarsen Prod.fst τ' σ (heq.symm ▸ ht)


/-- Coarsening by the first projection cannot increase signed smooth min-entropy when the source
ball is bounded above and the reference is positive definite. -/
theorem smoothMinEntropyReal_coarsen_le
    {Y F : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype F] [DecidableEq F] [Nonempty F] {d : ℕ} [NeZero d]
    (ρ : CQState (Y × F) d) (σ : SubDensityOp d) (hσ : σ.toOp.PosDef)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρ σ))) :
    smoothMinEntropyReal ε (CQState.coarsen (Prod.fst : Y × F → Y) ρ) σ ≤
      smoothMinEntropyReal ε ρ σ :=
  smoothMinEntropyReal_coarsen_le_of_exists_lift (Prod.fst : Y × F → Y) ρ σ hσ ε hε_nn hbdd
    (fun τ hτ => exists_coarsen_preimage_in_ball ρ ε τ hτ)

end InfoTheory.SmoothMinEntropy

end
