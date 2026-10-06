import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernel
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# A left-tensored spectator kernel is transparent to the register plumbing and to the de Finetti
analytic data

`CQState.tensorLeftKernel` attaches a block `K x` in the **high**
digits of the conditioning register, indexed by the classical register alone.  Two consequences are
collected here, both used by the PE-labelled floor chain, where the conditioning register carries
the announced `(syndrome, EV seed, EV tag)` kernel in the high digits, the announced PE-outcome
block
in the middle, and the de Finetti purifier `V` in the low ones.

## 1. Register plumbing (Nahar et al. `\label{eq:splittingoffV}`)

Tracing out the trailing register commutes with a left-tensored spectator block:
`Tr_V ((A ⊗ M) reassociated) = A ⊗ Tr_V M`.  `partialTraceB_reassoc_tensorLeft` is the two-factor
statement, `partialTraceB_reassoc_tensorLeft_pair` its three-factor iterate (`A` high, `L` middle,
the traced register low), and `partialTraceB_tensorLeftKernel_blocks` the `CQState`-level transport
that carries a blockwise trace-out identity across one spectator kernel — the form the floor chain
calls, once per kernel.  `partialTraceB_coarsen_blocks` pushes such an identity forward along a
classical coarsening, which is where the chain applies it.

## 2. The de Finetti post-filter analytic data

The coarsening assembler
`smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized` consumes five
data about a mixture
`ρ_mix` and a family `f : DensityOp d → CQState X dE`: blockwise Bochner integrability, the Nahar et
al. B13 blockwise integral split, blockwise continuity, the accepted weight, and the bad-branch
trace.  A kernel `K` that does not depend on the de Finetti component transports every one of them
to `fun τ => (f τ).tensorLeftKernel K`, at no cost:

* integrability and continuity — each block entry of the tensored family is a fixed scalar multiple
  of a block entry of the original;
* the integral split — the same scalar factors out of the Bochner integral;
* the accepted weight — `CQState.tensorLeftKernel_weight` at normalised blocks (provided);
* the bad-branch trace — `tr (K ⊗ M) = tr K · tr M` and `tr (K x) = 1`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`), App. B,
`main.tex:1393`, `\label{eq:splittingoffV}` (the trailing purifier
register), `main.tex:1428`, `\label{lemma:infsmoothedmin}` (the assembler whose data these are).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped BigOperators ComplexOrder

-- Bochner integrability of `Op`-valued block maps uses the Frobenius norm on matrices, as in
-- `PerSigmaFamily.lean` / `AcceptSplit.lean` / `FinitePostFilterFloor.lean`.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-! ## 1. Register plumbing: the spectator rides through the trailing partial trace -/

/-- A register-dimension cast of the right tensor factor commutes with left-tensoring a fixed
block. -/
lemma op_eqRec_tensorLeft_congr {dC a b : ℕ} (e : a = b) (A : Op dC) (M : Op a) :
    Op.tensor A (e ▸ M : Op b) =
      ((congrArg (fun t => dC * t) e) ▸ Op.tensor A M : Op (dC * b)) := by
  subst e; rfl

/-- Two successive register-dimension casts of an operator compose. -/
lemma op_eqRec_trans {a b c : ℕ} (e₁ : a = b) (e₂ : b = c) (M : Op a) :
    (e₂ ▸ (e₁ ▸ M : Op b) : Op c) = ((e₁.trans e₂) ▸ M : Op c) := by
  subst e₁; subst e₂; rfl

/-- **Tracing out a trailing register commutes with a left-tensored spectator block.**

For a spectator operator `A` on `dC` and a block `M` on `dE · dV`, tracing out the trailing `dV`
factor of the reassociated `dC · dE · dV` register leaves `A` untouched:

`Tr_V ((A ⊗ M) reassociated) = A ⊗ Tr_V M`.

This is what lets an announcement ride through a `V`-register extension without being re-charged:
the announcement lives in the high digits, the traced register in the low ones, and they never meet.

References: Nahar et al. 2024 (`arXiv:2403.11851`), `main.tex:1393`,
`\label{eq:splittingoffV}`. -/
lemma partialTraceB_reassoc_tensorLeft {dC dE dV : ℕ} (h : dC * (dE * dV) = dC * dE * dV)
    (A : Op dC) (M : Op (dE * dV)) :
    Quantum.TensorProducts.partialTraceB (h ▸ Op.tensor A M : Op (dC * dE * dV)) =
      Op.tensor A (Quantum.TensorProducts.partialTraceB M) := by
  -- All proofs of a `Nat` dimension equality are interchangeable, so fix the canonical one.
  change Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc dC dE dV).symm ▸ Op.tensor A M : Op (dC * dE * dV)) = _
  ext I J
  rw [Op_tensor_apply_finProd]
  simp only [Quantum.TensorProducts.partialTraceB, Matrix.of_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [matrix_eqRec_apply, Op_tensor_apply_finProd, finProdFinEquiv_symm_cast_assoc,
    finProdFinEquiv_symm_cast_assoc]
  simp only [Equiv.symm_apply_apply]

/-- **Two left-tensored spectator blocks both ride through the trailing partial trace.**

The three-factor iterate of `partialTraceB_reassoc_tensorLeft`: with `A` in the **high** digits, `L`
in the **middle** ones and the traced register `dV` in the **low** ones,

`Tr_V ((A ⊗ (L ⊗ M)) reassociated) = A ⊗ (L ⊗ Tr_V M)`.

This is the register order of the PE-labelled conditioning register — announced
`(syndrome, EV seed, EV tag)` kernel high, announced PE-outcome block middle, de Finetti purifier
`V` low — so neither announcement meets the purifier and neither is re-charged by the `V`
adjunction.

References: Nahar et al. 2024 (`arXiv:2403.11851`), `main.tex:1393`,
`\label{eq:splittingoffV}`. -/
lemma partialTraceB_reassoc_tensorLeft_pair {dA dL dE dV : ℕ}
    (h : dA * (dL * (dE * dV)) = dA * (dL * dE) * dV)
    (A : Op dA) (L : Op dL) (M : Op (dE * dV)) :
    Quantum.TensorProducts.partialTraceB
        (h ▸ Op.tensor A (Op.tensor L M) : Op (dA * (dL * dE) * dV)) =
      Op.tensor A (Op.tensor L (Quantum.TensorProducts.partialTraceB M)) := by
  have h₁ : dL * (dE * dV) = dL * dE * dV := (Nat.mul_assoc dL dE dV).symm
  have h₂ : dA * (dL * dE * dV) = dA * (dL * dE) * dV := (Nat.mul_assoc dA (dL * dE) dV).symm
  have hstep : (h ▸ Op.tensor A (Op.tensor L M) : Op (dA * (dL * dE) * dV)) =
      (h₂ ▸ Op.tensor A (h₁ ▸ Op.tensor L M : Op (dL * dE * dV)) : Op (dA * (dL * dE) * dV)) := by
    rw [op_eqRec_tensorLeft_congr h₁ A (Op.tensor L M), op_eqRec_trans]
  rw [hstep, partialTraceB_reassoc_tensorLeft h₂ A (h₁ ▸ Op.tensor L M),
    partialTraceB_reassoc_tensorLeft h₁ L M]

/-- **A blockwise trace-out identity transports across one spectator kernel.**

If tracing out the trailing `dV` factor of each block of `ρEV` (after the inner register cast `hin`)
returns the corresponding block of `ρE`, then the same holds for both states with a classical kernel
`K` tensored on the left — the kernel block is untouched by the trace.

This is the form the floor chain calls, once per announcement kernel: applying it with the PE-label
kernel and then with the `(syndrome, EV seed, EV tag)` kernel produces the three-factor identity of
`partialTraceB_reassoc_tensorLeft_pair` at `CQState` level, with the second application consuming
the first's conclusion as its `hblocks`. -/
lemma partialTraceB_tensorLeftKernel_blocks {X : Type*} [Fintype X] {dC dM dE dV : ℕ}
    (hin : dM = dE * dV) (hout : dC * dM = dC * dE * dV)
    (K : X → SubDensityOp dC) (ρEV : CQState X dM) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      Quantum.TensorProducts.partialTraceB (hin ▸ (ρEV.stateMap x).toOp : Op (dE * dV)) =
        (ρE.stateMap x).toOp)
    (x : X) :
    Quantum.TensorProducts.partialTraceB
        (hout ▸ ((ρEV.tensorLeftKernel K).stateMap x).toOp : Op (dC * dE * dV)) =
      ((ρE.tensorLeftKernel K).stateMap x).toOp := by
  subst hin
  rw [show ((ρEV.tensorLeftKernel K).stateMap x).toOp =
      Op.tensor (K x).toOp (ρEV.stateMap x).toOp from rfl,
    partialTraceB_reassoc_tensorLeft hout (K x).toOp (ρEV.stateMap x).toOp, hblocks x]
  rfl

/-- **A blockwise trace-out identity transports across a classical coarsening.**

Coarsening acts blockwise as the fibre sum (`CQState.coarsen_stateMap_toOp`) and `partialTraceB` is
additive, so a fine-register trace-out identity pushes forward to any coarsening of the classical
register.

The public form of a lemma that the referee and floor chains each carry privately;
the PE-labelled chain needs
it below the Alice-key coarsening and above the `V` adjunction. -/
lemma partialTraceB_coarsen_blocks {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    {dE dV : ℕ} (g : Xc → Yc)
    (ρEV : CQState Xc (dE * dV)) (ρE : CQState Xc dE)
    (hblocks : ∀ x : Xc,
      Quantum.TensorProducts.partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (y : Yc) :
    Quantum.TensorProducts.partialTraceB
        ((CQState.coarsen g ρEV).stateMap y).toOp =
      ((CQState.coarsen g ρE).stateMap y).toOp := by
  rw [CQState.coarsen_stateMap_toOp,
    CQState.coarsen_stateMap_toOp,
    Quantum.TensorProducts.partialTraceB_finset_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · rw [if_pos hx, if_pos hx]; exact hblocks x
  · rw [if_neg hx, if_neg hx,
      show (0 : Op (dE * dV)) = (0 : ℂ) • (0 : Op (dE * dV)) by rw [zero_smul],
      Quantum.TensorProducts.partialTraceB_smul, zero_smul]

/-! ## 2. The de Finetti post-filter analytic data under a spectator kernel -/

/-- Each block entry of a left-tensored state is the corresponding kernel entry times the
corresponding block entry of the original state. -/
lemma tensorLeftKernel_stateMap_toOp_apply {X : Type*} [Fintype X] {dC dE : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (x : X) (I J : Fin (dC * dE)) :
    ((ρ.tensorLeftKernel K).stateMap x).toOp I J =
      (K x).toOp (finProdFinEquiv.symm I).1 (finProdFinEquiv.symm J).1 *
        (ρ.stateMap x).toOp (finProdFinEquiv.symm I).2 (finProdFinEquiv.symm J).2 :=
  Op_tensor_apply_finProd (K x).toOp (ρ.stateMap x).toOp I J

/-- **Blockwise Bochner integrability transports across a spectator kernel.**

The assembler's `h_int` for `fun τ => (f τ).tensorLeftKernel K` when `K` does not depend on the de
Finetti component `τ`. -/
lemma tensorLeftKernel_blocks_integrable {X : Type*} [Fintype X] {dC dE : ℕ}
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → CQState X dE) (K : X → SubDensityOp dC) (x : X)
    (hf : MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ) :
    MeasureTheory.Integrable (fun a => (((f a).tensorLeftKernel K).stateMap x).toOp) μ := by
  let entryCLM : Fin dE → Fin dE → (Op dE →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hentry : ∀ i j, MeasureTheory.Integrable
      (fun a => ((f a).stateMap x).toOp i j) μ := fun i j => (entryCLM i j).integrable_comp hf
  have hentry' : ∀ I J : Fin (dC * dE), MeasureTheory.Integrable
      (fun a => (((f a).tensorLeftKernel K).stateMap x).toOp I J) μ := by
    intro I J
    simp_rw [tensorLeftKernel_stateMap_toOp_apply]
    exact (hentry _ _).const_mul _
  -- A matrix-valued map into a finite matrix space is integrable if all its entries are.
  let G : α → Fin (dC * dE) → Fin (dC * dE) → ℂ :=
    fun a I J => (((f a).tensorLeftKernel K).stateMap x).toOp I J
  have hG : MeasureTheory.Integrable G μ :=
    MeasureTheory.Integrable.of_eval fun I =>
      MeasureTheory.Integrable.of_eval fun J => hentry' I J
  let toMatrix : (Fin (dC * dE) → Fin (dC * dE) → ℂ) →L[ℝ] Op (dC * dE) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A => A
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  simpa [G, toMatrix] using toMatrix.integrable_comp hG

/-- **The Nahar et al. B13 blockwise integral split transports across a spectator kernel.**

The assembler's `hf_lin` for `fun τ => (f τ).tensorLeftKernel K` when `K` does not depend on the de
Finetti component `τ`: each entry of the tensored block is a fixed scalar times the corresponding
entry of the original block, and that scalar comes out of the Bochner integral.

References: Nahar et al. 2024 (`arXiv:2403.11851`), App. B,
`main.tex:1380`, `\label{eq:boundingsmoothedmin}`. -/
lemma tensorLeftKernel_blocks_integral_eq {X : Type*} [Fintype X] {dC dE : ℕ}
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (ρ : CQState X dE) (f : α → CQState X dE) (K : X → SubDensityOp dC)
    (hlin : ∀ (x : X) (i j : Fin dE),
      (ρ.stateMap x).toOp i j = ∫ a, ((f a).stateMap x).toOp i j ∂μ)
    (x : X) (I J : Fin (dC * dE)) :
    ((ρ.tensorLeftKernel K).stateMap x).toOp I J =
      ∫ a, (((f a).tensorLeftKernel K).stateMap x).toOp I J ∂μ := by
  simp_rw [tensorLeftKernel_stateMap_toOp_apply]
  rw [hlin x _ _, MeasureTheory.integral_const_mul]

/-- **Blockwise continuity transports across a spectator kernel.**

The assembler's `hcont` for `fun τ => (f τ).tensorLeftKernel K` when `K` does not depend on the de
Finetti component `τ`. -/
lemma tensorLeftKernel_blocks_continuous {X : Type*} [Fintype X] {dC dE : ℕ}
    {α : Type*} [TopologicalSpace α]
    (f : α → CQState X dE) (K : X → SubDensityOp dC) (x : X)
    (hf : Continuous (fun a => ((f a).stateMap x).toOp)) :
    Continuous (fun a => (((f a).tensorLeftKernel K).stateMap x).toOp) := by
  refine continuous_matrix (fun I J => ?_)
  simp_rw [tensorLeftKernel_stateMap_toOp_apply]
  exact continuous_const.mul (hf.matrix_elem _ _)

/-- **The bad-branch trace is unchanged by a spectator kernel with normalised blocks.**

`tr (K x ⊗ M) = tr (K x) · tr M = tr M`, entrywise under the set integral, so the assembler's
h_badBranch_traceNorm for `fun τ => (f τ).tensorLeftKernel K` is the untensored one verbatim. -/
lemma trace_setIntegral_tensorLeftKernel_blocks_eq {X : Type*} [Fintype X] {dC dE : ℕ}
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → CQState X dE) (K : X → SubDensityOp dC)
    (hK : ∀ x : X, Matrix.trace (K x).toOp = 1) (S : Set α) (x : X) :
    (Matrix.of fun I J : Fin (dC * dE) =>
        ∫ a in S, (((f a).tensorLeftKernel K).stateMap x).toOp I J ∂μ : Op (dC * dE)).trace =
      (Matrix.of fun i j : Fin dE =>
        ∫ a in S, ((f a).stateMap x).toOp i j ∂μ : Op dE).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := dC) (n := dE))
    (fun I => ∫ a in S, (((f a).tensorLeftKernel K).stateMap x).toOp I I ∂μ)]
  rw [Fintype.sum_prod_type]
  have hrw : ∀ (p : Fin dC) (i : Fin dE),
      (∫ a in S, (((f a).tensorLeftKernel K).stateMap x).toOp
          (finProdFinEquiv (p, i)) (finProdFinEquiv (p, i)) ∂μ) =
        (K x).toOp p p * ∫ a in S, ((f a).stateMap x).toOp i i ∂μ := by
    intro p i
    simp_rw [tensorLeftKernel_stateMap_toOp_apply, Equiv.symm_apply_apply]
    rw [MeasureTheory.integral_const_mul]
  simp_rw [hrw, ← Finset.mul_sum]
  rw [← Finset.sum_mul,
    show ∑ p : Fin dC, (K x).toOp p p = Matrix.trace (K x).toOp from rfl, hK x, one_mul]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
