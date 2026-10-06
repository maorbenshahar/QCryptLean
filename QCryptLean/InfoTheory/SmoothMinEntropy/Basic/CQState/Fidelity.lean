import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.Metrics.FidelityCPTP

/-!
# CQ State Fidelity Helpers — block decompositions and partial-trace trace identities

This module collects block-diagonal fidelity facts for classical-quantum joint
density operators, blockwise data-processing inequalities, and trace identities
used when assembling partial-trace fiber arguments.

## Main definitions
This file introduces no new definitions.

## Main statements
- `CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity`: ordinary fidelity
  of CQ joint densities decomposes as a sum over classical blocks
- `CQState.toJointDensity_trace_partialTraceB`: blockwise partial trace preserves
  the trace of the CQ joint density
- `CQState.toJointDensity_trace_eq_of_partialTraceB_eq`: a CQ extension and its
  prescribed blockwise partial trace have the same joint-density trace
- `CQState.toJointDensity_trace_eq_of_stateMap_apply_trace_preserving`: blockwise
  trace-preserving postprocessing preserves joint-density trace
- `CQState.fidelity_le_fidelity_blockwise_cptp`: ordinary fidelity is monotone
  under blockwise CPTP postprocessing
- `CQState.fidelityGen_le_fidelityGen_blockwise_cptp`: generalized fidelity is
  monotone under blockwise CPTP postprocessing
- `CQState.fidelityGen_toJointDensity_eq_of_forall_stateMap_fidelityGen_eq`:
  per-block generalized-fidelity equalities assemble to joint-density equality
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Ordinary fidelity of CQ joint densities is the sum of ordinary fidelities
of the corresponding classical blocks. -/
theorem CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity
    {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} [NeZero n] [NeZero (n * Fintype.card X)]
    (ρ σ : CQState X n) :
    Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp =
      ∑ x : X, Quantum.Metrics.fidelity
        (ρ.stateMap x).toPosSemidefOp (σ.stateMap x).toPosSemidefOp := by
  have hρjoint := ρ.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hσjoint := σ.toJointDensity_toPosSemidefOp_eq_cqBlock
  rw [hρjoint, hσjoint, Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
    Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]

/-- Blockwise partial trace preserves the trace of the CQ joint density. -/
lemma CQState.toJointDensity_trace_partialTraceB
    {X : Type*} [Fintype X] [DecidableEq X] {dE dR : ℕ}
    (ρ : CQState X (dE * dR)) :
    ρ.toJointDensity.trace = ρ.partialTraceB.toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
  exact (CQState.partialTraceB_weight ρ).symm

/-- A CQ extension and its prescribed blockwise partial trace have the same
joint-density trace. -/
lemma CQState.toJointDensity_trace_eq_of_partialTraceB_eq
    {X : Type*} [Fintype X] [DecidableEq X] {dE dR : ℕ}
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hpartial : ρER.partialTraceB = ρE) :
    ρER.toJointDensity.trace = ρE.toJointDensity.trace := by
  rw [← hpartial]
  exact CQState.toJointDensity_trace_partialTraceB ρER

/-- A blockwise trace-preserving postprocessing preserves the trace of the CQ
joint density. -/
lemma CQState.toJointDensity_trace_eq_of_stateMap_apply_trace_preserving
    {X : Type*} [Fintype X] [DecidableEq X]
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (ρ : CQState X dIn) (ρ' : CQState X dOut)
    (T : X → Op dIn →ₗ[ℂ] Op dOut)
    (hT : ∀ x, Quantum.Channels.IsTracePreserving ⇑(T x))
    (hρ' : ∀ x, (ρ'.stateMap x).toOp = T x (ρ.stateMap x).toOp) :
    ρ.toJointDensity.trace = ρ'.toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (ρ.stateMap x).toOp.trace.re = (ρ'.stateMap x).toOp.trace.re
  rw [hρ' x, hT x (ρ.stateMap x).toOp]

/-- Ordinary fidelity of CQ joint densities is monotone under a blockwise
classically-controlled CPTP postprocessing map. -/
theorem CQState.fidelity_le_fidelity_blockwise_cptp
    {X : Type*} [Fintype X] [DecidableEq X]
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    [NeZero (dIn * Fintype.card X)] [NeZero (dOut * Fintype.card X)]
    (ρ σ : CQState X dIn)
    (ρ' σ' : CQState X dOut)
    (T : X → Op dIn →ₗ[ℂ] Op dOut)
    (hT : ∀ x, Quantum.Channels.IsCPTP ⇑(T x))
    (hρ' : ∀ x, (ρ'.stateMap x).toOp = T x (ρ.stateMap x).toOp)
    (hσ' : ∀ x, (σ'.stateMap x).toOp = T x (σ.stateMap x).toOp) :
    Quantum.Metrics.fidelity
        ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp ≤
      Quantum.Metrics.fidelity
        ρ'.toJointDensity.toPosSemidefOp
        σ'.toJointDensity.toPosSemidefOp := by
  rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
    CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
  apply Finset.sum_le_sum
  intro x _
  exact Quantum.Metrics.fidelity_le_fidelity_cptp_of_toOp_eq
    (⇑(T x)) (hT x)
    (ρ.stateMap x).toPosSemidefOp
    (σ.stateMap x).toPosSemidefOp
    (ρ'.stateMap x).toPosSemidefOp
    (σ'.stateMap x).toPosSemidefOp
    (by simpa using hρ' x)
    (by simpa using hσ' x)

/-- Generalized fidelity of CQ joint densities is monotone under a blockwise
classically-controlled CPTP postprocessing map. -/
theorem CQState.fidelityGen_le_fidelityGen_blockwise_cptp
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (ρ σ : CQState X dIn)
    (ρ' σ' : CQState X dOut)
    (T : X → Op dIn →ₗ[ℂ] Op dOut)
    (hT : ∀ x, Quantum.Channels.IsCPTP ⇑(T x))
    (hρ' : ∀ x, (ρ'.stateMap x).toOp = T x (ρ.stateMap x).toOp)
    (hσ' : ∀ x, (σ'.stateMap x).toOp = T x (σ.stateMap x).toOp) :
    fidelityGen ρ.toJointDensity σ.toJointDensity ≤
      fidelityGen ρ'.toJointDensity σ'.toJointDensity := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (dIn * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dIn) (NeZero.ne _)⟩
  haveI : NeZero (dOut * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dOut) (NeZero.ne _)⟩
  have hF :
      Quantum.Metrics.fidelity
          ρ.toJointDensity.toPosSemidefOp
          σ.toJointDensity.toPosSemidefOp ≤
        Quantum.Metrics.fidelity
          ρ'.toJointDensity.toPosSemidefOp
          σ'.toJointDensity.toPosSemidefOp :=
    CQState.fidelity_le_fidelity_blockwise_cptp ρ σ ρ' σ' T hT hρ' hσ'
  have hρtrace :
      ρ.toJointDensity.trace = ρ'.toJointDensity.trace :=
    CQState.toJointDensity_trace_eq_of_stateMap_apply_trace_preserving
      ρ ρ' T (fun x => (hT x).2.2) hρ'
  have hσtrace :
      σ.toJointDensity.trace = σ'.toJointDensity.trace :=
    CQState.toJointDensity_trace_eq_of_stateMap_apply_trace_preserving
      σ σ' T (fun x => (hT x).2.2) hσ'
  unfold fidelityGen
  rw [hρtrace, hσtrace]
  exact add_le_add hF (le_refl _)

/-- Block-diagonal CQ generalized-fidelity assembly from per-outcome fiber
equalities. -/
theorem CQState.fidelityGen_toJointDensity_eq_of_forall_stateMap_fidelityGen_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    [NeZero (Fintype.card X)]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρER ρERtilde : CQState X (dE * dR))
    (ρEtilde : CQState X dE)
    (hpartial : ρERtilde.partialTraceB = ρEtilde)
    (hfid_block : ∀ x : X,
      fidelityGen (ρER.stateMap x) (ρERtilde.stateMap x) =
        fidelityGen (ρER.partialTraceB.stateMap x) (ρEtilde.stateMap x)) :
    fidelityGen ρER.toJointDensity ρERtilde.toJointDensity =
      fidelityGen ρER.partialTraceB.toJointDensity ρEtilde.toJointDensity := by
  have hfid_blocks : ∀ x : X,
      Quantum.Metrics.fidelity (ρER.stateMap x).toPosSemidefOp
          (ρERtilde.stateMap x).toPosSemidefOp =
        Quantum.Metrics.fidelity (ρER.partialTraceB.stateMap x).toPosSemidefOp
          (ρEtilde.stateMap x).toPosSemidefOp := by
    intro x
    refine SubDensityOp.fidelity_eq_of_fidelityGen_eq_of_trace_eq
      (hfid_block x) ?_ ?_
    · exact (CQState.partialTraceB_stateMap_trace ρER x).symm
    · simpa [hpartial] using (CQState.partialTraceB_stateMap_trace ρERtilde x).symm
  have hF :
      Quantum.Metrics.fidelity ρER.toJointDensity.toPosSemidefOp
          ρERtilde.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.fidelity ρER.partialTraceB.toJointDensity.toPosSemidefOp
          ρEtilde.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
    apply Finset.sum_congr rfl
    intro x _
    exact hfid_blocks x
  have hρtrace :
      ρER.toJointDensity.trace = ρER.partialTraceB.toJointDensity.trace :=
    CQState.toJointDensity_trace_partialTraceB ρER
  have hσtrace :
      ρERtilde.toJointDensity.trace = ρEtilde.toJointDensity.trace :=
    CQState.toJointDensity_trace_eq_of_partialTraceB_eq ρERtilde ρEtilde hpartial
  unfold fidelityGen
  rw [hF, hρtrace, hσtrace]

end InfoTheory.SmoothMinEntropy

namespace Quantum.Operators

/-- **(S0) PSD-sum.** The underlying operator of a finite sum of positive
semidefinite operators is the sum of the underlying operators. -/
lemma PosSemidefOp.sum_toOp {ι : Type*} (s : Finset ι) {n : ℕ}
    (A : ι → PosSemidefOp n) :
    (∑ z ∈ s, A z).toOp = ∑ z ∈ s, (A z).toOp := by
  classical
  refine Finset.cons_induction ?_ ?_ s
  · rfl
  · intro a t ha ih
    rw [Finset.sum_cons, Finset.sum_cons]
    change (A a).toOp + (∑ z ∈ t, A z).toOp = (A a).toOp + ∑ z ∈ t, (A z).toOp
    rw [ih]

end Quantum.Operators

namespace Quantum.Metrics

open Quantum.Operators

/-- Uhlmann fidelity depends only on the underlying operators of its arguments. -/
lemma fidelity_congr {n : ℕ} [NeZero n]
    {A B A' B' : PosSemidefOp n}
    (hA : A.toOp = A'.toOp) (hB : B.toOp = B'.toOp) :
    fidelity A B = fidelity A' B' := by
  unfold fidelity sqrtPosSemidefOp
  rw [hA, hB]

/-- **(S1) Partial trace of a `Z`-block-diagonal CQ operator = sum of blocks.**

Tracing out the classical register `Z` of the block-diagonal PSD operator
`cqBlockPosSemidefOp A` recovers the sum `∑_z A z` of its blocks.  This is the
pure index computation behind the classical-flag discard in Renner Eq. 3.59. -/
lemma cqBlockPosSemidefOp_partialTraceB_eq_sum
    {Z : Type*} [Fintype Z] [DecidableEq Z] {n : ℕ}
    (A : Z → PosSemidefOp n) :
    (cqBlockPosSemidefOp A).partialTraceB = ∑ z, A z := by
  apply PosSemidefOp.ext
  rw [PosSemidefOp.sum_toOp]
  change Quantum.TensorProducts.partialTraceB (cqBlockPosSemidefOp A).toOp = ∑ z, (A z).toOp
  ext i j
  rw [Matrix.sum_apply]
  change (∑ k : Fin (Fintype.card Z),
      (cqBlockPosSemidefOp A).toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)))
      = ∑ z, (A z).toOp i j
  have hterm : ∀ k : Fin (Fintype.card Z),
      (cqBlockPosSemidefOp A).toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))
        = (A ((Fintype.equivFin Z).symm k)).toOp i j := by
    intro k
    rw [cqBlockPosSemidefOp_toOp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm,
      Prod.map_apply, Equiv.refl_apply]
    rw [Matrix.blockDiagonal_apply_eq]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  exact Equiv.sum_comp (Fintype.equivFin Z).symm (fun z => (A z).toOp i j)

/-- **(S2) Finite super-additivity of the Uhlmann fidelity (Renner Eq. 3.59).**

`∑_z F(A z, B z) ≤ F(∑_z A z, ∑_z B z)`: discarding the classical flag `Z` from
the block-diagonal `cqBlockPosSemidefOp` is a CPTP partial trace, under which
the Uhlmann fidelity is monotone, while on the flagged (orthogonal-`Z`) operator
it equals the blockwise sum.  This is the fidelity super-additivity content of
Renner thesis Eq. 3.59 / Nahar, Tupkary, Zhao, Lütkenhaus, Tan Lemma 14 (B21). -/
theorem fidelity_sum_le_fidelity_sum
    {Z : Type*} [Fintype Z] {n : ℕ} [NeZero n]
    [NeZero (n * Fintype.card Z)]
    (A B : Z → PosSemidefOp n) :
    ∑ z, fidelity (A z) (B z) ≤ fidelity (∑ z, A z) (∑ z, B z) := by
  classical
  haveI : NeZero (Fintype.card Z) := ⟨fun h =>
    NeZero.ne (n * Fintype.card Z) (by rw [h, Nat.mul_zero])⟩
  have hstep1 : fidelity (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B)
      = ∑ z, fidelity (A z) (B z) := by
    rw [fidelity_eq_traceNorm_sqrtProduct, traceNorm_sqrtProduct_cqBlock_eq_sum]
    exact Finset.sum_congr rfl
      (fun z _ => (fidelity_eq_traceNorm_sqrtProduct (A z) (B z)).symm)
  have hstep2 : fidelity (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B)
      ≤ fidelity (cqBlockPosSemidefOp A).partialTraceB
          (cqBlockPosSemidefOp B).partialTraceB :=
    fidelity_le_fidelity_partialTraceB (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B)
  rw [cqBlockPosSemidefOp_partialTraceB_eq_sum A,
    cqBlockPosSemidefOp_partialTraceB_eq_sum B, hstep1] at hstep2
  exact hstep2

end Quantum.Metrics

end -- noncomputable section
