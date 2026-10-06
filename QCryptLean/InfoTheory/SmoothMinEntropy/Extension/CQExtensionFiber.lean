import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionFiberWitness

/-!
# CQ Extension Fibers — sub-normalized and blockwise Uhlmann extension properties

This module packages the partial-trace fiber form of Uhlmann's extension
property for sub-normalized operators and finite-dimensional
classical-quantum states with an explicit right register.

## Main definitions
This file introduces no new definitions.

## Main statements
- `SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge`: achievability
  half of the sub-normalized extension property on a partial-trace fiber
- `SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_eq`: equality form
  of the sub-normalized extension property
- `CQState.exists_extension_of_partialTraceB_fidelityGen_eq`: blockwise CQ
  extension preserving generalized fidelity
- `CQState.exists_extension_of_partialTraceB_purifiedDistance`: CQ extension
  preserving membership in a purified-distance ball
- `finiteDimensional_CQ_extension_fiber_of_partialTraceB_eq`: finite-dimensional
  CQ extension fiber from an equality of partial traces
- `finiteDimensional_CQ_extension_fiber_of_block_marginals`: finite-dimensional
  CQ extension fiber from block marginal identities
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Achievability half of the sub-normalized Uhlmann extension property on a
partial-trace fiber. -/
theorem SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE) :
    ∃ ρERtilde : SubDensityOp (dE * dR),
      ρERtilde.partialTraceB = ρEtilde ∧
      fidelityGen ρER.partialTraceB ρEtilde ≤
        fidelityGen ρER ρERtilde := by
  obtain ⟨ψER, η, hψER⟩ :=
    SubDensityOp.exists_externalFlagPurification_selfAncilla ρER
  exact
    SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge_of_externalFlagPurification
      ρER ρEtilde ψER η hψER

/-- Sub-normalized Uhlmann extension property for an explicit right register.

Given an `E ⊗ R` sub-density operator and a target `E` marginal, choose an
`E ⊗ R` extension of that target whose generalized fidelity with the original
joint state matches the generalized fidelity of the two `E` marginals. -/
theorem SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_eq
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE) :
    ∃ ρERtilde : SubDensityOp (dE * dR),
      ρERtilde.partialTraceB = ρEtilde ∧
      fidelityGen ρER ρERtilde =
        fidelityGen ρER.partialTraceB ρEtilde := by
  obtain ⟨ρERtilde, hpartial, hge⟩ :=
    SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge ρER ρEtilde
  refine ⟨ρERtilde, hpartial, ?_⟩
  have hle :
      fidelityGen ρER ρERtilde ≤
        fidelityGen ρER.partialTraceB ρEtilde := by
    simpa [hpartial] using
      SubDensityOp.fidelityGen_le_fidelityGen_partialTraceB ρER ρERtilde
  exact le_antisymm hle hge

/-- CQ blockwise assembly of the sub-normalized Uhlmann extension property.

Choose extensions of each block and preserve the generalized fidelity of the
block-diagonal joint density. -/
theorem CQState.exists_extension_of_partialTraceB_fidelityGen_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    [NeZero (Fintype.card X)]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρER : CQState X (dE * dR))
    (ρEtilde : CQState X dE) :
    ∃ ρERtilde : CQState X (dE * dR),
      ρERtilde.partialTraceB = ρEtilde ∧
      fidelityGen ρER.toJointDensity ρERtilde.toJointDensity =
        fidelityGen ρER.partialTraceB.toJointDensity ρEtilde.toJointDensity := by
  have hblock : ∀ x : X,
      ∃ ρERxtilde : SubDensityOp (dE * dR),
        ρERxtilde.partialTraceB = ρEtilde.stateMap x ∧
        fidelityGen (ρER.stateMap x) ρERxtilde =
          fidelityGen (ρER.partialTraceB.stateMap x) (ρEtilde.stateMap x) :=
    fun x =>
      SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_eq
        (ρER.stateMap x) (ρEtilde.stateMap x)
  let ρERxtilde : X → SubDensityOp (dE * dR) := fun x => Classical.choose (hblock x)
  have hpartial_block : ∀ x : X,
      (ρERxtilde x).partialTraceB = ρEtilde.stateMap x :=
    fun x => (Classical.choose_spec (hblock x)).1
  have hfid_block : ∀ x : X,
      fidelityGen (ρER.stateMap x) (ρERxtilde x) =
        fidelityGen (ρER.partialTraceB.stateMap x) (ρEtilde.stateMap x) :=
    fun x => (Classical.choose_spec (hblock x)).2
  have hweight : ∑ x : X, (ρERxtilde x).trace ≤ 1 :=
    CQState.sum_trace_le_one_of_partialTraceB_stateMap_eq
      ρERxtilde ρEtilde hpartial_block
  let ρERtilde : CQState X (dE * dR) := {
    stateMap := ρERxtilde
    weight_le_one := hweight }
  have hpartial : ρERtilde.partialTraceB = ρEtilde := by
    apply CQState.partialTraceB_eq_of_stateMap_partialTraceB_eq
    intro x
    simpa [ρERtilde] using hpartial_block x
  have hfid :
      fidelityGen ρER.toJointDensity ρERtilde.toJointDensity =
        fidelityGen ρER.partialTraceB.toJointDensity ρEtilde.toJointDensity :=
    CQState.fidelityGen_toJointDensity_eq_of_forall_stateMap_fidelityGen_eq
      ρER ρERtilde ρEtilde hpartial (by
        intro x
        simpa [ρERtilde] using hfid_block x)
  exact ⟨ρERtilde, hpartial, hfid⟩

/-- CQ Uhlmann extension property over an explicit right register.

If `ρEtilde` lies in the purified-distance ball around the `E`-marginal of
`ρER`, then it has an `E ⊗ R` CQ extension lying in the same ball around `ρER`. -/
theorem CQState.exists_extension_of_partialTraceB_purifiedDistance
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR))
    (ρEtilde : CQState X dE)
    (ε : ℝ)
    (hdist : CQState.purifiedDistance ρER.partialTraceB ρEtilde ≤ ε) :
    ∃ ρERtilde : CQState X (dE * dR),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      ρERtilde.partialTraceB = ρEtilde := by
  have : NeZero (dE * dR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero ((dE * dR) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (dE * dR)) (NeZero.ne (Fintype.card X))⟩
  have : NeZero (dE * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne (Fintype.card X))⟩
  obtain ⟨ρERtilde, hpartial, hfid⟩ :=
    CQState.exists_extension_of_partialTraceB_fidelityGen_eq ρER ρEtilde
  refine ⟨ρERtilde, ?_, hpartial⟩
  have hdist_eq :
      CQState.purifiedDistance ρER ρERtilde =
        CQState.purifiedDistance ρER.partialTraceB ρEtilde :=
    CQState.purifiedDistance_eq_of_fidelityGen_toJointDensity_eq
      ρER ρERtilde ρER.partialTraceB ρEtilde hfid
  exact hdist_eq.trans_le hdist

/-- CQ Uhlmann extension with blockwise operator marginals.

If an `E`-side CQ state lies in the purified-distance ball around the
`E`-marginal of `ρER`, it has an `E ⊗ R` extension in the same ball whose
blocks have the prescribed partial traces. -/
theorem CQState.exists_extension_of_partialTraceB_purifiedDistance_stateMap_toOp_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState α (dE * dR))
    (ρEtilde : CQState α dE)
    (ε : ℝ)
    (hdist : CQState.purifiedDistance ρER.partialTraceB ρEtilde ≤ ε) :
    ∃ ρERtilde : CQState α (dE * dR),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      ∀ x : α,
        Quantum.TensorProducts.partialTraceB (ρERtilde.stateMap x).toOp =
          (ρEtilde.stateMap x).toOp := by
  obtain ⟨ρERtilde, hdER, hpartial_tilde⟩ :=
    CQState.exists_extension_of_partialTraceB_purifiedDistance
      ρER ρEtilde ε hdist
  exact ⟨ρERtilde, hdER,
    CQState.partialTraceB_stateMap_toOp_eq_of_partialTraceB_eq hpartial_tilde⟩

/-- CQ Uhlmann/fiber extension from an equality of `E`-marginals.

If `ρER.partialTraceB = ρE`, every nearby `E`-side CQ state has a same-radius
blockwise extension over the original right register. -/
theorem finiteDimensional_CQ_extension_fiber_of_partialTraceB_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {d dE : ℕ} [NeZero d] [NeZero dE]
    (ρE : CQState α dE)
    (ρER : CQState α (dE * d))
    (hpartial : ρER.partialTraceB = ρE)
    (ε : ℝ)
    (ρEtilde : CQState α dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε) :
    ∃ ρERtilde : CQState α (dE * d),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      ∀ x : α,
        partialTraceB (ρERtilde.stateMap x).toOp =
          (ρEtilde.stateMap x).toOp := by
  exact
    CQState.exists_extension_of_partialTraceB_purifiedDistance_stateMap_toOp_eq
      ρER ρEtilde ε (by simpa [hpartial] using hdE)

/-- CQ Uhlmann/fiber extension over an explicit right register.

If the center `ρER` is a blockwise extension of `ρE`, every CQ state
`ρEtilde` in the same purified-distance ball has a blockwise extension over the
same `E ⊗ R` register, with no increase in the smoothing radius. -/
theorem finiteDimensional_CQ_extension_fiber_of_block_marginals
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {d dE : ℕ} [NeZero d] [NeZero dE] [NeZero (dE * d)]
    (ρE : CQState α dE)
    (ρER : CQState α (dE * d))
    (hblocks : ∀ x : α,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ)
    (ρEtilde : CQState α dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε) :
    ∃ ρERtilde : CQState α (dE * d),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      ∀ x : α,
        partialTraceB (ρERtilde.stateMap x).toOp =
          (ρEtilde.stateMap x).toOp := by
  have hρE : ρER.partialTraceB = ρE :=
    CQState.partialTraceB_eq_of_stateMap_toOp ρER ρE hblocks
  exact finiteDimensional_CQ_extension_fiber_of_partialTraceB_eq
    ρE ρER hρE ε ρEtilde hdE

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
