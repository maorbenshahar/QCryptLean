import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Recovered CQ Extensions — blockwise recovery maps and purified-distance contraction

This module packages the high-level glue for the CKR-style structured extension
penalty: assembling an `E ⊗ R` extension `CQState` from a per-block recovery map,
and the data-processing (Uhlmann monotonicity) contraction of purified distance
under a blockwise, classically-controlled recovery channel.

## Main definitions
- `recoveredExtension`: the `E ⊗ R` extension assembled from a family of
  positive partial-trace-section recovery maps applied to an `E`-marginal state.

## Main statements
- `recoveredExtension_stateMap_toOp`: the block operators of the recovered
  extension are `T x` applied to the marginal blocks.
- `recoveredExtension_partialTraceB_stateMap_toOp`: a recovered extension has
  the prescribed marginal blocks.
- `CQState.purifiedDistance_recovery_contract`: data-processing inequality for
  purified distance under a blockwise recovery channel.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Assemble the recovered `E ⊗ R` extension `CQState` from a family of per-block
recovery maps `T` (positive, trace-preserving) applied blockwise to the
`E`-marginal state `ρEtilde`.

Validity: each block `T x (ρEtilde x)` is PSD by positivity of `T x`, and its
trace equals that of `ρEtilde x` by trace preservation of `T x`; hence the block
traces sum to the weight of `ρEtilde`, which is at most one. -/
noncomputable def recoveredExtension
    {X : Type*} [Fintype X] {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρEtilde : CQState X dE)
    (T : X → (Op dE →ₗ[ℂ] Op (dE * dR)))
    (hpos : ∀ x, ∀ A : Op dE, A.PosSemidef → (T x A).PosSemidef)
    (htp : ∀ x, Quantum.Channels.IsTracePreserving ⇑(T x)) :
    CQState X (dE * dR) where
  stateMap x :=
    let hblock_psd : (T x (ρEtilde.stateMap x).toOp).PosSemidef :=
      hpos x _ (Quantum.Operators.posSemidefOp_implies_mathlib
        (ρEtilde.stateMap x).toPosSemidefOp)
    { toOp := T x (ρEtilde.stateMap x).toOp
      isHermitian := hblock_psd.isHermitian
      pos_semidef :=
        Quantum.Operators.posSemidef_re_quadraticForm_nonneg hblock_psd
      trace_le_one := by
        have htr : (T x (ρEtilde.stateMap x).toOp).trace.re =
            (ρEtilde.stateMap x).toOp.trace.re :=
          congr_arg Complex.re (htp x (ρEtilde.stateMap x).toOp)
        rw [htr]
        exact (ρEtilde.stateMap x).trace_le_one }
  weight_le_one := by
    refine le_trans (le_of_eq ?_) ρEtilde.weight_le_one
    apply Finset.sum_congr rfl
    intro x _
    change (T x (ρEtilde.stateMap x).toOp).trace.re = (ρEtilde.stateMap x).trace
    have htr : (T x (ρEtilde.stateMap x).toOp).trace.re =
        (ρEtilde.stateMap x).toOp.trace.re :=
      congr_arg Complex.re (htp x (ρEtilde.stateMap x).toOp)
    simp [SubDensityOp.trace, htr]

@[simp]
lemma recoveredExtension_stateMap_toOp
    {X : Type*} [Fintype X] {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρEtilde : CQState X dE)
    (T : X → (Op dE →ₗ[ℂ] Op (dE * dR)))
    (hpos : ∀ x, ∀ A : Op dE, A.PosSemidef → (T x A).PosSemidef)
    (htp : ∀ x, Quantum.Channels.IsTracePreserving ⇑(T x))
    (x : X) :
    ((recoveredExtension ρEtilde T hpos htp).stateMap x).toOp =
      T x (ρEtilde.stateMap x).toOp :=
  rfl

/-- A recovered extension has the prescribed marginal blocks whenever the
recovery maps send each smoothed block's partial trace back to itself.

The hypothesis `hmargid` is a pointwise marginal identity at the smoothed
blocks; it is weaker than the global partial-trace section `∀ A, partialTraceB (T x A) = A`. -/
lemma recoveredExtension_partialTraceB_stateMap_toOp
    {X : Type*} [Fintype X] {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρEtilde : CQState X dE)
    (T : X → Op dE →ₗ[ℂ] Op (dE * dR))
    (hpos : ∀ x : X, ∀ A : Op dE, A.PosSemidef → (T x A).PosSemidef)
    (htp : ∀ x : X, Quantum.Channels.IsTracePreserving ⇑(T x))
    (hmargid : ∀ x : X,
      partialTraceB (T x (ρEtilde.stateMap x).toOp) =
        (ρEtilde.stateMap x).toOp)
    (x : X) :
    partialTraceB ((recoveredExtension ρEtilde T hpos htp).stateMap x).toOp =
      (ρEtilde.stateMap x).toOp := by
  rw [recoveredExtension_stateMap_toOp]
  exact hmargid x

/-- **Data-processing for purified distance (Uhlmann monotonicity).**

If two `E ⊗ R` extensions `ρER`, `ρERtilde` arise from two `E`-marginals `ρE`,
`ρEtilde` by applying the *same* family of completely positive, trace-preserving
recovery maps `T x` blockwise, then the purified distance between the extensions
is at most the purified distance between the marginals.

Complete positivity (`hcp`) is essential and not implied by mere positivity:
data-processing / Uhlmann monotonicity fails for positive-but-not-CP maps (e.g.
the transpose).  The interface requires `IsTracePreserving` (`htp`) rather than a
global partial-trace section, reflecting the actual CPTP structure of the
recovery channels.

Mathematically this is monotonicity of generalized fidelity / purified distance
under the blockwise classically-controlled CPTP recovery channel `x ↦ T x`. -/
theorem CQState.purifiedDistance_recovery_contract
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρE ρEtilde : CQState X dE)
    (ρER ρERtilde : CQState X (dE * dR))
    (T : X → (Op dE →ₗ[ℂ] Op (dE * dR)))
    (_hmono : ∀ x, ∀ A B : Op dE, opLe A B → opLe (T x A) (T x B))
    (_hpos : ∀ x, ∀ A : Op dE, A.PosSemidef → (T x A).PosSemidef)
    (hcp : ∀ x, Quantum.Channels.IsCompletelyPositive ⇑(T x))
    (htp : ∀ x, Quantum.Channels.IsTracePreserving ⇑(T x))
    (hρER : ∀ x, (ρER.stateMap x).toOp = T x (ρE.stateMap x).toOp)
    (hρERtilde : ∀ x, (ρERtilde.stateMap x).toOp = T x (ρEtilde.stateMap x).toOp) :
    CQState.purifiedDistance ρER ρERtilde ≤
      CQState.purifiedDistance ρE ρEtilde := by
  have : NeZero (dE * dR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  have hT_cptp : ∀ x, Quantum.Channels.IsCPTP ⇑(T x) := fun x =>
    Quantum.Channels.isCPTP_of_isCompletelyPositive_isTracePreserving (T x) (hcp x) (htp x)
  apply purifiedDistance_le_of_fidelityGen_ge
  exact CQState.fidelityGen_le_fidelityGen_blockwise_cptp
    ρE ρEtilde ρER ρERtilde T hT_cptp hρER hρERtilde

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
