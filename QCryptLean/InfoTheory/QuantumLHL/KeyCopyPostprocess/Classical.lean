import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus

/-!
# Visible-Classical Key-Copy Postprocessing — label-dependent keys and transcripts

Defines the visible-classical variant of key-copy postprocessing where each
classical input label determines both the copied key and the public transcript.
This is used when the hash seed remains visible in the protocol transcript.

## Main definitions
- `classicalKeyCopyPostprocessInputIndex`: packed input index for Eve, reference, and label.
- `classicalKeyCopyPostprocessKraus`: Kraus operator for a fixed Eve basis index and label.
- `classicalKeyCopyPostprocess`: label-dependent key-copy postprocessing channel.

## Main statements
- `classicalKeyCopyPostprocess_isCPTP`: the visible-classical channel is CPTP.
- `classicalKeyCopyPostprocess_toJointDensity_eq_sum_outputBlocks`: action on a CQ joint density.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy
open Quantum.Channels

/-!
## Visible-classical key-copy postprocessing

The concrete BB84 PA channel writes the public hash seed into the transcript.
The classical input to the LHL postprocessing is therefore a general visible
label `c`, not just a key.  The following channel maps each classical block `c`
to the copied key `key c` and transcript `transcript c`, while tracing out Eve
and preserving the reference register.
-/

/-- Input index for the visible-classical key-copy channel:
`((eve, reference), classical_label)`. -/
def classicalKeyCopyPostprocessInputIndex
    {C : Type*} [Fintype C] {eveDim refDim : ℕ}
    (e : Fin eveDim) (r : Fin refDim) (c : C) :
    Fin ((eveDim * refDim) * Fintype.card C) :=
  finProdFinEquiv (finProdFinEquiv (e, r), Fintype.equivFin C c)

/-- Kraus operator for a fixed Eve basis index and visible classical label. -/
noncomputable def classicalKeyCopyPostprocessKraus
    {C : Type*} [Fintype C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim)
    (idx : Fin eveDim × C) :
    Matrix (Fin ((keyDim * keyDim * transcriptDim) * refDim))
      (Fin ((eveDim * refDim) * Fintype.card C)) ℂ :=
  ∑ r : Fin refDim,
    Matrix.single
      (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
        (transcript idx.2) (key idx.2) r)
      (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
        idx.1 r idx.2)
      (1 : ℂ)

/-- For a fixed Eve/classical label, the visible-classical Kraus operator is an
isometry on the corresponding reference block. -/
lemma classicalKeyCopyPostprocessKraus_adjoint_mul
    {C : Type*} [Fintype C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim)
    (idx : Fin eveDim × C) :
    (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript idx)ᴴ *
        classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript idx =
      ∑ r : Fin refDim,
        Matrix.single
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            idx.1 r idx.2)
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            idx.1 r idx.2)
          (1 : ℂ) := by
  unfold classicalKeyCopyPostprocessKraus
  rw [matrix_single_sum_conjTranspose_mul_of_injective]
  intro r r' h
  exact (keyCopyPostprocessOutputIndex_eq_iff
    (keyDim := keyDim) (refDim := refDim) (transcriptDim := transcriptDim)
    (transcript idx.2)).1 h |>.2

/-- The diagonal matrix units indexed by `((e, r), c)` partition the whole input
space of the visible-classical key-copy channel. -/
lemma classicalKeyCopyPostprocessInputIndex_sum_single_one
    {C : Type*} [Fintype C]
    (eveDim refDim : ℕ)
    [NeZero eveDim] [NeZero refDim] [NeZero (Fintype.card C)] :
    (∑ e : Fin eveDim, ∑ c : C, ∑ r : Fin refDim,
      Matrix.single
        (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
          e r c)
        (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
          e r c)
        (1 : ℂ)) =
      (1 : Op ((eveDim * refDim) * Fintype.card C)) := by
  classical
  rw [show
      (∑ e : Fin eveDim, ∑ c : C, ∑ r : Fin refDim,
        Matrix.single
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            e r c)
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            e r c)
          (1 : ℂ)) =
      (∑ e : Fin eveDim, ∑ r : Fin refDim, ∑ c : C,
        Matrix.single
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            e r c)
          (classicalKeyCopyPostprocessInputIndex (eveDim := eveDim) (refDim := refDim)
            e r c)
          (1 : ℂ)) by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_comm]]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  let f : (Fin eveDim × Fin refDim) × C ≃
      Fin ((eveDim * refDim) * Fintype.card C) :=
    (finProdFinEquiv.prodCongr (Fintype.equivFin C)).trans finProdFinEquiv
  exact Eq.trans
    (Equiv.sum_comp f
      (fun i : Fin ((eveDim * refDim) * Fintype.card C) => Matrix.single i i (1 : ℂ)))
    Matrix.sum_single_one

/-- The visible-classical key-copy postprocessing map. -/
noncomputable def classicalKeyCopyPostprocess
    {C : Type*} [Fintype C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim) :
    Op ((eveDim * refDim) * Fintype.card C) →ₗ[ℂ]
      Op ((keyDim * keyDim * transcriptDim) * refDim) :=
  krausMapFintype
    (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript)

/-- Completeness of the visible-classical key-copy Kraus family. -/
lemma classicalKeyCopyPostprocessKraus_completeness
    {C : Type*} [Fintype C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    [NeZero (Fintype.card C)]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim) :
    ∑ idx : Fin eveDim × C,
        (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim
          key transcript idx)ᴴ *
          classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim
            key transcript idx =
      (1 : Op ((eveDim * refDim) * Fintype.card C)) := by
  rw [show
      (∑ idx : Fin eveDim × C,
        (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim
          key transcript idx)ᴴ *
          classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim
            key transcript idx) =
      (∑ e : Fin eveDim, ∑ c : C,
        (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
          (e, c))ᴴ *
          classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
            (e, c)) by
        exact Fintype.sum_prod_type'
          (fun e : Fin eveDim => fun c : C =>
            (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
              (e, c))ᴴ *
              classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
                (e, c))]
  simp_rw [classicalKeyCopyPostprocessKraus_adjoint_mul]
  exact classicalKeyCopyPostprocessInputIndex_sum_single_one eveDim refDim

/-- The visible-classical key-copy postprocessing map is CPTP. -/
theorem classicalKeyCopyPostprocess_isCPTP
    {C : Type*} [Fintype C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    [NeZero (Fintype.card C)]
    [NeZero ((eveDim * refDim) * Fintype.card C)]
    [NeZero ((keyDim * keyDim * transcriptDim) * refDim)]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim) :
    IsCPTP
      (⇑(classicalKeyCopyPostprocess keyDim eveDim refDim transcriptDim key transcript)) := by
  exact
    krausMapFintype_isCPTP
      (K := classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript)
      (classicalKeyCopyPostprocessKraus_completeness keyDim eveDim refDim transcriptDim
        key transcript)

/-- Action of one visible-classical Kraus operator on a block-diagonal family. -/
lemma classicalKeyCopyPostprocessKraus_reindex_blockDiagonal_conjTranspose
    {C : Type*} [Fintype C] [DecidableEq C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim)
    (B : C → Op (eveDim * refDim))
    (idx : Fin eveDim × C) :
    classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript idx *
        (Matrix.reindex
          (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
            finProdFinEquiv)
          (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
            finProdFinEquiv)
          (Matrix.blockDiagonal B)) *
        (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim
          key transcript idx)ᴴ =
      ∑ r : Fin refDim, ∑ r' : Fin refDim,
        B idx.2 (finProdFinEquiv (idx.1, r)) (finProdFinEquiv (idx.1, r')) •
          Matrix.single
            (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
              (transcript idx.2) (key idx.2) r)
            (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
              (transcript idx.2) (key idx.2) r')
            (1 : ℂ) := by
  rw [classicalKeyCopyPostprocessKraus]
  rw [matrix_single_sum_mul_mul_conjTranspose]
  simp [classicalKeyCopyPostprocessInputIndex, keyCopyPostprocessOutputIndex,
    Matrix.reindex_apply, Matrix.blockDiagonal_apply]

/-- Block-family action of the visible-classical key-copy postprocessing channel. -/
lemma classicalKeyCopyPostprocess_reindex_blockDiagonal_eq_sum_outputBlocks
    {C : Type*} [Fintype C] [DecidableEq C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim)
    (B : C → Op (eveDim * refDim)) :
    classicalKeyCopyPostprocess keyDim eveDim refDim transcriptDim key transcript
        (Matrix.reindex
          (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
            finProdFinEquiv)
          (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
            finProdFinEquiv)
          (Matrix.blockDiagonal B)) =
      ∑ c : C,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
          (transcript c) (key c) (partialTraceA (B c)) := by
  unfold classicalKeyCopyPostprocess Quantum.Channels.krausMapFintype
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [show
      (∑ idx : Fin eveDim × C,
        classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript idx *
          Matrix.reindex
            (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
              finProdFinEquiv)
            (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
              finProdFinEquiv)
            (Matrix.blockDiagonal B) *
          (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
            idx)ᴴ) =
      (∑ e : Fin eveDim, ∑ c : C,
        classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
            (e, c) *
          Matrix.reindex
            (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
              finProdFinEquiv)
            (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
              finProdFinEquiv)
            (Matrix.blockDiagonal B) *
          (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
            (e, c))ᴴ) by
        exact Fintype.sum_prod_type'
          (fun e : Fin eveDim => fun c : C =>
            classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
                (e, c) *
              Matrix.reindex
                (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
                  finProdFinEquiv)
                (((Equiv.refl (Fin (eveDim * refDim))).prodCongr (Fintype.equivFin C)).trans
                  finProdFinEquiv)
                (Matrix.blockDiagonal B) *
              (classicalKeyCopyPostprocessKraus keyDim eveDim refDim transcriptDim key transcript
                (e, c))ᴴ)]
  simp_rw [classicalKeyCopyPostprocessKraus_reindex_blockDiagonal_conjTranspose]
  simp only [keyCopyPostprocessOutputBlock, Quantum.TensorProducts.partialTraceA,
    Matrix.of_apply, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r' _
  rw [← matrix_single_finset_sum]

/-- Block action on a CQ joint-density input with a visible classical label. -/
theorem classicalKeyCopyPostprocess_toJointDensity_eq_sum_outputBlocks
    {C : Type*} [Fintype C] [DecidableEq C]
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (key : C → Fin keyDim)
    (transcript : C → Fin transcriptDim)
    (ρ : CQState C (eveDim * refDim)) :
    classicalKeyCopyPostprocess keyDim eveDim refDim transcriptDim key transcript
        ρ.toJointDensity.toOp =
      ∑ c : C,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
          (transcript c) (key c) (partialTraceA ((ρ.stateMap c).toOp)) := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rw [classicalKeyCopyPostprocess_reindex_blockDiagonal_eq_sum_outputBlocks]

end InfoTheory.QuantumLHL

end -- noncomputable section
