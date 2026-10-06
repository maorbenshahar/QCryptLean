/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.PhaseOnlyPivot

/-!
# The component AEP floor at the phase-only pivot

Each pure paired component is measured against its own quantum marginal. Its Alice-key entropy
is at least the phase-only Devetak–Winter rate over `n - m` rounds minus the bit-register IID
AEP penalty. The PE announcement and register transport preserve that reference without a
postselection logarithm. The extended floor also applies to light components, whose entropy
is infinite when the smoothing ball contains zero.

The window `δ` controls acceptance, and `dev` controls the soundness edge `Q + δ + dev ≤ 1/2`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `lemma:infsmoothedmin`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- The labelled Alice-key component floor against its own quantum marginal.
At the soundness edge `Q + δ + dev ≤ 1/2`, the floor is the phase-only entropy rate minus the
bit-register IID AEP penalty, cast by `ENNReal.ofReal` into the extended entropy.
The component must be pure. -/
theorem bb84_keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAliceKeyDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ dev : ℝ) (hbound : Q + δ + dev ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (ψ : DensityOp (signalDim * signalDim))
    (hψ : DensityOp.partialTraceB ψ ∈ goodRateSetPhaseOnly Q (δ + dev))
    (hψPure : ψ.IsPure) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ)).quantumMarginal := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hEve : NeZero (1 * signalDim ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hPEpow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hsplit : NeZero (bb84PEAnnounceLabelDim n m *
      (signalDim ^ bb84KeyRoundCount n m *
        signalDim ^ (n - bb84KeyRoundCount n m))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  have hnK : NeZero (bb84KeyRoundCount n m) := bb84KeyRoundCount_neZero hmn
  -- (C1) good error bounds on the component `σ = Tr_B ψ`, at the deviation edge `Q + δ + dev`.
  -- Only the PHASE rate is read: the phase-only floor needs no bit-flip hypothesis.
  have hphase : phaseFlipErrorRate_single (DensityOp.partialTraceB ψ) ≤ Q + δ + dev := by
    have h : phaseFlipErrorRate_single
        (componentAliceBobMarginal (DensityOp.partialTraceB ψ)) ≤ Q + (δ + dev) := hψ
    rw [componentAliceBobMarginal_eq] at h
    linarith
  have hrate := bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev (DensityOp.partialTraceB ψ) Q δ
    dev hbound hphase
  rw [bb84ComponentAliceZRate] at hrate
  -- (C2) the `n_K`-fold smooth AEP lift and its penalty leaf, at `n_K = n − m`.
  have hAEP := bb84_perSigma_smoothHmin_ge_nfold_DW (DensityOp.partialTraceB ψ)
    (bb84KeyRoundCount n m) εTensor hεTensor_pos
  have hnn : (0 : ℝ) ≤ (bb84KeyRoundCount n m : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrate hnn
  -- (e) the key-round isometric invariance.
  have he := bb84_keyRoundCQ_tensorPower_smoothMinEntropy_ge_componentAliceZ
    (n := n) (m := m) εTensor ψ hψPure
  -- the labelled announce, free.
  have hA1 := bb84_peLabelledAnnounce_smoothMinEntropy_ge_key (m := m)
    peSel xSel Q δ εTensor ψ
  -- the labelled register transport.
  rw [bb84_peLabelledCoarsenAliceKey_smoothMinEntropy_quantumMarginal_eq_sortedSplit
    peSel xSel hcount Q δ εTensor ψ]
  unfold bb84PairedHaarFloorLevelDev
  have hid : (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
        (Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) =
      (bb84KeyRoundCount n m : ℝ) *
        ((Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) / Real.log 2) := by ring
  rw [hid]
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hmul _)).trans
    (hAEP.trans (he.trans hA1))

/-- The labelled Alice-key component floor against its own quantum marginal.
At the soundness edge `Q + 2δ ≤ 1/2`, the floor is the phase-only entropy rate minus the
bit-register IID AEP penalty, cast by `ENNReal.ofReal` into the extended entropy.
The component must be pure. -/
theorem bb84_keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAliceKey {n m : ℕ}
    [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (ψ : DensityOp (signalDim * signalDim))
    (hψ : DensityOp.partialTraceB ψ ∈ goodRateSetPhaseOnly Q (2 * δ))
    (hψPure : ψ.IsPure) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevel n m Q δ εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ)).quantumMarginal := by
  -- the `2δ` floor is the Dev floor at `dev = δ`: the pivot widens to
  -- `goodRateSetPhaseOnly Q (δ + δ)` (the same membership up to the edge associativity), the
  -- level reads back via `bb84PairedHaarFloorLevelDev_eq`, and `hbound` is `Q + 2 * δ ≤ 1/2`
  -- at `dev = δ`.
  have h := bb84_keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAliceKeyDev
    peSel xSel hcount Q δ δ (by linarith) hmn εTensor hεTensor_pos ψ
    (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hψ; exact hψ) hψPure
  rwa [bb84PairedHaarFloorLevelDev_eq] at h

end QKD.BB84.Engine

end -- noncomputable section
