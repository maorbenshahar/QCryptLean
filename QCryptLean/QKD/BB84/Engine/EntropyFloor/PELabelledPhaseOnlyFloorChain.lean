/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnouncePEFloorChainEnV
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaPhaseOnlyFloor

/-!
# The basic PE-labelled phase-only entropy floor

The good set is the phase-good preimage alone. Its complement has accepted mass at most `E`.
Each component is measured against its own marginal. Light components use zero-state smoothing
witnesses, so the mixture radius is `εTensor + √(2E)` without a light-component mass charge.
The mixture reference is its full quantum marginal.

The announcement costs `leakEC + ℓEV` bits. Adjoining the symmetric purifier costs
`2 * log₂ (bb84PolyDim n)`, where `bb84PolyDim n = C(n+15,15)`. The soundness edge is
`Q + δ + dev ≤ 1/2`; the doubled-window declarations specialize at `dev = δ`.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin`,
`eq:splittingoffV`, `lemma:infsmoothedmin`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. The phase-only accept-split interface -/

/-- The accepted mass outside `Tr_B⁻¹'(goodRateSetPhaseOnly Q (2 * δ))` is at most `E`.
The PE-label register is included in the family, and no component-weight cut is imposed. -/
def IsPELabelledAcceptSplitPhaseBadBranchBounded {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ E : ℝ) : Prop :=
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (eveDim * (signalDim ^ n))) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                    DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                  (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
                eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n)))).trace).re ≤
      E

/-- The accepted mass outside `Tr_B⁻¹'(goodRateSetPhaseOnly Q (δ + dev))` is at most `E`.
The PE-label register is included in the family, and no component-weight cut is imposed. -/
def IsPELabelledAcceptSplitPhaseBadBranchBoundedDev {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ dev E : ℝ) : Prop :=
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (eveDim * (signalDim ^ n))) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                    DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                  (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
                eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n)))).trace).re ≤
      E

/-- The `dev = δ` interface bridge `IsPELabelledAcceptSplitPhaseBadBranchBounded → …Dev`: at
`dev = δ` the two pivot radii agree after the `δ + δ = 2 * δ` rewrite (not defeq, as the Dev
def's docstring records). -/
theorem isPELabelledAcceptSplitBoundedDev_of_isPELabelledAcceptSplitBounded
    (n m : ℕ) [NeZero n] [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ E : ℝ)
    (h : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) eveDim pre hpre peSel xSel Q δ E) :
    IsPELabelledAcceptSplitPhaseBadBranchBoundedDev
      (m := m) eveDim pre hpre peSel xSel Q δ δ E := by
  rw [IsPELabelledAcceptSplitPhaseBadBranchBoundedDev,
    show (δ : ℝ) + δ = 2 * δ from by ring]
  exact h

/-! ## 2. The general-`m` floor chain at the phase-only pivot

The mixture floor uses the closed phase-good set and the component floor
`bb84_keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAliceKeyDev`.
The announcement and register-split theorems transport that floor. Positivity of the floor
implies `m < n`, ensuring that the key-round count is nonzero.
-/

/-- The extended labelled mixture floor `ofReal k ≤ smoothMinEntropy` against its marginal.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announcePE_ofTailDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ dev : ℝ)
    (hbelowDev : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBoundedDev (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ dev E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev εTensor) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ))
        (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal := by
  by_cases hLevelPos : 0 < bb84PairedHaarFloorLevelDev n m Q δ dev εTensor
  swap
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hLevelPos)]
    exact bot_le
  have hmn := lt_of_bb84PairedHaarFloorLevelDev_pos hLevelPos
  haveI hNd : NeZero (signalDim * signalDim) := ⟨by norm_num⟩
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hN' : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLab : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  set G : Set (DensityOp (signalDim * signalDim)) :=
    (DensityOp.partialTraceB :
      DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
        goodRateSetPhaseOnly Q (δ + dev) with hG
  have hgoodClosed : IsClosed G := bb84_pairedHaar_goodSetPhaseOnly_isClosedDev Q δ dev
  -- The general-`m` labelled per-σ floor at the deviation, at PURE accepting rate-good `τ`.
  have hf_smoothFloor : ∀ τ ∈ G, τ.IsPure →
      ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev εTensor) ≤
        smoothMinEntropy εTensor
          (CQState.coarsen (aliceKeyString peSel)
            (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ τ))
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ τ).quantumMarginal := by
    intro τ hτ hτpure
    have hfloor :=
      bb84_keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAliceKeyDev
        (m := m) peSel xSel hcount Q δ dev hbelowDev hmn εTensor
        hεTensor_pos τ hτ hτpure
    rw [CQState.coarsen_quantumMarginal] at hfloor
    exact hfloor
  -- The de Finetti Haar measure is supported on the closed pure-state locus.
  have hPpure_closed : IsClosed
      (setOf (fun σ : DensityOp (signalDim * signalDim) => σ.IsPure)) := by
    have hcont : Continuous (fun σ : DensityOp (signalDim * signalDim) => σ.toOp) :=
      continuous_induced_dom
    exact isClosed_eq (hcont.mul hcont) hcont
  have hPpure_ae :
      ∀ᵐ τ ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure,
        τ ∈ setOf (fun σ : DensityOp (signalDim * signalDim) => σ.IsPure) :=
    deFinetti_haarMeasure_isProductStateMeasure (signalDim * signalDim)
  exact
    smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor
    (g := aliceKeyString peSel)
    (μ := deFinetti_haarMeasure (signalDim * signalDim))
    (ρ_mix := bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
    (f := bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
    (bb84_peLabelledRhoEtilde_eq_haar_integral_blocks (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
    (bb84PELabelledPairedHaarPerSigmaFamily_blocks_continuous (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
    G hgoodClosed
    (P := setOf (fun σ : DensityOp (signalDim * signalDim) => σ.IsPure))
    hPpure_closed hPpure_ae
    (bb84PairedHaarFloorLevelDev n m Q δ dev εTensor) εTensor
    E
    hεTensor_pos.le
    hBad
    (fun τ hτ hP _ => hf_smoothFloor τ hτ hP)

/-- The extended labelled mixture floor after charging the syndrome and verification tag.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announce_ofTailDev
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelowDev : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBoundedDev (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ dev E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev εTensor - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).tensorLeftKernel
            (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))))
        ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV))) := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hN' : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLab : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  -- The announcement is constant on the fibres of the Alice-key coarsening, so it slides across it.
  have hslide := CQState.coarsen_tensorLeftKernel_of_fiberConstant
    (aliceKeyString peSel) (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
    (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))
    (bb84AnnounceKernel ℓEV peSel ec) (fun _ => rfl)
  rw [hslide]
  -- The labelled mixture floor at the deviation (Dev base rung), charged with the announcement.
  have hfloor := bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announcePE_ofTailDev
      (m := m)
    peSel xSel hcount Q δ dev hbelowDev hBad εTensor hεTensor_pos
  have hann := bb84_smoothMinEntropy_announce_ge_sub_leak ℓEV peSel ec
    (εTensor + Real.sqrt (2 * E))
    (CQState.coarsen (aliceKeyString peSel)
      (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ))
    (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal
  rw [ENNReal.ofReal_sub _ (by positivity)]
  exact tsub_le_iff_right.mpr (hfloor.trans hann)

/-! ## 3. Adjoining the de Finetti purifier `V` -/

/-- A CQ register-dimension cast transports each block's operator along the matrix cast. -/
private lemma castCQ_stateMap_toOpLab {Xq : Type*} [Fintype Xq] {a b : ℕ} (h : a = b)
    (ρ : CQState Xq a) (x : Xq) :
    ((bb84CastCQState h ρ).stateMap x).toOp = h ▸ ((ρ.stateMap x).toOp) := by
  subst h; rfl

/-- Classical coarsening commutes with the CQ register-dimension cast. -/
private lemma coarsen_castCQLab {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    {a b : ℕ} (h : a = b) (g : Xc → Yc) (ρ : CQState Xc a) :
    CQState.coarsen g (bb84CastCQState h ρ) = bb84CastCQState h (CQState.coarsen g ρ) := by
  subst h; rfl

/-- The extended announced labelled floor after adjoining the symmetric purifier.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem naharSiftedDeFinetti_peLabelledEnV_smoothFloorPhaseOnly_announcePE_ofTailDev
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBoundedDev (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ dev E)
    (V : BB84SymmetricPurifier n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP) :
    haveI _hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI _hRdim : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * ((signalDim ^ n) * V.dV)))),
      ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev ε_AEP -
        2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
              (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
                (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
                    (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
                  (bb84EnVCKRPurification V)).toCQState)).tensorLeftKernel
            (bb84AnnounceKernel ℓEV peSel ec)) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hVdv : NeZero V.dV := V.dV_neZero
  haveI hRdim : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hEveDimR : NeZero (1 * ((signalDim ^ n) * V.dV)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabPow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
    ⟨pow_ne_zero _ (by norm_num [signalDim])⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hAnn : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num)))⟩
  haveI hAnnLabE : NeZero ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)) *
      (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n)))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  haveI hAnnDim : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI hAnnLabRef : NeZero ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)) *
      (bb84PEAnnounceLabelDim n m *
        (1 * (signalDim ^ n)))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  set dAnn : ℕ := 2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) with hdAnn
  set dLab : ℕ := signalDim ^ (n - bb84KeyRoundCount n m) with hdLab
  set dE : ℕ := 1 * (signalDim ^ n) with hdE
  set K : KeyBitString n peSel → SubDensityOp dAnn := bb84AnnounceKernel ℓEV peSel ec
    with hKdef
  set Lab : (Fin n → Fin signalDim) → SubDensityOp dLab :=
    bb84PELabelKernel (m := m) peSel with hLabDef
  set gmap : (Fin n → Fin signalDim) → KeyBitString n peSel :=
    aliceKeyString peSel with hgmap
  set r : ℝ := Real.sqrt (2 * E) with hrdef
  -- The fine-register objects: the `Eⁿ`-marginal mixture and the EnV state.
  set ρEtfine : CQState (Fin n → Fin signalDim) dE :=
    bb84EnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
        with hρEtfine
  set ρEVfine : CQState (Fin n → Fin signalDim)
      (1 * ((signalDim ^ n) * V.dV)) :=
    bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
      (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
        (bb84EnVCKRPurification V)).toCQState with hρEVfine
  -- The three register reassociations: announcement high, PE label middle, purifier `V` low.
  have h1 : 1 * ((signalDim ^ n) * V.dV) = dE * V.dV := by
    rw [hdE]; ring
  have h2 : dLab * (1 * ((signalDim ^ n) * V.dV)) =
      dLab * dE * V.dV := by rw [hdE]; ring
  have h3 : dAnn * (dLab * (1 * ((signalDim ^ n) * V.dV))) =
      dAnn * (dLab * dE) * V.dV := by rw [hdE]; ring
  -- (1) the base trace-out-`V` blocks identity (Nahar et al. `\label{eq:splittingoffV}`).
  have hbase : ∀ x : Fin n → Fin signalDim,
      Quantum.TensorProducts.partialTraceB (h1 ▸ (ρEVfine.stateMap x).toOp : Op (dE * V.dV)) =
        (ρEtfine.stateMap x).toOp := by
    intro x
    rw [← castCQ_stateMap_toOpLab h1 ρEVfine x]
    exact bb84_EnV_rhoEV_partialTraceB_eq_forCoarsen 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ V x
  -- (2) across the general-`m` PE-label kernel.
  have hlab : ∀ x : Fin n → Fin signalDim,
      Quantum.TensorProducts.partialTraceB
          (h2 ▸ ((ρEVfine.tensorLeftKernel Lab).stateMap x).toOp : Op (dLab * dE * V.dV)) =
        ((ρEtfine.tensorLeftKernel Lab).stateMap x).toOp :=
    fun x => partialTraceB_tensorLeftKernel_blocks h1 h2 Lab ρEVfine ρEtfine hbase x
  -- (3) pushed forward along the Alice-key coarsening.
  have hcoarse : ∀ y : KeyBitString n peSel,
      Quantum.TensorProducts.partialTraceB
          (h2 ▸ ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).stateMap y).toOp :
            Op (dLab * dE * V.dV)) =
        ((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).stateMap y).toOp := by
    intro y
    have hstep := partialTraceB_coarsen_blocks gmap
      (bb84CastCQState h2 (ρEVfine.tensorLeftKernel Lab))
      (ρEtfine.tensorLeftKernel Lab)
      (fun x => by rw [castCQ_stateMap_toOpLab h2]; exact hlab x) y
    rwa [coarsen_castCQLab h2, castCQ_stateMap_toOpLab h2] at hstep
  -- (4) across the `(syndrome, EV seed, EV tag)` announce kernel.
  have hblocks : ∀ y : KeyBitString n peSel,
      Quantum.TensorProducts.partialTraceB
          (h3 ▸ (((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel
              K).stateMap y).toOp : Op (dAnn * (dLab * dE) * V.dV)) =
        (((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).tensorLeftKernel K).stateMap
          y).toOp :=
    fun y => partialTraceB_tensorLeftKernel_blocks h2 h3 K
      (CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab))
      (CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)) hcoarse y
  -- The announced labelled mixture floor at the deviation, slid into
  -- `(coarsen ·).tensorLeftKernel K` shape.
  have hFloor : ENNReal.ofReal (bb84PairedHaarFloorLevelDev n m Q δ dev ε_AEP -
      ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy (ε_AEP + r)
        ((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).tensorLeftKernel K)
        ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor
          dAnn) := by
    have hbaseF := bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announce_ofTailDev
      (m := m) (ℓEV := ℓEV)
      peSel xSel hcount ec Q δ dev hbelow hBad ε_AEP hAEP
    rw [CQState.coarsen_tensorLeftKernel_of_fiberConstant (aliceKeyString peSel)
      (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ)
      (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))
      (bb84AnnounceKernel ℓEV peSel ec) (fun _ => rfl)] at hbaseF
    exact hbaseF
  -- The register-extension host: the `−2·log₂ g` purifier-adjunction penalty.
  have hext := smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    (bb84CastCQState h3
      ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K))
    ((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).tensorLeftKernel K)
    ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
      (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor dAnn)
    (fun y => by rw [castCQ_stateMap_toOpLab h3]; exact hblocks y) (ε_AEP + r)
  have hmono : 2 * Real.log (V.dV : ℝ) / Real.log 2 ≤
      2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 := by
    gcongr
    · exact_mod_cast NeZero.pos V.dV
    · exact V.dV_le_polyDim
  have hpen : 0 ≤ 2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 := by
    apply div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ?_))
      (Real.log_pos one_lt_two).le
    exact_mod_cast bb84PolyDim_pos n
  have hhost := tsub_le_iff_right.mpr
    (hFloor.trans (hext.trans (add_le_add_right (ENNReal.ofReal_le_ofReal hmono) _)))
  rw [← ENNReal.ofReal_sub _ hpen] at hhost
  refine ⟨SubDensityOp.castDim h3.symm
    (((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor
          dAnn).tensorMaxMixed
      V.dV), ?_⟩
  -- The register reassociation transported back onto the protocol's own object.
  have hround : bb84CastCQState h3.symm (bb84CastCQState h3
      ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K)) =
      (CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K :=
    bb84CastCQState_symm_cast h3.symm _
  rw [bb84_smoothMinEntropy_castDim h3.symm (ε_AEP + r)
    (bb84CastCQState h3 ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K))
    (((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor
          dAnn).tensorMaxMixed
      V.dV),
    hround] at hhost
  have harith : bb84PairedHaarFloorLevelDev n m Q δ dev ε_AEP -
        2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) =
      (bb84PairedHaarFloorLevelDev n m Q δ dev ε_AEP - ((leakEC : ℝ) + (ℓEV : ℝ))) -
        2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 := by ring
  rw [harith, hrdef]
  exact hhost

/-! ## 4. The `2δ` specializations

Each `2δ` theorem specializes the free-deviation theorem at `dev = δ`: the accept-split
marker converts through the interface bridge `isPELabelledAcceptSplitBoundedDev_of_…`, the
threshold hypothesis through `Q + δ + δ = Q + 2 * δ`, and the carried level reads back through
`bb84PairedHaarFloorLevelDev_eq`. -/

/-- The extended labelled mixture floor `ofReal k ≤ smoothMinEntropy` against its marginal.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announcePE_ofTail
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow2 : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevel n m Q δ εTensor) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ))
        (bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- bridge, and the carried level reads back through `bb84PairedHaarFloorLevelDev_eq`.
  have h := bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announcePE_ofTailDev
      (m := m)
    peSel xSel hcount Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (isPELabelledAcceptSplitBoundedDev_of_isPELabelledAcceptSplitBounded n m 1
      (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E hBad)
    εTensor hεTensor_pos
  rwa [bb84PairedHaarFloorLevelDev_eq] at h

/-! The announcement specialization. -/

/-- The extended labelled mixture floor after charging the syndrome and verification tag.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announce_ofTail
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow2 : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ENNReal.ofReal (bb84PairedHaarFloorLevel n m Q δ εTensor - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).tensorLeftKernel
            (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))))
        ((bb84PELabelledEnVRhoEtilde (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).quantumMarginal.maxMixedTensor
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV))) := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- bridge, and the carried level reads back through `bb84PairedHaarFloorLevelDev_eq`.
  have h := bb84_peLabelledEnVRhoEtilde_smoothMinEntropyFloorPhaseOnly_announce_ofTailDev
      (m := m) (ℓEV := ℓEV)
    peSel xSel hcount ec Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (isPELabelledAcceptSplitBoundedDev_of_isPELabelledAcceptSplitBounded n m 1
      (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E hBad)
    εTensor hεTensor_pos
  rwa [bb84PairedHaarFloorLevelDev_eq] at h

/-! The register-split specialization. -/

/-- The extended announced labelled floor after adjoining the symmetric purifier.
The phase-only bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem naharSiftedDeFinetti_peLabelledEnV_smoothFloorPhaseOnly_announcePE_ofTail
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (V : BB84SymmetricPurifier n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP) :
    haveI _hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI _hRdim : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * ((signalDim ^ n) * V.dV)))),
      ENNReal.ofReal (bb84PairedHaarFloorLevel n m Q δ ε_AEP -
        2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
              (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
                (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
                    (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
                  (bb84EnVCKRPurification V)).toCQState)).tensorLeftKernel
            (bb84AnnounceKernel ℓEV peSel ec)) σref := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- bridge, and the carried level reads back through `bb84PairedHaarFloorLevelDev_eq`.
  have h := naharSiftedDeFinetti_peLabelledEnV_smoothFloorPhaseOnly_announcePE_ofTailDev
      (m := m) (ℓEV := ℓEV)
    peSel xSel hcount ec Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (isPELabelledAcceptSplitBoundedDev_of_isPELabelledAcceptSplitBounded n m 1
      (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E hBad)
    V ε_AEP hAEP
  rw [bb84PairedHaarFloorLevelDev_eq] at h
  exact h

end QKD.BB84.Engine

end -- noncomputable section
