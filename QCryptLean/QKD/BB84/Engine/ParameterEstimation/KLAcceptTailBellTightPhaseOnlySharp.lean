/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailBellTight
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.BellAcceptTailCapPhaseOnly
import QCryptLean.QKD.BB84.Engine.PerRound.BellPerSigmaFloorSecondOrderSharpPhaseOnly
import QCryptLean.QKD.BB84.Engine.InnerBudget.PassBlocks

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
# Extended Bell entropy floors and privacy amplification

The Bell route combines a phase-only component floor with the accepted-mixture bound at radius
`ε_AEP + √(2E)`. The completed signed floor is cast by `ENNReal.ofReal`; its reference is the
component's own quantum marginal. The syndrome and verification announcement cost
`leakEC + ℓEV`, and adjoining the Bell purifier costs `2 log₂ C(n+3,3)`.

The leftover-hashing theorem consumes these extended entropy floors at every retained weight,
including zero.
Free Rényi offsets require `0 < β < 1` and positive smoothing. The fixed optimizer uses
`ε_AEP < 1` and a nonzero key count to ensure its offset is positive.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin`,
`eq:splittingoffV` and `eq:condLHL`; Dupuis–Fawzi 2018, arXiv:1805.11652, Corollary IV.2.
-/

/-! ## 0. Register-cast plumbing -/

/-- A CQ register-dimension cast transports each block's operator along the matrix cast.  Register
plumbing; nothing here reads `m`, the pivot, the accept tail or the AEP penalty. -/
private lemma bb84CastCQState_stateMap_toOp_klTailBellSharpPhaseOnly {Xc : Type*} [Fintype Xc]
    {a b : ℕ} (h : a = b) (ρ : CQState Xc a) (x : Xc) :
    ((bb84CastCQState h ρ).stateMap x).toOp = h ▸ ((ρ.stateMap x).toOp) := by
  subst h; rfl

/-- Classical coarsening commutes with the CQ register-dimension cast. -/
private lemma bb84Coarsen_castCQ_klTailBellSharpPhaseOnly {Xc Yc : Type*} [Fintype Xc]
    [Fintype Yc] [DecidableEq Yc] {a b : ℕ} (h : a = b) (g : Xc → Yc) (ρ : CQState Xc a) :
    CQState.coarsen g (bb84CastCQState h ρ) = bb84CastCQState h (CQState.coarsen g ρ) := by
  subst h; rfl

/-! ## 1. The general-`m` sharp-cap Bell floor chain at the phase-only pivot -/

/-- The extended Bell mixture floor after the PE announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail_ofLevelDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ∃ σref : SubDensityOp
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  refine ⟨((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n)
    (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).tensorLeftKernel
      (bb84PELabelKernel (m := m) peSel)).quantumMarginal, ?_⟩
  by_cases hmn : m < n
  swap
  · by_cases hεlt1 : ε_AEP < 1
    · have hzero : bb84KeyRoundCount n m = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hpen := finiteSizePenaltySecondOrderSharpAt_nonneg bb84SharpVarianceCap
        bb84SharpVarianceCap_pos.le (bb84KeyRoundCount n m) ε_AEP β hAEP
        hεlt1.le hβpos.le hβ1.le
      have hlevel : bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β ≤ 0 := by
        unfold bb84BellFloorLevelSecondOrderSharpAtDev
        rw [hzero, Nat.cast_zero, zero_div, zero_mul]
        rw [hzero] at hpen
        linarith
      rw [ENNReal.ofReal_eq_zero.mpr hlevel]
      exact bot_le
    · rw [smoothMinEntropy_eq_top_of_weight_le_eps_sq (by positivity)]
      · exact le_top
      · have hw := (CQState.coarsen (aliceKeyString peSel)
          ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))).weight_le_one
        nlinarith [Real.sqrt_nonneg (2 * E)]
  set G : Set (DensityOp 4) :=
    (fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
      goodRateSetPhaseOnly Q (δ + dev) with hG
  have hgoodClosed : IsClosed G := by
    have hphase : Continuous (fun σ : DensityOp signalDim =>
        phaseFlipErrorRate_single (componentAliceBobMarginal σ)) :=
      phaseFlipErrorRate_single_continuous.comp componentAliceBobMarginal_continuous
    exact bb84_bell_goodPreimage_isClosed_ofClosed (isClosed_le hphase continuous_const)
  -- The general-`m` sharp-cap per-σ Bell labelled floor at the PHASE-ONLY pivot, at the deviation
  -- edge, at PURE accepting rate-good components.
  have hf_smoothFloor : ∀ φ ∈ G, φ ∈ setOf (fun φ' : DensityOp 4 => φ'.IsPure) →
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β) ≤
        smoothMinEntropy ε_AEP
          (CQState.coarsen (aliceKeyString peSel)
            (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ)))
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ)).quantumMarginal := by
    intro φ hφ hφpure
    have hfloor :=
      keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAtDev
        (m := m) peSel xSel hcount Q δ dev
        hbelow hmn
        ε_AEP hAEP β hβpos hβ1 φ hφ hφpure
    rw [CQState.coarsen_quantumMarginal] at hfloor
    exact hfloor
  -- The Bell de Finetti Haar measure is supported on the closed pure-state locus.
  have hPpure_closed : IsClosed (setOf (fun φ : DensityOp 4 => φ.IsPure)) := by
    have hcont : Continuous (fun φ : DensityOp 4 => φ.toOp) := continuous_induced_dom
    exact isClosed_eq (hcont.mul hcont) hcont
  have hPpure_ae : ∀ᵐ φ ∂(deFinetti_haarMeasure 4).measure,
      φ ∈ setOf (fun φ' : DensityOp 4 => φ'.IsPure) :=
    deFinetti_haarMeasure_isProductStateMeasure 4
  exact
    smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor
    (g := aliceKeyString peSel)
    (μ := deFinetti_haarMeasure 4)
    (ρ_mix := (bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        peSel xSel Q δ).tensorLeftKernel
      (bb84PELabelKernel (m := m) peSel))
    (f := fun φ : DensityOp 4 =>
      bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ))
    (bb84_bellPeLabelledEnVRhoEtilde_eq_haar_integral_blocks (m := m) peSel xSel Q δ)
    (fun x => tensorLeftKernel_blocks_continuous
      (fun φ : DensityOp 4 =>
        bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ (bellWembed φ))
      (bb84PELabelKernel (m := m) peSel) x
      (bb84_bellPairedHaarPerSigmaFamily_blocks_continuous peSel xSel Q δ x))
    G hgoodClosed
    (P := setOf (fun φ : DensityOp 4 => φ.IsPure))
    hPpure_closed hPpure_ae
    (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β) ε_AEP
    E
    hAEP.le
    (by
      rw [hG]
      exact bb84_bellPeLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev
        (m := m) peSel xSel Q δ dev E hE0 hCap)
    (fun τ hτ hP _ => hf_smoothFloor τ hτ hP)

/-- The extended Bell mixture floor after the PE announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail_ofLevel
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ∃ σref : SubDensityOp
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  -- The doubled-window form is the special case `dev = δ` of the free-deviation rung above.
  obtain ⟨σ0, hfloor⟩ :=
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail_ofLevelDev
      (m := m) peSel xSel hcount Q δ δ
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) ε_AEP hAEP β hβpos hβ1
      hE0
      (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap)
  exact ⟨σ0, by rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq] at hfloor⟩

/-- The extended Bell mixture floor after the PE announcement, at
the fixed Rényi optimizer. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    ∃ σref : SubDensityOp
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))) σref := by
  haveI hnK : NeZero (bb84KeyRoundCount n m) := bb84KeyRoundCount_neZero hmn
  refine bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail_ofLevel
    (m := m) peSel xSel hcount Q δ hbelow ε_AEP hAEP
    (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP) ?_ ?_
    hE0 hCap
  · exact secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
      (bb84KeyRoundCount n m) ε_AEP hAEP hεS
  · exact (secondOrderSharpBeta_le_one_sixteenth bb84SharpVarianceCap (bb84KeyRoundCount n m)
      ε_AEP).trans_lt (by norm_num)

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail_ofLevelDev
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    haveI hAnnLabE : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))) :=
      ⟨Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
          (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))).tensorLeftKernel
            (bb84AnnounceKernel ℓEV peSel ec)) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  -- The free-deviation per-σ PE-announcement rung is the witness.
  obtain ⟨σ0, hfloor⟩ :=
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announcePE_soSharp_ofTail_ofLevelDev
      (m := m) peSel xSel hcount Q δ dev hbelow ε_AEP hAEP β hβpos hβ1 hE0
      hCap
  refine ⟨σ0.maxMixedTensor (2 ^ leakEC *
    (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)), ?_⟩
  have hann := bb84_smoothMinEntropy_announce_ge_sub_leak ℓEV peSel ec
    (ε_AEP + Real.sqrt (2 * E))
    (CQState.coarsen (aliceKeyString peSel)
      ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
          Q δ).tensorLeftKernel
        (bb84PELabelKernel (m := m) peSel)))
    σ0
  rw [ENNReal.ofReal_sub _ (by positivity)]
  exact tsub_le_iff_right.mpr (hfloor.trans hann)

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail_ofLevel
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    haveI hAnnLabE : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))) :=
      ⟨Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
          (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))).tensorLeftKernel
            (bb84AnnounceKernel ℓEV peSel ec)) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  haveI hAnnLabE : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  -- The doubled-window form is the special case `dev = δ` of the free-deviation rung above.
  obtain ⟨σ0, hfloor⟩ :=
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail_ofLevelDev
      (m := m) (ℓEV := ℓEV) peSel xSel hcount ec Q δ δ
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) ε_AEP hAEP β hβpos hβ1
      hE0
      (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap)
  exact ⟨σ0, by rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq] at hfloor⟩

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
the fixed Rényi optimizer. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail
    {n m leakEC ℓEV : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
        (1 * (signalDim ^ n))) :=
      ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    haveI hAnnLabE : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))) :=
      ⟨Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
          (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
                peSel xSel Q δ).tensorLeftKernel
              (bb84PELabelKernel (m := m) peSel))).tensorLeftKernel
            (bb84AnnounceKernel ℓEV peSel ec)) σref := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hEnDim : NeZero (1 * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hLabE : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      (1 * (signalDim ^ n))) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  -- The fixed-`β⋆` row is the free-`β` rung at the clamped optimiser `β⋆`.
  haveI hnK : NeZero (bb84KeyRoundCount n m) := bb84KeyRoundCount_neZero hmn
  refine bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail_ofLevel
    (m := m) peSel xSel hcount ec Q δ hbelow ε_AEP hAEP
    (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP) ?_ ?_
    hE0 hCap
  · exact secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
      (bb84KeyRoundCount n m) ε_AEP hAEP hεS
  · exact (secondOrderSharpBeta_le_one_sixteenth bb84SharpVarianceCap (bb84KeyRoundCount n m)
      ε_AEP).trans_lt (by norm_num)

/-- The extended Bell leftover-hash input floor after the purifier charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail_ofLevelDev
    {n m ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E)
    (V : BB84BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * ((signalDim ^ n) * V.dV)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
            2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (bb84PELabelledLHLInput (m := m) ℓEV 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel ec Q δ
            (bb84EnVBellPurification V)) σref := by
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
  -- The fine-register objects: the Bell `Eⁿ`-marginal mixture and the Bell EnV state.
  set ρEtfine : CQState (Fin n → Fin signalDim) dE :=
    bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
        with hρEtfine
  set ρEVfine : CQState (Fin n → Fin signalDim)
      (1 * ((signalDim ^ n) * V.dV)) :=
    bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
      (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
        (bb84EnVBellPurification V)).toCQState with hρEVfine
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
    rw [← bb84CastCQState_stateMap_toOp_klTailBellSharpPhaseOnly h1 ρEVfine x]
    exact bb84_EnV_bellRhoEV_partialTraceB_eq_forCoarsen 1 (bb84UnitRegisterEmbed n)
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
      (fun x => by
        rw [bb84CastCQState_stateMap_toOp_klTailBellSharpPhaseOnly h2]; exact hlab x) y
    rwa [bb84Coarsen_castCQ_klTailBellSharpPhaseOnly h2,
      bb84CastCQState_stateMap_toOp_klTailBellSharpPhaseOnly h2] at hstep
  -- (4) across the `(syndrome, EV seed, EV tag)` announce kernel.
  have hblocks : ∀ y : KeyBitString n peSel,
      Quantum.TensorProducts.partialTraceB
          (h3 ▸ (((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel
              K).stateMap y).toOp : Op (dAnn * (dLab * dE) * V.dV)) =
        (((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).tensorLeftKernel K).stateMap y).toOp
            :=
    fun y => partialTraceB_tensorLeftKernel_blocks h2 h3 K
      (CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab))
      (CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)) hcoarse y
  -- The Bell mixture floor at the abstract tail, at the `τ_Bell`-side accept weight, at the free
  -- `β`, at the free deviation.
  obtain ⟨σ0, hFloor⟩ :=
    bellPeLabelledEnVRhoEtilde_smoothFloorPhaseOnly_announce_secondOrderSharp_ofTail_ofLevelDev
      (m := m) (ℓEV := ℓEV) peSel xSel hcount ec Q δ dev hbelow ε_AEP hAEP
      β hβpos hβ1 hE0 hCap
  -- The register-extension host: the `−2·log₂ C(n+3,3)` purifier-adjunction penalty.
  have hext := smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    (bb84CastCQState h3
      ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K))
    ((CQState.coarsen gmap (ρEtfine.tensorLeftKernel Lab)).tensorLeftKernel K) σ0
    (fun y => by
      rw [bb84CastCQState_stateMap_toOp_klTailBellSharpPhaseOnly h3]; exact hblocks y) (ε_AEP + r)
  have hmono : 2 * Real.log (V.dV : ℝ) / Real.log 2 ≤
      2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 := by
    gcongr
    · exact_mod_cast NeZero.pos V.dV
    · exact V.dV_le_polyDimTight
  have hpen : 0 ≤ 2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 := by
    apply div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ?_))
      (Real.log_pos one_lt_two).le
    exact_mod_cast bb84PolyDimTight_pos n
  have hhost := tsub_le_iff_right.mpr
    (hFloor.trans (hext.trans (add_le_add_right (ENNReal.ofReal_le_ofReal hmono) _)))
  rw [← ENNReal.ofReal_sub _ hpen] at hhost
  refine ⟨SubDensityOp.castDim h3.symm (σ0.tensorMaxMixed V.dV), ?_⟩
  -- The register reassociation transported back onto the protocol's own object.
  have hround : bb84CastCQState h3.symm (bb84CastCQState h3
      ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K)) =
      (CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K :=
    bb84CastCQState_symm_cast h3.symm _
  rw [bb84_smoothMinEntropy_castDim h3.symm (ε_AEP + r)
    (bb84CastCQState h3 ((CQState.coarsen gmap (ρEVfine.tensorLeftKernel Lab)).tensorLeftKernel K))
    (σ0.tensorMaxMixed V.dV), hround] at hhost
  have harith : bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
        2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) =
      (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
        ((leakEC : ℝ) + (ℓEV : ℝ))) -
        2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 := by ring
  rw [harith, hrdef]
  exact hhost

/-- The extended Bell leftover-hash input floor after the purifier charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail_ofLevel
    {n m ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E)
    (V : BB84BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * ((signalDim ^ n) * V.dV)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β -
            2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (bb84PELabelledLHLInput (m := m) ℓEV 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel ec Q δ
            (bb84EnVBellPurification V)) σref := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation host above.
  obtain ⟨σ0, hFloor⟩ :=
    peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail_ofLevelDev
      (m := m) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) β hβpos hβ1
      hAEP hcount hE0
      (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap) V
  exact ⟨σ0, by rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq] at hFloor⟩

/-- The extended Bell leftover-hash input floor after the purifier charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail
    {n m ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : bb84KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E)
    (V : BB84BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * ((signalDim ^ n) * V.dV)))),
      ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
            2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (bb84PELabelledLHLInput (m := m) ℓEV 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel ec Q δ
            (bb84EnVBellPurification V)) σref := by
  -- The fixed-`β⋆` row is the free-`β` rung at the clamped optimiser `β⋆`.
  haveI hnK : NeZero (bb84KeyRoundCount n m) := bb84KeyRoundCount_neZero hmn
  refine peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail_ofLevel
    (m := m) peSel xSel ec Q δ ε_AEP hbelow
    (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP) ?_ ?_
    hAEP hcount hE0 hCap V
  · exact secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
      (bb84KeyRoundCount n m) ε_AEP hAEP hεS
  · exact (secondOrderSharpBeta_le_one_sixteenth bb84SharpVarianceCap (bb84KeyRoundCount n m)
      ε_AEP).trans_lt (by norm_num)

/-! ## 2. The general-`m` sharp-cap AGREE-block secrecy residual at the phase-only pivot -/

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E)
    (V : BB84BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1
            (bb84UnitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1
              (bb84UnitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (bb84EnVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  exact agreeBlockTraceDistance_le_lhlOutput_of_floor_anyRef
    (m := m) (ℓ := ℓ) 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
    peSel xSel ec Q δ (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (bb84EnVBellPurification V)
    (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
      2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)))
    epsPA hcap
    (peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail_ofLevelDev
      (m := m) peSel xSel ec Q δ dev ε_AEP hbelow β hβpos hβ1 hAEP hcount hE0 hCap V)

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevel
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E)
    (V : BB84BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1
            (bb84UnitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1
              (bb84UnitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (bb84EnVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation residual above.
  exact
    bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
    (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) hAEP hcount β hβpos hβ1 hE0
    (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap) V
    epsPA
    (by rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq])

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : bb84KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E)
    (V : BB84BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1
            (bb84UnitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1
              (bb84UnitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (bb84EnVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  apply agreeBlockTraceDistance_le_lhlOutput_of_floor_anyRef
    (m := m) (ℓ := ℓ) 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
    peSel xSel ec Q δ (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (bb84EnVBellPurification V)
    (bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
      2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)))
    epsPA hcap
  by_cases hk : 0 < bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
      2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))
  · exact peLabelledLHLInput_bellRef_smoothFloorPhaseOnly_soSharp_ofTail
      (m := m) peSel xSel ec Q δ ε_AEP hbelow
      (lt_of_bb84BellFloorLevelSecondOrderSharp_charged_pos hk) hAEP hεS hcount hE0 hCap V
  · exact ⟨0, by rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hk)]; exact bot_le⟩

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    naharBellRef_budget_withPEAnnounce_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bb84BellCKRDeFinettiPurification n) ≤
      bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP epsPA := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  -- The Bell symmetric purifier `V_Bell` at the affordable register `V.dV ≤ C(n+3,3)`.
  obtain ⟨V⟩ := bb84_bellSymmetricPurifier_exists n
  haveI hRdim : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  refine (mul_le_mul_of_nonneg_left
    (bb84SymPassBlockDelta_ckrTensorTraceNorm_le false n m ℓ ℓEV Q δ peSel xSel
    leakEC ec (bb84BellCKRDeFinettiPurification n)
    (bb84BellCKRDeFinettiPurification_isPairedPermInvariant n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  simp only [bb84PassBlockDelta, Bool.false_eq_true, ↓reduceIte]
  -- B19: move the agree bound from the canonical `τ_Bell` to the `Eⁿ⊗V` split.
  have hL3 := bb84_bellTensorTraceNorm_EnV_eq_canonical (n := n) V
    (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  rw [hL3]
  -- SECRECY HALF: the sharp-cap Bell-reference agree-block residual, at the free deviation.
  have hRes :=
  bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ dev ε_AEP hbelow hAEP
    hcount β hβpos hβ1 hE0 hCap V epsPA hcap
  exact hRes

/-! ## 3. The general-`m` sharp-cap Bell collective inner budget at the phase-only pivot -/

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    naharBellRef_budget_withPEAnnounce_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevel
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : bb84KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bb84BellCKRDeFinettiPurification n) ≤
      bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP epsPA := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation rung above.
  exact naharBellRef_budget_withPEAnnounce_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
    (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) hAEP hcount β hβpos hβ1
    epsPA
    (by rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq]) hE0
    (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap)

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    naharBellRef_budget_withPEAnnounce_ofScalars_secondOrderSharp_ofTail_phaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : bb84KeyCount n m peSel)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bb84BellCKRDeFinettiPurification n) ≤
      bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP epsPA := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  -- The Bell symmetric purifier `V_Bell` at the affordable register `V.dV ≤ C(n+3,3)`.
  obtain ⟨V⟩ := bb84_bellSymmetricPurifier_exists n
  haveI hRdim : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  refine (mul_le_mul_of_nonneg_left
    (bb84SymPassBlockDelta_ckrTensorTraceNorm_le false n m ℓ ℓEV Q δ peSel xSel
    leakEC ec (bb84BellCKRDeFinettiPurification n)
    (bb84BellCKRDeFinettiPurification_isPairedPermInvariant n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  simp only [bb84PassBlockDelta, Bool.false_eq_true, ↓reduceIte]
  -- B19: move the agree bound from the canonical `τ_Bell` to the `Eⁿ⊗V` split.
  have hL3 := bb84_bellTensorTraceNorm_EnV_eq_canonical (n := n) V
    (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  rw [hL3]
  -- SECRECY HALF: the sharp-cap Bell-reference agree-block residual, at the free deviation.
  have hRes :=
  bellRefAgreeBlockTraceDistance_le_lhlOut_ofScalars_secondOrderSharp_ofTail_phaseOnly
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hAEP hεS
    hcount hE0 hCap V epsPA hcap
  exact hRes

/-! ## 3. The general-`m` sharp-cap Bell collective inner budget at the phase-only pivot -/

end QKD.BB84.Engine

end -- noncomputable section
