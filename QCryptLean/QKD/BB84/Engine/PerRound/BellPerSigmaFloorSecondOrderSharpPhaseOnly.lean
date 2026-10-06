/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.Budgets.BellFloorLevelSecondOrderSharp
import QCryptLean.QKD.BB84.Engine.PerRound.SecondOrderSharpPenalty
import QCryptLean.QKD.BB84.Engine.PerRound.BellPerSigmaFloorBennettPhaseOnly

/-!
# The Bell per-σ collective floor at the sharp-cap Cor IV.2 penalty, general `m`, phase-only pivot

The Bell per-σ PE-labelled floor `ofReal k ≤ smoothMinEntropy`, charged at the Dupuis–Fawzi
Cor IV.2 penalty at the sharp variance cap, a general parameter-estimation test-set size `m`, and
the phase-only de Finetti pivot `goodRateSetPhaseOnly Q (2δ)` (`PhaseOnlyPivot.lean`).

The good branch's Carathéodory membership `Tr_B (bellWembed φ) ∈ goodRateSetPhaseOnly Q (2δ)`
already supplies the phase bound `bb84ComponentAliceZRate_ge_phaseOnly_of_good` needs, so the
bit-flip conjunct is never read; the floor level depends only on this phase bound. The penalty
enters only through the `n_K`-fold AEP lift
`bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharp`, which reads the component's rate and
not the pivot, so the two axes do not interact.

## Direction

`goodRateSet Q δ ⊆ goodRateSetPhaseOnly Q δ` (`goodRateSet_subset_goodRateSetPhaseOnly`), strictly.
The good set therefore **grows**: the floor below is a statement about strictly more Carathéodory
points than a `goodRateSet`-scoped floor would be.  That is the burden the phase-only pivot moves
onto the good branch, and it is discharged here.

## The charge and penalty

`sharpCharge`, in some sibling theorem names, is the Bell `C(n+3,3)` de Finetti charge
`bb84PolyDimTight`; `finiteSizePenaltySecondOrderSharp`, read in this module, is the Dupuis–Fawzi
Cor IV.2 penalty at the sharp variance cap `bb84SharpVarianceCap = log₂²(1+√2)`
(`secondOrderSharpBeta` clamped at `1/16`).

## No regime hypothesis is read

`secondOrderSharpRegime` does not appear.  The sharp-cap lift is unconditional because
`secondOrderSharpBeta` is clamped at `1/16`, which guarantees `β⋆ < 1`.

## What is `m`-scoped and what is not

The key-round count `n_K = bb84KeyRoundCount n m = n − m` scopes the phase-only rate factor, the AEP
copy count and the second argument of `finiteSizePenaltySecondOrderSharp` (the first is the
variance cap), and it scopes the register split and the announced-PE label register. The component
reference is its own quantum marginal, including zero accepted blocks.

## Window and deviation

`keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAtDev` is the
free-deviation twin: the window `δ` keeps its protocol role (accept masses, accept sets,
integrands), while the pivot membership `goodRateSetPhaseOnly Q (δ + dev)` and the floor level
`bb84BellFloorLevelSecondOrderSharpAtDev` charge the soundness edge `Q + δ + dev`; the `2δ` rung
`…_soSharpAt` is the case `dev = δ` (Nahar et al. 2024, arXiv:2403.11851, Lemma 9 Eq. 44 with
§V.C).

## Relation to the literature

The phase-only restriction is **not** in the cited literature.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-only conjunction, not authority for
dropping the bit ball.  What licenses it here is
`QKD.BB84.Engine.bb84ComponentAliceZRate_ge_phaseOnly_of_good`.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`), `\label{lem:divergence-variance-general-bounds}` (`:394`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`), §3.1, §6.5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), `\label{lem:groupPurification}`
(`main.tex:354`), `\label{eq:boundingsmoothedmin}` (`main.tex:1380`), `\label{eq:splittingoffV}`
(`main.tex:1393`), §V.C (`main.tex:909` — the general test-set size `m`; `main.tex:913` —
`n_key = n − m`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- **The Bell per-σ PE-labelled collective floor at the Cor IV.2 penalty charged at a free Rényi
offset `β ∈ (0, 1)`, a general test-set size `m`, the phase-only pivot, and a free phase-error
deviation.**

The free-deviation version of
`keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAt`: the pivot
hypothesis is membership in `goodRateSetPhaseOnly Q (δ + dev)` at the **deviation edge**
`Q + δ + dev`
rather than the window edge `Q + 2·δ`.  Here `δ = p.tolerance` keeps only its protocol role — the
half-width of the accept-test window — and `dev` is the phase-error **deviation** between the
window edge and the phase-error rate the floor is charged at; `dev = δ` gives the
doubled-window floor.

The phase-only membership again supplies the phase bound
`bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev` needs, so the bit-flip conjunct is never read;
the floor level is `bb84BellFloorLevelSecondOrderSharpAtDev` (entropy argument `Q + δ + dev`).
The penalty enters only through the `n_K`-fold AEP lift
`bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt`, which reads the component's rate and
not the pivot, so the deviation and the penalty axes do not interact; the announcement
and register transport use only the window `δ`.

This is the separation of Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44 with §V.C: the entropy floor is charged at the soundness edge, not at the
completeness window. -/
theorem
    keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAtDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ dev : ℝ) (hbound : Q + δ + dev ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (φ : DensityOp 4)
    (hφ : DensityOp.partialTraceB (bellWembed φ) ∈ goodRateSetPhaseOnly Q (δ + dev))
    (hφPure : φ.IsPure) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev εTensor β) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ))).quantumMarginal := by
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
  -- (C1) the good rate bound on the component `σ = Tr_B (Wembed φ)`, at the deviation edge.
  -- The phase-only membership IS the phase bound; membership carries `Q + (δ + dev)`.
  have hphase : phaseFlipErrorRate_single (DensityOp.partialTraceB (bellWembed φ))
      ≤ Q + δ + dev := by
    have h : phaseFlipErrorRate_single
        (componentAliceBobMarginal (DensityOp.partialTraceB (bellWembed φ))) ≤ Q + (δ + dev) := hφ
    rw [componentAliceBobMarginal_eq] at h
    linarith
  have hrate := bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev
    (DensityOp.partialTraceB (bellWembed φ)) Q δ dev hbound hphase
  rw [bb84ComponentAliceZRate] at hrate
  -- (C2) the `n_K`-fold smooth AEP lift at the Cor IV.2 penalty at the FREE offset `β`,
  -- at `n_K = n − m`.  Deviation-blind: reads the component's rate, not the pivot.
  have hAEP := bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt
    (DensityOp.partialTraceB (bellWembed φ)) (bb84KeyRoundCount n m) εTensor β hεTensor_pos
    hβpos hβ1
  have hnn : (0 : ℝ) ≤ (bb84KeyRoundCount n m : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrate hnn
  -- (e) the key-round isometric invariance, at the general-`m` copy count.
  have he := bb84_keyRoundCQ_tensorPower_smoothMinEntropy_ge_componentAliceZ
    (n := n) (m := m) εTensor (bellWembed φ)
    (bellWembed_isPure hφPure)
  -- the labelled announce, free.
  have hA1 := bb84_peLabelledAnnounce_smoothMinEntropy_ge_key (m := m)
    peSel xSel Q δ εTensor (bellWembed φ)
  -- the labelled register transport.
  rw [bb84_peLabelledCoarsenAliceKey_smoothMinEntropy_quantumMarginal_eq_sortedSplit
    peSel xSel hcount Q δ εTensor (bellWembed φ)]
  unfold bb84BellFloorLevelSecondOrderSharpAtDev
  have hid : (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
        (Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) =
      (bb84KeyRoundCount n m : ℝ) *
        ((Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) / Real.log 2) := by ring
  rw [hid]
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hmul _)).trans
    (hAEP.trans (he.trans hA1))

/-- **The Bell per-σ PE-labelled collective floor at the Cor IV.2 penalty charged at a free Rényi
offset `β ∈ (0, 1)`, a general test-set size `m`, and the phase-only pivot.**

The free-`β` version of
`keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharp`: the floor level
is `bb84BellFloorLevelSecondOrderSharpAt n m Q δ εTensor β` and the single penalty-bearing step is
the `n_K`-fold AEP lift `bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt` (Dupuis–Fawzi
Cor. IV.2 holds at every `β ∈ (0, 1)`, not only at the clamped optimiser).  All other
hypotheses and scoping conventions are as in the fixed-`β⋆` twin. -/
theorem
    keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAt
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (φ : DensityOp 4)
    (hφ : DensityOp.partialTraceB (bellWembed φ) ∈ goodRateSetPhaseOnly Q (2 * δ))
    (hφPure : φ.IsPure) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharpAt n m Q δ εTensor β) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ))).quantumMarginal := by
  -- the doubled-window floor is the Dev floor at `dev = δ`: the pivot widens to
  -- `goodRateSetPhaseOnly Q (δ + δ)` (the same membership up to the edge associativity), the
  -- level reads back via `bb84BellFloorLevelSecondOrderSharpAtDev_eq`, and `hbound` is
  -- `Q + 2 * δ ≤ 1/2` at `dev = δ`.
  have h := keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAtDev
    peSel xSel hcount Q δ δ (by linarith) hmn εTensor hεTensor_pos β hβpos hβ1
    φ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hφ; exact hφ) hφPure
  rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq] at h

/-- **The Bell per-σ PE-labelled collective floor at the sharp-cap Cor IV.2 penalty, a general
test-set size `m`, and the phase-only pivot.**

The pivot hypothesis is `hφ : Tr_B (bellWembed φ) ∈ goodRateSetPhaseOnly Q (2δ)`, quantified over
a strictly larger set of components than `goodRateSet Q (2δ)` would give
(`goodRateSet_subset_goodRateSetPhaseOnly`), at the floor level
`bb84BellFloorLevelSecondOrderSharp n m Q δ εTensor` and reference
the component’s own quantum marginal.  This costs nothing: `hφ` already supplies the phase bound
`bb84ComponentAliceZRate_ge_phaseOnly_of_good` needs, which binds `hbound` and the phase bound
alone.

The single penalty-bearing step is the `n_K`-fold AEP lift
`bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharp` at `n_K = bb84KeyRoundCount n m`; the
pivot does not reach it.

The key-round count `n_K = n − m` scopes the phase-only rate factor, AEP copy count,
finite-size penalty, register split, and announced label register.

**Restricted to the trivial attack slot**, per Carathéodory point, and at a **pure** `φ`: `hφPure`
supplies the key-round purification unitary.

`hmn : m < n` supplies `NeZero (bb84KeyRoundCount n m)` to the AEP lift.  **No regime hypothesis
is read**, because `secondOrderSharpBeta` is clamped at `1/16`.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `\label{eq_eathmin_halpha}` (`:1053`); Renner 2005 (`arXiv:quant-ph/0512258v2`)
`\label{thm:Hmincondrep}` (`main.tex:4561`), `\label{lem:rtbound}` (`main.tex:10487`), §3.1, §6.5;
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`), `\label{lem:groupPurification}` (`main.tex:354`),
`\label{eq:boundingsmoothedmin}` (`main.tex:1380`), `\label{eq:splittingoffV}` (`main.tex:1393`),
§V.C (`main.tex:909`, `:913`). -/
theorem
    keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharp
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) (hεTensor_lt_one : εTensor < 1)
    (φ : DensityOp 4)
    (hφ : DensityOp.partialTraceB (bellWembed φ) ∈ goodRateSetPhaseOnly Q (2 * δ))
    (hφPure : φ.IsPure) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ENNReal.ofReal (bb84BellFloorLevelSecondOrderSharp n m Q δ εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)))
        (CQState.coarsen (aliceKeyString peSel)
          (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ))).quantumMarginal := by
  -- the fixed-`β⋆` row is the free-`β` floor at `β = secondOrderSharpBeta …`.
  have hnK : NeZero (bb84KeyRoundCount n m) := bb84KeyRoundCount_neZero hmn
  refine keyScoped_perSigmaLabelled_collective_smoothFloorPhaseOnly_coarsenAlice_soSharpAt
    peSel xSel hcount Q δ hbound hmn εTensor hεTensor_pos
    (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) εTensor) ?_ ?_
    φ hφ hφPure
  · exact secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
      (bb84KeyRoundCount n m) εTensor hεTensor_pos hεTensor_lt_one
  · exact (secondOrderSharpBeta_le_one_sixteenth bb84SharpVarianceCap (bb84KeyRoundCount n m)
      εTensor).trans_lt (by norm_num)

end QKD.BB84.Engine

end -- noncomputable section
