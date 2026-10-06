/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailBellTightPhaseOnlySharp
import QCryptLean.QKD.BB84.Engine.Budgets.ImprovedKeyRateCondition
import QCryptLean.QKD.BB84.Engine.Postselection.BellReductionGeneral
import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp

/-!
# The Bell tight-rate budget at the sharp Cor IV.2 penalty, exact KL accept tail, general selectors

The Bell-postselection-lifted BB84 composable security bound at the `C(n+3,3)` de Finetti charge,
the tightened `εPA`, the Dupuis–Fawzi Cor IV.2 finite-size penalty at the sharp variance cap
`bb84SharpVarianceCap = log₂²(1+√2)`, a general parameter-estimation test-set size `m`, the exact
Bernoulli-KL accept tail
priced on the realised X-subsample size, and arbitrary (not selector-pinned) PE/X-test selectors.

## Main results

-
`QKD.BB84.Engine.ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnly`:
  the security bound at a free privacy-amplification error `ε_PA` and a free Rényi offset
  `β ∈ (0, 1)`. For `ε_AEP < 1`, the fixed-`β⋆` cell follows at
  `εPA = exp(−n·δ²/2)`, `β = secondOrderSharpBeta …`; larger smoothing uses the channel bound.
-
`QKD.BB84.Engine.ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev`:
  the same at a free phase-error deviation `dev`: the window `δ` stays the protocol's, the entropy
  floor and the accept tail are charged at `Q + δ + dev` and the budget prices
  `klAcceptTailPhaseOnlyDev peSel xSel Q δ dev`; the `…At` cell below specializes it at
  `dev = δ ≥ 0` and handles negative windows by rejection.
-
`QKD.BB84.Engine.ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly`:
  the security bound. `peSel`, `xSel` are universally quantified; the only selector-facing
  hypothesis is `hcount : bb84KeyCount n m peSel`. The tail reads the realised X-test count
  without a lower bound on that count. No completeness bound is discharged here.

## Model scope

Announced-PE LOCC two-basis parameter estimation, key-round hash, error verification charged
additively, the source permuted rather than the distributed pairs, fixed key length, no
detector/loss
model, and `hec : ec.IsTranslationEquivariant` funding the `C(n+3,3)` prefactor on the channel
side. `ℓ` occurs in the budget nowhere and the budget is not asserted to be below `1`: this is a
budget statement, not a key-rate claim.

## Relation to the literature

The phase-only pivot is **not** in the cited literature; it is licensed by
`QKD.BB84.Engine.bb84ComponentAliceZRate_ge_phaseOnly_of_good`. Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-only conjunction, not authority for
dropping the bit ball.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`), `\label{lem:divergence-variance-general-bounds}` (`:394`);
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B
(`main.tex:1341`–`:1413`, `\label{eq:tausplit}` `:1356`–`:1362`, `\label{eq:boundingsmoothedmin}`
`:1380`, `\label{eq:splittingoffV}` `:1393`), `\label{eq:condLHL}` (`:462`–`:467`),
`\label{lem:groupPurification}` (`:354`) at `x = ∑ᵢ mᵢ² = 4`, §V.C (`:906`–`:919`; general test-set
size `m` at `:909`, `n_key = n − m` at `:913`, `m = 0.05·n` at `:970`); Renner 2005
(`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`), §5, §6.5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`) `main.tex:447`–`:448`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## The selector-generic sharp-cap bound at free `ε_PA` and Rényi offset `β` -/

/-- **BB84 composable security at the Bell `C(n+3,3)` charge, a free `ε_PA`, a free Rényi offset
`β ∈ (0, 1)`, a general PE test-set size `m`, the exact Bernoulli KL accept tail priced on the
realised X-subsample, arbitrary selectors, and a free phase-error deviation `dev`.**

The free-deviation version of
`ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnly`: the window `δ`
of the accept test stays the protocol's (completeness), while the entropy floor, the accept tail
and the key-rate condition are charged at the soundness edge `Q + δ + dev` (Nahar, Tupkary, Zhao,
Lütkenhaus and Tan 2024, arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C). The budget prices the
deviation-scoped tail `klAcceptTailPhaseOnlyDev peSel xSel Q δ dev =
exp(−m_X·klBer (Q+δ) (Q+δ+dev))`; `dev = δ` gives the doubled-window specialization.
The soundness edge satisfies `Q + δ + dev ≤ 1/2`, the increasing domain of binary entropy.
The key-rate condition alone does not imply this domain: binary entropy is symmetric about `1/2`.

The deviation satisfies `0 ≤ dev`. If the actual tail is at least `1/8`, the budget is at
least one. Otherwise the tail forces `dev > 0`, and the extended entropy floor applies at every
positive smoothing radius and every positive privacy-amplification error.

It is a budget statement, not a key-rate claim, and not a delivered-key claim: no completeness
bound is discharged here.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) Cor. IV.2; Nahar et al. 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`), Lemma 9 Eq. 44, §V.C, App. B;
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`). -/
theorem ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (2 ^ n)] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (Q δ dev ε_AEP εPA β : ℝ)
    (hdev : 0 ≤ dev)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hKeyTight : improvedKeyRateConditionAtDev n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β)
    (hAEP : 0 < ε_AEP)
    (hεPApos : 0 < εPA)
    (hβpos : 0 < β) (hβ1 : β < 1) :
    (1 / 2) * diamondNorm
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      improvedBudgetAt (klAcceptTailPhaseOnlyDev peSel xSel Q δ dev) n ℓEV ε_AEP εPA := by
  have hnorm := diamondNorm_sub_le_two
    (bb84SymRealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymIdealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  have hone : (1 / 2 : ℝ) * diamondNorm
      (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤ 1 := by linarith only [hnorm]
  have hg : (4 : ℝ) ≤ (Nat.choose (n + 3) 3 : ℝ) := by
    exact_mod_cast (show 4 ≤ Nat.choose (n + 3) 3 from
      (by norm_num : 4 = Nat.choose 4 3) ▸ Nat.choose_le_choose 3
        (by have := NeZero.ne n; omega))
  by_cases hE8 : klAcceptTailPhaseOnlyDev peSel xSel Q δ dev < 1 / 8
  · have hdevpos : 0 < dev := by
      rcases hdev.eq_or_lt with hzero | hpos
      · norm_num [← hzero, klAcceptTailPhaseOnlyDev] at hE8
      · exact hpos
    have hgen :=
      naharBellRef_budget_withPEAnnounce_ofScalars_secondOrderSharp_ofTail_phaseOnly_ofLevelDev
      (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV)
      peSel xSel ec Q δ dev ε_AEP hbelow hAEP hcount β hβpos hβ1 εPA
      (bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharpAtDev
        hKeyTight hεPApos)
      (klAcceptTailPhaseOnlyDev_nonneg peSel xSel Q δ dev)
      (bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev peSel xSel Q δ dev hdevpos)
    unfold improvedBudgetAt
    refine (bb84SymChannels_diamondDist_le_correctness_add_bellSymDim_mul_agreeTraceDistance
      n m ℓ ℓEV Q δ peSel xSel leakEC ec hec).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgen (Nat.cast_nonneg _))
  · exact hone.trans (Real.one_le_add_mul_add_sqrt_of_large hg (by positivity) hAEP.le hεPApos.le
      (Or.inr (Or.inl (le_of_not_gt hE8))))

/-- **BB84 composable security at the Bell `C(n+3,3)` charge, a free `ε_PA` (`\label{eq:condLHL}`,
Nahar et al. 2024), a free Rényi offset `β ∈ (0, 1)` (Dupuis–Fawzi Cor. IV.2 penalty at `β`), a
general PE test-set size `m`, the exact Bernoulli KL accept tail priced on the realised X-subsample,
and arbitrary selectors.**

Generalization of the fixed row below with the two freedoms of the `…At` row: the
privacy-amplification error is the free parameter `ε_PA`, funded by `2·log(1/ε_PA) − 2·log 2` nats
through
`improvedKeyRateConditionAt` instead of being pinned to `exp(−n·δ²/2)`, and the Dupuis–Fawzi
finite-size penalty is charged at an arbitrary admissible offset `β` instead of the clamped
optimiser `secondOrderSharpBeta`.  The budget `improvedBudgetAt` contains neither `β` nor the
penalty: the penalty reaches the statement only through the key-rate condition, and `β` only
through the key-rate condition together with its admissibility hypotheses (`hβpos`, `hβ1`), via
the single hashing-cap obligation of the level-generic chain. This obligation requires
`0 < εPA`, with no upper bound. When the actual accept tail `E ≥ 1/8`, the budget covers the
channel-distance bound of one.

For `δ ≥ 0`, the doubled-window row is the Dev row
`ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev` at `dev = δ`
(`klAcceptTailPhaseOnlyDev_self`, `improvedKeyRateConditionAtDev_eq`). A negative window rejects
every outcome, so the real and ideal channels agree.

It is a budget statement, not a key-rate claim, and not a delivered-key claim: no completeness
bound is discharged here.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) Cor. IV.2; Nahar et al. 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`), Lemma 9 Eq. 44, App. B; Renner
2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`). -/
theorem ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (2 ^ n)] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (Q δ ε_AEP εPA β : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKeyTight : improvedKeyRateConditionAt n m ℓ ℓEV leakEC Q δ ε_AEP εPA β)
    (hAEP : 0 < ε_AEP)
    (hεPApos : 0 < εPA)
    (hβpos : 0 < β) (hβ1 : β < 1) :
    (1 / 2) * diamondNorm
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      improvedBudgetAt (klAcceptTailPhaseOnly peSel xSel Q δ) n ℓEV ε_AEP εPA := by
  by_cases hδ : 0 ≤ δ
  · rw [← klAcceptTailPhaseOnlyDev_self]
    exact ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev
      peSel xSel hcount ec hec Q δ δ ε_AEP εPA β hδ
      (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
      ((improvedKeyRateConditionAtDev_eq n m ℓ ℓEV leakEC Q δ ε_AEP εPA β).mpr hKeyTight)
      hAEP hεPApos hβpos hβ1
  · have hchannels := bb84SymChannels_eq_of_empty_acceptance
      n m ℓ ℓEV Q δ peSel xSel leakEC ec (Or.inl (lt_of_not_ge hδ))
    rw [hchannels, sub_self, diamondNorm_zero, mul_zero]
    unfold improvedBudgetAt bb84CKRPostselectionInnerBudgetOfEpsPAOfTail
    positivity

/-- **BB84 composable security at the Bell `C(n+3,3)` charge, the tightened `εPA`, the Dupuis–Fawzi
Cor IV.2 penalty at the sharp variance cap, a general PE test-set size `m`, the exact Bernoulli KL
accept tail priced on the realised X-subsample, and arbitrary selectors.**

No budget object contains the penalty: the sharp cap buys admissible key length, and it reaches
the statement through the key-rate condition alone.

There is no `hmXZ` anywhere: the phase-only pivot deletes the bit arm, so parameter estimation
rejects on a single phase inequality and the Chernoff exponent is `m_X` outright. The key-rate
condition forces `m < n` when the entropic proof is used. The window is unrestricted: zero gives
tail one and a negative value forces rejection. There is no `hregime` binder: the sharp-cap AEP
lift is unconditional because `secondOrderSharpBeta` is clamped at `1/16`.

**Proof.** For `ε_AEP < 1`, the δ-pinned row is the free-`ε_PA`, free-`β` row
`ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnly` above at
`εPA := exp(−n·δ²/2)` and `β := secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m)
ε_AEP`: the pinned key-rate condition is the free one at those parameters
(`improvedKeyRateConditionAt_of_improvedKeyRateCondition`), positivity of `εPA` is `Real.exp_pos`,
and the admissibility of the clamped optimiser `β⋆` is `secondOrderSharpBeta_pos` /
`secondOrderSharpBeta_le_one_sixteenth` at the positive key count derived from the key-rate
condition.
For `1 ≤ ε_AEP`, the budget covers the channel-distance bound of one.

It is a budget statement, not a key-rate claim, and not a delivered-key claim: no completeness
bound is discharged here.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `\label{eq_eathmin_halpha}` (`:1053`); Nahar et al. 2024 (`arXiv:2403.11851`)
`\label{lem:groupPurification}` (`main.tex:354`) at `x = ∑ᵢ mᵢ² = 4`, `\label{eq:condLHL}`
(`:462`–`:467`), Lemma 9 Eq. 44, §V.C (`:906`–`:919`), App. B; Renner 2005
(`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`), §5, §6.5; CKR 2009
(`arXiv:0809.3019`) `main.tex:447`–`:448`. -/
theorem ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (2 ^ n)] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKeyTight : improvedKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP) :
    (1 / 2) * diamondNorm
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      improvedBudgetOfTail (klAcceptTailPhaseOnly peSel xSel Q δ) n ℓEV δ ε_AEP := by
  by_cases hεS : ε_AEP < 1
  · have hmn : m < n := by
      by_contra hmn
      have hzero : bb84KeyRoundCount n m = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hg : (2 : ℝ) < (Nat.choose (n + 3) 3 : ℝ) := by
        exact_mod_cast (show 2 < Nat.choose (n + 3) 3 from lt_of_lt_of_le
          (by norm_num : 2 < Nat.choose 4 3)
          (Nat.choose_le_choose 3 (by have := NeZero.ne n; omega)))
      have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) hg
      have hpen := finiteSizePenaltySecondOrderSharp_nonneg bb84SharpVarianceCap
        bb84SharpVarianceCap_pos.le (bb84KeyRoundCount n m) ε_AEP
      have hL : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
      have hk := hKeyTight
      unfold improvedKeyRateCondition at hk
      rw [hzero, Nat.cast_zero, zero_mul] at hk
      rw [hzero] at hpen
      nlinarith [mul_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hL,
        mul_nonneg (Nat.cast_nonneg leakEC : (0 : ℝ) ≤ leakEC) hL,
        mul_nonneg (Nat.cast_nonneg ℓEV : (0 : ℝ) ≤ ℓEV) hL, mul_nonneg hL hpen,
        mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg δ)]
    haveI hnK := bb84KeyRoundCount_neZero hmn
    refine ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnly
      peSel xSel hcount ec hec Q δ ε_AEP (Real.exp (-(n : ℝ) * δ ^ 2 / 2))
      (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP)
      hbelow ?_ hAEP (Real.exp_pos _) ?_ ?_
    · exact improvedKeyRateConditionAt_of_improvedKeyRateCondition hKeyTight
    · exact secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
        (bb84KeyRoundCount n m) ε_AEP hAEP (by linarith)
    · exact (secondOrderSharpBeta_le_one_sixteenth _ _ _).trans_lt (by norm_num)
  · have hnorm := diamondNorm_sub_le_two
      (bb84SymRealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
      (bb84SymIdealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    have hlarge := Real.one_le_add_mul_add_sqrt_of_large
      (g := (Nat.choose (n + 3) 3 : ℝ)) (c := (2 : ℝ) ^ (-(ℓEV : ℝ)))
      (E := klAcceptTailPhaseOnly peSel xSel Q δ)
      (p := Real.exp (-(n : ℝ) * δ ^ 2 / 2))
          (by exact_mod_cast (show 4 ≤ Nat.choose (n + 3) 3 from
            (by norm_num : 4 = Nat.choose 4 3) ▸ Nat.choose_le_choose 3
              (by have := NeZero.ne n; omega)))
          (by positivity) hAEP.le (Real.exp_pos _).le (Or.inl (by linarith [le_of_not_gt hεS]))
    refine le_trans ?_ hlarge
    linarith only [hnorm]

end QKD.BB84.Engine

end -- noncomputable section
