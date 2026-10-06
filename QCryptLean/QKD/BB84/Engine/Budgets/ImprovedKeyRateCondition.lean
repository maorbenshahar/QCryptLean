/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.Budgets.BellFloorLevelSecondOrderSharp
import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound

/-!
# Improved BB84 key-rate conditions and leftover-hashing funding

The key-rate conditions fund the Bell purifier charge, syndrome and verification leakage, the
sharp second-order penalty and a fixed or freely chosen privacy-amplification error. Their
scalar inequalities bound the real leftover-hashing expression at the completed signed floor.

References: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL` and Appendix B;
Dupuis–Fawzi 2018, arXiv:1805.11652, Corollary IV.2.
-/

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.Engine

/-- **The Bell-tightened tight-rate sharp-cap key-rate condition at a general test-set size `m`.**

Charges the hash length `ℓ`, the error-correction syndrome (`leakEC` bits), the
error-verification tag (`ℓEV` bits), the `2·log C(n+3,3)` de Finetti charge, the Dupuis–Fawzi
Cor IV.2 penalty at the sharp variance cap over the key-round count `bb84KeyRoundCount n m
= n − m`, and the δ-scale term `n·δ² − 2 log 2` funding `εPA = exp(−n·δ²/2)` on the whole block,
against the secret-rate term at entropy argument `Q + 2·δ` over the same key-round count. -/
def improvedKeyRateCondition
    (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP : ℝ) : Prop :=
  (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap
        (bb84KeyRoundCount n m) ε_AEP +
      ((n : ℝ) * δ ^ 2 - 2 * Real.log 2) ≤
    (bb84KeyRoundCount n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ))

/-- **The free-parameter Bell-tightened tight-rate sharp-cap key-rate condition** (Nahar et al.
`\label{eq:condLHL}` with a free privacy-amplification error `ε_PA` and a free Rényi offset
`β ∈ (0, 1)`, Dupuis–Fawzi Cor. IV.2).

Like `improvedKeyRateCondition`, with two freedoms: the Dupuis–Fawzi Cor IV.2 penalty is charged
at an arbitrary admissible offset `β` (`finiteSizePenaltySecondOrderSharpAt`), and the
privacy-amplification error is the free parameter `ε_PA` of `\label{eq:condLHL}`, funded by
`2·log(1/ε_PA) − 2·log 2` nats, instead of being pinned to `exp(−n·δ²/2)`.  The AEP/security chain
requires `0 < β < 1`; the scalar funders require no beta-admissibility hypotheses. The
single hashing-cap obligation requires `0 < ε_PA`, with no upper bound on the
privacy-amplification error and no positivity requirement on its logarithmic charge. -/
def improvedKeyRateConditionAt
    (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) : Prop :=
  (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap
        (bb84KeyRoundCount n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (bb84KeyRoundCount n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ))

/-- The δ-pinned key-rate condition is the free-`ε_PA`, free-`β` key-rate condition at
`ε_PA = exp(−n·δ²/2)` and `β = secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m)
ε_AEP`. -/
lemma improvedKeyRateConditionAt_of_improvedKeyRateCondition
    {n m ℓ ℓEV leakEC : ℕ} {Q δ ε_AEP : ℝ}
    (h : improvedKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP) :
    improvedKeyRateConditionAt n m ℓ ℓEV leakEC Q δ ε_AEP
      (Real.exp (-(n : ℝ) * δ ^ 2 / 2))
      (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP) := by
  have hlog : 2 * Real.log (1 / Real.exp (-(n : ℝ) * δ ^ 2 / 2)) = (n : ℝ) * δ ^ 2 := by
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  unfold improvedKeyRateConditionAt
  rw [← finiteSizePenaltySecondOrderSharp_eq, hlog]
  exact h

/-- The free-`ε_PA`, free-`β` key-rate condition at the δ-pinned `ε_PA = exp(−n·δ²/2)` and
`β = secondOrderSharpBeta …` is the fixed key-rate condition
(`improvedKeyRateConditionAt_of_improvedKeyRateCondition`, converse direction). -/
lemma improvedKeyRateCondition_of_improvedKeyRateConditionAt
    {n m ℓ ℓEV leakEC : ℕ} {Q δ ε_AEP : ℝ}
    (h : improvedKeyRateConditionAt n m ℓ ℓEV leakEC Q δ ε_AEP
      (Real.exp (-(n : ℝ) * δ ^ 2 / 2))
      (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) ε_AEP)) :
    improvedKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP := by
  have hlog : 2 * Real.log (1 / Real.exp (-(n : ℝ) * δ ^ 2 / 2)) = (n : ℝ) * δ ^ 2 := by
    rw [one_div, Real.log_inv, Real.log_exp]; ring
  unfold improvedKeyRateConditionAt at h
  unfold improvedKeyRateCondition
  rwa [← finiteSizePenaltySecondOrderSharp_eq, hlog] at h

/-- **The free-parameter key-rate condition at a free phase-error deviation `dev`.**

Like `improvedKeyRateConditionAt`, with the secret-rate term charged at the deviation edge
`Q + δ + dev` instead of the doubled window edge `Q + 2·δ`: the window half-width `δ =
p.tolerance` keeps only its protocol role — the accept-test window — while `dev` is the
phase-error **deviation** between the window edge and the rate the entropy floor is charged at
(`dev = δ` gives the doubled-window condition up to the arithmetic rewrite `δ + δ = 2 * δ`).

This is the separation of Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44 with §V.C: the rate is charged at the soundness edge, not at the completeness
window. -/
def improvedKeyRateConditionAtDev
    (n m ℓ ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) : Prop :=
  (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap
        (bb84KeyRoundCount n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (bb84KeyRoundCount n m : ℝ) * (Real.log 2 - binaryEntropy (Q + δ + dev))

/-- The doubled-window key-rate condition is the Dev condition at `dev = δ`
(up to `δ + δ = 2 * δ`). -/
lemma improvedKeyRateConditionAtDev_eq (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) :
    improvedKeyRateConditionAtDev n m ℓ ℓEV leakEC Q δ δ ε_AEP εPA β
      ↔ improvedKeyRateConditionAt n m ℓ ℓEV leakEC Q δ ε_AEP εPA β := by
  have hadd : Q + δ + δ = Q + 2 * δ := by ring
  unfold improvedKeyRateConditionAtDev improvedKeyRateConditionAt
  constructor
  · intro h; rwa [hadd] at h
  · intro h; rwa [← hadd] at h

/-- **The Dev key-rate condition funds the leftover-hash bound at the free `ε_PA`** (`0 < ε_PA`),
with the floor level charged at the deviation edge `Q + δ + dev`.

The `…At` funder is the special case `dev = δ` of this theorem; the deviation only
moves the entropy argument. -/
theorem
    bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharpAtDev
    {n m ℓ ℓEV leakEC : ℕ} {Q δ dev ε_AEP εPA β : ℝ}
    (h : improvedKeyRateConditionAtDev n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β)
    (hεPA : 0 < εPA) :
    (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤
      εPA := by
  set lpa : ℝ := Real.log (1 / εPA) - Real.log 2 with hlpadef
  set α : ℝ := Real.log 2 - binaryEntropy (Q + δ + dev) with hαdef
  set loss : ℝ :=
    Real.log 2 * finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap
      (bb84KeyRoundCount n m) ε_AEP β +
      2 * Real.log (bb84PolyDimTight n : ℝ) + ((leakEC : ℝ) + (ℓEV : ℝ)) * Real.log 2 with hlossdef
  have hCdef : (bb84PolyDimTight n : ℝ) = (Nat.choose (n + 3) 3 : ℝ) := by rw [bb84PolyDimTight]
  have hkey_loss : (ℓ : ℝ) * Real.log 2 + loss + 2 * lpa ≤
      (bb84KeyRoundCount n m : ℝ) * α := by
    have hk := h
    unfold improvedKeyRateConditionAtDev at hk
    rw [← hCdef] at hk
    rw [hlossdef, hαdef, hlpadef]
    linarith [hk]
  have hcap := real_lhl_budget_with_pa_loss (bb84KeyRoundCount n m) ℓ α loss lpa hkey_loss
  have hexp_eq : bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ dev ε_AEP β -
        2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) =
      (bb84KeyRoundCount n m : ℝ) / Real.log 2 * α - loss / Real.log 2 := by
    rw [bb84BellFloorLevelSecondOrderSharpAtDev, hαdef, hlossdef]
    field_simp
    ring
  rw [hexp_eq]
  have hexp : Real.exp (-lpa) = 2 * εPA := by
    rw [hlpadef, neg_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (one_div_pos.mpr hεPA)]
    field_simp
  rw [hexp] at hcap
  linarith

/-- **The free-parameter key-rate condition funds the leftover-hash bound at the free
`ε_PA`** (`0 < ε_PA`).

Setting `lpa := log(1/ε_PA) − log 2` in `real_lhl_budget_with_pa_loss` converts the funded budget
into `½·exp(−lpa) = ε_PA` — the free-`ε_PA` slot of Nahar et al.'s `\label{eq:condLHL}`.  The
doubled-window form is the Dev funder at `dev = δ`
(`improvedKeyRateConditionAtDev_eq`, `bb84BellFloorLevelSecondOrderSharpAtDev_eq`). -/
theorem
    bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharpAt
    {n m ℓ ℓEV leakEC : ℕ} {Q δ ε_AEP εPA β : ℝ}
    (h : improvedKeyRateConditionAt n m ℓ ℓEV leakEC Q δ ε_AEP εPA β)
    (hεPA : 0 < εPA) :
    (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharpAt n m Q δ ε_AEP β -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤
      εPA := by
  have h' : improvedKeyRateConditionAtDev n m ℓ ℓEV leakEC Q δ δ ε_AEP εPA β :=
    (improvedKeyRateConditionAtDev_eq n m ℓ ℓEV leakEC Q δ ε_AEP εPA β).mpr h
  have hcap := bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharpAtDev
    h' hεPA
  rwa [bb84BellFloorLevelSecondOrderSharpAtDev_eq] at hcap

/-- **The general-`m` sharp-cap Bell tight-rate key-rate condition funds the δ-scale
privacy-amplification exponent at the full `n`.**

The conclusion's exponent `exp(−n·δ²/2)` keeps the full `n`: it is the `εPA` slot of the
tightened inner budget, a free `\label{eq:condLHL}` parameter priced on the whole block and
independent of the accept split.  Only the rate scope and the penalty copy count move with `m`. -/
theorem
    bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharp
    {n m ℓ ℓEV leakEC : ℕ} {Q δ ε_AEP : ℝ}
    (h : improvedKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP) :
    (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) *
        2 ^ (-(bb84BellFloorLevelSecondOrderSharp n m Q δ ε_AEP -
          2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤
      Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by
  have hεPA : 0 < Real.exp (-(n : ℝ) * δ ^ 2 / 2) := Real.exp_pos _
  exact bellPeLabelledFloorSOSharp_lhlCap_of_keyRateCondBellTightTightRateSOSharpAt
    (improvedKeyRateConditionAt_of_improvedKeyRateCondition h) hεPA

end QKD.BB84.Engine

end -- noncomputable section
