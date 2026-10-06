/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetPhaseOnlyAssembly
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailPhaseOnlyGeneral

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
# The basic BB84 security bound

The normalized diamond distance is bounded by
`2^(-ℓEV) + C(n+15,15) * (PA + 2 ε_AEP + 2 √(2E))`, where
`E = exp(-m_X * klBer (Q+δ) (Q+2δ))` and
`PA = ½ exp(-(n-m)/4 * (log 2 - h(Q+2δ)))`.

The exact agree/differ decomposition charges correctness directly. The CKR reduction applies
only to the agree block. The key-rate condition pays `2 log₂ C(n+15,15)` and the bit-register
IID AEP penalty. Its doubled length convention gives a coefficient `4 log C(n+15,15)` in nats.

When the tail is at least `1/8`, the budget is at least one. Empty acceptance gives identical
channels. The remaining branch uses the extended entropy floor at every positive radius.
The only explicit
numerical conditions are positive smoothing, the key-rate inequality and `Q + 2δ ≤ 1/2`.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B; Renner 2005,
`cor:Hmincondrepclass`; Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1.
-/

/-- The basic BB84 diamond bound at the exact phase-only KL acceptance tail.
The decoder and selectors are arbitrary. The key-count identity ties the entropy copy count
to the actual retained rounds. Only the secrecy part receives the CKR factor `C(n+15,15)`. -/
theorem bb84_ckr_security_klTailPhaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (2 ^ n)] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : basicKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP) :
    (1 / 2) * diamondNorm
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      standardBudgetOfTail (klAcceptTailPhaseOnly peSel xSel Q δ) n m ℓEV Q δ ε_AEP := by
  have hnorm := diamondNorm_sub_le_two
    (bb84SymRealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (bb84SymIdealChannel_isCPTP n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  have hone : (1 / 2 : ℝ) * diamondNorm
      (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤ 1 := by linarith only [hnorm]
  have hg : (4 : ℝ) ≤
      (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) := by
    have h16 : (16 : ℝ) ≤ (bb84PolyDim n : ℝ) := by
      exact_mod_cast bb84PolyDim_ge_16 (n := n)
    exact (by norm_num : (4 : ℝ) ≤ 16).trans h16
  have hlarge (h : 1 / 8 ≤ klAcceptTailPhaseOnly peSel xSel Q δ) :
      1 ≤ standardBudgetOfTail (klAcceptTailPhaseOnly peSel xSel Q δ) n m ℓEV Q δ ε_AEP := by
    have hb := Real.one_le_add_mul_add_sqrt_of_large hg
      (show 0 ≤ (2 : ℝ) ^ (-(ℓEV : ℝ)) by positivity) hAEP.le
      (show 0 ≤ (1 / 2 : ℝ) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) from by positivity)
      (Or.inr (Or.inl h))
    simpa only [standardBudgetOfTail, bb84CKRPostselectionInnerBudgetOfTail,
      mul_add, add_comm, add_left_comm, add_assoc] using hb
  by_cases hE8 : klAcceptTailPhaseOnly peSel xSel Q δ < 1 / 8
  · by_cases hempty : δ < 0 ∨ Q + δ < 0
    · rw [bb84SymChannels_eq_of_empty_acceptance n m ℓ ℓEV Q δ peSel xSel leakEC ec hempty,
        sub_self, diamondNorm_zero, mul_zero]
      unfold standardBudgetOfTail bb84CKRPostselectionInnerBudgetOfTail
      positivity
    · have hδ : 0 ≤ δ := le_of_not_gt (fun h => hempty (Or.inl h))
      have hδpos : 0 < δ := by
        rcases hδ.eq_or_lt with hzero | hpos
        · norm_num only [← hzero, klAcceptTailPhaseOnly, mul_zero, add_zero,
            Math.Concentration.BernoulliKL.klBer_self, Real.exp_zero] at hE8
        · exact hpos
      have hbound :=
        bb84_nahar_bareReference_innerBudget_withPEAnnounce_ofTail_phaseOnly
          (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hKey hAEP
          (bb84UnitRegisterEmbed_isAcceptSplitPhaseBadBranchBounded_klTailPhaseOnly
            (m := m) Q δ hδpos peSel xSel) hcount
      unfold standardBudgetOfTail
      refine (bb84SymChannels_diamondDist_le_correctness_add_symDim_mul_agreeTraceDistance
        n m ℓ ℓEV Q δ peSel xSel leakEC ec).trans ?_
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))
  · exact hone.trans (hlarge (le_of_not_gt hE8))

end QKD.BB84.Engine

end -- noncomputable section
