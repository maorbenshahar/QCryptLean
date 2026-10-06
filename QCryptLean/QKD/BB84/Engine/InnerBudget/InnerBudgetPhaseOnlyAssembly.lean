/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.Budgets.BennettPostselectionBudget
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetCorrectness
import QCryptLean.QKD.BB84.Engine.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.InnerBudgetPhaseOnlyAgreeBlock

/-!
# The basic agree-block budget at the phase-only pivot

The own-marginal extended smooth-entropy floor and leftover hashing give
`PA + 2 ε_AEP + 2 √(2E)` on the CKR reference for every accepted weight.
Verification is charged separately by the engine's exact agree/differ decomposition.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:condLHL`;
Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- The agree-block CKR secrecy budget at the phase-only pivot.
The labelled extended entropy floor supplies the leftover-hashing bound on a symmetric purifier.
Purification invariance transfers the result to the canonical CKR reference. -/
theorem bb84_nahar_bareReference_innerBudget_withPEAnnounce_ofTail_phaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : basicKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
      (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (hcount : bb84KeyCount n m peSel) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SymPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bb84SymCKRDeFinettiPurification n) ≤
      bb84CKRPostselectionInnerBudgetOfTail E n m Q δ ε_AEP := by
  refine (mul_le_mul_of_nonneg_left
    (bb84SymPassBlockDelta_ckrTensorTraceNorm_le false n m ℓ ℓEV Q δ
    peSel xSel leakEC ec (bb84SymCKRDeFinettiPurification n)
    (bb84SymCKRDeFinettiPurification_isPairedPermInvariant n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hOutDim : NeZero (2 ^ ℓ * 2 ^ ℓ *
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).transcriptDim *
      1) := by
    change NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC 1)
    infer_instance
  -- The rank-`g` symmetric purifier carrying Nahar et al.'s `R = Eⁿ ⊗ V` register split (B13/B17).
  obtain ⟨V⟩ := bb84_symmetricPurifier_exists n
  haveI hRdim : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- The general-`m` raw leftover-hashing output bound on the agree block, at the `EⁿV` reference.
  have hRes :=
      agreeBlockTraceDistance_le_lhlOutput_ofTail_phaseOnly
    (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hKey hAEP hBad
    hcount V
  -- B19: `ckrTensorTraceNorm` is purification-invariant, so the bound moves from the `EⁿV` register
  -- back to the canonical CKR de Finetti purification.
  have hL3 := bb84_ckrTensorTraceNorm_EnV_eq_canonical (n := n) V
    (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1 (bb84UnitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  change (1 / 2) * ckrTensorTraceNorm
    (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1
      (bb84UnitRegisterEmbed n) peSel xSel leakEC ec Q δ -
      bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1
        (bb84UnitRegisterEmbed n) peSel xSel leakEC ec Q δ)
    (bb84SymCKRDeFinettiPurification n) ≤ _
  rw [hL3]
  unfold bb84CKRPostselectionInnerBudgetOfTail
  linarith only [hRes]

end QKD.BB84.Engine

end -- noncomputable section
