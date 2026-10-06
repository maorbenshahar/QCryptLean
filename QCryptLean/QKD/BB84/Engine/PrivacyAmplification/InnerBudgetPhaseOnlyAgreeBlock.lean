/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.InnerBudgetAgreeBlock
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPhaseOnlyFloorChain

/-!
# Basic phase-only agree-block secrecy

The phase-only bad branch has mass at most `E`. The own-marginal mixture floor uses radius
`ε_AEP + √(2E)`. The extended floor and leftover hashing give
`PA + 2 ε_AEP + 2 √(2E)` for every decoder. The phase-only soundness edge is at most one half.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin`,
`eq:splittingoffV` and `eq:condLHL`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. The PE-label axis floor at the phase-only pivot -/

/-- The labelled leftover-hash input floor at radius `ε_AEP + √(2E)`.
Announcement costs `leakEC + ℓEV`, and purifier adjunction costs `2 log₂ C(n+15,15)`.
The extended entropy floor includes every accepted weight. -/
theorem bb84PELabelledLHLInput_smoothMinEntropyFloorPhaseOnly_ofTail
    {n m ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (hcount : bb84KeyCount n m peSel)
    (V : BB84SymmetricPurifier n) :
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
          (bb84PELabelledLHLInput (m := m) ℓEV 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel ec Q δ (bb84EnVCKRPurification V)) σref :=
              by
  exact naharSiftedDeFinetti_peLabelledEnV_smoothFloorPhaseOnly_announcePE_ofTail
    (m := m) (ℓEV := ℓEV) peSel xSel hcount ec Q δ hbelow hBad V ε_AEP hAEP

/-- The phase-only secrecy bound on the symmetric purifier.
The key count, AEP penalty and PA exponent use `n - m`, while the purifier charge uses the
full-block dimension `C(n+15,15)`. The decoder is arbitrary. -/
theorem agreeBlockTraceDistance_le_lhlOutput_ofTail_phaseOnly
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : basicKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP)
    {E : ℝ}
    (hBad : IsPELabelledAcceptSplitPhaseBadBranchBounded (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ E)
    (hcount : bb84KeyCount n m peSel)
    (V : BB84SymmetricPurifier n) :
    haveI _hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI _hRdim : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV 1
            (bb84UnitRegisterEmbed n)
            peSel xSel leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV 1
              (bb84UnitRegisterEmbed n)
            peSel xSel leakEC ec Q δ)
        (bb84EnVCKRPurification V) ≤
      (1 / 2) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) +
        2 * (ε_AEP + Real.sqrt (2 * E)) := by
  exact agreeBlockTraceDistance_le_lhlOutput_of_peLabelledFloor_ofTail
    (m := m) 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
    peSel xSel ec Q δ ε_AEP hKey hAEP V
    (bb84PELabelledLHLInput_smoothMinEntropyFloorPhaseOnly_ofTail (m := m) (ℓEV := ℓEV)
      peSel xSel ec Q δ ε_AEP hbelow hAEP hBad hcount V)

end QKD.BB84.Engine

end -- noncomputable section
