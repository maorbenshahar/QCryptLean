import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Engine.Budgets
import QCryptLean.QKD.BB84.Engine.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AnyRefAgreeBlock
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Engine.Budgets

/-!
# The basic agree-block leftover-hash bound

The agree-block trace distance is at most
`PA + 2 * (ε_AEP + √(2E))`, with
`PA = ½ exp(-(n-m)/4 * (log 2 - h(Q+2δ)))`.
The extended labelled entropy floor feeds reference-optimised leftover hashing at every weight.
The basic key-rate condition funds the
bit-register AEP penalty, `2 log₂ C(n+15,15)`, the public syndrome and the verification tag.

References: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL`, Appendix B;
Renner 2005, `cor:Hmincondrepclass`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- The secrecy bound from an extended labelled entropy floor.
The key-rate condition funds `loss = log 2 * P + 2 log g + (leakEC + ℓEV) log 2`, where
`g = C(n+15,15)`. Reference optimisation and leftover hashing cost `2 * (ε_AEP + √(2E))`.
The PA exponent uses exactly the phase-only rate `log 2 - h(Q+2δ)`. Reference: Nahar et al. 2024,
Appendix B, `eq:condLHL`. -/
theorem
 agreeBlockTraceDistance_le_lhlOutput_of_peLabelledFloor_ofTail
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hKey : basicKeyRateCondition n m ℓ ℓEV leakEC Q δ ε_AEP)
    {E : ℝ}
    (hAEP : 0 < ε_AEP)
    (V : BB84SymmetricPurifier n)
    (hFloor :
      haveI _hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
      haveI _hRdim : NeZero ((signalDim ^ n) * V.dV) :=
        ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
      ∃ σref : SubDensityOp
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
            (signalDim ^ (n - bb84KeyRoundCount n m) *
              (eveDim * ((signalDim ^ n) * V.dV)))),
        ENNReal.ofReal (bb84PairedHaarFloorLevel n m Q δ ε_AEP -
          2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
          smoothMinEntropy
            (ε_AEP + Real.sqrt (2 * E))
            (bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
                (bb84EnVCKRPurification V))
            σref) :
    haveI _hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI _hRdim : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
            xSel leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
              xSel leakEC ec Q δ)
        (bb84EnVCKRPurification V) ≤
      (1 / 2) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) +
        2 * (ε_AEP + Real.sqrt (2 * E)) := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hRdim : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- The B16-B17-B19 floor `kEV = kfloor − P − 2·log₂ g − (leakEC + ℓEV)`, at `n_K = n − m`.
  set kEV : ℝ := bb84PairedHaarFloorLevel n m Q δ ε_AEP -
    2 * Real.log (bb84PolyDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) with hkEVdef
  -- **B18 cap: the general-`m` key-rate condition funds `2·ℓ·log 2 + 2·loss` exactly.**
  have hcap_acc :
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) * 2 ^ (-kEV)) ≤
        (1 / 2) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
          (Real.log 2 - binaryEntropy (Q + 2 * δ))) := by
    -- The key-rate condition and component floor charge the same phase-only entropy rate.
    set α : ℝ := Real.log 2 - binaryEntropy (Q + 2 * δ) with hαdef
    set loss : ℝ :=
      Real.log 2 * finiteSizePenalty (bb84KeyRoundCount n m) ε_AEP +
        2 * Real.log (bb84PolyDim n : ℝ) + ((leakEC : ℝ) + (ℓEV : ℝ)) * Real.log 2 with hlossdef
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCdef :
        (bb84PolyDim n : ℝ) =
          (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) := by
      rw [bb84PolyDim]
    have hkey_loss : 2 * (ℓ : ℝ) * Real.log 2 + 2 * loss ≤
        (bb84KeyRoundCount n m : ℝ) * α := by
      have hk := hKey
      unfold basicKeyRateCondition at hk
      rw [← hCdef] at hk
      rw [hlossdef, hαdef]
      -- `hk` is this inequality with `loss` expanded term by term.
      linear_combination hk
    have hcap := real_lhl_budget_at_key_rate_with_log_loss (bb84KeyRoundCount n m) ℓ α loss
      hkey_loss
    have hexp_eq : kEV =
        (bb84KeyRoundCount n m : ℝ) / Real.log 2 * α - loss / Real.log 2 := by
      rw [hkEVdef, bb84PairedHaarFloorLevel, hαdef, hlossdef]
      field_simp
      ring
    rw [hexp_eq]
    exact hcap
  exact agreeBlockTraceDistance_le_lhlOutput_of_floor_anyRef
    (m := m) eveDim pre hpre peSel xSel ec Q δ
    (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (bb84EnVCKRPurification V) kEV
    ((1 / 2) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ))))
    hcap_acc hFloor

end QKD.BB84.Engine

end -- noncomputable section
