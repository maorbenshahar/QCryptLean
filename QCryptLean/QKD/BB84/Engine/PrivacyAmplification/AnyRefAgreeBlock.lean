import QCryptLean.QKD.BB84.Engine.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Engine.Budgets

/-!
# Agree-block secrecy from an extended entropy floor

An arbitrary reference and a signed floor `kEV` for the PE-labelled input give the bound
`½‖Real_agree − Ideal_agree‖ ≤ epsPA + 2r` whenever the floor funds the leftover-hashing cap.
The extended entropy floor includes zero states and arbitrary retained weights.
Reference regularization
and agree filtering transport it to the positive-definite references used by leftover hashing.

The test-set size `m` controls the announced-PE register width. The result applies to every
CPTP pre-channel, decoder, reference state and split point.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `lemma:infsmoothedmin` and `eq:condLHL`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- An extended labelled entropy floor funds agree-block secrecy at every retained weight.
Reference regularization supplies positive-definite references for the leftover-hashing
bound, and filtering the disagreeing keys preserves the floor. -/
theorem agreeBlockTraceDistance_le_lhlOutput_of_floor_anyRef
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ r : ℝ) (hr : 0 ≤ r)
    {dimR : ℕ} [NeZero dimR] (τ : DensityOp ((signalDim ^ n) * dimR))
    (kEV : ℝ)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin (2 ^ ℓ)) : ℝ) * 2 ^ (-kEV)) ≤
      epsPA)
    (hFloor :
      haveI : NeZero (eveDim * dimR) :=
        ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
      ∃ σref : SubDensityOp
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
            (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))),
        ENNReal.ofReal kEV ≤
          smoothMinEntropy
            r
            (bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ) σref) :
    (1 / 2) * ckrTensorTraceNorm
        (bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
            xSel leakEC ec Q δ -
          bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel (m := m) ℓ ℓEV eveDim pre peSel
              xSel leakEC ec Q δ)
        τ ≤
      epsPA + 2 * r := by
  have hEveDimR : NeZero (eveDim * dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hSeedNE : Nonempty (KeyHashSeed n ℓ peSel) :=
    (aliceKeyHashFamily n ℓ peSel).seedNonempty
  have hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim])) (NeZero.ne _))⟩
  obtain ⟨σref, hLabFloor⟩ := hFloor
  set ρA : CQState (KeyBitString n peSel)
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ with hρAdef
  -- Reference optimisation, then the agree axis at zero charge.
  have hRefFamily : ∀ t : ℝ, t < kEV →
      ∃ σ' : SubDensityOp (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))),
        σ'.toOp.PosDef ∧
          ENNReal.ofReal t ≤ smoothMinEntropy r ρA σ' := by
    intro t ht
    obtain ⟨σ', hσ'_pd, hσ'_floor⟩ :=
      InfoTheory.SmoothMinEntropy.exists_posDef_smoothMinEntropy_ge_of_lt r
        (bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ)
        σref kEV hLabFloor t ht
    exact ⟨σ', hσ'_pd,
      bb84PEAnnounceAgreeLHLInput_smoothMinEntropy_ge_of_pELabelled (m := m) ℓEV eveDim pre hpre
        peSel xSel ec Q δ τ r σ' t hσ'_floor⟩
  -- B18: leftover hashing on Alice's binary key hash family, in reference-optimised form.
  have hLHL :=
    InfoTheory.QuantumLHL.quantum_seedKey_LHL_smooth_of_refOptimisedFloor
      (aliceKeyHashFamily n ℓ peSel)
      (aliceKeyHashFamily_isUniversal n ℓ peSel) ρA
      r hr kEV hRefFamily
  -- The general-`m` structural half of the leaf.
  have hbridge :=
    bb84SiftedPEAnnounceEveVisible_agreeBlock_traceDistance_le_LHL_distance
      (m := m) ℓ ℓEV eveDim pre hpre peSel xSel ec Q δ τ
  refine hbridge.trans ?_
  linarith [hLHL, hcap]

end QKD.BB84.Engine

end
