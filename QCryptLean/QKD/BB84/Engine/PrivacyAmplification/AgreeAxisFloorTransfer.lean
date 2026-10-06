import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnouncePEFloorChainEnV
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecompositionReferee
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Engine.Budgets
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.CoarsenFilterKeep
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.ReferenceOptimisedFloor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyReferenceOptimised

/-!
# The agree axis of the secrecy leaf, at a general test-set size `m`

The leaf's leftover-hashing input is filtered by *PE test ∧ agree*, while the floor construction
supplies a smooth-min-entropy floor only for the PE-filtered (unagreed) object.  This module closes
that **agree axis**: the agree flag is kept in the **classical** register, where its entropy charge
is zero, so `InfoTheory.SmoothMinEntropy.smoothMinEntropy_coarsen_filterKeep_ge`
(`InfoTheory/SmoothMinEntropy/CoarsenFilterKeep.lean`) transfers any floor for the PE-filtered
object onto the agree-and-PE-filtered one at every radius and retained weight.

The rejected alternative is announcing the agree flag into the **conditioning** register: the
natural block reference there is `ν_b = w_b·σ`, which costs `log₂(1/w_agree)` — a flat reference
in disguise, unfunded by the protocol's key-rate condition.

## Main definitions

* `bb84PELabelledLHLInput` — the PE-filtered, PE-labelled leftover-hashing input: the leaf's own
  input with the agree filter removed and everything else (the `bb84PEBlockIndex` label, the
  syndrome / error-verification kernel, the Alice-key coarsening) unchanged.
* `bb84PELabelledLHLFineInput` — the same input before the Alice-key coarsening, the common
  fine-register ancestor of the PE-filtered and agree-filtered inputs.

## Main results

* `bb84PELabelledLHLInput_eq_coarsen`, `bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep` — both
  leftover-hashing inputs are the Alice-key coarsening of the fine ancestor, the agree one after
  one extra classical filter.
* `bb84PEAnnounceAgreeLHLInput_weight_le_pELabelled` — the agree filter only removes weight.
* `bb84PEAnnounceAgreeLHLInput_smoothMinEntropy_ge_of_pELabelled` — the agree-axis transfer: a
  floor for the PE-filtered labelled input is a floor for the agree-filtered one.

## What must NOT be done

No hypothesis asserting that the error-correction scheme decodes correctly may be added: `decode`
is an arbitrary function of `ECScheme` and the security statements quantify over **every**
`ec`.  Nothing below uses one — the agree flag is carried, never bounded.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`),
`main.tex:919`, `\Cfull = C^{\nkey} \Cat^m C_E C_P` (the announced
error-verification and PE registers are transcript side information, not upstream filters);
Portmann-Renner 2021 (arXiv:2102.00021, `qkd.tex:801`, `\label{eq:qkd.sec}`, the accept-weight
prefactor of the secrecy definition); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## The agree axis at a general test-set size `m`

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol at a **general** test-set size `m`
(arXiv:2403.11851, `main.tex:909`, `:913`) and simulate at `m = 0.05·n` (`:970`,
`\label{sec:plots}`); at `m = ⌈n/2⌉` the declarations below specialise definitionally to
`bb84KeyRoundCountCanonical n`.

The block below is stated over the split-point-parametrised label register
`signalDim ^ (n − bb84KeyRoundCount n m)`, the general-`m` announced PE digit
`bb84PEBlockIndex` (`AgreeBlockLHLBridge.lean`) and the general-`m` agree input
`bb84PEAnnounceAgreeLHLInput` (same file).  It carries **no** constraint relating `m` to `n`:
the agree axis costs nothing at every `m`, and `m = 0` and `m ≥ n` are covered and degenerate
rather than excluded.  The announce kernel `bb84AnnounceKernel` is `m`-free — it reads Alice's key
string only — so it slides across the coarsening at every `m` by the same fibre-constancy argument.

References: Nahar et al. 2024 (`arXiv:2403.11851`) `main.tex:909`, `:913`, `:970`, App. B;
Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/

/-- **The PE-filtered, PE-labelled leftover-hashing input at a general test-set size `m`.**

The sifted τ-side post-measurement CQ state filtered
by the fail-closed local two-basis PE test alone, labelled by the general-`m` announced PE-outcome
block `bb84PEBlockIndex`, coarsened onto Alice's key bits, and tensored on the left by the
`(syndrome, EV seed, EV tag)` announce kernel.

The quantum register is
`2^leakEC · (|S_EV| · 2^ℓEV) · signalDim^(n − bb84KeyRoundCount n m) · (eveDim · dimR)` —
the *same* register as the general-`m` agree input `bb84PEAnnounceAgreeLHLInput`
(`AgreeBlockLHLBridge.lean`), the only difference between the two states being the classical
filter.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) `main.tex:909`, `:913`, App. B. -/
def bb84PELabelledLHLInput {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    CQState (KeyBitString n peSel)
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
  (bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
      (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
        (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
          τ).toCQState)).tensorLeftKernel
    (bb84AnnounceKernel ℓEV peSel ec)

/-- **The PE-filtered general-`m` labelled input before the Alice-key coarsening.**

The common fine-register ancestor of
`bb84PELabelledLHLInput` and `bb84PEAnnounceAgreeLHLInput`. -/
def bb84PELabelledLHLFineInput {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    CQState (Fin n → Fin signalDim)
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
  ((CQState.filterKeep (bb84SiftedLocalPETestPassed peSel xSel δ Q)
        (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
            τ).toCQState).tensorLeftKernel
      (fun ω => stdProj (signalDim ^ (n - bb84KeyRoundCount n m))
        (bb84PEBlockIndex (m := m) peSel ω))).tensorLeftKernel
    (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))

/-- The general-`m` PE-labelled leftover-hashing input is the Alice-key coarsening of its
    general-`m`
fine ancestor; general-`m` form of `bb84PELabelledLHLInput_eq_coarsen`, at the same fibre-constancy
argument (`CQState.coarsen_tensorLeftKernel_of_fiberConstant`).  The announce kernel is `m`-free. -/
theorem bb84PELabelledLHLInput_eq_coarsen {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ =
      CQState.coarsen (aliceKeyString peSel)
        (bb84PELabelledLHLFineInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ) := by
  rw [bb84PELabelledLHLInput, bb84PELabelledLHLFineInput, bb84AliceKeyAnnounceCQ,
    bb84AnnounceCoarsenCQ, bb84PostMeasurementCQSiftedLocalPEPassFilter_eq_filterKeep]
  exact (CQState.coarsen_tensorLeftKernel_of_fiberConstant (aliceKeyString peSel) _
    (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))
    (bb84AnnounceKernel ℓEV peSel ec) (fun _ => rfl)).symm

/-- The general-`m` agree-block leftover-hashing input is the Alice-key coarsening of the
**agree-filtered** general-`m` fine ancestor; general-`m` form of
`bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep`.

The agree-and-accept keep predicate factors as `PE test ∧ ¬differ` (`bb84SiftedAgreeAcceptKeep`),
so the agree conjunct is a second classical filter applied after the PE filter; it commutes with
both announce kernels at every `m`, because a dropped block stays dropped under `K ⊗ ·`. -/
theorem bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (ℓEV : ℕ) (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ =
      CQState.coarsen (aliceKeyString peSel)
        (CQState.filterKeep (fun ω => !bb84SiftedKeyStringsDiffer peSel ec ω)
          (bb84PELabelledLHLFineInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ)) := by
  rw [bb84PEAnnounceAgreeLHLInput, bb84AliceKeyAnnounceCQ, bb84AnnounceCoarsenCQ,
    bb84SiftedAgreeAcceptCQState]
  rw [show (CQState.filterKeep (bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q)
        (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ).toCQState) =
      CQState.filterKeep (fun ω => !bb84SiftedKeyStringsDiffer peSel ec ω)
        (CQState.filterKeep (bb84SiftedLocalPETestPassed peSel xSel δ Q)
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ).toCQState)
              from
    (CQState.filterKeep_filterKeep _ _ _).symm]
  rw [bb84PELabelledLHLFineInput]
  conv_lhs => rw [CQState.tensorLeftKernel_filterKeep]
  conv_rhs => rw [← CQState.tensorLeftKernel_filterKeep]
  exact (CQState.coarsen_tensorLeftKernel_of_fiberConstant (aliceKeyString peSel) _
    (fun ω => bb84AnnounceKernel ℓEV peSel ec (aliceKeyString peSel ω))
    (bb84AnnounceKernel ℓEV peSel ec) (fun _ => rfl)).symm

/-- **The agree filter only removes weight, at every `m`.**

Both leftover-hashing inputs
are the Alice-key coarsening of the same general-`m` fine ancestor — the agree one after one extra
classical filter — and a classical coarsening preserves total weight, so
`CQState.sum_filterKeep_stateMap_trace_le` applies on the fine register. -/
theorem bb84PEAnnounceAgreeLHLInput_weight_le_pELabelled {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (ℓEV : ℕ) (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    ∑ x : KeyBitString n peSel,
        ((bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
          τ).stateMap x).trace ≤
      ∑ x : KeyBitString n peSel,
        ((bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
          τ).stateMap x).trace := by
  rw [bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep,
    bb84PELabelledLHLInput_eq_coarsen,
    InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq,
    InfoTheory.QuantumLHL.CQState.sum_coarsen_stateMap_trace_eq]
  exact InfoTheory.SmoothMinEntropy.CQState.sum_filterKeep_stateMap_trace_le _ _

/-- **The agree axis costs nothing at every `m`: a floor for the PE-filtered general-`m` labelled
input is a floor for the agree-filtered one.**

Keeping the
agree flag as a second classical coordinate turns the non-fibre-constant filter into a
`CQState.filterKeep` at `Prod.snd` on the refined register, where its smooth-min-entropy charge is
zero; the generic statement is
`InfoTheory.SmoothMinEntropy.smoothMinEntropy_coarsen_filterKeep_ge`, independently of the
split point.

The floor is `ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ`; zero filtered witnesses have
infinite entropy, so no retained-weight or reference-positivity condition is needed. -/
theorem bb84PEAnnounceAgreeLHLInput_smoothMinEntropy_ge_of_pELabelled
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR))
    (ε : ℝ)
    (σ : SubDensityOp (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))))
    (k : ℝ)
    (hFloor : ENNReal.ofReal k ≤ smoothMinEntropy ε
      (bb84PELabelledLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ) σ) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε
      (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ) σ := by
  haveI hNZ : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  rw [bb84PEAnnounceAgreeLHLInput_eq_coarsen_filterKeep]
  rw [bb84PELabelledLHLInput_eq_coarsen] at hFloor
  refine le_trans hFloor
    (InfoTheory.SmoothMinEntropy.smoothMinEntropy_coarsen_filterKeep_ge ε
      (aliceKeyString peSel) (fun ω => !bb84SiftedKeyStringsDiffer peSel ec ω)
      (bb84PELabelledLHLFineInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ) σ)

end QKD.BB84.Engine

end -- noncomputable section
