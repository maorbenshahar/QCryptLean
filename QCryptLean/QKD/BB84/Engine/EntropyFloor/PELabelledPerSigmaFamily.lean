import QCryptLean.QKD.BB84.Engine.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.TensorLeftKernelSpectator

/-!
# The PE-labelled component family and mixture

The public PE outcome is a normalised projector determined by the outcome string. Attaching it
to the conditioning register preserves total weight and transports the component family and
its mixture's Haar integral entry by entry. Continuity, integrability and the accepted-weight
identity supply the own-marginal coarsening assembler. The good set depends only on phase rate;
light components remain in it and use zero smoothing witnesses.

The label dimension is `signalDim ^ (n - bb84KeyRoundCount n m)` at general test size `m`.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin` and
`lemma:infsmoothedmin`.
-/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PerSigmaFamily.lean` / `AcceptSplit.lean`, this uses the Frobenius norm on matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

private local instance {n : ℕ} : ContinuousENorm (Op n) :=
  SeminormedAddGroup.toContinuousENorm

/-! ## 1. The PE-labelled family and mixture -/

/-- **The PE-label kernel at a general test-set size `m`.**  The announced PE-outcome block of the
outcome string `ω` — its sorted PE-round restriction `(bb84PartEquiv peSel ω).2` read as a digit
string — as a normalised computational-basis projector on
`Fin (signalDim ^ (n − bb84KeyRoundCount n m))`.

At `m = ⌈n/2⌉` the index is `bb84PEBlockIndex`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
def bb84PELabelKernel {n m : ℕ} (peSel : Fin n → Bool) (ω : Fin n → Fin signalDim) :
    SubDensityOp (signalDim ^ (n - bb84KeyRoundCount n m)) :=
  stdProj (signalDim ^ (n - bb84KeyRoundCount n m))
    (finFunctionFinEquiv ((bb84PartEquiv (m := m) peSel ω).2))

@[simp] lemma bb84PELabelKernel_trace {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    (bb84PELabelKernel (m := m) peSel ω).trace = 1 :=
  stdProj_trace _ _

/-- The matrix trace of a general-`m` PE-label block is `1`; the form the bad-branch transport
reads. -/
lemma bb84PELabelKernel_matrix_trace {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    Matrix.trace (bb84PELabelKernel (m := m) peSel ω).toOp = 1 := by
  refine Complex.ext ?_ ?_
  · change (bb84PELabelKernel (m := m) peSel ω).trace = _
    rw [bb84PELabelKernel_trace]; rfl
  · rw [(bb84PELabelKernel (m := m) peSel ω).trace_im_eq_zero]; rfl

/-- **The PE-labelled `Eⁿ`-marginal de Finetti reference at a general test-set size `m`.**

`bb84EnVRhoEtilde` (`PerSigmaFamily.lean:61`) with the announced PE-outcome block of the `m`
sorted test rounds tensored into the high digits of the conditioning register. -/
def bb84PELabelledEnVRhoEtilde {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    CQState (Fin n → Fin signalDim)
      (signalDim ^ (n - bb84KeyRoundCount n m) *
        (eveDim * (signalDim ^ n))) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  (bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).tensorLeftKernel
      (bb84PELabelKernel (m := m) peSel)

/-- **The PE-labelled paired-Haar per-σ family at a general test-set size `m`.**

`bb84PairedHaarPerSigmaFamily` (`AcceptSplit.lean:72`) with the announced PE-outcome block of the
`m` sorted test rounds tensored into the high digits of the conditioning register.  The block
depends on the outcome string `ω` only, never on the de Finetti component `ψ`. -/
def bb84PELabelledPairedHaarPerSigmaFamily {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    CQState (Fin n → Fin signalDim)
      (signalDim ^ (n - bb84KeyRoundCount n m) *
        (eveDim * (signalDim ^ n))) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  (bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).tensorLeftKernel
    (bb84PELabelKernel (m := m) peSel)

/-! ## 2. The labelled twins of the assembler's analytic data -/

/-- **`h_int` (labelled, general `m`).**  Each register block of the general-`m` PE-labelled
family is Bochner-integrable against the paired Haar measure.

Labelled form of `bb84_f_blocks_integrable` (`AcceptSplit.lean:90`), which mentions no split
point: the label block is a fixed operator, so each entry of the labelled block is a constant
multiple of an entry of the unlabelled one. -/
theorem bb84_peLabelledF_blocks_integrable {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∀ x : Fin n → Fin signalDim,
      MeasureTheory.Integrable
        (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
            eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
        (deFinetti_haarMeasure (signalDim * signalDim)).measure := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x
  exact tensorLeftKernel_blocks_integrable
    (fun ψ => bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ)
    (bb84PELabelKernel (m := m) peSel) x (bb84_f_blocks_integrable eveDim pre hpre peSel xSel Q δ x)

/-- **`hf_lin` (labelled, general `m`) — the Nahar et al. B13 integral split for the general-`m`
PE-labelled family.**

Each register-block entry of the general-`m` PE-labelled `Eⁿ`-marginal de Finetti reference is
the Bochner integral over the paired Haar measure of the corresponding entry of the general-`m`
PE-labelled per-σ family.

Labelled form of `bb84_rhoEtilde_eq_haar_integral_blocks` (`PerSigmaFamily.lean:93`), which
mentions no split point.  The label block is a function of the outcome string alone, so
`X ↦ (label block) ⊗ X` is a fixed linear map: each entry of the labelled block is the same fixed
scalar times the corresponding entry of the unlabelled block, and that scalar comes out of the
integral.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B,
`main.tex:1380`, `\label{eq:boundingsmoothedmin}`;
`main.tex:909`, `:913` (the general-`m` protocol). -/
theorem bb84_peLabelledRhoEtilde_eq_haar_integral_blocks {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ (x : Fin n → Fin signalDim)
      (i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
        (eveDim * (signalDim ^ n)))),
      ((bb84PELabelledEnVRhoEtilde (m := m) eveDim pre hpre peSel xSel Q δ).stateMap x).toOp i j =
        ∫ ψ : DensityOp (signalDim * signalDim),
          ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
            eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
          ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x i j
  exact tensorLeftKernel_blocks_integral_eq
    (bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ)
    (fun ψ => bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ)
    (bb84PELabelKernel (m := m) peSel)
    (bb84_rhoEtilde_eq_haar_integral_blocks eveDim pre hpre peSel xSel Q δ) x i j

/-- **`hcont` (labelled, general `m`).**  Each register block of the general-`m` PE-labelled
family is continuous in the de Finetti component.

Labelled form of `bb84PairedHaarPerSigmaFamily_blocks_continuous` (`AcceptSplit.lean:198`),
which mentions no split point. -/
theorem bb84PELabelledPairedHaarPerSigmaFamily_blocks_continuous {n m : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∀ x : Fin n → Fin signalDim,
      Continuous
        (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
            eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp) := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x
  exact tensorLeftKernel_blocks_continuous
    (fun ψ => bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ)
    (bb84PELabelKernel (m := m) peSel) x
    (bb84PairedHaarPerSigmaFamily_blocks_continuous eveDim pre hpre peSel xSel Q δ x)

/-- The accept-weight trace-out identity for the general-`m` PE-labelled mixture.

The total accepted weight of the general-`m` PE-labelled `Eⁿ`-marginal reference equals the
accepted weight of the physical accept state on the `ckrMixtureMeasure` de Finetti source: the
label blocks are normalised, so the label costs no weight, and the unlabelled identity
`bb84_rhoEtilde_acceptWeight_eq_ckrMixture` (`PerSigmaFamily.lean`, which mentions no split
point) closes it. -/
theorem bb84_peLabelledRhoEtilde_acceptWeight_eq_ckrMixture {n m : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x : Fin n → Fin signalDim,
        ((bb84PELabelledEnVRhoEtilde (m := m) eveDim pre hpre peSel xSel Q δ).stateMap x).trace =
      ∑ ω : Fin n → Fin signalDim,
        ((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel
            (Quantum.Channels.ckrMixtureMeasure signalDim) Q δ).stateMap ω).trace := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  rw [show ∑ x : Fin n → Fin signalDim,
        ((bb84PELabelledEnVRhoEtilde (m := m) eveDim pre hpre peSel xSel Q δ).stateMap x).trace =
      ∑ x : Fin n → Fin signalDim,
        ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).trace from
    CQState.tensorLeftKernel_weight _ _ (bb84PELabelKernel_trace (m := m) peSel)]
  exact bb84_rhoEtilde_acceptWeight_eq_ckrMixture eveDim pre hpre peSel xSel Q δ

end QKD.BB84.Engine

end -- noncomputable section
