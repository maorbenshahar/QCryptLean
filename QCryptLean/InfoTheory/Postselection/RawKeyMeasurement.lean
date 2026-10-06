import QCryptLean.InfoTheory.Postselection.Framework
import QCryptLean.InfoTheory.Postselection.MixtureFloorGlue
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference
import QCryptLean.Quantum.Operators.MatrixIntegral

/-!
# Raw-key measurement and mixture entropy

The measure-then-hash model records raw-key CQ states and their reference operators. Finite-
mixture smooth entropy floors pass through measurement and register extension, with logarithmic
extension penalties written additively.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels MeasureTheory
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The maximally-mixed register extension of a CQ state -/

/-- Tensor each outcome block of a CQ state with the normalized maximally mixed reference on a
    register of dimension `dR` — the explicit `V`-register extension witness underlying
    `CQState.tensorMaxMixed_exists` (Nahar et al. App. B register extension). -/
def CQState.tensorMaxMixed {X : Type*} [Fintype X] {dE : ℕ} (dR : ℕ) [NeZero dR]
    (ρ : CQState X dE) : CQState X (dE * dR) where
  stateMap x := (ρ.stateMap x).tensorMaxMixed dR
  weight_le_one := by
    simpa [SubDensityOp.tensorMaxMixed_trace] using ρ.weight_le_one

@[simp]
lemma CQState.tensorMaxMixed_stateMap_toOp {X : Type*} [Fintype X] {dE : ℕ} (dR : ℕ) [NeZero dR]
    (ρ : CQState X dE) (x : X) :
    ((ρ.tensorMaxMixed dR).stateMap x).toOp =
      (ρ.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)) := by
  simp [CQState.tensorMaxMixed]

/-- Tracing the `V`-register out of the max-mixed extension recovers the original block. -/
lemma CQState.tensorMaxMixed_partialTraceB {X : Type*} [Fintype X] {dE : ℕ} (dR : ℕ) [NeZero dR]
    (ρ : CQState X dE) (x : X) :
    Quantum.TensorProducts.partialTraceB ((ρ.tensorMaxMixed dR).stateMap x).toOp =
      (ρ.stateMap x).toOp := by
  rw [CQState.tensorMaxMixed_stateMap_toOp]
  exact partialTraceB_tensor_maxMixed_toOp _

/-! ## Entrywise Bochner integral of a CQ-state family -/

/-- The block-`x` trace of the entrywise Bochner integral of a CQ-state family equals the integral
    of the block-`x` traces. Trace is a continuous ℝ-linear functional, so it commutes with the
    Bochner integral (`ContinuousLinearMap.integral_comp_comm`). -/
lemma integral_block_trace_re {α : Type*} [MeasurableSpace α] {X : Type*} [Fintype X]
    {dE : ℕ} (f : α → CQState X dE) (μ : Measure α) [IsProbabilityMeasure μ]
    (h_int : ∀ x : X, MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ) (x : X) :
    (∫ a, ((f a).stateMap x).toOp ∂μ).trace.re = ∫ a, ((f a).stateMap x).trace ∂μ := by
  have h := (Complex.reCLM.comp
      (Matrix.traceLinearMap (Fin dE) ℝ ℂ).toContinuousLinearMap).integral_comp_comm (h_int x)
  exact h.symm

/-- The block-`x` trace of a CQ-state family is integrable when the family is. -/
lemma block_trace_integrable {α : Type*} [MeasurableSpace α] {X : Type*} [Fintype X]
    {dE : ℕ} (f : α → CQState X dE) (μ : Measure α)
    (h_int : ∀ x : X, MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ) (x : X) :
    MeasureTheory.Integrable (fun a => ((f a).stateMap x).trace) μ :=
  ((Matrix.traceLinearMap (Fin dE) ℝ ℂ).toContinuousLinearMap.integrable_comp (h_int x)).re

/-- **Entrywise Bochner integral of a CQ-state family.** Each outcome block is the matrix Bochner
    integral `∫ (f a).stateMap x ∂μ`; positive semidefiniteness (`matrix_setIntegral_posSemidef`)
    and the sub-normalization weight bound (the integral of the per-sample weights `≤ 1`) are
    preserved.

    This is Nahar et al.'s main.tex:483–:486 (unlabeled; the `\tau_{A^nB^n}` mixture inside
    `\label{thm:maintheorem}` :481–:491) mixture at the CQ-state level: `∫ f dμ` is the accepting
    raw-key mixture
    `τ⁽¹⁾` when `f σ = σ_{Zⁿ Cⁿ C_E Eⁿ ∧ Ω_acc}`. No `Classical.choose`: the operator is the
    explicit entrywise integral. -/
def cqStateIntegral {α : Type*} [MeasurableSpace α] {X : Type*} [Fintype X] {dE : ℕ}
    (f : α → CQState X dE) (μ : Measure α) [IsProbabilityMeasure μ]
    (h_int : ∀ x : X, MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ) :
    CQState X dE where
  stateMap x :=
    haveI hpsd : (∫ a, ((f a).stateMap x).toOp ∂μ).PosSemidef := by
      rw [← MeasureTheory.setIntegral_univ]
      refine matrix_setIntegral_posSemidef Set.univ (fun a => ((f a).stateMap x).toOp) ?_
        (fun a => posSemidefOp_implies_mathlib ((f a).stateMap x).toPosSemidefOp)
      rw [Measure.restrict_univ]; exact h_int x
    { toOp := ∫ a, ((f a).stateMap x).toOp ∂μ
      isHermitian := hpsd.isHermitian
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hpsd v
      trace_le_one := by
        rw [integral_block_trace_re f μ h_int x]
        calc ∫ a, ((f a).stateMap x).trace ∂μ
            ≤ ∫ _a, (1 : ℝ) ∂μ :=
              integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun a => (f a).classicalMarginal_nonneg x))
                (integrable_const 1)
                (Filter.Eventually.of_forall (fun a => (f a).classicalMarginal_le_one x))
          _ = 1 := by simp }
  weight_le_one := by
    change ∑ x : X, (∫ a, ((f a).stateMap x).toOp ∂μ).trace.re ≤ 1
    simp_rw [integral_block_trace_re f μ h_int]
    rw [← integral_finset_sum Finset.univ (fun x _ => block_trace_integrable f μ h_int x)]
    calc ∫ a, ∑ x : X, ((f a).stateMap x).trace ∂μ
        ≤ ∫ _a, (1 : ℝ) ∂μ :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun a => Finset.sum_nonneg (fun x _ => (f a).classicalMarginal_nonneg x)))
            (integrable_const 1)
            (Filter.Eventually.of_forall (fun a => (f a).weight_le_one))
      _ = 1 := by simp

@[simp]
lemma cqStateIntegral_stateMap_toOp {α : Type*} [MeasurableSpace α] {X : Type*} [Fintype X]
    {dE : ℕ} (f : α → CQState X dE) (μ : Measure α) [IsProbabilityMeasure μ]
    (h_int : ∀ x : X, MeasureTheory.Integrable (fun a => ((f a).stateMap x).toOp) μ) (x : X) :
    ((cqStateIntegral f μ h_int).stateMap x).toOp = ∫ a, ((f a).stateMap x).toOp ∂μ := rfl

end InfoTheory.SmoothMinEntropy

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

omit [NeZero n] in
/-- `dA^n · dB^n` (the `n`-round input register `AⁿBⁿ`) is nonzero. -/
private theorem neZero_powPairDim : NeZero (dA ^ n * dB ^ n) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero n (NeZero.ne dA)) (pow_ne_zero n (NeZero.ne dB))⟩

/-- The raw-key register dimension of a PMQKD protocol is nonzero (instance form of the
    structure field `rawKeyDim_neZero`, exposing `Nonempty (Fin P.rawKeyDim)` for
    `smoothMinEntropy` over the raw-key register). -/
instance instNeZeroRawKeyDim (P : PMQKDProtocol dA dB n) : NeZero P.rawKeyDim :=
  P.rawKeyDim_neZero

/-! ## Protocols with accept-supported differences -/

/-- Construct a protocol from CPTP real and ideal variants whose difference is fixed by the
idempotent accept map. This support condition proves agreement of the abort branches.
Instrument and hash semantics require the additional data in `MeasureThenHash`. -/
def PMQKDProtocol.ofAcceptSupported
    (keyDim cDim ceDim cpDim rawKeyDim : ℕ)
    [hkey : NeZero keyDim] [hann : NeZero (cDim * ceDim * cpDim)] [hraw : NeZero rawKeyDim]
    (l : ℕ)
    (variantReal variantIdeal :
      ℕ → (Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (keyDim * (cDim * ceDim * cpDim))))
    (hcptpReal : ∀ l',
      haveI := neZero_powPairDim (dA := dA) (dB := dB) (n := n)
      haveI : NeZero (keyDim * (cDim * ceDim * cpDim)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne keyDim) (NeZero.ne (cDim * ceDim * cpDim))⟩
      IsCPTP (⇑(variantReal l')))
    (hcptpIdeal : ∀ l',
      haveI := neZero_powPairDim (dA := dA) (dB := dB) (n := n)
      haveI : NeZero (keyDim * (cDim * ceDim * cpDim)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne keyDim) (NeZero.ne (cDim * ceDim * cpDim))⟩
      IsCPTP (⇑(variantIdeal l')))
    (acceptProj :
      Op (keyDim * (cDim * ceDim * cpDim)) →ₗ[ℂ] Op (keyDim * (cDim * ceDim * cpDim)))
    (hidem : acceptProj.comp acceptProj = acceptProj)
    (hAccept : ∀ l',
      acceptProj.comp (variantReal l' - variantIdeal l') = variantReal l' - variantIdeal l') :
    PMQKDProtocol dA dB n where
  keyDim := keyDim
  keyDim_neZero := hkey
  cDim := cDim
  ceDim := ceDim
  cpDim := cpDim
  annDim := cDim * ceDim * cpDim
  annDim_factored := rfl
  annDim_neZero := hann
  rawKeyDim := rawKeyDim
  rawKeyDim_neZero := hraw
  l := l
  variantReal := variantReal
  variantIdeal := variantIdeal
  variantReal_isCPTP := hcptpReal
  variantIdeal_isCPTP := hcptpIdeal
  acceptProj := acceptProj
  acceptProj_idem := hidem
  abortAgreement := fun l' => by
    rw [LinearMap.sub_comp, LinearMap.id_comp, hAccept l']
    exact sub_self _

/-! ## `NeZero` of the de Finetti prefactor `g = C(n+x-1, x-1)`, `x = dA² dB²` -/

/-- `x = dA² dB²` is nonzero. -/
instance neZero_sqPairDim : NeZero (dA ^ 2 * dB ^ 2) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero 2 (NeZero.ne dA)) (pow_ne_zero 2 (NeZero.ne dB))⟩

/-- The de Finetti prefactor `g_{n,x} = C(n+x-1, x-1)` with `x = dA² dB²` is nonzero
    (`dV := g` exactly, so the B17 penalty is `2 log₂ g`). -/
instance neZero_deFinettiPrefactor : NeZero (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n) :=
  ⟨(deFinettiPrefactor_pos (dA ^ 2 * dB ^ 2) n).ne'⟩

/-! ## The raw-key measurement layer -/

/-- Accepted IID raw-key states and a common positive-definite entropy reference for a protocol.

`rawKeyCQ` specifies the accepted classical key and conditioning register for each IID component.
`sigmaE` is explicit data shared by every component. This common-reference choice is a
specialization of the optimized conditional-entropy argument in Nahar et al., arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` (main.tex:1380–1387) and `lemma:infsmoothedmin` (1426–1446).
The `MeasureThenHash` structure additionally identifies these states with a CP instrument and
specifies the protocol's actual privacy-amplification hash. -/
structure RawKeyMeasurement (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n] where
  /-- The underlying PMQKD protocol. -/
  toProtocol : PMQKDProtocol dA dB n
  /-- Dimension of the conditioning register `Cⁿ C_E Eⁿ`. -/
  condDim : ℕ
  /-- The conditioning register is nonzero. -/
  condDim_neZero : NeZero condDim
  /-- Per-component `Ω_acc`-filtered raw-key CQ channel `σ ↦ σ_{Zⁿ Cⁿ C_E Eⁿ ∧ Ω_acc}`
      (Nahar et al. line 2086): the classical raw key `Zⁿ` with quantum side `Cⁿ C_E Eⁿ`,
      conditioned on
      accept, as a function of the single-round de Finetti component `σ_AB`. -/
  rawKeyCQ : DensityOp (dA * dB) → CQState (Fin toProtocol.rawKeyDim) condDim
  /-- **The common `Eⁿ`-level reference** (`\label{eq:boundingsmoothedmin}`
  (main.tex:1379–:1387)/(B17) all use a
      single common `PosDef` reference); supplied as explicit witness data, e.g. `maxMixed condDim`
      or, for the BB84 instantiation, a CKR de Finetti calibration reference. -/
  sigmaE : SubDensityOp condDim
  /-- The common reference `σE` is positive definite. -/
  sigmaE_posDef : sigmaE.toOp.PosDef

attribute [instance] RawKeyMeasurement.condDim_neZero

namespace RawKeyMeasurement

variable (M : RawKeyMeasurement dA dB n)

/-- Integrability of the raw-key CQ channel against a de Finetti measure `μ` (the `h_int` analytic
    side-condition of the mixture-floor glue). -/
@[reducible] def Integrable (μ : DensityMeasure (dA * dB)) : Prop :=
  ∀ x : Fin M.toProtocol.rawKeyDim,
    MeasureTheory.Integrable (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp)
      μ.measure

/-- The constant per-component reference `ref σ = σE`. -/
def refCommon : DensityOp (dA * dB) → SubDensityOp M.condDim :=
  fun _ => M.sigmaE

/-- The register-extended conditioning dimension `condDim · g` (matches `referenceSecrecy`). -/
def mixCondDim : ℕ :=
  M.condDim * deFinettiPrefactor (dA ^ 2 * dB ^ 2) n

/-- The register-extended conditioning dimension is nonzero. -/
instance instNeZeroMixCondDim : NeZero M.mixCondDim :=
  ⟨Nat.mul_ne_zero M.condDim_neZero.out (deFinettiPrefactor_pos (dA ^ 2 * dB ^ 2) n).ne'⟩

/-- **The per-component accept probability** `Pr(Ω_acc)_σ = ∑_z tr(rawKeyCQ σ z)` — the total
    weight of the accept-filtered raw-key CQ state (Nahar et al. `\label{eq:condS}`
    (main.tex:457–:459)). -/
def pAcc (σ : DensityOp (dA * dB)) : ℝ :=
  ∑ x : Fin M.toProtocol.rawKeyDim, ((M.rawKeyCQ σ).stateMap x).trace

/-- **The `Eⁿ`-level accepting mixture** `mixCQ_En = ∫ rawKeyCQ dμ`
    (Nahar et al. `τ⁽¹⁾_{Zⁿ Cⁿ C_E Eⁿ ∧ Ω_acc}`), the explicit entrywise Bochner integral. -/
def mixCQ_En (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ) :
    CQState (Fin M.toProtocol.rawKeyDim) M.condDim :=
  haveI := μ.isProbability
  cqStateIntegral M.rawKeyCQ μ.measure h_int

/-- Adjoin a maximally mixed register of dimension `deFinettiPrefactor (dA ^ 2 * dB ^ 2) n`
to the accepting mixture. This supplies a concrete extension with marginal `mixCQ_En`.
The instrument factorization can instead use another extension with the same marginal. -/
def mixCQ (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ) :
    CQState (Fin M.toProtocol.rawKeyDim) M.mixCondDim :=
  (M.mixCQ_En μ h_int).tensorMaxMixed (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)

/-- **The register-extended common reference** `mixRef = σE ⊗ I_g/g`
    (Nahar et al. App. B, `[47, Eq. (8)]`). -/
def mixRef : SubDensityOp M.mixCondDim :=
  M.sigmaE.tensorMaxMixed (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)

/-! ## Basic API of the derived objects -/

/-- **`hf_lin` — `mixCQ_En` is entrywise `∫ rawKeyCQ dμ`.** The `(i,j)` entry of the mixture block
    is the Bochner integral of the per-component entries (`matrix_integral_entry`). -/
theorem mixCQ_En_hf_lin (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (x : Fin M.toProtocol.rawKeyDim) (i j : Fin M.condDim) :
    ((M.mixCQ_En μ h_int).stateMap x).toOp i j =
      ∫ σ : DensityOp (dA * dB), ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure := by
  haveI := μ.isProbability
  have hstate : ((M.mixCQ_En μ h_int).stateMap x).toOp =
      ∫ σ : DensityOp (dA * dB), ((M.rawKeyCQ σ).stateMap x).toOp ∂μ.measure := rfl
  rw [hstate]
  exact matrix_integral_entry (fun σ => ((M.rawKeyCQ σ).stateMap x).toOp) (h_int x) i j

/-- **`hblocks` — tracing out `V` recovers `mixCQ_En`** (Nahar et al. B17 register-marginal
identity). -/
theorem mixCQ_hblocks (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (x : Fin M.toProtocol.rawKeyDim) :
    Quantum.TensorProducts.partialTraceB ((M.mixCQ μ h_int).stateMap x).toOp =
      ((M.mixCQ_En μ h_int).stateMap x).toOp :=
  CQState.tensorMaxMixed_partialTraceB _ (M.mixCQ_En μ h_int) x

/-- **`mixRef` is positive definite** (`σE` PosDef ⊗ maximally mixed). -/
theorem mixRef_posDef : M.mixRef.toOp.PosDef :=
  SubDensityOp.tensor_posDef M.sigmaE
    (DensityOp.toSubDensityOp (DensityOp.maxMixed (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)))
    M.sigmaE_posDef maxMixed_toSubDensityOp_posDef

/-- **The mixture weight equals `∫ pAcc dμ`** (Nahar et al. B14 accept mass). This is an *equality*
only:
    the accept-mass lower bound `2(ε̄+√(2ε_AT)) < weight` is the load-bearing non-trivial-accept
    guard `h_subNorm` and stays an explicit hypothesis downstream —
    it is *not* proved here, since an unconditional weight lower bound is a false claim in
    general. -/
theorem mixCQ_En_weight_eq (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ) :
    ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace =
      ∫ σ : DensityOp (dA * dB), M.pAcc σ ∂μ.measure := by
  haveI := μ.isProbability
  have hblock : ∀ x : Fin M.toProtocol.rawKeyDim,
      ((M.mixCQ_En μ h_int).stateMap x).trace =
        ∫ σ : DensityOp (dA * dB), ((M.rawKeyCQ σ).stateMap x).trace ∂μ.measure := fun x =>
    integral_block_trace_re M.rawKeyCQ μ.measure h_int x
  simp_rw [hblock, RawKeyMeasurement.pAcc]
  exact (integral_finset_sum Finset.univ
    (fun x _ => block_trace_integrable M.rawKeyCQ μ.measure h_int x)).symm

/-! ## The register-extended mixture floor (Nahar et al. App. B, `\label{eq:boundingsmoothedmin}`
(main.tex:1379–:1387)/(B17)) -/

/-- An extended floor on a closed set of accepted components passes to every extension of the
raw-key mixture, with an additive dimension penalty preserving infinite floors. The bad-branch
trace bound supplies `0 ≤ ε`. -/
theorem registerExtendedMixtureFloor_le_add
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (dV : ℕ) (hdV : NeZero dV)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet : Set (DensityOp (dA * dB))) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp (dA * dB))) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (K : ENNReal) (εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ ε)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ P →
      K ≤ smoothMinEntropy εBar (M.rawKeyCQ σ) M.sigmaE)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) (M.condDim * dV))
    (hblocks : ∀ x : Fin M.toProtocol.rawKeyDim,
      Quantum.TensorProducts.partialTraceB (ρ_EnV.stateMap x).toOp =
        ((M.mixCQ_En μ h_int).stateMap x).toOp) :
    haveI := hdV
    haveI : NeZero (M.condDim * dV) :=
      ⟨Nat.mul_ne_zero M.condDim_neZero.out hdV.out⟩
    K ≤ smoothMinEntropy (εBar + Real.sqrt (2 * ε)) ρ_EnV
      (M.sigmaE.tensorMaxMixed dV) + ENNReal.ofReal (2 * Real.logb 2 (dV : ℝ)) := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  exact smoothMinEntropy_registerExtended_le_add_of_deFinetti_postFilter_floor
    dV μ (M.mixCQ_En μ h_int) ρ_EnV M.rawKeyCQ M.sigmaE hblocks
    (M.mixCQ_En_hf_lin μ h_int) hcont goodSet hClosed P hP_closed hP_ae K εBar ε
    hεBar_nonneg h_badBranch_traceNorm hf_smoothFloor

/-- The completed signed component floor on a closed accepting set, after the register penalty,
bounds the extended smooth entropy of the accepted mixture. The bad-branch trace bound supplies
`0 ≤ ε`, and no positive accepted-weight premise is needed. -/
theorem registerExtendedMixtureFloor
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (dV : ℕ) (hdV : NeZero dV)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet : Set (DensityOp (dA * dB))) (hClosed : IsClosed goodSet)
    (P : Set (DensityOp (dA * dB))) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ ε)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ P →
      ENNReal.ofReal k ≤ smoothMinEntropy εBar (M.rawKeyCQ σ) M.sigmaE)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) (M.condDim * dV))
    (hblocks : ∀ x : Fin M.toProtocol.rawKeyDim,
      Quantum.TensorProducts.partialTraceB (ρ_EnV.stateMap x).toOp =
        ((M.mixCQ_En μ h_int).stateMap x).toOp) :
    haveI := hdV
    haveI : NeZero (M.condDim * dV) :=
      ⟨Nat.mul_ne_zero M.condDim_neZero.out hdV.out⟩
    ENNReal.ofReal (k - 2 * Real.logb 2 (dV : ℝ)) ≤
      smoothMinEntropy (εBar + Real.sqrt (2 * ε)) ρ_EnV (M.sigmaE.tensorMaxMixed dV) := by
  have h := M.registerExtendedMixtureFloor_le_add μ h_int dV hdV hcont goodSet hClosed
    P hP_closed hP_ae (ENNReal.ofReal k) εBar ε hεBar_nonneg h_badBranch_traceNorm
    hf_smoothFloor ρ_EnV hblocks
  have hp : 0 ≤ 2 * Real.logb 2 (dV : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hdV.pos)
  rw [ENNReal.ofReal_sub k hp]
  exact tsub_le_iff_right.mpr h


/-- The raw-key mixture inherits the signed floor `k - 2 * logb 2 dV` at radius `εBar + sqrt (2
* ε)` after extension by a register of dimension `dV`. -/
theorem registerExtendedMixtureFloorReal
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (dV : ℕ) (hdV : NeZero dV)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet : Set (DensityOp (dA * dB))) (hMeas : MeasurableSet goodSet)
    (hClosed : IsClosed goodSet)
    (P : Set (DensityOp (dA * dB))) (hP_closed : IsClosed P)
    (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (k εBar ε : ℝ) (hεBar_nonneg : 0 ≤ εBar) (hε_nonneg : 0 ≤ ε)
    (h_subNorm : 2 * (εBar + Real.sqrt (2 * ε)) <
      ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re
        ≤ ε)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ P →
      k ≤ smoothMinEntropyReal εBar (M.rawKeyCQ σ) M.sigmaE)
    (ρ_EnV : CQState (Fin M.toProtocol.rawKeyDim) (M.condDim * dV))
    (hblocks : ∀ x : Fin M.toProtocol.rawKeyDim,
      Quantum.TensorProducts.partialTraceB ((ρ_EnV).stateMap x).toOp =
        ((M.mixCQ_En μ h_int).stateMap x).toOp) :
    haveI := hdV
    haveI : NeZero (M.condDim * dV) :=
      ⟨Nat.mul_ne_zero M.condDim_neZero.out hdV.out⟩
    k - 2 * Real.logb 2 (dV : ℝ)
      ≤ smoothMinEntropyReal (εBar + Real.sqrt (2 * ε)) ρ_EnV (M.sigmaE.tensorMaxMixed dV) := by
  have hw := (M.mixCQ_En μ h_int).weight_le_one
  have hsum_lt_one : εBar + Real.sqrt (2 * ε) < 1 := by linarith
  have hε_lt_half : ε < 1 / 2 := by
    have hs : Real.sqrt (2 * ε) < 1 / 2 := by linarith
    have hs2 := Real.lt_sq_of_sqrt_lt hs
    nlinarith
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI := M.condDim_neZero
  haveI := M.toProtocol.rawKeyDim_neZero
  haveI : Nonempty (Fin M.toProtocol.rawKeyDim) := ⟨(0 : Fin M.toProtocol.rawKeyDim)⟩
  exact smoothMinEntropyReal_registerExtended_ge_of_deFinetti_postFilter_finiteSmoothFloor
    dV μ (M.mixCQ_En μ h_int) ρ_EnV
    M.rawKeyCQ M.sigmaE M.sigmaE_posDef hblocks h_int (M.mixCQ_En_hf_lin μ h_int)
    hcont goodSet hMeas hClosed P hP_closed hP_ae k εBar ε hεBar_nonneg hε_nonneg hε_lt_half
    hsum_lt_one h_subNorm h_badBranch_traceNorm hf_smoothFloor

end RawKeyMeasurement

end InfoTheory.Postselection

end
