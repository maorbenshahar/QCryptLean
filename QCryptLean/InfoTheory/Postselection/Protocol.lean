import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# QKD postselection — PMQKD protocols and fixed-marginal secrecy

Faithful transcription of the generic prepare-and-measure QKD (PMQKD) framework of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851), Section III A.

## the generic PMQKD object (`InfoTheory.Postselection.PMQKDProtocol`)

Nahar et al. considers a QKD protocol map
`E_QKD^{(l)} ∈ C(AⁿBⁿ, K_A C̃_e)` (Section III A, lines 407–428), where

- `AⁿBⁿ` is the `n`-round joint input register (single-round dims `d_A`, `d_B`);
- `K_A` is Alice's key register (holds an `l`-bit key on accept, `⊥` on abort);
- `C̃_e = C · C_E · C_P` is the classical announcement register: round-by-round
  announcements `Cⁿ`, error-correction/verification `C_E`, and the PA hash seed `C_P`
  (line 501);
- `E_QKD^{(l),ideal}` replaces the key by a perfect key on accept and agrees with the
  real map on abort (lines 418–428);
- the accept event `Ω_acc` is an idempotent output projection (line 510);
- the raw key `Zⁿ` and the pre-PA registers `Cⁿ, C_E, Eⁿ` are the systems just before
  privacy amplification (lines 491–502).

This generalises a dim-hardwired BB84 protocol scheme to abstract dimensions and abstract
announcement structure. Eve's register `Eⁿ` is not
a field of the structure: it enters only through the `⊗ id_{Eⁿ}` and the input state in
Definition 4 below, exactly as in Nahar et al., where `E_QKD` is a fixed map on `AⁿBⁿ`.

## fixed-marginal secrecy (`InfoTheory.Postselection.IsFixedMarginalSecret`)

Nahar et al. Definition 4 (lines 431–439):
`E_QKD` is `ε_sec`-secret with fixed marginal `σA` iff
  `½ ‖((E - E_ideal) ⊗ id_{Eⁿ}) ρ_{AⁿBⁿEⁿ}‖₁ ≤ ε_sec`
for all `ρ_{AⁿBⁿEⁿ}` with `Tr_{BⁿEⁿ}(ρ) = (σA)^{⊗n}`.

**Reconciliation (i): the ½.** The bound carries an explicit `½`. The library's
`diamondNorm` and `ckrTensorTraceNorm` are bare `‖·‖₁` (no `½`); reusing either as
Definition 4 would double Nahar et al.'s bound. This file bakes the `½` directly into
`IsFixedMarginalSecret` and does *not* reuse those wrappers. It is also weaker (hence
different) than `IsProtocolSecure = diamondNorm Δ ≤ ε`: Definition 4 restricts the
input to the fixed-marginal set, whereas the diamond norm ranges over all inputs.

## Non-vacuity
- `PMQKDProtocol.trivial` : an explicit protocol with identical real and ideal channels.
- `exists_fixedMarginal_input` : the fixed-marginal input set is non-empty, so the
  `∀ρ` in Definition 4 is not vacuously satisfied.
- `not_isFixedMarginalSecret_of_input_violation` : Definition 4 has teeth — a difference
  map that is large on a legitimate fixed-marginal input is *not* `ε_sec`-secret for
  small `ε_sec`. A trivial/degenerate channel therefore fails Definition 4.
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- Positivity of `dA ^ n * dB ^ n` from positivity of `dA, dB`. -/
private theorem neZero_inputDim (dA dB n : ℕ) [NeZero dA] [NeZero dB] :
    NeZero (dA ^ n * dB ^ n) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n))⟩

/-! ## generic PMQKD protocol object -/

/-- **Generic PMQKD protocol object** (Nahar et al. 2024, arXiv:2403.11851, Section III A).

    A protocol map `E_QKD^{(l)} ∈ C(AⁿBⁿ, K_A C̃_e)` on abstract single-round dimensions
    `dA` (Alice) and `dB` (Bob), together with its ideal counterpart, the accept event,
    the pre-PA register dimensions, and the hash-length family `l' ↦ E^{(l')}`.

    The announcement register `C̃_e` factors as `C · C_E · C_P`; its total dimension is
    `annDim = cDim * ceDim * cpDim`. The full output register is `K_A ⊗ C̃_e`, of dimension
    `keyDim * annDim`. -/
structure PMQKDProtocol (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n] where
  /-- Dimension of Alice's key register `K_A` (`2^l` on accept, plus the `⊥` slot). -/
  keyDim : ℕ
  /-- `K_A` is nonzero. -/
  keyDim_neZero : NeZero keyDim
  /-- Dimension of the round-by-round announcement register `Cⁿ`. -/
  cDim : ℕ
  /-- Dimension of the error-correction/verification register `C_E`. -/
  ceDim : ℕ
  /-- Dimension of the privacy-amplification hash-seed register `C_P`. -/
  cpDim : ℕ
  /-- Total announcement dimension `C̃_e`. -/
  annDim : ℕ
  /-- `C̃_e = C · C_E · C_P`. -/
  annDim_factored : annDim = cDim * ceDim * cpDim
  /-- `C̃_e` is nonzero. -/
  annDim_neZero : NeZero annDim
  /-- Dimension of the raw-key register `Zⁿ` (Alice's PA input string), Nahar et al. line 492. -/
  rawKeyDim : ℕ
  /-- `Zⁿ` is nonzero. -/
  rawKeyDim_neZero : NeZero rawKeyDim
  /-- Hash length `l` produced on accept (Nahar et al. line 408). -/
  l : ℕ
  /-- The hash-length variant family: `variantReal l'` is the protocol map that hashes to
      length `l'` on accept (Nahar et al. Theorem 3 / Corollary 3.1, `E_QKD^{(l')}`). Modelled on a
      shared output register `K_A C̃_e` so the family lives in one type. -/
  variantReal : ℕ → (Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (keyDim * annDim))
  /-- The ideal variant family (`E_QKD^{(l'),ideal}`). -/
  variantIdeal : ℕ → (Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (keyDim * annDim))
  /-- Every real variant is a channel (CPTP). -/
  variantReal_isCPTP : ∀ l',
    haveI := neZero_inputDim dA dB n
    haveI := keyDim_neZero
    haveI := annDim_neZero
    haveI : NeZero (keyDim * annDim) := ⟨Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos keyDim_neZero.pos annDim_neZero.pos)⟩
    IsCPTP (⇑(variantReal l'))
  /-- Every ideal variant is a channel (CPTP). -/
  variantIdeal_isCPTP : ∀ l',
    haveI := neZero_inputDim dA dB n
    haveI : NeZero (keyDim * annDim) := ⟨Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos keyDim_neZero.pos annDim_neZero.pos)⟩
    IsCPTP (⇑(variantIdeal l'))
  /-- The accept event `Ω_acc`, an idempotent output projection superoperator (Nahar et al. line
  510). -/
  acceptProj : Op (keyDim * annDim) →ₗ[ℂ] Op (keyDim * annDim)
  /-- `Ω_acc` is idempotent. -/
  acceptProj_idem : acceptProj.comp acceptProj = acceptProj
  /-- Real and ideal agree on the abort branch, for every hash length `l'` (Nahar et al. lines
  418–428):
      applying the abort projection `id - Ω_acc` to `E^{(l')} - E^{(l'),ideal}` yields `0`. -/
  abortAgreement : ∀ l',
    (LinearMap.id - acceptProj).comp (variantReal l' - variantIdeal l') = 0

namespace PMQKDProtocol

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- The base real map `E_QKD^{(l)}` at the protocol's own hash length. -/
def realMap (P : PMQKDProtocol dA dB n) :
    Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (P.keyDim * P.annDim) :=
  P.variantReal P.l

/-- The base ideal map `E_QKD^{(l),ideal}` at the protocol's own hash length. -/
def idealMap (P : PMQKDProtocol dA dB n) :
    Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (P.keyDim * P.annDim) :=
  P.variantIdeal P.l

/-- The difference map `Δ^{(l')} = E^{(l')} - E^{(l'),ideal}` for a given hash length `l'`.
    This is the object whose fixed-marginal secrecy (Definition 4) constrains, and whose
    permutation-invariance drives Corollary 3.1. -/
def differenceMap (P : PMQKDProtocol dA dB n) (l' : ℕ) :
    Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (P.keyDim * P.annDim) :=
  P.variantReal l' - P.variantIdeal l'

/-- Real and ideal variants agree outside the accepted branch. -/
lemma acceptProj_comp_differenceMap (P : PMQKDProtocol dA dB n) (l' : ℕ) :
    P.acceptProj.comp (P.differenceMap l') = P.differenceMap l' := by
  have h := P.abortAgreement l'
  rw [LinearMap.sub_comp, LinearMap.id_comp] at h
  exact (sub_eq_zero.mp h).symm

end PMQKDProtocol

/-- An explicit PMQKD protocol with identical real and ideal channels on
    single qubits: identity real and ideal maps, the never-accept event `Ω_acc = 0`.
    This witnesses that `PMQKDProtocol` is a non-vacuous structure type. The sharp,
    *security*-flavoured non-vacuity (that a trivial channel fails Definition 4) is
    `not_isFixedMarginalSecret_of_input_violation` below. -/
def PMQKDProtocol.trivial : PMQKDProtocol 2 2 1 where
  keyDim := 2
  keyDim_neZero := ⟨by norm_num⟩
  cDim := 2
  ceDim := 1
  cpDim := 1
  annDim := 2
  annDim_factored := by norm_num
  annDim_neZero := ⟨by norm_num⟩
  rawKeyDim := 2
  rawKeyDim_neZero := ⟨by norm_num⟩
  l := 0
  variantReal := fun _ => LinearMap.id
  variantIdeal := fun _ => LinearMap.id
  variantReal_isCPTP := fun _ => by simpa using id_is_cptp (2 * 2)
  variantIdeal_isCPTP := fun _ => by simpa using id_is_cptp (2 * 2)
  acceptProj := 0
  acceptProj_idem := by simp
  abortAgreement := fun _ => by simp

/-! ## fixed-marginal secrecy (Nahar et al. Definition 4) -/

/-- **Nahar et al. Definition 4** (arXiv:2403.11851, lines 431–439). A difference map
    `Δ = E - E_ideal` between the real and ideal PMQKD maps is `ε_sec`-secret with
    fixed marginal `σA` iff

      `½ ‖(Δ ⊗ id_{Eⁿ}) ρ_{AⁿBⁿEⁿ}‖₁ ≤ ε_sec`

    for every `ρ_{AⁿBⁿEⁿ}` (over every Eve dimension) whose Alice marginal is
    `Tr_{BⁿEⁿ}(ρ) = (σA)^{⊗n}`.

    The `½` is baked in (reconciliation (i)); the library's `ckrTensorTraceNorm` /
    `diamondNorm` are the bare `‖·‖₁` and are deliberately *not* reused here.

    Input registers are grouped `AⁿBⁿEⁿ = (dA^n * dB^n) * eveDim`, so tracing out
    `BⁿEⁿ` is `partialTraceB (partialTraceB ρ)` (trace out `Eⁿ`, then `Bⁿ`), and
    `Δ ⊗ id_{Eⁿ}` is `mapTensorId Δ` with ancilla `eveDim`. -/
def IsFixedMarginalSecret {dA dB n K : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero K]
    (Δ : Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op K) (σA : DensityOp dA) (εsec : ℝ) : Prop :=
  haveI := neZero_inputDim dA dB n
  ∀ (eveDim : ℕ) [NeZero eveDim] (ρ : DensityOp (dA ^ n * dB ^ n * eveDim)),
    partialTraceB (partialTraceB ρ.toOp) = (σA.tensorPowGen n).toOp →
    (1 / 2 : ℝ) * traceNorm (mapTensorId Δ ρ.toOp) ≤ εsec

/-- Fixed-marginal secrecy of a PMQKD protocol at hash length `l'`: the difference map
    `E^{(l')} - E^{(l'),ideal}` is `ε_sec`-secret with fixed marginal `σA`. -/
def PMQKDProtocol.IsSecretAt {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (P : PMQKDProtocol dA dB n) (l' : ℕ) (σA : DensityOp dA) (εsec : ℝ) : Prop :=
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  IsFixedMarginalSecret (P.differenceMap l') σA εsec

/-! ### Basic API and non-vacuity of Definition 4 -/

variable {dA dB n K : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero K]

/-- The zero difference map (real ≡ ideal) is `0`-secret: a perfectly-implementing
    protocol satisfies Definition 4 with `ε_sec = 0`. Shows Definition 4 is satisfiable. -/
theorem isFixedMarginalSecret_zero (σA : DensityOp dA) :
    IsFixedMarginalSecret (0 : Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op K) σA 0 := by
  haveI := neZero_inputDim dA dB n
  intro eveDim _ ρ _
  have hzero : mapTensorId (0 : Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op K) ρ.toOp = 0 := by
    ext p q
    simp [mapTensorId]
  rw [hzero, traceNorm_zero]
  simp

/-- Monotonicity of Definition 4 in the secrecy parameter. -/
theorem IsFixedMarginalSecret.mono {Δ : Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op K}
    {σA : DensityOp dA} {εsec εsec' : ℝ} (hle : εsec ≤ εsec')
    (h : IsFixedMarginalSecret Δ σA εsec) :
    IsFixedMarginalSecret Δ σA εsec' := by
  haveI := neZero_inputDim dA dB n
  intro eveDim _ ρ hρ
  exact le_trans (h eveDim ρ hρ) hle

omit [NeZero n] in
/-- **Non-vacuity of the fixed-marginal quantifier.** For every fixed marginal `σA` and
    every Eve dimension there is an input state `ρ_{AⁿBⁿEⁿ}` with
    `Tr_{BⁿEⁿ}(ρ) = (σA)^{⊗n}`. Hence the `∀ρ` in Definition 4 is not vacuously true, so
    Definition 4 is not automatically satisfied for negative `ε_sec`. -/
theorem exists_fixedMarginal_input [NeZero n] (σA : DensityOp dA)
    (eveDim : ℕ) [NeZero eveDim] :
    ∃ ρ : DensityOp (dA ^ n * dB ^ n * eveDim),
      partialTraceB (partialTraceB ρ.toOp) = (σA.tensorPowGen n).toOp := by
  haveI : NeZero (dB ^ n) := ⟨pow_ne_zero n (NeZero.ne dB)⟩
  refine ⟨((σA.tensorPowGen n).tensor (DensityOp.maxMixed (dB ^ n))).tensor
      (DensityOp.maxMixed eveDim), ?_⟩
  have h1 : partialTraceB
      (((σA.tensorPowGen n).tensor (DensityOp.maxMixed (dB ^ n))).tensor
        (DensityOp.maxMixed eveDim)).toOp =
      ((σA.tensorPowGen n).tensor (DensityOp.maxMixed (dB ^ n))).toOp :=
    partialTraceB_tensor _ _
  rw [h1]
  exact partialTraceB_tensor _ _

/-- **Definition 4 has teeth.** If some legitimate fixed-marginal input `ρ` makes the
    half-trace-norm strictly exceed `ε_sec`, then the difference map is *not*
    `ε_sec`-secret. In particular a channel whose real and ideal maps differ measurably on
    a fixed-marginal input fails Definition 4 for `ε_sec` below that measure: a trivial or
    degenerate channel does not satisfy Definition 4. -/
theorem not_isFixedMarginalSecret_of_input_violation
    {Δ : Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op K} {σA : DensityOp dA} {εsec : ℝ}
    {eveDim : ℕ} [NeZero eveDim] (ρ : DensityOp (dA ^ n * dB ^ n * eveDim))
    (hmarg : partialTraceB (partialTraceB ρ.toOp) = (σA.tensorPowGen n).toOp)
    (hviol : εsec < (1 / 2 : ℝ) * traceNorm (mapTensorId Δ ρ.toOp)) :
    ¬ IsFixedMarginalSecret Δ σA εsec := by
  intro h
  exact absurd (h eveDim ρ hmarg) (not_le.mpr hviol)

end InfoTheory.Postselection

end
