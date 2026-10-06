import QCryptLean.Quantum.Symmetry.BellPairedDeFinetti
import QCryptLean.QKD.BB84.Engine.Postselection.BellReference
import QCryptLean.QKD.BB84.Engine.InnerBudget.BaseScheme
import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.Quantum.Channels.CPTP.CKRBound.CovarianceBundles
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.TensorTraceNormInvariance

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

/-!
# Bell de Finetti inner-budget core — the Bell symmetric purifier `V_Bell`

Part of the Bell reference/floor construction (with `BellDickeCore.lean`, `BellHaarIntegral.lean`
and `BellFloorChain.lean`): the Bell symmetric-purifier datum `BB84BellSymmetricPurifier`/`V_Bell`,
its `Eⁿ⊗V` purification, and the B19 purification-register-invariance identity for the CKR tensor
trace norm.
-/

noncomputable section

namespace QKD.BB84.Engine

/-! ## The Bell symmetric purifier `V_Bell` (Nahar et al. B13/B17, the affordable register) -/

/-- **The Nahar et al. B13/B17 Bell purifier datum at a prescribed `Aⁿ ⊗ Eⁿ` marginal `ρ₀`**
(re-keyed to `bb84PolyDimTight n = C(n+3,3)`).

The `ρ₀`-parameterised form of the Bell analogue of `BB84SymmetricPurifier`
(`SymmetricPurifier.lean`): a pure purifier on `(Aⁿ ⊗ Eⁿ) ⊗ V` of the **joint** state `ρ₀` on
`Aⁿ ⊗ Eⁿ`, together with the **affordable** register-dimension bound
`dV ≤ bb84PolyDimTight n = C(n+3,3)` (Nahar et al. B17), exactly as the CKR `BB84SymmetricPurifier`
packages `pairedDeFinettiState signalDim n` with its rank-`g` purifier.

The structure fields are the verbatim Bell analogues of the CKR ones, with the joint state left as
the parameter `ρ₀`:
* the pure purifier on `((4ⁿ · 4ⁿ) · dV)` (the `V`-register is the trailing factor, NOT yet
  reassociated — `bb84EnVBellPurification` reassociates it);
* tracing out only `V` recovers `ρ₀` (the joint-after-`V` state the d2/B16 AEP floor reads, not just
  the `Aⁿ` marginal);
* the register dimension is bounded by `C(n+3,3) = bb84PolyDimTight n` (Nahar et al. B17).

The Nahar et al. B13 instance is `BB84BellSymmetricPurifier n`, at
`ρ₀ = bb84BellPairedDeFinettiState n`.  Only `purifier_partialTraceB` (and, through it,
`purifier_isPure` where purity is paired with the marginal) depends on `ρ₀`: the
register-dimension arithmetic, the `Eⁿ⊗V` reassociation and the trace-norm collapse
(`tensorTraceNorm_eq_of_shared_marginal`) are uniform in `ρ₀`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Thm 3, Eqs. (B13),
(B17), (B19); Watrous §2.2. -/
structure BB84BellPurifierOfMarginal (n : ℕ) [NeZero n]
    (ρ₀ : DensityOp ((4 ^ n) * (4 ^ n))) where
  /-- The dimension of the purifying register `V`. -/
  dV : ℕ
  /-- The purifier register is nonempty. -/
  dV_neZero : NeZero dV
  /-- The pure purifier of `ρ₀` on `(Aⁿ ⊗ Eⁿ) ⊗ V`. -/
  purifier : DensityOp (((signalDim ^ n) * (signalDim ^ n)) * dV)
  /-- The purifier is a pure state. -/
  purifier_isPure : purifier.IsPure
  /-- Tracing out only `V` recovers the prescribed joint marginal `ρ₀` (Nahar et al. B13). -/
  purifier_partialTraceB : purifier.partialTraceB = ρ₀
  /-- The purifier register dimension is bounded by `C(n+3,3) = bb84PolyDimTight n`
      (Nahar et al. B17). -/
  dV_le_polyDimTight : dV ≤ bb84PolyDimTight n

attribute [instance] BB84BellPurifierOfMarginal.dV_neZero

/-- **The Nahar et al. B13/B17 Bell symmetric-purifier datum**
    (re-keyed to `bb84PolyDimTight n = C(n+3,3)`):
`BB84BellPurifierOfMarginal` at the Bell **joint** de Finetti mixture
`bb84BellPairedDeFinettiState n` on `Aⁿ ⊗ Eⁿ` (Nahar et al. B13, the rank-`C(n+3,3)` type-mixture,
`BellPairedDeFinetti.lean`).

This is the faithful joint encoding: exposing the joint-after-`V` mixture (rather than only the
whole `Aⁿ` marginal) is what lets the Bell EnV floor build the filtered de Finetti reference from
`bb84BellPairedDeFinettiState n` and trace out `V` block-by-block, mirroring the CKR construction.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Thm 3, Eqs. (B13),
(B17), (B19); Watrous §2.2. -/
abbrev BB84BellSymmetricPurifier (n : ℕ) [NeZero n] : Type :=
  BB84BellPurifierOfMarginal n (bb84BellPairedDeFinettiState n)

/-- **The Bell `Eⁿ⊗V` de Finetti purification** (Nahar et al. B13/B19, `R = Eⁿ ⊗ V`).

The reassociated pure purifier carried by a `BB84BellPurifierOfMarginal`: the verbatim Bell analogue
of `bb84EnVCKRPurification`, reassociating `((4ⁿ · 4ⁿ) · dV) → (4ⁿ · (4ⁿ · dV))` (where `dV` is the
purifier's dimension field) so the reference register is the single block `Eⁿ ⊗ V` of dimension `4ⁿ
· dV`. The reassociation reads only the purifier's dimension and state fields, so it is uniform in
the marginal `ρ₀`. -/
def bb84EnVBellPurification {n : ℕ} [NeZero n]
    {ρ₀ : DensityOp ((4 ^ n) * (4 ^ n))} (V : BB84BellPurifierOfMarginal n ρ₀) :
    DensityOp ((signalDim ^ n) * ((signalDim ^ n) * V.dV)) :=
  DensityOp.castDim (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV) V.purifier

/-- `DensityOp.castDim` commutes with `.toOp`: the underlying operator is transported along the
dimension equality. -/
private lemma bell_densityOp_castDim_toOp {a b : ℕ} (h : a = b) (ρ : DensityOp a) :
    (DensityOp.castDim h ρ).toOp = h ▸ ρ.toOp := by
  subst h; rfl

/-- **The Bell `Eⁿ⊗V` purification is pure** — the reassociation cast preserves purity, at any
marginal `ρ₀`. -/
theorem bb84EnVBellPurification_isPure {n : ℕ} [NeZero n]
    {ρ₀ : DensityOp ((4 ^ n) * (4 ^ n))} (V : BB84BellPurifierOfMarginal n ρ₀) :
    (bb84EnVBellPurification V).IsPure :=
  DensityOp.castDim_IsPure _ _ V.purifier_isPure

/-- **Nahar et al. B13 at an arbitrary marginal — the `4ⁿ` marginal of the Bell `Eⁿ⊗V` purification
is the `Aⁿ` marginal of `ρ₀`.**

Tracing out the whole `Eⁿ ⊗ V` block factors as tracing out `V` (giving `ρ₀`, via the purifier's
own partial-trace field) then tracing out `Eⁿ`, and the iterated partial trace equals the single
partial trace over the reassociated reference register (`partialTraceB_partialTraceB_eq_assoc`).
This is the only place the purifier's marginal field is read on the `Eⁿ⊗V` side. -/
theorem bb84EnVBellPurification_partialTraceB {n : ℕ} [NeZero n]
    {ρ₀ : DensityOp ((4 ^ n) * (4 ^ n))} (V : BB84BellPurifierOfMarginal n ρ₀) :
    (bb84EnVBellPurification V).partialTraceB = ρ₀.partialTraceB := by
  apply DensityOp.ext
  change Quantum.TensorProducts.partialTraceB
      (DensityOp.castDim (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV)
        V.purifier).toOp =
    Quantum.TensorProducts.partialTraceB ρ₀.toOp
  have hA : Quantum.TensorProducts.partialTraceB V.purifier.toOp = ρ₀.toOp :=
    congrArg (·.toOp) V.purifier_partialTraceB
  rw [bell_densityOp_castDim_toOp, ← partialTraceB_partialTraceB_eq_assoc, hA]

/-- **The Bell `Eⁿ⊗V` purification is a Bell CKR de Finetti purification**: it is pure and its `4ⁿ`
marginal — tracing out the whole `Eⁿ ⊗ V` block — is `bb84BellDeFinettiDensity n`.

Mirrors `bb84EnVCKRPurification_isPurification`: purity is `bb84EnVBellPurification_isPure` and the
marginal is `bb84EnVBellPurification_partialTraceB` (giving `bb84BellPairedDeFinettiState n` after
tracing out `V`, Nahar et al. B13) followed by its `Aⁿ` marginal
`bb84BellPairedDeFinettiState_partialTraceB`. -/
theorem bb84EnVBellPurification_isPurification {n : ℕ} [NeZero n]
    (V : BB84BellSymmetricPurifier n) :
    IsBellCKRDeFinettiPurification
      (n := n) (dimR := (signalDim ^ n) * V.dV) (bb84EnVBellPurification V) :=
  ⟨bb84EnVBellPurification_isPure V,
    (bb84EnVBellPurification_partialTraceB V).trans
      (bb84BellPairedDeFinettiState_partialTraceB n)⟩

/-- **Nahar et al. B13/B17 — existence of the Bell symmetric purifier at the affordable register
    dimension
`V.dV ≤ C(n+3,3)`.**

There exists a `BB84BellSymmetricPurifier n`: a pure purifier of the Bell joint de Finetti
mixture `bb84BellPairedDeFinettiState n` on a register `V` of dimension `V.dV ≤ bb84PolyDimTight n =
C(n+3,3)`.

The Bell joint mixture `bb84BellPairedDeFinettiState n` (`BellPairedDeFinetti.lean`) is the
rank-`C(n+3,3)` type-coherent mixture purifying `τ_Bell`, with
`Matrix.rank (bb84BellPairedDeFinettiState n).toOp ≤ bb84PolyDimTight n`
(`bb84BellPairedDeFinettiState_rank_le_polyDimTight`).  A density operator of rank `r` admits a pure
purification on a reference register of dimension `r` (Schmidt decomposition; reference-register
dimension equals state rank, Watrous §2.2, `densityOp_purification_exists_at_rank`).  Choosing
`dV = rank ≤ C(n+3,3)` yields the datum — the verbatim Bell analogue of
`bb84_symmetricPurifier_exists` at the rank-`C(n+3,3)` Bell joint state.

This realizes the genuine Nahar et al. B17 register-extension structure: `V` is the rank-`C(n+3,3)`
joint Bell symmetric purifier (`dV = rank ≤ C(n+3,3)`), so the B17 penalty is the affordable `2 log
C(n+3,3)` and tracing out only `V` returns the joint mixture the AEP floor reads.

References: Nahar et al. 2024 (`arXiv:2403.11851`) Thm 3, Eqs. (B13), (B17); the dimension bound
`[47, Eq. 8]`; Watrous §2.2 (purifications; reference-register dimension = Schmidt rank = state
rank). -/
theorem bb84_bellSymmetricPurifier_exists (n : ℕ) [NeZero n] [NeZero (4 ^ n)] :
    Nonempty (BB84BellSymmetricPurifier n) := by
  classical
  haveI hSig : NeZero ((signalDim ^ n) * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (pow_ne_zero n (by norm_num)) (pow_ne_zero n (by norm_num))⟩
  set ρ : DensityOp ((signalDim ^ n) * (signalDim ^ n)) :=
    bb84BellPairedDeFinettiState n with hρ_def
  -- the purifier register dimension is the rank `r ≤ C(n+3,3)`, and `r ≥ 1`
  haveI hr : NeZero (Matrix.rank ρ.toOp) := ⟨(densityOp_rank_pos ρ).ne'⟩
  have hr_le : Matrix.rank ρ.toOp ≤ bb84PolyDimTight n := by
    rw [hρ_def]; exact bb84BellPairedDeFinettiState_rank_le_polyDimTight n
  -- the generic rank-dimension purification
  obtain ⟨ψ, hψ_pure, hψ_marg⟩ := densityOp_purification_exists_at_rank ρ
  exact ⟨{
    dV := Matrix.rank ρ.toOp
    dV_neZero := hr
    purifier := ψ
    purifier_isPure := hψ_pure
    purifier_partialTraceB := by
      apply DensityOp.ext
      change Quantum.TensorProducts.partialTraceB ψ.toOp = ρ.toOp
      rw [hψ_marg]
    dV_le_polyDimTight := hr_le }⟩

/-! ## Nahar et al. B19 — purification-register invariance of the Bell CKR tensor trace norm -/

/-- **Nahar et al. B19 — `ckrTensorTraceNorm` is invariant under the choice of Bell de Finetti
    purification
register** (canonical `R = 4ⁿ` vs the `Eⁿ⊗V` split `R = 4ⁿ·V.dV`).

`ckrTensorTraceNorm Δ τ = ‖(Δ ⊗ id_R)(τ)‖₁` depends on `τ` only through its action transported by
the reference register `R`.  Both `bb84BellCKRDeFinettiPurification n` (canonical, `R = 4ⁿ`) and
`bb84EnVBellPurification V` (the `Eⁿ⊗V` split, `R = 4ⁿ·V.dV`) purify the **same** Bell de Finetti
marginal `bb84BellDeFinettiDensity n`, so by purification freedom (Uhlmann,
`purification_unique_up_to_partial_isometry_on_reference`, at `4ⁿ ≤ 4ⁿ·V.dV`) they are related by a
reference-side left-isometry `W` (`Wᴴ W = 1`), `τ_EnV.toOp = (1_{4ⁿ} ⊗ W)·τ_Bell.toOp·(1 ⊗ W)ᴴ`.
Since `Δ ⊗ id` acts on the signal register and `W` on the reference register, they commute
(`mapTensorIdLinear_idTensorRect_conj`, purely algebraic), and the trace norm is invariant
under the rectangular tensor isometry `1 ⊗ W`
(`Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left`).

This is the generic B19 argument along the public Uhlmann path, instantiated at `ρ =
bb84BellDeFinettiDensity n`; it is the Bell analogue of the CKR
`bb84_ckrTensorTraceNorm_EnV_eq_canonical` (which is hard-wired to `ckrDeFinettiState` via the
private `ckrDeFinettiPurification_relate_canonical_via_partial_isometry`).
References: Nahar et al. 2024 (`arXiv:2403.11851`) B19; Watrous §2.2. -/
theorem bb84_bellTensorTraceNorm_EnV_eq_canonical
    {n dimOut : ℕ} [NeZero n] [NeZero (4 ^ n)] [NeZero dimOut]
    (V : BB84BellSymmetricPurifier n)
    (Δ : Op (signalDim ^ n) →ₗ[ℂ] Op dimOut) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ckrTensorTraceNorm Δ (bb84BellCKRDeFinettiPurification n) =
      ckrTensorTraceNorm Δ (bb84EnVBellPurification V) := by
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  exact tensorTraceNorm_eq_of_shared_marginal Δ (bb84BellDeFinettiDensity n)
    (bb84BellCKRDeFinettiPurification n) (bb84EnVBellPurification V)
    (bb84BellCKRDeFinettiPurification_isPurification n).isPure
    (bb84EnVBellPurification_isPurification V).isPure
    (bb84BellCKRDeFinettiPurification_isPurification n).marginal
    (bb84EnVBellPurification_isPurification V).marginal

end QKD.BB84.Engine

end -- noncomputable section
