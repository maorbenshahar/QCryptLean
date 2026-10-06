import QCryptLean.QKD.BB84.Engine.Postselection.CKRPairedSupport
import QCryptLean.InfoTheory.DeFinetti.PurificationAncillaEmbed
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.PostFilter
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP
import QCryptLean.QKD.BB84.Engine.InnerBudget.BaseScheme
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SupportPreservation
import QCryptLean.Quantum.Channels.CPTP.PositiveTransport
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.Math.SpectralTheory.PSDDecomposition
import QCryptLean.Quantum.Metrics.RectangularPolar

/-!
# BB84 symmetric purifier — the Nahar et al. B17 register-extension datum (dim V ≤ g)

This module isolates the symmetric purifier `V` of Nahar et al. App. B (eq. B13/B17): the purifying
register whose dimension is bounded by the paired symmetric-subspace dimension
`g = bb84PolyDim n`, and whose `2·log₂ g` register-extension penalty cancels the B18
shortened hash.

This register is **distinct** from the de Finetti mixture purification `τ` used for the
postselection Eq. 9 domination.  `τ` (`IsCKRDeFinettiPurification`,
`bb84SymCKRDeFinettiPurification`) purifies the **full-rank** CKR de Finetti marginal
`ckrDeFinettiState signalDim n` (rank `4^n`), so any purifier of it needs reference dimension `≥
4^n`, giving the prohibitive `2·log₂(4^n) = 4n` penalty.  Nahar et al. B17 instead extends the
symmetric **joint** state `τ_{A^n B^n E^n} = ∫_{σ∈S} σ_{ABE}^{⊗n} dσ` (Nahar et al. B13), which is
supported on `Sym^n(ℂ^{d_A² d_B²})` and therefore has rank `≤ g`; its purifier `V` can be chosen of
dimension `dim V ≤ g`, giving the affordable `2·log₂ g` penalty.

The symmetric joint state at rank `≤ g` is the Leaf B object
`pairedDeFinettiState signalDim n` (`Quantum.Channels.pairedDeFinettiState`), with rank
bound `bb84_pairedDeFinettiState_rank_le_polyDim`.  This file packages it together with a
purifier register `V` of dimension `dV ≤ bb84PolyDim n`.

## Main definitions
- `BB84SymmetricPurifier`: the symmetric joint state together with a purifier
  register `V` of dimension `dV ≤ bb84PolyDim n` whose `V`-marginal is the symmetric state.

## Main statements
- `QKD.BB84.Engine.BB84SymmetricPurifier.dV_le_polyDim`: the purifier register dimension is `≤ g`.
- `bb84_symmetricPurifier_exists`: such a datum exists.

## References
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) Theorem 3, App. B:
- B13 (`Nahar et al. 2024 transcript` ~:2100): `τ_{A^n B^n E^n} = ∫_{σ∈S} σ_{ABE}^{⊗n} dσ`,
supported on
  `Sym^n(ℂ^{d_A² d_B²})`.
- B17 (~:2162-2174): `dim V ≤ dim Sym^n(ℂ^{d_A² d_B²}) = g_{n,x}`, x = d_A²d_B², and the
  `[47, Eq. 8]` register-extension penalty `Hmin^{ε̄}(Z^n|C^n C_E E^n V) ≥
  Hmin^{ε̄}(Z^n|C^n C_E E^n) − 2 log g_{n,x}`.

Leaf B (paired rank-`g`): `bb84_pairedDeFinettiState_rank_le_polyDim`.

Matrix-analysis fact for the purifier dimension: a state of rank `r` has a pure purification
on a reference register of dimension `r` (Schmidt decomposition / purification reference-
register dimension = state rank; Watrous, *Theory of Quantum Information*, §2.2).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- The Nahar et al. B17 symmetric-purifier datum: the symmetric joint de Finetti state
`pairedDeFinettiState signalDim n` on `A^n B^n` (Nahar et al. B13, rank `≤ g` by Leaf B),
together with a purifying register `V` of dimension `dV`, the pure joint purifier on
`(d^n · d^n) · dV`, and the data that
* the purifier is pure,
* its `V`-marginal is the symmetric joint state, and
* the register dimension is bounded by `g = bb84PolyDim n`.

The `V`-register is **not** the de Finetti mixture purification register `R` (which is forced
to be `4^n`-dimensional); it is the genuinely smaller register that purifies the **joint**
symmetric state and carries the affordable `2·log₂ g` Nahar et al. B17 penalty. -/
structure BB84SymmetricPurifier (n : ℕ) [NeZero n] where
  /-- The dimension of the purifying register `V`. -/
  dV : ℕ
  /-- The purifier register is nonempty. -/
  dV_neZero : NeZero dV
  /-- The pure purifier of the symmetric joint state on `(A^n B^n) ⊗ V`. -/
  purifier : DensityOp (((signalDim ^ n) * (signalDim ^ n)) * dV)
  /-- The purifier is a pure state. -/
  purifier_isPure : purifier.IsPure
  /-- Tracing out `V` recovers the symmetric joint de Finetti state (Nahar et al. B13). -/
  purifier_partialTraceB :
    purifier.partialTraceB = pairedDeFinettiState signalDim n
  /-- The purifier register dimension is bounded by `g = bb84PolyDim n` (Nahar et al. B17). -/
  dV_le_polyDim : dV ≤ bb84PolyDim n

namespace BB84SymmetricPurifier

attribute [instance] BB84SymmetricPurifier.dV_neZero

end BB84SymmetricPurifier

/-- **Nahar et al. B17 symmetric-purifier existence (dim V ≤ g).**

There exists a symmetric-purifier datum for the BB84 symmetric joint de Finetti state: a pure
purifier of `pairedDeFinettiState signalDim n` on a register `V` of dimension
`dV ≤ bb84PolyDim n`.

The symmetric joint state `pairedDeFinettiState signalDim n` is the Leaf B object
supported on the paired symmetric subspace `Sym^n(ℂ^{signalDim²})`, with
`Matrix.rank (pairedDeFinettiState signalDim n).toOp ≤ bb84PolyDim n`
(`bb84_pairedDeFinettiState_rank_le_polyDim`).  A density operator of rank `r` admits a pure
purification on a reference register of dimension `r` (Schmidt decomposition; purification
reference-register dimension equals state rank, Watrous, *Theory of Quantum Information*,
§2.2).  Choosing `dV = rank ≤ g` yields the datum.

This is the one construction the papers leave implicit: Nahar et al. App. B asserts
`dim V ≤ dim Sym^n = g_{n,x}` (B17) by exactly this rank/purification-dimension argument.
The Leaf B rank bound supplies `rank ≤ g` (`bb84_pairedDeFinettiState_rank_le_polyDim`); the
general matrix-analysis fact that a rank-`r` state purifies onto a dimension-`r` register is
proved here as `densityOp_purification_exists_at_rank` (PSD column factorization `ρ = B Bᴴ`
with `B` of width `rank` from `psd_eq_sum_rank_vecMulVec`, then vectorize `B` into a unit ket).
This is the rank-dimension purification, *distinct* from the `purificationDensityOp`,
which purifies onto the **full** `d^n` register and would give only the prohibitive `dV = d^n`.

References: Nahar et al. 2024 (arXiv:2403.11851) Theorem 3, `\label{eq:tausplit}`
(main.tex:1356–:1362), (B17); the dimension bound `[47, Eq. 8]`; Renner 2005
(arXiv:quant-ph/0512258v2) §6.5; Watrous, *Theory of Quantum Information*, §2.2 (purifications;
reference-register dimension = Schmidt rank = state rank). -/
theorem bb84_symmetricPurifier_exists (n : ℕ) [NeZero n] :
    Nonempty (BB84SymmetricPurifier n) := by
  classical
  set ρ : DensityOp ((signalDim ^ n) * (signalDim ^ n)) :=
    pairedDeFinettiState signalDim n with hρ_def
  -- the purifier register dimension is the rank `r ≤ g`, and `r ≥ 1`
  haveI hr : NeZero (Matrix.rank ρ.toOp) := ⟨(densityOp_rank_pos ρ).ne'⟩
  have hr_le : Matrix.rank ρ.toOp ≤ bb84PolyDim n := by
    rw [hρ_def]; exact bb84_pairedDeFinettiState_rank_le_polyDim n
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
    dV_le_polyDim := hr_le }⟩

/-- **The `Eⁿ ⊗ V` (split-`R`) rank-`g` de Finetti purification.**

Nahar et al. App. B builds the postselection reference register as `R = Eⁿ ⊗ V`: the IID Eve
register `Eⁿ` (full-rank `dⁿ`, carrying the AEP floor with no dimension penalty) tensored with the
rank-`g` symmetric purifier of the symmetric mixture (its register dimension is at most `g =
bb84PolyDim n`, carrying the affordable `−2 log g` register-extension cost) — a pure state on `(Aⁿ ⊗
Eⁿ) ⊗ V`, with `Aⁿ ⊗ Eⁿ = pairedDeFinettiState signalDim n` (Nahar et al. B13) — reassociated to `Aⁿ
⊗ (Eⁿ ⊗ V)`, so that the reference register is the single block `Eⁿ ⊗ V`.

Reassociating `((dⁿ · dⁿ) · dV)` to `(dⁿ · (dⁿ · dV))` exposes `Eⁿ ⊗ V` as the CKR reference
register `R`; the `Aⁿ`-marginal is `ckrDeFinettiState signalDim n`
(`bb84EnVCKRPurification_isPurification`), so Nahar et al. B19 ("identifying `Eⁿ V` with `R`") is
definitional — `R` *is* `Eⁿ ⊗ V` by construction.

The purifier datum `V` is threaded explicitly (the existence lemma `bb84_symmetricPurifier_exists`
supplies one); its register dimension is bounded by `bb84PolyDim n`, the affordable extension cost.

References: Nahar et al. 2024 (arXiv:2403.11851) Theorem 3, `\label{eq:tausplit}`
(main.tex:1356–:1362), (B17), (B19); Watrous, *Theory of Quantum Information*, §2.2 (purifications).
-/
noncomputable def bb84EnVCKRPurification {n : ℕ} [NeZero n]
    (V : BB84SymmetricPurifier n) :
    DensityOp ((signalDim ^ n) * ((signalDim ^ n) * V.dV)) :=
  DensityOp.castDim (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV) V.purifier

/-- **`bb84EnVCKRPurification V` is a CKR de Finetti purification.**

The reassociated symmetric purifier is pure (purity is preserved by `castDim`) and its
`Aⁿ`-marginal — tracing out the whole `Eⁿ ⊗ V` reference block — is
`ckrDeFinettiState signalDim n`.  Tracing out `Eⁿ ⊗ V` factors as tracing out `V` (giving
`pairedDeFinettiState`, via the purifier's own partial-trace field, Nahar et al. B13) then tracing
out `Eⁿ` (giving its CKR marginal `ckrDeFinettiState`, by definition of `ckrDeFinettiState`), and
the iterated partial trace equals the single partial trace over the reassociated reference register
(`partialTraceB_partialTraceB_eq_assoc`).

This is the piece that makes Nahar et al. B19 definitional and lets the generic,
purification-invariant lift `ckrDeFinetti_traceNorm_le_ckrTensorTraceNorm` (generic in the reference
dimension) instantiate at the `Eⁿ ⊗ V` reference register `R = Eⁿ ⊗ V`.

References: Nahar et al. 2024 (arXiv:2403.11851) Theorem 3, `\label{eq:tausplit}`
(main.tex:1356–:1362), (B19). -/
theorem bb84EnVCKRPurification_isPurification {n : ℕ} [NeZero n]
    (V : BB84SymmetricPurifier n) :
    Quantum.Channels.IsCKRDeFinettiPurification
      (d := signalDim) (n := n) (dimR := (signalDim ^ n) * V.dV)
      (bb84EnVCKRPurification V) := by
  refine ⟨DensityOp.castDim_IsPure _ _ V.purifier_isPure, ?_⟩
  apply DensityOp.ext
  change Quantum.TensorProducts.partialTraceB
      (DensityOp.castDim (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV)
        V.purifier).toOp =
    (ckrDeFinettiState signalDim n).toOp
  have hA : Quantum.TensorProducts.partialTraceB V.purifier.toOp =
      (pairedDeFinettiState signalDim n).toOp :=
    congrArg (·.toOp) V.purifier_partialTraceB
  rw [densityOp_castDim_toOp, Op.castDim, ← partialTraceB_partialTraceB_eq_assoc, hA]
  rfl

section ExtensionFloor

variable {XR : Type*} [Fintype XR]

end ExtensionFloor

end QKD.BB84.Engine

end -- noncomputable section
