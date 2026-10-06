import QCryptLean.Quantum.Channels.CPTP.CKRBound.Main
import QCryptLean.Quantum.Symmetry.Covariance

/-!
# CKR Covariance Hypothesis Bundles (`d = 4`) — permutation covariance, Hermiticity, sym. factoring

The `d = 4` covariance hypothesis bundles for the Christandl-Konig-Renner postselection
technique: `PermutationCovariantBB84` (the standard CKR covariance bundle specialized to
BB84's qudit dimension `d = 4`), `PermutationCovariantHermitian` (covariance plus
conjugate-transpose preservation), and `PermutationCovariantTight` (covariance plus
Hermiticity plus symmetric-support factoring, used by the tight `(n+1)^{d-1}` postselection
route).

These structures are pure channel/covariance infrastructure with no protocol-level (QKD
transcript, key-rate, error-correction) content, and `PermutationCovariantTight` is consumed
directly by the CKR postselection theorem `ckr_postselection_tight`
(`TightPostselectionBound.lean`).

The d-generic `PermutationCovariant` primitive (no hardcoded `d = 4`) is
`Quantum.Symmetry.PermutationCovariant`; this file keeps the `d = 4` BB84-specialized bundles
that build on it.

## Main definitions
- `PermutationCovariantBB84`: CKR covariance with a CPTP correction family, `d = 4`.
- `PermutationCovariantHermitian`: covariance plus conjugate-transpose preservation.
- `PermutationCovariantTight`: covariance plus Hermiticity plus symmetric factoring.
-/

open Quantum.Operators Matrix Quantum.Channels
open Quantum.Symmetry
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-!
## CKR Postselection Hypotheses

The Christandl-Konig-Renner postselection theorem is a statement about linear
maps satisfying permutation covariance, with extra structure required for the
tight symmetric-support route. The bare `PermutationCovariant` primitive is
`Quantum.Symmetry.PermutationCovariant`; this file adds the `d = 4` BB84 specializations.
-/

/-- Standard CKR hypothesis bundle for the postselection technique, specialized to
    the BB84 qudit dimension `d = 4`.

    The specialized BB84 route keeps a separate name so the standard and tight
    postselection files can stay explicit about the `d = 4` setting. -/
structure PermutationCovariantBB84 {n dimOut : ℕ} [NeZero n] [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut) : Prop where
  /-- For each permutation `π`, there exists a CPTP correction map `K_π`
      such that `Δ` intertwines conjugation by the permutation representation
      with `K_π`. -/
  covariance : ∀ (π : Equiv.Perm (Fin n)),
    ∃ (K_π : Op dimOut → Op dimOut), Quantum.Channels.IsCPTP K_π ∧
      ∀ (ρ : Op (4 ^ n)),
        Δ (permutationRepresentation 4 n π * ρ *
          (permutationRepresentation 4 n π)ᴴ) =
        K_π (Δ ρ)

/-- Stronger CKR helper hypothesis: standard covariance plus
    Hermiticity preservation. -/
structure PermutationCovariantHermitian {n dimOut : ℕ} [NeZero n] [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut) : Prop extends PermutationCovariantBB84 Δ where
  /-- `Δ(M†) = Δ(M)†` for all operators `M`. -/
  preserves_conjTranspose :
    ∀ M : Op (4 ^ n), Δ M.conjTranspose = (Δ M).conjTranspose

/-- Stronger CKR hypothesis bundle used by the current tight `d - 1` proof path. -/
structure PermutationCovariantTight {n dimOut : ℕ} [NeZero n] [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut) : Prop extends PermutationCovariantHermitian Δ where
  /-- `Δ` factors through the symmetric projector on inputs. -/
  factors_through_sym :
    ∀ A : Op (4 ^ n),
      Δ (symmetricProjector 4 n * A * symmetricProjector 4 n) = Δ A

end QKD.BB84.Engine
