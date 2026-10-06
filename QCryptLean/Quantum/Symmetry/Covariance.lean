import QCryptLean.Quantum.Channels.CPTP.CKRBound.Main
import QCryptLean.Quantum.Symmetry.SymmetricSubspace

/-!
# CKR Permutation Covariance — the general (d-generic) primitive

The d-generic permutation-covariance hypothesis for the Christandl–Konig–Renner
postselection technique. This is pure quantum-channel infrastructure with no BB84
or QKD-protocol content: it is consumed by the BB84 security stack, the general
QKD postselection layer, and the randomized/stratified blocking twirls.

Also carries two small covariance-witness lemmas: unitary conjugation being
CPTP, and the `d = 4` symmetric projector being fixed by permutation conjugation.

## Main definitions
- `PermutationCovariant`: d-generic CKR permutation covariance for linear maps

## Main statements
- `isCPTP_unitary_conjugation`: unitary conjugation `X ↦ U · X · U†` is CPTP.
- `permRep_conj_symmetricProjector`: the symmetric projector is fixed by conjugation
  with a permutation representation.
-/

open Quantum.Operators Matrix Quantum.Channels
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- A linear map `Δ : End(H^⊗n) → End(H')` is permutation-covariant if every
    permutation of the input tensor factors can be transferred through `Δ`
    using some CPTP correction map on the output. -/
structure PermutationCovariant {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) : Prop where
  /-- For each permutation `π`, there exists a CPTP correction map `K_π`
      such that `Δ` intertwines permutation conjugation with `K_π`. -/
  covariance : ∀ (π : Equiv.Perm (Fin n)),
    ∃ (K_π : Op dimOut → Op dimOut), Quantum.Channels.IsCPTP K_π ∧
      ∀ (ρ : Op (d ^ n)),
        Δ (permutationRepresentation d n π * ρ *
          (permutationRepresentation d n π)ᴴ) =
        K_π (Δ ρ)

/-- Unitary conjugation `X ↦ U * X * U†` is CPTP. -/
lemma isCPTP_unitary_conjugation {m : ℕ} [NeZero m]
    (U : Op m) (hUU' : Uᴴ * U = 1) :
    Quantum.Channels.IsCPTP (fun X : Op m => U * X * Uᴴ) := by
  have hK : (∑ i : Fin 1, (![U] i)ᴴ * (![U] i)) = (1 : Op m) := by
    simp [hUU']
  let K : Quantum.Channels.KrausRepresentation m m :=
    ⟨1, ![U], hK⟩
  have hK_apply : ∀ (X : Op m), K.applyOp X = U * X * Uᴴ := by
    intro X
    change ∑ i : Fin 1, ![U] i * X * (![U] i)ᴴ = U * X * Uᴴ
    simp
  have h := K.is_cptp
  rwa [show K.applyOp = (fun X : Op m => U * X * Uᴴ)
    from funext hK_apply] at h

/-- The symmetric projector is fixed by conjugation with a permutation representation. -/
lemma permRep_conj_symmetricProjector (n : ℕ) [NeZero n] (π : Equiv.Perm (Fin n)) :
    permutationRepresentation 4 n π * symmetricProjector 4 n *
      (permutationRepresentation 4 n π)ᴴ =
    symmetricProjector 4 n := by
  let U : Op (4 ^ n) := permutationRepresentation 4 n π
  let P : Op (4 ^ n) := symmetricProjector 4 n
  have hP : Pᴴ = P := (symmetricProjector_is_projector 4 n).2
  have hUP : U * P = P := by
    simpa [U, P] using Quantum.Symmetry.permRep_mul_symmetricProjector (d := 4) (n := n) π
  have hPUH : P * Uᴴ = P := by
    simpa [Matrix.conjTranspose_mul, hP, U, P] using congrArg Matrix.conjTranspose hUP
  calc
    permutationRepresentation 4 n π * symmetricProjector 4 n *
        (permutationRepresentation 4 n π)ᴴ =
      U * P * Uᴴ := by rfl
    _ = (U * P) * Uᴴ := by rw [Matrix.mul_assoc]
    _ = P * Uᴴ := by rw [hUP]
    _ = P := by rw [hPUH]
    _ = symmetricProjector 4 n := by rfl

end Quantum.Symmetry
