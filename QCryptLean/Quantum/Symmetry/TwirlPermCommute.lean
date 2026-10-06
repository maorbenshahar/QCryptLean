import QCryptLean.Quantum.Symmetry.SignalPermutation
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination

/-!
# The IID Bell twirl commutes with the round permutation

The two lemmas below mention no BB84 or QKD-protocol object: the `n`-fold bilateral-Pauli
(Bell) twirl unitary `bellTwirlUnitary n g` commutes with the `n`-site round permutation
representation `permutationRepresentation 4 n π` up to
a **relabelling of the per-round twirl string** `g ↦ g ∘ π⁻¹`.

`bellTwirlUnitary n g = ⊗ₐ G(g a)` (`BellDeFinettiDomination.lean`) is a tensor family and
`U_π` permutes the sites of `(ℂ⁴)^{⊗n}`, so the commutation is the "Church of the symmetric
subspace" site-wise equivariance (Harrow `arXiv:1308.6595` §3), stated generically as
`Quantum.TensorProducts.permutationRepresentation_conj_tensorFamily`
(`SymmetricSubspace.lean`).  Specialised to the twirl family
`A a = bb84BellSinglePairTwirlGroup (g a)`, the `σ⁻¹`-relabelling of the family is exactly the
relabelling `g ↦ g ∘ π⁻¹` of the twirl string.

This is the per-`π` summand transport fact: under the announced-permutation symmetrization the
per-round twirl `g` reaching round `i` of the original input becomes the twirl `g (π⁻¹ i)` reaching
the canonical round `i` after `permuteSignalLinear n π`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B; Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5; Harrow "The Church of the Symmetric Subspace" §3.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Symmetry
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- **the Bell twirl commutes with the round permutation up to relabelling `g ↦ g ∘ π⁻¹`.**

`U_π · bellTwirlUnitary n g · U_π† = bellTwirlUnitary n (g ∘ π⁻¹)` with `U_π =
permutationRepresentation 4 n π`.  The round permutation conjugation relabels the per-round twirl
string by `π⁻¹`: the bilateral Pauli that acted on the original round `π⁻¹ i` now acts on the
canonical round `i`.

The twirl unitary is the tensor family `⊗ₐ G(g a)`, so this is the site-permutation law
`permutationRepresentation_conj_tensorFamily` specialised to the twirl family. -/
theorem bellTwirlUnitary_perm_conj (n : ℕ) (π : Equiv.Perm (Fin n)) (g : Fin n → Fin 4) :
    permutationRepresentation 4 n π * bellTwirlUnitary n g *
        (permutationRepresentation 4 n π)ᴴ =
      bellTwirlUnitary n (g ∘ ⇑π⁻¹) := by
  rw [bellTwirlUnitary, bellTwirlUnitary, permutationRepresentation_conj_tensorFamily]
  rfl

/-- **Channel form: the input twirl commutes through the signal-permutation channel.**

`permuteSignalLinear n π (U_g · M · U_g†) = U_{g∘π⁻¹} · permuteSignalLinear n π M · U_{g∘π⁻¹}†`
with `U_g = bellTwirlUnitary n g`.  Pushing the input Bell twirl past the round permutation
`permuteSignalLinear n π` (conjugation by `U_π`) relabels the twirl string to `g ∘ π⁻¹`.

This is the per-`π` summand transport used in the attack-covariance assembly: the twirl applied to
the original input, after the symmetrization permutation, becomes the `π⁻¹`-relabelled twirl on the
canonical-frame state. -/
theorem permuteSignalLinear_bellTwirl_conj (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin 4) (M : Op (4 ^ n)) :
    permuteSignalLinear n π (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) =
      bellTwirlUnitary n (g ∘ ⇑π⁻¹) * permuteSignalLinear n π M *
        (bellTwirlUnitary n (g ∘ ⇑π⁻¹))ᴴ := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  set Uπ := permutationRepresentation 4 n π with hUπ
  have hconj : Uπ * bellTwirlUnitary n g = bellTwirlUnitary n (g ∘ ⇑π⁻¹) * Uπ := by
    have h := bellTwirlUnitary_perm_conj n π g
    calc Uπ * bellTwirlUnitary n g
        = (Uπ * bellTwirlUnitary n g * Uπᴴ) * Uπ := by
          rw [Matrix.mul_assoc, (permutationRepresentation_unitary 4 n π).1, Matrix.mul_one]
      _ = bellTwirlUnitary n (g ∘ ⇑π⁻¹) * Uπ := by rw [h]
  have hconjH : (bellTwirlUnitary n g)ᴴ * Uπᴴ = Uπᴴ * (bellTwirlUnitary n (g ∘ ⇑π⁻¹))ᴴ := by
    have := congrArg Matrix.conjTranspose hconj
    simpa only [Matrix.conjTranspose_mul] using this
  simp only [permuteSignalLinear, LinearMap.coe_mk, AddHom.coe_mk, ← hUπ]
  rw [show Uπ * (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) * Uπᴴ
        = (Uπ * bellTwirlUnitary n g) * M * ((bellTwirlUnitary n g)ᴴ * Uπᴴ) by noncomm_ring,
    hconj, hconjH]
  noncomm_ring

end Quantum.Symmetry

end
