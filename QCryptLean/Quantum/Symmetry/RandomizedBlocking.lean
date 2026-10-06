import QCryptLean.Quantum.Symmetry.Covariance

/-!
# Randomized Blocking Preserves Signal-Level Permutation Covariance

Advantage distillation (AD) is a *block-structured* two-way post-processing map:
it groups the `n` signals into blocks and announces block parities. A fixed block
partition is **not** permutation-covariant, so the CKR postselection lift does not
apply to it directly — and naively symmetrizing at the *block* level would replace
the single-signal de Finetti prefactor `C(n+3,3) ~ n³` by a block-dimensional one
(`x = 4^b`), which explodes the finite-size rates.

This file proves the standard escape is sound: **first apply a uniformly random
signal permutation, then block**. Averaging any fixed post-processing map `F` over
signal permutations yields a map that is *exactly* permutation-invariant, hence
CKR-covariant with the identity correction channel. The postselection lift then
applies at the **signal-level** prefactor; the block structure of `F` is irrelevant.

Concretely, for `Φ := (n!)⁻¹ ∑_π F ∘ (U_π · U_πᴴ)` and every permutation `τ`:

  `Φ(U_τ ρ U_τᴴ) = (n!)⁻¹ ∑_π F(U_{πτ} ρ U_{πτ}ᴴ) = Φ(ρ)`

by reindexing the group average (`Equiv.mulRight τ`).

This file holds the d-generic content (general quantum-symmetry layer).

## Main definitions
- `permConjLin`: conjugation `ρ ↦ U_π ρ U_πᴴ` as a linear map
- `randomizedBlockingTwirl`: the signal-permutation average `(n!)⁻¹ ∑_π F ∘ permConjLin π`

## Main statements
- `randomizedBlockingTwirl_perm_invariant`: exact permutation invariance of the average
- `randomizedBlockingTwirl_permutationCovariant`: d-generic CKR covariance (correction = `id`)
- `randomizedBlockingTwirl_preserves_conjTranspose`: Hermiticity preservation is inherited
  from `F` (needed by `ckr_security_reduction_exact`'s `hΔ_conj` hypothesis)

## Caveat (public seed)
The lemma treats the permutation seed as internal randomness of the averaged map.
A protocol that *announces* the seed is covariant only up to a classical relabeling
of the seed register; the covariance-up-to-relabeling generalization is future work
(it does not change the prefactor, since both real and ideal resources reveal the
same seed).
-/

open Quantum.Operators Matrix Quantum.Channels
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- Conjugation by the permutation representation, `ρ ↦ U_π ρ U_πᴴ`, as a linear map. -/
def permConjLin (d n : ℕ) [NeZero d] (π : Equiv.Perm (Fin n)) :
    Op (d ^ n) →ₗ[ℂ] Op (d ^ n) where
  toFun ρ := permutationRepresentation d n π * ρ * (permutationRepresentation d n π)ᴴ
  map_add' ρ σ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c ρ := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] lemma permConjLin_apply {d n : ℕ} [NeZero d] (π : Equiv.Perm (Fin n))
    (ρ : Op (d ^ n)) :
    permConjLin d n π ρ =
      permutationRepresentation d n π * ρ * (permutationRepresentation d n π)ᴴ :=
  rfl

/-- **Randomized blocking**: the average of a fixed post-processing map `F` over a
    uniformly random signal permutation applied before `F`.

    This is the honest channel model of "randomly permute the signals, then run the
    block-structured post-processing (e.g. advantage distillation)". -/
def randomizedBlockingTwirl {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    (F : Op (d ^ n) →ₗ[ℂ] Op dimOut) : Op (d ^ n) →ₗ[ℂ] Op dimOut :=
  (Nat.factorial n : ℂ)⁻¹ • ∑ π : Equiv.Perm (Fin n), F ∘ₗ permConjLin d n π

lemma randomizedBlockingTwirl_apply {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    (F : Op (d ^ n) →ₗ[ℂ] Op dimOut) (ρ : Op (d ^ n)) :
    randomizedBlockingTwirl F ρ =
      (Nat.factorial n : ℂ)⁻¹ •
        ∑ π : Equiv.Perm (Fin n),
          F (permutationRepresentation d n π * ρ *
              (permutationRepresentation d n π)ᴴ) := by
  simp only [randomizedBlockingTwirl, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, permConjLin_apply]

/-- Conjugating the input by any signal permutation `τ` leaves the randomized-blocking
    average unchanged: the group average absorbs `τ` by reindexing.

    This is the *exact* invariance `Φ(U_τ ρ U_τᴴ) = Φ(ρ)` — the correction channel in
    the CKR covariance hypothesis can be taken to be the identity. -/
theorem randomizedBlockingTwirl_perm_invariant {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (F : Op (d ^ n) →ₗ[ℂ] Op dimOut) (τ : Equiv.Perm (Fin n)) (ρ : Op (d ^ n)) :
    randomizedBlockingTwirl F
        (permutationRepresentation d n τ * ρ * (permutationRepresentation d n τ)ᴴ) =
      randomizedBlockingTwirl F ρ := by
  rw [randomizedBlockingTwirl_apply, randomizedBlockingTwirl_apply]
  congr 1
  -- Each summand at `π` equals the plain summand at `π * τ`.
  have key : ∀ π : Equiv.Perm (Fin n),
      permutationRepresentation d n π *
          (permutationRepresentation d n τ * ρ * (permutationRepresentation d n τ)ᴴ) *
          (permutationRepresentation d n π)ᴴ =
        permutationRepresentation d n (π * τ) * ρ *
          (permutationRepresentation d n (π * τ))ᴴ := by
    intro π
    rw [← permutationRepresentation_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp_rw [key]
  -- Reindex the group sum by right multiplication with `τ`.
  exact Equiv.sum_comp (Equiv.mulRight τ)
    (fun σ => F (permutationRepresentation d n σ * ρ *
      (permutationRepresentation d n σ)ᴴ))

/-- **Theorem 1 (d-generic form).** The randomized-blocking average of any fixed
    post-processing map is CKR permutation-covariant, with the identity channel as
    the correction map for every permutation.

    Consequence: the CKR/postselection coherent-attack lift applies to
    randomly-pre-blocked protocols at the **signal-level** de Finetti prefactor —
    the block structure of `F` (e.g. advantage distillation) never enters. -/
theorem randomizedBlockingTwirl_permutationCovariant {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (F : Op (d ^ n) →ₗ[ℂ] Op dimOut) :
    PermutationCovariant (randomizedBlockingTwirl F) where
  covariance π :=
    ⟨id, id_is_cptp dimOut,
      fun ρ => randomizedBlockingTwirl_perm_invariant F π ρ⟩

/-- The randomized-blocking average preserves conjugate transposition whenever the
    underlying post-processing map does. Together with
    `randomizedBlockingTwirl_permutationCovariant` this discharges both hypotheses
    of `ckr_security_reduction_exact` for randomly-pre-blocked protocols. -/
theorem randomizedBlockingTwirl_preserves_conjTranspose {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (F : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hF : ∀ M : Op (d ^ n), F Mᴴ = (F M)ᴴ) (M : Op (d ^ n)) :
    randomizedBlockingTwirl F Mᴴ = (randomizedBlockingTwirl F M)ᴴ := by
  rw [randomizedBlockingTwirl_apply, randomizedBlockingTwirl_apply,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hstar : star ((Nat.factorial n : ℂ))⁻¹ = ((Nat.factorial n : ℂ))⁻¹ := by
    rw [star_inv₀, star_natCast]
  rw [hstar]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  -- `(U M U ᴴ)ᴴ = U Mᴴ Uᴴ`, then push through `F` via `hF`.
  rw [← hF]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end Quantum.Symmetry
