import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired

/-!
# CKR Reference Commutant — the CKR de Finetti state as a permutation-character average

The Hilbert–Schmidt de Finetti reference state `ckrDeFinettiState d n` on `H^n = (ℂ^d)^{⊗n}`
is *in the image of the group algebra* `ℂ[S_n]`: explicitly, it is the permutation average
weighted by the characters `tr(U_σ) = d^{c(σ)}` of the tensor-factor permutation
representation,

  `τ_{H^n} = (g_{n,d} · n!)⁻¹ Σ_{σ ∈ S_n} tr(U_σ) · U_σ`,   `g_{n,d} = C(n + d²−1, d²−1)`.

This single identity carries the whole commutant theory used by the CKR reference-marginal
arguments: everything that commutes with all the `U_σ` automatically commutes with
`τ_{H^n}`, and every unitary in that commutant fixes `τ_{H^n}` under conjugation.  The
identity also explains the two symmetry facts already recorded in `Reference/Paired.lean`
(`ckrDeFinettiState_isPermutationInvariant_gen`, because `σ ↦ tr(U_σ)` is a class function,
and `ckrDeFinettiState_toOp_transpose`, because `U_σᵀ = U_{σ⁻¹}`).

The proved inclusion is `comm({U_σ}) ⊆ comm(τ_{H^n})`.  No reverse inclusion or strictness
claim is proved here.  `Reference/InvariantPurification.lean` relates the two commutants
to paired invariance and equality of the reference marginal, respectively.

## Main definitions
- This file defines no new data structures.

## Main statements
- `ckrDeFinettiState_permutationCharacterSum`: scalar-cleared character-average identity.
- `ckrDeFinettiState_toOp_eq_permutationCharacterAverage`: its normalized reading.
- `permutationRepresentation_mul_ckrDeFinettiState_toOp`: a single tensor-factor permutation
  commutes with the CKR marginal.
- `ckrDeFinettiState_commutes_of_commutes_permutationRepresentations`: the commutant
  inclusion.
- `ckrDeFinettiState_unitary_conj_eq_of_commutes_permutationRepresentation`: a unitary in
  that commutant fixes the CKR marginal under conjugation.

**References.**
- Christandl, König, Renner, *Postselection technique for quantum channels…* (2009),
  arXiv:0809.3019, `main.tex:307–338` (the state `τ_{H^n K^n}` proportional to the
  identity on `Sym^n(H ⊗ K)` and its marginal `τ_{H^n}`).
- Renner, *Security of Quantum Key Distribution* (2005), §4.3.2 and §6.4 (symmetric
  subspace, de Finetti reference states).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## The character-average identity -/

/-- **The CKR de Finetti state is the character-weighted permutation average, in
scalar-cleared form.**

  `g_{n,d} · n! · τ_{H^n} = Σ_{σ ∈ S_n} tr(U_σ) · U_σ`,   `g_{n,d} = C(n + d²−1, d²−1)`.

This is the form proofs use, since it carries no invertibility side condition.  It combines
`choose_smul_ckrDeFinettiState_eq_partialTraceB_symmetricProjectorPaired` (normalization of
the paired symmetric projector) with
`partialTraceB_symmetricProjectorPaired_eq_weighted_sum` (tracing out one copy of a
self-tensor `U_σ ⊗ U_σ` leaves `tr(U_σ) · U_σ`). -/
theorem ckrDeFinettiState_permutationCharacterSum (d n : ℕ) [NeZero d] [NeZero n] :
    ((Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) * (Nat.factorial n : ℂ)) •
        (ckrDeFinettiState d n).toOp =
      ∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ := by
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    ((Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) * (Nat.factorial n : ℂ)) •
        (ckrDeFinettiState d n).toOp =
        (Nat.factorial n : ℂ) •
          ((Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) •
            (ckrDeFinettiState d n).toOp) := by
      rw [smul_smul, mul_comm]
    _ = (Nat.factorial n : ℂ) • partialTraceB (symmetricProjectorPaired d n) := by
      rw [choose_smul_ckrDeFinettiState_eq_partialTraceB_symmetricProjectorPaired]
    _ = (Nat.factorial n : ℂ) •
          ((1 / (Nat.factorial n : ℂ)) •
            ∑ σ : Equiv.Perm (Fin n),
              (permutationRepresentation d n σ).trace •
                permutationRepresentation d n σ) := by
      rw [partialTraceB_symmetricProjectorPaired_eq_weighted_sum]
    _ = ∑ σ : Equiv.Perm (Fin n),
          (permutationRepresentation d n σ).trace • permutationRepresentation d n σ := by
      rw [smul_smul, mul_one_div_cancel hfact, one_smul]

/-- **The CKR de Finetti state is the normalized character-weighted permutation average.**

  `τ_{H^n} = (g_{n,d} · n!)⁻¹ Σ_{σ ∈ S_n} tr(U_σ) · U_σ`.

By `permutationRepresentation_trace_eq_fixed_card`, `tr(U_σ) = d^{c(σ)}` counts the tensor
words fixed by `σ`, so the weights are positive integers and in particular `τ_{H^n}` is a
*positive* combination of the permutation operators. -/
theorem ckrDeFinettiState_toOp_eq_permutationCharacterAverage
    (d n : ℕ) [NeZero d] [NeZero n] :
    (ckrDeFinettiState d n).toOp =
      ((Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) * (Nat.factorial n : ℂ))⁻¹ •
        ∑ σ : Equiv.Perm (Fin n),
          (permutationRepresentation d n σ).trace • permutationRepresentation d n σ := by
  have hchoose : (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) ≠ 0 := by
    exact_mod_cast (ckr_paired_dim_choose_pos d n).ne'
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [← ckrDeFinettiState_permutationCharacterSum d n, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero hchoose hfact), one_smul]

/-! ## The commutant of the CKR reference state -/

/-- Tensor-factor permutation representations commute with the CKR reference marginal.

This is `ckrDeFinettiState_isPermutationInvariant_gen` read as a commutation relation. -/
lemma permutationRepresentation_mul_ckrDeFinettiState_toOp
    (d n : ℕ) [NeZero d] [NeZero n] (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ * (ckrDeFinettiState d n).toOp =
      (ckrDeFinettiState d n).toOp * permutationRepresentation d n σ :=
  (Quantum.Symmetry.isPermutationInvariant_iff_commutes
    (ckrDeFinettiState d n)).mp (ckrDeFinettiState_isPermutationInvariant_gen d n) σ

/-- **Everything in the commutant of the permutation representation commutes with the CKR
reference marginal.**

Immediate from `ckrDeFinettiState_permutationCharacterSum`: the CKR marginal is a nonzero
scalar multiple of a linear combination of the `U_σ`, and the scalar cancels because
`Op (d ^ n)` has no zero smul divisors. -/
lemma ckrDeFinettiState_commutes_of_commutes_permutationRepresentations
    {d n : ℕ} [NeZero d] [NeZero n]
    (W : Op (d ^ n))
    (hW : ∀ σ : Equiv.Perm (Fin n),
      W * permutationRepresentation d n σ =
        permutationRepresentation d n σ * W) :
    W * (ckrDeFinettiState d n).toOp = (ckrDeFinettiState d n).toOp * W := by
  set K : ℂ :=
    (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) * (Nat.factorial n : ℂ) with hK
  have hK_ne : K ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (ckr_paired_dim_choose_pos d n).ne'
    · exact_mod_cast Nat.factorial_ne_zero n
  have hscaled : W * (K • (ckrDeFinettiState d n).toOp) =
      (K • (ckrDeFinettiState d n).toOp) * W := by
    rw [hK, ckrDeFinettiState_permutationCharacterSum d n]
    exact permutationRepresentation_trace_weighted_sum_commutes_of_commutes W hW
  rw [Matrix.mul_smul, Matrix.smul_mul] at hscaled
  exact smul_right_injective (Op (d ^ n)) hK_ne hscaled

/-- **A unitary in the commutant of the permutation representation fixes the CKR reference
marginal under conjugation.** -/
theorem ckrDeFinettiState_unitary_conj_eq_of_commutes_permutationRepresentation
    {d n : ℕ} [NeZero d] [NeZero n]
    (W : UnitaryOp (d ^ n))
    (hW : ∀ σ : Equiv.Perm (Fin n),
      W.toOp * permutationRepresentation d n σ =
        permutationRepresentation d n σ * W.toOp) :
    W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† = (ckrDeFinettiState d n).toOp :=
  Quantum.Operators.unitary_conj_eq_of_mul_comm W (ckrDeFinettiState d n).toOp
    (ckrDeFinettiState_commutes_of_commutes_permutationRepresentations W.toOp hW)

end Quantum.Channels

end -- noncomputable section
