import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness

/-!
# PGM Optimality — Perturbation Infrastructure for the KRS Lemma

This module hosts the perturbation-argument infrastructure used to prove the
Koenig–Renner–Schaffner dual-witness domination lemma
`InfoTheory.SmoothMinEntropy.pgmDualWitness_dominates`
in `PGMDualWitness.lean`.

The first construction is the *hard perturbed POVM*: given a POVM `M`, an index
`x₀`, and a projector `E`, we define

    `perturbedPovm M x₀ E y := (1 - E) * M y * (1 - E) + [y = x₀] · E`

and prove that it is again a POVM, i.e. each `perturbedPovm M x₀ E y` is PSD
(`perturbedPovm_posSemidef`) and `∑ y, perturbedPovm M x₀ E y = 1`
(`perturbedPovm_sum_eq_one`).  We also derive the primal-optimality consequence
`perturbedPovm_objective_le`, used downstream as a sup-bound input to the
domination lemma.

The second construction is the *small first-order perturbation*
`smallPerturbedPovm`, which replaces `E` by `εP` and adds the normalization
correction `(ε - ε²)P` at the distinguished outcome.

## Main definitions

- `perturbedPovm` : the perturbed POVM family.
- `smallPerturbedPovm` : the normalization-preserving first-order perturbation.

## Main statements

- `perturbedPovm_posSemidef` : each component is PSD.
- `perturbedPovm_sum_eq_one`  : the components sum to the identity.
- `perturbedPovm_objective_le` : primal-optimality sup-bound for the perturbed
  POVM's objective.
- `smallPerturbedPovm_posSemidef`, `smallPerturbedPovm_sum_eq_one`, and
  `smallPerturbedPovm_objective_le` : the corresponding facts for the small
  perturbation.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Sandwich PSD.**  `B * A * B` is PSD when `A` is PSD and `B` is Hermitian.
This is `Matrix.PosSemidef.conjTranspose_mul_mul_same` combined with the
Hermitian identity `B.conjTranspose = B`. -/
private lemma posSemidef_sandwich_of_isHermitian {n : ℕ} {B A : Op n}
    (hA : Matrix.PosSemidef A) (hB : B.IsHermitian) :
    Matrix.PosSemidef (B * A * B) := by
  have h := hA.conjTranspose_mul_mul_same B
  rwa [hB] at h

/-- The *perturbed POVM* used in the KRS optimality perturbation argument.

Given a POVM `M : X → Op n`, an index `x₀ : X`, and an operator `E : Op n`
(thought of as a small projector direction), define

    `perturbedPovm M x₀ E y = (1 - E) * M y * (1 - E) + [y = x₀] · E`.

When `E` is a Hermitian projector (`E * E = E`, `E.IsHermitian`) and every
`M y` is PSD with `∑ y, M y = 1`, the resulting family is again a POVM
(`perturbedPovm_posSemidef`, `perturbedPovm_sum_eq_one`). -/
noncomputable def perturbedPovm
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) (E : Op n) : X → Op n :=
  fun y => (1 - E) * M y * (1 - E) + (if y = x₀ then E else 0)

/-- Each component of `perturbedPovm` is PSD when `M y` and `E` are PSD and
`E` is Hermitian. -/
lemma perturbedPovm_posSemidef
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) {E : Op n}
    (hM : ∀ y, (M y).PosSemidef)
    (hE : E.PosSemidef) :
    ∀ y, (perturbedPovm M x₀ E y).PosSemidef := by
  intro y
  unfold perturbedPovm
  refine Matrix.PosSemidef.add ?_ ?_
  · -- `(1 - E) * M y * (1 - E)` is PSD: sandwich of a PSD by the Hermitian `1 - E`.
    have h1_sub_E_herm : ((1 : Op n) - E).IsHermitian :=
      Matrix.isHermitian_one.sub hE.isHermitian
    exact posSemidef_sandwich_of_isHermitian (hM y) h1_sub_E_herm
  · -- The `if`-summand: `E` or `0`, both PSD.
    split_ifs
    · exact hE
    · exact Matrix.PosSemidef.zero

/-- General normalization identity for the hard perturbation before imposing
idempotence on the direction. -/
private lemma perturbedPovm_sum_eq_sandwich_add
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) {E : Op n}
    (hM_sum : ∑ y, M y = 1) :
    ∑ y, perturbedPovm M x₀ E y = (1 - E) * (1 - E) + E := by
  unfold perturbedPovm
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ y, (1 - E) * M y * (1 - E)) = (1 - E) * (1 - E) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hM_sum, mul_one]
  have hsum2 : (∑ y : X, (if y = x₀ then E else 0)) = E := by
    simp [Finset.sum_ite_eq']
  rw [hsum1, hsum2]

/-- `∑ y, perturbedPovm M x₀ E y = 1` when `M` is a POVM (`∑ M = 1`) and `E`
is a (Hermitian) projector (`E * E = E`). -/
lemma perturbedPovm_sum_eq_one
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) {E : Op n}
    (hM_sum : ∑ y, M y = 1) (hE_proj : E * E = E) :
    ∑ y, perturbedPovm M x₀ E y = 1 := by
  rw [perturbedPovm_sum_eq_sandwich_add M x₀ hM_sum]
  have h_sq : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hE_proj, sub_self, sub_zero]
  rw [h_sq, sub_add_cancel]

/-- A Hermitian idempotent operator is positive semidefinite: `E = Eᴴ * E`,
which is PSD by `Matrix.posSemidef_conjTranspose_mul_self`. -/
private lemma posSemidef_of_isHermitian_of_isIdempotent {n : ℕ} {E : Op n}
    (hE : E.IsHermitian) (hE2 : E * E = E) : E.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self E
  rw [hE, hE2] at h
  exact h

/-- **Primal-optimality sup-bound for the perturbed POVM.**

Under the standing hypotheses of `pgmDualWitness_dominates` — each `M x` is
PSD and `∑ x M x = 1` — plus the extra data that `E` is a Hermitian
projector, the perturbed POVM is a valid element of the sSup-set defining
`povmGuessingProb ρ`, so its objective is bounded above by `povmGuessingProb ρ`:

    ∑ y, ((ρ.stateMap y).toOp * perturbedPovm M x₀ E y).trace.re
      ≤ povmGuessingProb ρ. -/
lemma perturbedPovm_objective_le
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (x₀ : X) {E : Op n}
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hE_herm : E.IsHermitian) (hE_proj : E * E = E) :
    (∑ y : X, ((ρ.stateMap y).toOp * perturbedPovm M x₀ E y).trace.re)
      ≤ povmGuessingProb ρ := by
  have hE_psd : E.PosSemidef :=
    posSemidef_of_isHermitian_of_isIdempotent hE_herm hE_proj
  have hP_psd : ∀ y, (perturbedPovm M x₀ E y).PosSemidef :=
    perturbedPovm_posSemidef M x₀ hM_psd hE_psd
  have hP_sum : ∑ y, perturbedPovm M x₀ E y = 1 :=
    perturbedPovm_sum_eq_one M x₀ hM_sum hE_proj
  have hP_feas : (perturbedPovm M x₀ E : X → Op n) ∈ povmFeasible :=
    ⟨fun y v => posSemidef_re_quadraticForm_nonneg (hP_psd y) v, hP_sum⟩
  rw [← povmObjective_eq_sum_state_mul ρ (perturbedPovm M x₀ E)]
  exact povmObjective_le_povmGuessingProb_of_mem ρ hP_feas

/-! ## Small first-order perturbation -/

/-- The small Yuen-Kennedy-Lax perturbation of a POVM in a projector direction.

This is written as the hard perturbation with `E = εP`, plus the correction
`(ε - ε²)P` at the distinguished outcome.  Equivalently,

`(smallPerturbedPovm M x₀ ε P) y =
  (1 - εP) * M y * (1 - εP) + [y = x₀] (2ε - ε²)P`.

The split form is useful because the hard-perturbation trace expansion applies
directly to the first summand. -/
noncomputable def smallPerturbedPovm
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) (ε : ℝ) (P : Op n) : X → Op n :=
  fun y => perturbedPovm M x₀ ((Complex.ofReal ε) • P) y
    + (if y = x₀ then (Complex.ofReal (ε - ε ^ 2)) • P else 0)

/-- A scaled idempotent squares by squaring the scalar. -/
private lemma scaled_idempotent_sq {n : ℕ} {ε : ℝ} {P : Op n}
    (hP_proj : P * P = P) :
    ((Complex.ofReal ε) • P) * ((Complex.ofReal ε) • P)
      = (Complex.ofReal (ε ^ 2)) • P := by
  calc
    ((Complex.ofReal ε) • P) * ((Complex.ofReal ε) • P)
        = (Complex.ofReal ε) • (P * ((Complex.ofReal ε) • P)) := by
            rw [Matrix.smul_mul]
    _ = (Complex.ofReal ε) • ((Complex.ofReal ε) • (P * P)) := by
            rw [Matrix.mul_smul]
    _ = (Complex.ofReal (ε ^ 2)) • P := by
            rw [smul_smul, hP_proj]
            congr 1
            rw [← Complex.ofReal_mul, pow_two]

/-- The algebraic normalization identity for the small perturbation. -/
private lemma smallPerturbedPovm_sum_algebra {n : ℕ} {ε : ℝ} {P : Op n}
    (hP_proj : P * P = P) :
    (1 - (Complex.ofReal ε) • P) * (1 - (Complex.ofReal ε) • P)
      + (Complex.ofReal ε) • P
      + (Complex.ofReal (ε - ε ^ 2)) • P = (1 : Op n) := by
  set E : Op n := (Complex.ofReal ε) • P with hEdef
  have hE_sq : E * E = (Complex.ofReal (ε ^ 2)) • P := by
    simpa [hEdef] using scaled_idempotent_sq (ε := ε) hP_proj
  have hsq : (1 - E) * (1 - E) = 1 - E - E + E * E := by
    noncomm_ring
  have hscalar :
      (Complex.ofReal (ε ^ 2)) • P
        + (Complex.ofReal (ε - ε ^ 2)) • P = E := by
    rw [hEdef, ← add_smul, ← Complex.ofReal_add]
    ring_nf
  calc
    (1 - (Complex.ofReal ε) • P) * (1 - (Complex.ofReal ε) • P)
        + (Complex.ofReal ε) • P
        + (Complex.ofReal (ε - ε ^ 2)) • P
        = (1 - E) * (1 - E) + E
          + (Complex.ofReal (ε - ε ^ 2)) • P := by
            simp [hEdef]
    _ = (1 - E - E + E * E) + E
          + (Complex.ofReal (ε - ε ^ 2)) • P := by rw [hsq]
    _ = 1 - E
          + ((Complex.ofReal (ε ^ 2)) • P
            + (Complex.ofReal (ε - ε ^ 2)) • P) := by
            rw [hE_sq]
            abel
    _ = 1 - E + E := by rw [hscalar]
    _ = (1 : Op n) := by abel

/-- Each component of the small perturbation is PSD for `0 ≤ ε ≤ 1`, provided
`P` is PSD. -/
lemma smallPerturbedPovm_posSemidef
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) {ε : ℝ} {P : Op n}
    (hM : ∀ y, (M y).PosSemidef)
    (hP : P.PosSemidef) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ y, (smallPerturbedPovm M x₀ ε P y).PosSemidef := by
  intro y
  unfold smallPerturbedPovm
  refine Matrix.PosSemidef.add ?_ ?_
  · unfold perturbedPovm
    refine Matrix.PosSemidef.add ?_ ?_
    · have hεP_herm : ((Complex.ofReal ε) • P).IsHermitian := by
        have hε_sa : IsSelfAdjoint (Complex.ofReal ε) := by
          change star (Complex.ofReal ε) = Complex.ofReal ε
          rw [Complex.star_def, Complex.conj_ofReal]
        exact hε_sa.smul hP.isHermitian
      have h1_sub_herm : ((1 : Op n) - (Complex.ofReal ε) • P).IsHermitian :=
        Matrix.isHermitian_one.sub hεP_herm
      exact posSemidef_sandwich_of_isHermitian (hM y) h1_sub_herm
    · split_ifs
      · exact Matrix.PosSemidef.smul hP (RCLike.ofReal_nonneg.mpr hε0)
      · exact Matrix.PosSemidef.zero
  · split_ifs
    · have hcoeff_nonneg : 0 ≤ ε - ε ^ 2 := by
        nlinarith [hε0, hε1]
      exact Matrix.PosSemidef.smul hP (RCLike.ofReal_nonneg.mpr hcoeff_nonneg)
    · exact Matrix.PosSemidef.zero

/-- The small perturbation is normalized when `M` is normalized and `P` is an
idempotent. -/
lemma smallPerturbedPovm_sum_eq_one
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (M : X → Op n) (x₀ : X) {ε : ℝ} {P : Op n}
    (hM_sum : ∑ y, M y = 1) (hP_proj : P * P = P) :
    ∑ y, smallPerturbedPovm M x₀ ε P y = 1 := by
  unfold smallPerturbedPovm
  rw [Finset.sum_add_distrib]
  rw [perturbedPovm_sum_eq_sandwich_add M x₀ hM_sum]
  have hsum_extra :
      (∑ y : X, (if y = x₀ then (Complex.ofReal (ε - ε ^ 2)) • P else 0))
        = (Complex.ofReal (ε - ε ^ 2)) • P := by
    simp [Finset.sum_ite_eq']
  rw [hsum_extra]
  exact smallPerturbedPovm_sum_algebra (ε := ε) hP_proj

/-- Primal-optimality upper bound for the small perturbation. -/
lemma smallPerturbedPovm_objective_le
    {X : Type*} [DecidableEq X] [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (x₀ : X) {ε : ℝ} {P : Op n}
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hP_psd : P.PosSemidef) (hP_proj : P * P = P)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∑ y : X, ((ρ.stateMap y).toOp * smallPerturbedPovm M x₀ ε P y).trace.re)
      ≤ povmGuessingProb ρ := by
  have hPovm_psd : ∀ y, (smallPerturbedPovm M x₀ ε P y).PosSemidef :=
    smallPerturbedPovm_posSemidef M x₀ hM_psd hP_psd hε0 hε1
  have hPovm_sum : ∑ y, smallPerturbedPovm M x₀ ε P y = 1 :=
    smallPerturbedPovm_sum_eq_one M x₀ hM_sum hP_proj
  have hPovm_feas : (smallPerturbedPovm M x₀ ε P : X → Op n) ∈ povmFeasible :=
    ⟨fun y v => posSemidef_re_quadraticForm_nonneg (hPovm_psd y) v, hPovm_sum⟩
  rw [← povmObjective_eq_sum_state_mul ρ (smallPerturbedPovm M x₀ ε P)]
  exact povmObjective_le_povmGuessingProb_of_mem ρ hPovm_feas

end InfoTheory.SmoothMinEntropy

end
