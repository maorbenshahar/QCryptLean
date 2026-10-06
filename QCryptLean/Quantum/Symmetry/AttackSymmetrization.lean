import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.InfoTheory.Measurement.POVM
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth

/-!
# Attack Symmetrization — Renner §6.4–6.5 collective-lift infrastructure

For a general attack `E : DensityOp (d^n) → DensityOp ((d^n) * e)`, define
the **input-symmetrized channel**

  E_avg(ρ) := (1/n!) Σ_{π ∈ Sₙ} E(U_π ρ U_π†)

which pre-averages conjugation by permutation unitaries over the input.

## Mathematical content

The collective-lift argument (Renner thesis §6.4–6.5) proceeds as follows:

1. For any general attack E on n rounds, E_avg has an explicit Kraus representation
   (hence is CPTP) whenever E has one (`channelPermAverage_isCPTP`).

2. For **permutation-invariant** input ρ (i.e. U_π ρ U_π† = ρ for all π, in
   particular for iid input σ^⊗n), the averaged channel equals the original:
   E_avg(ρ) = E(ρ) (`channelPermAverage_on_permInvariant_input`).

3. For any π ∈ Sₙ and any ρ, averaging over all permutations is unchanged by
   first applying U_π to the input (`channelPermAverage_is_permCovariant`):
   E_avg(U_π ρ U_π†) = E_avg(ρ).

The collective-product factorization `E(σ^⊗n) = (Φ_σ σ)^⊗n` — expressing the output
on iid input as an n-fold tensor power of a single-round map — is **not** provided in
this module. Permutation covariance of E_avg alone does not force round-independent
factorization: it is false for a general permutation-covariant channel on an iid input,
and a correct collective-lift needs the symmetric-pure-state / θ-decomposition of
Renner's exponential de Finetti (see the deletion note at the end of the file).

Points 1–3 are therefore what this module delivers: E_avg is CPTP, agrees with E on
iid (permutation-invariant) input, and is permutation-covariant. The collective
factorization required to lift the collective-attack Hmin bound to general attacks on
iid input is not established here.

## Main definitions

- `permConjInput`: apply U_π to the input of a general attack.
- `unitaryConjDensityOp`: conjugate a density operator by a permutation unitary U_π.
- `channelPermAverage`: the input-symmetrized attack E_avg(ρ) = (1/n!) Σ_π E(U_π ρ U_π†).

## Main statements

- `channelPermAverage_isCPTP`: the linear extension of E_avg is IsCPTP whenever
  E has a Kraus representation.
- `channelPermAverage_on_permInvariant_input`: E_avg(ρ) = E(ρ) when ρ is perm-invariant.
- `channelPermAverage_tensorPow_iid_eq`: E_avg(σ^⊗n) = E(σ^⊗n) for iid input.
- `channelPermAverage_is_permCovariant`: E_avg(U_π ρ U_π†) = E_avg(ρ) for all π.

The collective-product factorization on iid input is deliberately *not* a theorem here:
it is false for a general permutation-covariant channel (see the deletion note at the
end of the file) and is left to future work.

## References

- Renner (2005) §6.4–6.5 ("ket symmetrization" / collective-lift step).
- Tomamichel (2016) §6.5.3 (Corollary 7.1).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Quantum.Symmetry Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.Measurement
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry.AttackSymmetrization

/-!
## 1. Input conjugation by a single permutation
-/

/-- Conjugate a density operator on `(ℂ^d)^⊗n` by the permutation unitary U_π.

    `unitaryConjDensityOp π ρ := U_π ρ U_π†`

    This is again a valid density operator (Hermitian, PSD, trace 1) because
    conjugation by a unitary preserves all three properties. -/
noncomputable def unitaryConjDensityOp {d n : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (π : Equiv.Perm (Fin n)) (ρ : DensityOp (d ^ n)) : DensityOp (d ^ n) :=
  let U := permutationRepresentation d n π
  let hU := permutationRepresentation_unitary d n π
  let hpsd_conj : Matrix.PosSemidef (U * ρ.toOp * U†) :=
    (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same U
  ⟨⟨⟨U * ρ.toOp * U†,
    hpsd_conj.isHermitian⟩,
    fun x => by
      unfold quadraticForm
      exact le_trans (le_refl _)
        (RCLike.nonneg_iff.mp (hpsd_conj.dotProduct_mulVec_nonneg x)).1⟩,
   by
    rw [Matrix.trace_mul_comm (U * ρ.toOp), ← Matrix.mul_assoc,
        hU.1, Matrix.one_mul, ρ.trace_one]⟩

/-- Conjugate the input of a general attack by the permutation unitary U_π.

    `permConjInput E π ρ := E(U_π ρ U_π†) = E (unitaryConjDensityOp π ρ)`

    This is a CPTP map when E is CPTP, since conjugation by a unitary is CPTP
    and composition of CPTP maps is CPTP. -/
noncomputable def permConjInput {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (π : Equiv.Perm (Fin n))
    (ρ : DensityOp (d ^ n)) : DensityOp ((d ^ n) * e) :=
  E (unitaryConjDensityOp π ρ)

/-- `unitaryConjDensityOp` recovers the same `toOp` expression as the inline conjugation
    used in `permConjInput`. -/
theorem unitaryConjDensityOp_toOp {d n : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (π : Equiv.Perm (Fin n)) (ρ : DensityOp (d ^ n)) :
    (unitaryConjDensityOp π ρ).toOp =
      permutationRepresentation d n π * ρ.toOp * (permutationRepresentation d n π)† := by
  rfl

/-!
## 2. Input-symmetrized channel
-/

/-- The input-symmetrized attack channel.

For a general attack `E : DensityOp (d^n) → DensityOp ((d^n) * e)` and density
operator ρ, the input-symmetrized channel averages conjugation by all permutation
unitaries over the input:

  E_avg(ρ) := (1/n!) Σ_{π ∈ Sₙ} E(U_π ρ U_π†)

This is a valid density operator because it is a uniform convex combination of
density operators (each `E(U_π ρ U_π†)` is a density operator). -/
noncomputable def channelPermAverage {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (ρ : DensityOp (d ^ n)) : DensityOp ((d ^ n) * e) :=
  let card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  -- Enumerate Sₙ as Fin(n!): first cast Fin(n!) to Fin(|Sₙ|), then use equivFin.symm.
  let enum : Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
    (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  DensityOp.fromEnsemble
    (fun i => 1 / (Nat.factorial n : ℝ))
    (fun i => permConjInput E (enum i) ρ)
    (fun _ => by positivity)
    (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)

/-!
## 3. Key structural theorems
-/

/-- Explicit Kraus representation for the input-symmetrized channel.

Given a Kraus representation `K` for `E`, the averaged channel `channelPermAverage E`
has explicit Kraus operators `(1/√(n!)) · Kₖ · U_π` for all k and π ∈ Sₙ, indexed by
`Fin (K.numOps * n!)` via `finProdFinEquiv`.

The completeness relation holds because
  ∑_{π,k} (Kₖ · Uπ)† (Kₖ · Uπ) = ∑_{π,k} Uπ† Kₖ† Kₖ Uπ
  = (1/n!) ∑_π Uπ† (n! · I) Uπ = I. -/
noncomputable def channelPermAverage_kraus {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    [NeZero e] [NeZero ((d ^ n) * e)]
    (K : KrausRepresentation (d ^ n) (d ^ n * e)) :
    KrausRepresentation (d ^ n) (d ^ n * e) :=
  let card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  let enum : Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
    (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  let U : Equiv.Perm (Fin n) → Op (d ^ n) :=
    permutationRepresentation d n
  let c_r : ℝ := Real.sqrt (1 / (Nat.factorial n : ℝ))
  let c : ℂ := (c_r : ℂ)
  let pair : Fin (K.numOps * Nat.factorial n) → Fin K.numOps × Fin (Nat.factorial n) :=
    finProdFinEquiv.symm
  have h_star_c : star c = c := by simp [c, Complex.conj_ofReal]
  have h_c_sq : c * c = (1 / Nat.factorial n : ℂ) := by
    have hpos : (0 : ℝ) ≤ 1 / (Nat.factorial n : ℝ) :=
      div_nonneg zero_le_one (Nat.cast_nonneg _)
    have hr : c_r * c_r = 1 / (Nat.factorial n : ℝ) := Real.mul_self_sqrt hpos
    change (c_r : ℂ) * c_r = 1 / (Nat.factorial n : ℂ)
    rw [← Complex.ofReal_mul, hr, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast]
  { numOps := K.numOps * Nat.factorial n
    operators := fun a => c • (K.operators (pair a).1 * U (enum (pair a).2))
    completeness := by
      have hU : ∀ τ : Equiv.Perm (Fin n), (U τ)† * U τ = 1 :=
        fun τ => (permutationRepresentation_unitary d n τ).1
      change ∑ a : Fin (K.numOps * Nat.factorial n),
          (c • (K.operators (pair a).1 * U (enum (pair a).2)))† *
            (c • (K.operators (pair a).1 * U (enum (pair a).2))) =
        (1 : Op (d ^ n))
      rw [show
          (∑ a : Fin (K.numOps * Nat.factorial n),
            (c • (K.operators (pair a).1 * U (enum (pair a).2)))† *
              (c • (K.operators (pair a).1 * U (enum (pair a).2)))) =
          ∑ p : Fin K.numOps × Fin (Nat.factorial n),
            (c • (K.operators p.1 * U (enum p.2)))† *
              (c • (K.operators p.1 * U (enum p.2))) by
        exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)]
      simp only [conjTranspose_smul, h_star_c]
      simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [Fintype.sum_prod_type_right]
      have h_comp_term : ∀ j : Fin (Nat.factorial n),
          ∑ i : Fin K.numOps,
            (c * c) • ((K.operators i * U (enum j))† * (K.operators i * U (enum j))) =
          (c * c) • (1 : Op (d ^ n)) := by
        intro j
        rw [← Finset.smul_sum]
        congr 1
        calc
          ∑ i : Fin K.numOps,
              (K.operators i * U (enum j))† * (K.operators i * U (enum j))
              = ∑ i : Fin K.numOps,
                  (U (enum j))† * ((K.operators i)† * K.operators i) * U (enum j) := by
                apply Finset.sum_congr rfl
                intro i _
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = (U (enum j))† *
                (∑ i : Fin K.numOps, (K.operators i)† * K.operators i) *
                U (enum j) := by
                rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = (1 : Op (d ^ n)) := by
                rw [K.completeness, Matrix.mul_one, hU]
      simp_rw [h_comp_term]
      have hfact : (Nat.factorial n : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos n).ne'
      ext a b
      by_cases hab : a = b
      · subst b
        simp [h_c_sq, hfact]
      · simp [h_c_sq, hab] }

/-- The Kraus map of `channelPermAverage_kraus K` equals `channelPermAverage E` on
    every density operator, whenever `K` is a Kraus representation of `E`. -/
theorem channelPermAverage_kraus_spec {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    [NeZero e] [NeZero ((d ^ n) * e)]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (K : KrausRepresentation (d ^ n) (d ^ n * e))
    (hK : ∀ ρ : DensityOp (d ^ n), krausMapFintype K.operators ρ.toOp = (E ρ).toOp)
    (ρ : DensityOp (d ^ n)) :
    krausMapFintype (channelPermAverage_kraus K).operators ρ.toOp =
      (channelPermAverage E ρ).toOp := by
  let card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  let enum : Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
    (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  let U : Equiv.Perm (Fin n) → Op (d ^ n) :=
    permutationRepresentation d n
  let c_r : ℝ := Real.sqrt (1 / (Nat.factorial n : ℝ))
  let c : ℂ := (c_r : ℂ)
  have h_star_c : star c = c := by simp [c, Complex.conj_ofReal]
  have h_c_sq : c * c = (1 / Nat.factorial n : ℂ) := by
    have hpos : (0 : ℝ) ≤ 1 / (Nat.factorial n : ℝ) :=
      div_nonneg zero_le_one (Nat.cast_nonneg _)
    have hr : c_r * c_r = 1 / (Nat.factorial n : ℝ) := Real.mul_self_sqrt hpos
    change (c_r : ℂ) * c_r = 1 / (Nat.factorial n : ℂ)
    rw [← Complex.ofReal_mul, hr, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast]
  let pair : Fin (K.numOps * Nat.factorial n) → Fin K.numOps × Fin (Nat.factorial n) :=
    finProdFinEquiv.symm
  change (∑ a : Fin (K.numOps * Nat.factorial n),
      (c • (K.operators (pair a).1 * U (enum (pair a).2))) * ρ.toOp *
        (c • (K.operators (pair a).1 * U (enum (pair a).2)))†) =
    (channelPermAverage E ρ).toOp
  rw [show
      (∑ a : Fin (K.numOps * Nat.factorial n),
        (c • (K.operators (pair a).1 * U (enum (pair a).2))) * ρ.toOp *
          (c • (K.operators (pair a).1 * U (enum (pair a).2)))†) =
      ∑ p : Fin K.numOps × Fin (Nat.factorial n),
        (c • (K.operators p.1 * U (enum p.2))) * ρ.toOp *
          (c • (K.operators p.1 * U (enum p.2)))† by
    exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)]
  simp only [conjTranspose_smul, h_star_c]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rw [Fintype.sum_prod_type_right]
  rw [h_c_sq]
  have h_term : ∀ j : Fin (Nat.factorial n),
      ∑ i : Fin K.numOps,
        (1 / Nat.factorial n : ℂ) •
          (K.operators i *
            (U (enum j) * (ρ.toOp * ((U (enum j))† * (K.operators i)†)))) =
        (1 / Nat.factorial n : ℂ) • (E (unitaryConjDensityOp (enum j) ρ)).toOp := by
    intro j
    rw [← Finset.smul_sum]
    congr 1
    have hKj := hK (unitaryConjDensityOp (enum j) ρ)
    simpa [krausMapFintype, unitaryConjDensityOp_toOp, U, Matrix.mul_assoc] using hKj
  simp_rw [h_term]
  unfold channelPermAverage
  simp only [DensityOp.fromEnsemble, InfoTheory.Measurement.ensembleAverage]
  apply Finset.sum_congr rfl
  intro i _
  simp [enum, permConjInput]

/-- The linear extension of the input-symmetrized channel is CPTP.

If `E` has a Kraus representation `K`, then the averaged channel `channelPermAverage E`
admits the explicit Kraus representation `channelPermAverage_kraus K`, witnessing IsCPTP.
The explicit operators are `(1/√(n!)) · Kₖ · U_π` for all k and π ∈ Sₙ. -/
theorem channelPermAverage_isCPTP {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    [NeZero e] [NeZero ((d ^ n) * e)]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (K : KrausRepresentation (d ^ n) (d ^ n * e))
    (hK : ∀ ρ : DensityOp (d ^ n), krausMapFintype K.operators ρ.toOp = (E ρ).toOp) :
    ∃ (K_avg : KrausRepresentation (d ^ n) (d ^ n * e)),
      ∀ ρ : DensityOp (d ^ n),
        krausMapFintype K_avg.operators ρ.toOp = (channelPermAverage E ρ).toOp :=
  ⟨channelPermAverage_kraus K, channelPermAverage_kraus_spec E K hK⟩

/-- For permutation-invariant input, the input-symmetrized channel equals the original.

For ρ satisfying `IsPermutationInvariant ρ` (i.e. U_π ρ U_π† = ρ for all π ∈ Sₙ),
each term in the sum `E(U_π ρ U_π†) = E(ρ)`, so the average equals E(ρ):

  E_avg(ρ) = (1/n!) Σ_π E(U_π ρ U_π†) = (1/n!) Σ_π E(ρ) = E(ρ).

In particular, for iid input σ^⊗n (which satisfies `tensorPow_isPermutationInvariant`),
E_avg(σ^⊗n) = E(σ^⊗n). -/
theorem channelPermAverage_on_permInvariant_input
    {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (ρ : DensityOp (d ^ n))
    (hinv : IsPermutationInvariant ρ) :
    channelPermAverage E ρ = E ρ := by
  have hconj : ∀ σ : Equiv.Perm (Fin n), unitaryConjDensityOp σ ρ = ρ := by
    intro σ
    apply DensityOp.ext
    rw [unitaryConjDensityOp_toOp]
    exact hinv σ
  apply DensityOp.ext
  unfold channelPermAverage DensityOp.fromEnsemble ensembleAverage permConjInput
  simp only [hconj, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp [smul_smul, Nat.factorial_ne_zero]

/-- The input-symmetrized channel equals the original on iid input σ^⊗n.

Corollary of `channelPermAverage_on_permInvariant_input` and
`tensorPow_isPermutationInvariant`. -/
theorem channelPermAverage_tensorPow_iid_eq
    {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (σ : DensityOp d) :
    channelPermAverage E (σ.tensorPowGen n) = E (σ.tensorPowGen n) := by
  exact channelPermAverage_on_permInvariant_input E (σ.tensorPowGen n)
    (tensorPow_isPermutationInvariant σ)

/-- The input-symmetrized channel is permutation-covariant on the input.

For any π ∈ Sₙ and any density operator ρ:

  E_avg(U_π ρ U_π†) = E_avg(ρ).

The proof: in the sum `(1/n!) Σ_τ E(U_τ (U_π ρ U_π†) U_τ†)
= (1/n!) Σ_τ E(U_{τ∘π} ρ U_{τ∘π}†)`, substituting σ = τ ∘ π gives
`(1/n!) Σ_σ E(U_σ ρ U_σ†) = E_avg(ρ)`. -/
theorem channelPermAverage_is_permCovariant
    {d n e : ℕ} [NeZero d] [NeZero (d ^ n)] [NeZero n]
    (E : DensityOp (d ^ n) → DensityOp ((d ^ n) * e))
    (ρ : DensityOp (d ^ n))
    (π : Equiv.Perm (Fin n)) :
    channelPermAverage E (unitaryConjDensityOp π ρ) = channelPermAverage E ρ := by
  have hcomp : ∀ τ : Equiv.Perm (Fin n),
      unitaryConjDensityOp τ (unitaryConjDensityOp π ρ) =
        unitaryConjDensityOp (τ * π) ρ := by
    intro τ
    apply DensityOp.ext
    rw [unitaryConjDensityOp_toOp, unitaryConjDensityOp_toOp, unitaryConjDensityOp_toOp]
    rw [← permutationRepresentation_mul]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  let card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  let enum : Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
    (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  let reindex : Fin (Nat.factorial n) ≃ Fin (Nat.factorial n) :=
    { toFun := fun x => enum.symm (enum x * π)
      invFun := fun x => enum.symm (enum x * π⁻¹)
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc] }
  let g : Fin (Nat.factorial n) → Op (d ^ n * e) :=
    fun x => ((Nat.factorial n : ℂ)⁻¹) • (E (unitaryConjDensityOp (enum x) ρ)).toOp
  have hsum : (∑ x, g (reindex x)) = ∑ x, g x :=
    Fintype.sum_equiv reindex (fun x => g (reindex x)) g (by intro x; rfl)
  apply DensityOp.ext
  unfold channelPermAverage DensityOp.fromEnsemble ensembleAverage permConjInput
  simp only [hcomp]
  simpa [g, reindex, enum] using hsum

-- A tensor-power collective-factorization statement for `channelPermAverage` — permutation
-- covariance of E_avg forcing round-independent factorization on iid input — is FALSE in
-- general: a permutation-covariant channel on a permutation-invariant input is not the same as
-- a tensor product of single-round channels. A correct collective-lift theorem needs additional
-- structure (e.g. the symmetric pure-state / θ-decomposition of Renner's exponential de Finetti)
-- mapping general attacks to collective attacks at the level of the de Finetti decomposition,
-- not at the level of permutation-averaged channels on iid inputs (Renner §6.4 lem:PEsec /
-- §6.5 thm:main).

end Quantum.Symmetry.AttackSymmetrization

end -- noncomputable section
