import QCryptLean.Quantum.Channels.CPTP.CKRBound.FullRank
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Commutant
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Purification
import QCryptLean.Quantum.Metrics.SameAncillaStabilizer
import QCryptLean.Quantum.Metrics.SameAncillaTransport

/-!
# CKR Invariant Purifications — the reference marginal of a paired-invariant purification

`IsCKRDeFinettiPurification τ` prescribes only the *purified* marginal
`Tr_R τ = τ_{H^n} = ckrDeFinettiState d n`.  The reference marginal `Tr_{H^n} τ` is free up
to a unitary, so asking for it is asking a genuine question.  This file answers it at the
square reference dimension `dim R = d^n`, which is the minimal one
(`isCKRDeFinettiPurification_dimR_ge`) and the dimension used by `IsPairedPermInvariant`.

## The result and its shape

At `dim R = d^n` every CKR purification is `rightTensorUnitaryConj W` of the canonical one
(`ckrDeFinetti_squareAncilla_unitary_transport`), and the reference marginal is then
`W τ_{H^n} W†` — using that `τ_{H^n}` is transpose-invariant.  So the whole question is
*where `W` sits*:

| condition on `W`             | consequence                                            |
|---|---|
| none                         | `Tr_{H^n} τ` is a unitary conjugate of `τ_{H^n}`, hence |
|                              | isospectral to it and positive definite                |
| commutes with `τ_{H^n}`      | `Tr_{H^n} τ = τ_{H^n}` — and this is *exactly* the      |
|                              | condition for that identity                            |
| commutes with every `U_σ`    | `τ` is paired-permutation-invariant — and this too is   |
|                              | exactly the condition                                  |

The commutant of `{U_σ}` is contained in the commutant of `τ_{H^n}`
(`ckrDeFinettiState_commutes_of_commutes_permutationRepresentations`, because `τ_{H^n}` is a
character-weighted average of the `U_σ`), which is why paired permutation invariance
*implies* the reference-marginal identity.  The two equivalences in the table characterize
these properties separately.  A strictness example distinguishing them is not proved here.

## What the cited source does and does not give

Christandl–König–Renner construct *one* symmetric purification: with
`𝒩 ≅ Sym^n(H ⊗ K)` and `{|ν_i⟩}` an eigenbasis, `|Ψ⟩ ∝ Σ_i |ν_i⟩ ⊗ |ν_i⟩` purifies the state
proportional to the identity on `Sym^n(H ⊗ K)`
(arXiv:0809.3019, `main.tex:319–347`, Lemma `\label{lem:extractpart}`; the
reference state itself is `main.tex:299–312`).  That is an *existence* statement about a
particular purification.  The theorems here are statements about an **arbitrary**
paired-permutation-invariant purification, and they are not in the cited source; the proof
is the commutant argument above, assembled from the library's own stabilizer and
permutation-representation facts.

## Why the paired action, and not the signal action

`Quantum.TensorProducts.partialTraceA_tensor_one_unitary_conj` says that signal-side
unitary conjugation leaves the reference marginal unchanged.  That partial-trace identity
alone imposes no condition on the reference marginal.  It does not classify pure CKR states
satisfying `IsSignalPermInvariant`, which is a separate full-state condition.  The argument
below instead uses paired invariance to constrain the reference transport `W`.

## Invariant operators versus invariant kets

`IsPairedPermInvariant` is invariance of the *density operator* under conjugation by
`U_σ ⊗ U_σ`.  For a pure `τ` this is invariance of the ket only up to a phase, and that
phase is exactly what the projective step below has to remove.  It is removed using
`tr(U_σ) = d^{c(σ)} ≠ 0` (`permutationRepresentation_trace_ne_zero`): the phase cannot be
discarded by fiat, and for a traceless paired unitary the argument would not close.

## Main definitions
- This file defines no new data structures.

## Main statements
- `ckrDeFinettiCanonicalPurification_isPairedPermInvariant`: the canonical purification is
  itself paired-permutation-invariant, giving an explicit witness for
  `ckrDeFinetti_dn_equivariant_purification_exists`.
- `ckrDeFinetti_isPairedPermInvariant_iff_referenceUnitary_commutes` and
  `ckrDeFinetti_isPairedPermInvariant_iff_exists_commutant_transport`: paired invariance is
  exactly transport by a unitary in the commutant of the permutation representation.
- `ckrDeFinetti_partialTraceA_of_pairedPermInvariant`: **any** paired-permutation-invariant
  CKR purification at the canonical reference dimension has the CKR marginal on *both*
  tensor factors.
- `ckrDeFinetti_squareAncilla_partialTraceA_mem_unitary_orbit` and
  `ckrDeFinetti_squareAncilla_partialTraceA_toOp_posDef`: what holds without any invariance.
- `ckrDeFinetti_partialTraceA_toOp_eq_iff_referenceUnitary_commutes` and
  `ckrDeFinetti_exists_squareAncilla_purification_partialTraceA_ne`: the sharp condition, and
  the failure of the conclusion for a transport outside the commutant of `τ_{H^n}`.

**References.**
- Christandl, König, Renner (2009), arXiv:0809.3019, `main.tex:265–347`
  (post-selection theorem, reference state, `lem:extractpart`).
- Renner, *Security of Quantum Key Distribution* (2005), §4.2.2 (purification freedom),
  §4.3.2 and §6.4 (symmetric subspace and de Finetti reference states).
- Watrous (2018), Theorem 2.21 (isometric equivalence of purifications).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open Quantum.Metrics.KitaevWatrousPurification
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## The transported reference marginal -/

/-- Right-unitary transports of the canonical CKR purification have conjugated
`partialTraceA` marginal.

The generic computation is
`Quantum.Metrics.partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity`, which
produces `W τ_{H^n}ᵀ W†`; the transpose disappears by
`ckrDeFinettiState_toOp_transpose`. -/
lemma ckrDeFinettiCanonicalPurification_partialTraceA_rightTensorUnitaryConj_toOp
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (W : UnitaryOp (d ^ n)) :
    partialTraceA
        (Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp) =
      W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† := by
  have hcanon : ckrDeFinettiCanonicalPurification d n =
      sameAncillaPurificationDensity (ckrDeFinettiState d n) := rfl
  rw [hcanon,
    Quantum.Metrics.partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity,
    ckrDeFinettiState_toOp_transpose]

/-! ## The canonical purification is paired-invariant -/

/-- **The canonical CKR purification is paired-permutation-invariant.**

Since `U_σ` commutes with `τ_{H^n}` and satisfies `U_σᵀ = U_σ†`, the paired action fixes
`vec(√τ_{H^n})` outright.  Together with
`ckrDeFinettiCanonicalPurification_isCKRDeFinettiPurification` this exhibits an explicit
witness for `ckrDeFinetti_dn_equivariant_purification_exists`, whose existing proof goes
through the abstract symmetric-purification construction instead. -/
theorem ckrDeFinettiCanonicalPurification_isPairedPermInvariant
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)] :
    IsPairedPermInvariant (ckrDeFinettiCanonicalPurification d n) := fun σ =>
  sameAncillaPurificationDensity_paired_fixed_of_commutes
    (ckrDeFinettiState d n) (permutationRepresentation d n σ)
    (permutationRepresentation_unitary d n σ)
    (permutationRepresentation_mul_ckrDeFinettiState_toOp d n σ)
    ((permutationRepresentation_transpose d n σ).trans
      (permutationRepresentation_inv d n σ))

/-! ## Paired invariance pins the reference unitary into the commutant -/

/-- Paired permutation invariance of a right-unitary transport forces reference unitary
conjugation to preserve each permutation representation up to a phase.

This is the step that uses positive definiteness of `τ_{H^n}`
(`ckrDeFinettiState_toOp_posDef`): a pure state determines its ket only up to phase, and the
full-rank stabilizer lemma is what converts the ket-level ambiguity into a *scalar* on the
reference side. -/
lemma ckrDeFinetti_referenceUnitary_projective_conj_permutationRepresentation_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hτ_paired : IsPairedPermInvariant τ)
    (σ : Equiv.Perm (Fin n)) :
    ∃ α : ℂ,
      W.toOp * permutationRepresentation d n σ * W.toOp† =
        α • permutationRepresentation d n σ := by
  have hfixed :
      Op.tensor (permutationRepresentation d n σ) (permutationRepresentation d n σ) *
            Quantum.TensorProducts.rightTensorUnitaryConj W
              (sameAncillaPurificationDensity (ckrDeFinettiState d n)).toOp *
          (Op.tensor (permutationRepresentation d n σ)
            (permutationRepresentation d n σ))† =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity (ckrDeFinettiState d n)).toOp := by
    simpa only [ckrDeFinettiCanonicalPurification, htransport] using hτ_paired σ
  exact
    sameAncillaPurificationDensity_projective_right_unitary_of_paired_fixed
      (ckrDeFinettiState d n) (permutationRepresentation d n σ) W
      (ckrDeFinettiState_toOp_posDef d n)
      (permutationRepresentation_unitary d n σ)
      (permutationRepresentation_mul_ckrDeFinettiState_toOp d n σ)
      ((permutationRepresentation_transpose d n σ).trans
        (permutationRepresentation_inv d n σ))
      hfixed

/-- Paired permutation invariance of a right-unitary transport forces the transporting
unitary to commute with every tensor-factor permutation.

The phase from the projective step is removed by the nonvanishing character
`tr(U_σ) = d^{c(σ)} ≠ 0`. -/
lemma ckrDeFinetti_referenceUnitary_commutes_permutationRepresentation_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hτ_paired : IsPairedPermInvariant τ)
    (σ : Equiv.Perm (Fin n)) :
    W.toOp * permutationRepresentation d n σ =
      permutationRepresentation d n σ * W.toOp :=
  Quantum.Operators.unitary_commutes_of_projective_conj_of_trace_ne_zero W
    (permutationRepresentation d n σ)
    (permutationRepresentation_trace_ne_zero d n σ)
    (ckrDeFinetti_referenceUnitary_projective_conj_permutationRepresentation_of_pairedPermInvariant
      τ W htransport hτ_paired σ)

/-- Conversely, a transport by a unitary in the commutant of the permutation representation
is paired-permutation-invariant. -/
lemma ckrDeFinetti_pairedPermInvariant_of_referenceUnitary_commutes_permutationRepresentation
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hW : ∀ σ : Equiv.Perm (Fin n),
      W.toOp * permutationRepresentation d n σ =
        permutationRepresentation d n σ * W.toOp) :
    IsPairedPermInvariant τ := by
  intro σ
  have hcanon : ckrDeFinettiCanonicalPurification d n =
      sameAncillaPurificationDensity (ckrDeFinettiState d n) := rfl
  rw [htransport, hcanon]
  exact rightTensorUnitaryConj_paired_fixed_of_commutes
    (ckrDeFinettiState d n) (permutationRepresentation d n σ) W
    (permutationRepresentation_unitary d n σ)
    (permutationRepresentation_mul_ckrDeFinettiState_toOp d n σ)
    ((permutationRepresentation_transpose d n σ).trans
      (permutationRepresentation_inv d n σ))
    (hW σ).symm

/-- **Paired permutation invariance of a transport is exactly commutant membership of the
transporting unitary.** -/
theorem ckrDeFinetti_isPairedPermInvariant_iff_referenceUnitary_commutes
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp) :
    IsPairedPermInvariant τ ↔
      ∀ σ : Equiv.Perm (Fin n),
        W.toOp * permutationRepresentation d n σ =
          permutationRepresentation d n σ * W.toOp :=
  ⟨fun hτ_paired σ =>
      ckrDeFinetti_referenceUnitary_commutes_permutationRepresentation_of_pairedPermInvariant
        τ W htransport hτ_paired σ,
    ckrDeFinetti_pairedPermInvariant_of_referenceUnitary_commutes_permutationRepresentation
      τ W htransport⟩

/-- **Classification of the paired-invariant CKR purifications at the canonical reference
dimension**: they are precisely the transports of the canonical purification by a unitary
commuting with every tensor-factor permutation. -/
theorem ckrDeFinetti_isPairedPermInvariant_iff_exists_commutant_transport
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ) :
    IsPairedPermInvariant τ ↔
      ∃ W : UnitaryOp (d ^ n),
        (∀ σ : Equiv.Perm (Fin n),
          W.toOp * permutationRepresentation d n σ =
            permutationRepresentation d n σ * W.toOp) ∧
        τ.toOp =
          Quantum.TensorProducts.rightTensorUnitaryConj W
            (ckrDeFinettiCanonicalPurification d n).toOp := by
  obtain ⟨W, htransport⟩ := ckrDeFinetti_squareAncilla_unitary_transport τ hτ
  refine ⟨fun hτ_paired => ⟨W, ?_, htransport⟩, fun ⟨V, hV, htransportV⟩ => ?_⟩
  · exact (ckrDeFinetti_isPairedPermInvariant_iff_referenceUnitary_commutes
      τ W htransport).mp hτ_paired
  · exact (ckrDeFinetti_isPairedPermInvariant_iff_referenceUnitary_commutes
      τ V htransportV).mpr hV

/-- Paired permutation invariance of a right-unitary transport of the canonical CKR
purification forces the reference unitary into the CKR marginal commutant. -/
theorem ckrDeFinetti_referenceUnitary_commutes_ckrMarginal_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hτ_paired : IsPairedPermInvariant τ) :
    W.toOp * (ckrDeFinettiState d n).toOp =
      (ckrDeFinettiState d n).toOp * W.toOp :=
  ckrDeFinettiState_commutes_of_commutes_permutationRepresentations W.toOp
    (fun σ =>
      ckrDeFinetti_referenceUnitary_commutes_permutationRepresentation_of_pairedPermInvariant
        τ W htransport hτ_paired σ)

/-- Conjugation by the reference unitary from a paired-invariant transported canonical CKR
purification fixes the CKR marginal. -/
theorem ckrDeFinetti_referenceUnitary_conj_fixes_ckrMarginal_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hτ_paired : IsPairedPermInvariant τ) :
    W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† =
      (ckrDeFinettiState d n).toOp :=
  Quantum.Operators.unitary_conj_eq_of_mul_comm W (ckrDeFinettiState d n).toOp
    (ckrDeFinetti_referenceUnitary_commutes_ckrMarginal_of_pairedPermInvariant
      τ W htransport hτ_paired)

/-! ## The reference-marginal theorem -/

/-- A paired-permutation-invariant CKR purification has equal operator marginals at the
canonical reference dimension. -/
lemma ckrDeFinetti_partialTraceA_toOp_eq_partialTraceB_toOp_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ)
    (hτ_paired : IsPairedPermInvariant τ) :
    τ.partialTraceA.toOp = τ.partialTraceB.toOp := by
  haveI : NeZero (d ^ n * d ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (d ^ n)) (NeZero.ne (d ^ n))⟩
  obtain ⟨W, htransport⟩ := ckrDeFinetti_squareAncilla_unitary_transport τ hτ
  have hfix :
      W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† =
        (ckrDeFinettiState d n).toOp :=
    ckrDeFinetti_referenceUnitary_conj_fixes_ckrMarginal_of_pairedPermInvariant
      τ W htransport hτ_paired
  have hmarginal : partialTraceB τ.toOp = (ckrDeFinettiState d n).toOp :=
    congrArg (fun σ : DensityOp (d ^ n) => σ.toOp) hτ.marginal
  change partialTraceA τ.toOp = partialTraceB τ.toOp
  calc
    partialTraceA τ.toOp =
        partialTraceA
          (Quantum.TensorProducts.rightTensorUnitaryConj W
            (ckrDeFinettiCanonicalPurification d n).toOp) := by
      rw [htransport]
    _ = W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† :=
      ckrDeFinettiCanonicalPurification_partialTraceA_rightTensorUnitaryConj_toOp W
    _ = (ckrDeFinettiState d n).toOp := hfix
    _ = partialTraceB τ.toOp := hmarginal.symm

/-- Operator-level form of the reference-side marginal identity for a
paired-permutation-invariant CKR purification. -/
theorem ckrDeFinetti_partialTraceA_toOp_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ)
    (hτ_paired : IsPairedPermInvariant τ) :
    τ.partialTraceA.toOp = (ckrDeFinettiState d n).toOp := by
  calc
    τ.partialTraceA.toOp = τ.partialTraceB.toOp :=
      ckrDeFinetti_partialTraceA_toOp_eq_partialTraceB_toOp_of_pairedPermInvariant
        τ hτ hτ_paired
    _ = (ckrDeFinettiState d n).toOp :=
      congrArg (fun σ : DensityOp (d ^ n) => σ.toOp) hτ.marginal

/-- **Any paired-permutation-invariant CKR de Finetti purification at the canonical
reference dimension has the CKR marginal on both tensor factors.**

This is the arbitrary-purification statement: no canonicity, no construction and no choice
of eigenbasis is assumed of `τ`, only that it is pure, that its `H^n` marginal is
`τ_{H^n}`, and that it is invariant under the paired permutation action.  Compare
`ckrDeFinettiCanonicalPurification_partialTraceA_toOp`, which is the same conclusion for the
one explicitly constructed purification, and
`pairedDeFinettiState_partialTraceA_eq_ckrDeFinettiState`, which is the corresponding
statement for the *mixed* normalized paired symmetric projector. -/
theorem ckrDeFinetti_partialTraceA_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ)
    (hτ_paired : IsPairedPermInvariant τ) :
    τ.partialTraceA = ckrDeFinettiState d n :=
  Quantum.Operators.DensityOp.ext
    (ckrDeFinetti_partialTraceA_toOp_of_pairedPermInvariant τ hτ hτ_paired)

/-- Density-operator form of the equality of the two marginals. -/
theorem ckrDeFinetti_partialTraceA_eq_partialTraceB_of_pairedPermInvariant
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ)
    (hτ_paired : IsPairedPermInvariant τ) :
    τ.partialTraceA = τ.partialTraceB :=
  (ckrDeFinetti_partialTraceA_of_pairedPermInvariant τ hτ hτ_paired).trans hτ.marginal.symm

/-! ## What holds without any invariance hypothesis -/

/-- **Without any invariance hypothesis, the reference marginal of a square-ancilla CKR
purification is a unitary conjugate of `τ_{H^n}`.**

Purification prescribes the `H^n` marginal only; the reference marginal ranges over the
whole unitary orbit.  In particular it is isospectral to `τ_{H^n}`. -/
theorem ckrDeFinetti_squareAncilla_partialTraceA_mem_unitary_orbit
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ) :
    ∃ W : UnitaryOp (d ^ n),
      τ.partialTraceA.toOp =
        W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† := by
  haveI : NeZero (d ^ n * d ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (d ^ n)) (NeZero.ne (d ^ n))⟩
  obtain ⟨W, htransport⟩ := ckrDeFinetti_squareAncilla_unitary_transport τ hτ
  refine ⟨W, ?_⟩
  change partialTraceA τ.toOp = _
  rw [htransport,
    ckrDeFinettiCanonicalPurification_partialTraceA_rightTensorUnitaryConj_toOp]

/-- The reference marginal of a square-ancilla CKR purification is positive definite, hence
of full rank `d ^ n`, invariance or not: it is a unitary conjugate of the positive definite
`τ_{H^n}` (`ckrDeFinettiState_toOp_posDef`). -/
theorem ckrDeFinetti_squareAncilla_partialTraceA_toOp_posDef
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ) :
    τ.partialTraceA.toOp.PosDef := by
  obtain ⟨W, hW⟩ := ckrDeFinetti_squareAncilla_partialTraceA_mem_unitary_orbit τ hτ
  have hunit : IsUnit W.toOp :=
    ⟨⟨W.toOp, W.toOp†, W.unitary_right, W.unitary_left⟩, rfl⟩
  rw [hW, show W.toOp† = star W.toOp from rfl]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hunit).mpr
    (ckrDeFinettiState_toOp_posDef d n)

/-! ## The sharp condition, and failure outside the commutant -/

/-- **The transported reference marginal is `τ_{H^n}` exactly when the transporting unitary
commutes with `τ_{H^n}`.**

Paired permutation invariance is *sufficient* for the left-hand side, by
`ckrDeFinetti_partialTraceA_of_pairedPermInvariant` together with
`ckrDeFinettiState_commutes_of_commutes_permutationRepresentations`.  The equivalence here
characterizes the marginal identity directly by commutation with `τ_{H^n}` itself. -/
theorem ckrDeFinetti_partialTraceA_toOp_eq_iff_referenceUnitary_commutes
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp) :
    τ.partialTraceA.toOp = (ckrDeFinettiState d n).toOp ↔
      W.toOp * (ckrDeFinettiState d n).toOp =
        (ckrDeFinettiState d n).toOp * W.toOp := by
  have hmarg : τ.partialTraceA.toOp =
      W.toOp * (ckrDeFinettiState d n).toOp * W.toOp† := by
    change partialTraceA τ.toOp = _
    rw [htransport,
      ckrDeFinettiCanonicalPurification_partialTraceA_rightTensorUnitaryConj_toOp]
  rw [hmarg]
  refine ⟨fun hconj => ?_, Quantum.Operators.unitary_conj_eq_of_mul_comm W _⟩
  calc
    W.toOp * (ckrDeFinettiState d n).toOp =
        (W.toOp * (ckrDeFinettiState d n).toOp * W.toOp†) * W.toOp := by
      simp only [Matrix.mul_assoc]
      rw [W.unitary_left, Matrix.mul_one]
    _ = (ckrDeFinettiState d n).toOp * W.toOp := by rw [hconj]

/-- A transport by a unitary outside the commutant of `τ_{H^n}` has reference marginal
different from `τ_{H^n}`.  The noncommuting unitary is an explicit premise. -/
theorem ckrDeFinetti_partialTraceA_ne_of_referenceUnitary_not_commutes
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (W : UnitaryOp (d ^ n))
    (htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp)
    (hW : W.toOp * (ckrDeFinettiState d n).toOp ≠
      (ckrDeFinettiState d n).toOp * W.toOp) :
    τ.partialTraceA ≠ ckrDeFinettiState d n := fun hmarg =>
  hW ((ckrDeFinetti_partialTraceA_toOp_eq_iff_referenceUnitary_commutes τ W htransport).mp
    (congrArg (fun σ : DensityOp (d ^ n) => σ.toOp) hmarg))

/-- Given a unitary outside the commutant of `τ_{H^n}`, construct a CKR purification
whose reference marginal differs from `τ_{H^n}`.

This proves existence of the purification from the supplied `W` and `hW`; it does not
construct a noncommuting unitary or prove that one exists. -/
theorem ckrDeFinetti_exists_squareAncilla_purification_partialTraceA_ne
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (W : UnitaryOp (d ^ n))
    (hW : W.toOp * (ckrDeFinettiState d n).toOp ≠
      (ckrDeFinettiState d n).toOp * W.toOp) :
    ∃ τ : DensityOp ((d ^ n) * (d ^ n)),
      IsCKRDeFinettiPurification τ ∧ τ.partialTraceA ≠ ckrDeFinettiState d n := by
  have hcanon : ckrDeFinettiCanonicalPurification d n =
      sameAncillaPurificationDensity (ckrDeFinettiState d n) := rfl
  set τ : DensityOp ((d ^ n) * (d ^ n)) :=
    UnitaryOp.evolve (Quantum.TensorProducts.rightTensorUnitary (n := d ^ n) W)
      (ckrDeFinettiCanonicalPurification d n) with hτ_def
  have htransport :
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp := rfl
  have hpurif : τ.IsPure ∧ τ.partialTraceB = ckrDeFinettiState d n := by
    rw [hcanon] at htransport
    exact (Quantum.Metrics.isPurification_squareAncilla_iff_exists_rightTensorUnitaryConj
      (ckrDeFinettiState d n) τ).mpr ⟨W, htransport⟩
  exact ⟨τ, ⟨hpurif.1, hpurif.2⟩,
    ckrDeFinetti_partialTraceA_ne_of_referenceUnitary_not_commutes τ W htransport hW⟩

end Quantum.Channels

end -- noncomputable section
