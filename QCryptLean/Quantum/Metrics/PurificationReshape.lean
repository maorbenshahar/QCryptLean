import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Tensor-Purification Carrier Reshapes — finite-index reshapes and associativity casts

This file packages carrier reshapes used to reinterpret purification kets across
equivalent tensor parenthesizations.  It includes both the explicit finite-index
reshape

  `Fin ((dE * dR) * (dE * dR)) ≃ Fin (dE * (dR * (dE * dR)))`

and the simpler associativity casts between `(E ⊗ R) ⊗ A` and `E ⊗ (R ⊗ A)`.

Given a ket on `Ket ((dE * dR) * (dE * dR))` (a joint purification of a
density operator on `(dE * dR)` over an ancilla of size `(dE * dR)`),
its `reshapeKet` reinterprets the carrier as `Ket (dE * (dR * (dE * dR)))`,
so the partial trace over the *new* right factor (size `dR * (dE * dR)`)
recovers the further-reduced state on `Op dE` after also tracing out the
inner `Fin dR`.

The reshape is a sum-reindexing on coefficients, so any inner product is
preserved.  The iterated partial-trace identity is the genuine
mathematical content of the reshape.

## Main definitions

- `Quantum.TensorProducts.reshapeIdx`: the carrier bijection
- `Quantum.TensorProducts.reshapeKet`: the reshaped ket
- `Quantum.TensorProducts.regroupJointPurification`: reassociation from
  `(E ⊗ R) ⊗ A` to `E ⊗ (R ⊗ A)`.
- `Quantum.TensorProducts.ungroupJointPurification`: inverse reassociation

## Main statements

- `reshapeKet_overlap_eq`: overlap is preserved
- `reshapeKet_partialTraceB_iterated_eq`: the iterated partial-trace identity
- `regroupJointPurification_overlap_eq`: associativity casts preserve
  grouped-branch overlaps
- `ungroupJointPurification_iterated_partialTraceB_ketbra`: inverse
  reassociation commutes with iterated partial trace
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- Reassociate a live joint purification branch from `(E ⊗ R) ⊗ A` to
`E ⊗ (R ⊗ A)`. -/
def regroupJointPurification {dE dR anc : ℕ}
    (ψ : Ket ((dE * dR) * anc)) :
    Ket (dE * (dR * anc)) :=
  Ket.cast (Nat.mul_assoc dE dR anc) ψ

/-- Reassociate a live branch from `E ⊗ (R ⊗ A)` back to `(E ⊗ R) ⊗ A`,
so that tracing out only `A` produces an operator on `E ⊗ R`. -/
def ungroupJointPurification {dE dR anc : ℕ}
    (ψ : Ket (dE * (dR * anc))) :
    Ket ((dE * dR) * anc) :=
  Ket.cast (Nat.mul_assoc dE dR anc).symm ψ

private lemma ket_cast_overlap {n m : ℕ} (h : n = m)
    (ψ φ : Ket n) :
    (Ket.cast h ψ).dag * (Ket.cast h φ) = ψ.dag * φ := by
  subst h
  rfl

private lemma ket_overlap_cast_symm_eq_cast_overlap {n m : ℕ} (h : n = m)
    (ψ : Ket n) (φ : Ket m) :
    ψ.dag * (Ket.cast h.symm φ) = (Ket.cast h ψ).dag * φ := by
  subst h
  rfl

private lemma cast_ketbra_of_cast_symm {n m : ℕ} (h : n = m)
    (ψ : Ket m) :
    h ▸ (Ket.cast h.symm ψ * (Ket.cast h.symm ψ).dag) = ψ * ψ.dag := by
  subst h
  rfl

/-- Reassociation preserves the overlap of two grouped live branches. -/
theorem regroupJointPurification_overlap_eq {dE dR anc : ℕ}
    (ψ φ : Ket ((dE * dR) * anc)) :
    (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag *
        (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) φ) =
      ψ.dag * φ := by
  exact ket_cast_overlap (Nat.mul_assoc dE dR anc) ψ φ

/-- Inverse reassociation preserves the overlap of two ungrouped live branches. -/
theorem ungroupJointPurification_overlap_eq {dE dR anc : ℕ}
    (ψ φ : Ket (dE * (dR * anc))) :
    (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) φ) =
      ψ.dag * φ := by
  exact ket_cast_overlap (Nat.mul_assoc dE dR anc).symm ψ φ

/-- Moving the reassociation from the source branch to the target branch
preserves their overlap. -/
theorem regroupJointPurification_overlap_ungroup_eq {dE dR anc : ℕ}
    (ψ : Ket ((dE * dR) * anc)) (φ : Ket (dE * (dR * anc))) :
    ψ.dag *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) φ) =
      (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag * φ := by
  exact ket_overlap_cast_symm_eq_cast_overlap (Nat.mul_assoc dE dR anc) ψ φ

/-- Iterated partial trace of the inverse-reassociated ketbra equals the
one-step partial trace of the grouped ketbra. -/
theorem ungroupJointPurification_iterated_partialTraceB_ketbra {dE dR anc : ℕ}
    (ψ : Ket (dE * (dR * anc))) :
    partialTraceB
        (partialTraceB
          ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
            (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)) =
      partialTraceB (ψ * ψ.dag) := by
  rw [partialTraceB_partialTraceB_eq_assoc]
  unfold ungroupJointPurification
  rw [cast_ketbra_of_cast_symm (Nat.mul_assoc dE dR anc)]

/-- Inverse reassociation preserves the real trace of the live branch after
tracing out the purifier. -/
theorem ungroup_joint_purification_partialTraceB_trace_re_eq {dE dR anc : ℕ}
    (ψ : Ket (dE * (dR * anc))) :
    (partialTraceB
      ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re =
      (partialTraceB (ψ * ψ.dag)).trace.re := by
  calc
    (partialTraceB
      ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re
        =
      (partialTraceB
        (partialTraceB
          ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
            (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag))).trace.re := by
          rw [← trace_partialTraceB]
    _ = (partialTraceB (ψ * ψ.dag)).trace.re := by
          rw [ungroupJointPurification_iterated_partialTraceB_ketbra]

/-- Tracing out the right composite system after regrouping a live branch is the
same as tracing out the purifier and then the `R` register. -/
lemma partialTraceB_regroupJointPurification_ketbra
    {dE dR anc : ℕ} (ψ : Ket ((dE * dR) * anc)) :
    partialTraceB
        ((regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
          (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)
      =
    partialTraceB (partialTraceB (ψ * ψ.dag)) := by
  rw [regroupJointPurification, Ket.cast_mul_dag]
  exact (partialTraceB_partialTraceB_eq_assoc
    (a := dE) (b := dR) (c := anc) (ψ * ψ.dag)).symm

/-- Reassociating a joint live branch preserves its self inner product. -/
lemma regroupJointPurification_dag_mul
    {dE dR anc : ℕ} (ψ : Ket ((dE * dR) * anc)) :
    (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag *
        regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ =
      ψ.dag * ψ := by
  rw [regroupJointPurification, Ket.cast_dag_mul_cast]

/-- Carrier reshape

`Fin ((dE * dR) * (dE * dR)) ≃ Fin (dE * (dR * (dE * dR)))`,

built from `finProdFinEquiv` and `Equiv.prodAssoc`. -/
def reshapeIdx (dE dR : ℕ) :
    Fin ((dE * dR) * (dE * dR)) ≃ Fin (dE * (dR * (dE * dR))) :=
  finProdFinEquiv.symm.trans <|
    (finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans <|
      (Equiv.prodAssoc (Fin dE) (Fin dR) (Fin (dE * dR))).trans <|
        ((Equiv.refl (Fin dE)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- The reshape sends the explicit index `((e, r), (e', r'))` of
`Fin ((dE * dR) * (dE * dR))` to `(e, (r, (e', r')))` of
`Fin (dE * (dR * (dE * dR)))`. -/
lemma reshapeIdx_apply {dE dR : ℕ}
    (e : Fin dE) (r : Fin dR) (e' : Fin dE) (r' : Fin dR) :
    reshapeIdx dE dR
        (finProdFinEquiv (finProdFinEquiv (e, r), finProdFinEquiv (e', r'))) =
      finProdFinEquiv (e, finProdFinEquiv (r, finProdFinEquiv (e', r'))) := by
  simp [reshapeIdx]

/-- The `.symm` direction of the reshape, given an index decomposed as
`(e, (r, (e', r')))` on the new carrier. -/
lemma reshapeIdx_symm_apply {dE dR : ℕ}
    (e : Fin dE) (r : Fin dR) (e' : Fin dE) (r' : Fin dR) :
    (reshapeIdx dE dR).symm
        (finProdFinEquiv (e, finProdFinEquiv (r, finProdFinEquiv (e', r')))) =
      finProdFinEquiv (finProdFinEquiv (e, r), finProdFinEquiv (e', r')) := by
  apply (reshapeIdx dE dR).injective
  rw [Equiv.apply_symm_apply, reshapeIdx_apply]

/-- Reshape a ket on `(dE * dR) * (dE * dR)` to a ket on
`dE * (dR * (dE * dR))` by pulling back along `reshapeIdx`. -/
def reshapeKet {dE dR : ℕ} (ψ : Ket ((dE * dR) * (dE * dR))) :
    Ket (dE * (dR * (dE * dR))) :=
  ⟨fun p => ψ.vec ((reshapeIdx dE dR).symm p)⟩

@[simp]
lemma reshapeKet_vec {dE dR : ℕ} (ψ : Ket ((dE * dR) * (dE * dR)))
    (p : Fin (dE * (dR * (dE * dR)))) :
    (reshapeKet ψ).vec p = ψ.vec ((reshapeIdx dE dR).symm p) := rfl

/-- The overlap `⟨ψ | φ⟩` is invariant under the reshape: both sides are
sums over a bijection of the underlying coefficient pairs. -/
lemma reshapeKet_overlap_eq {dE dR : ℕ}
    (ψ φ : Ket ((dE * dR) * (dE * dR))) :
    ((reshapeKet ψ).dag * reshapeKet φ : ℂ) = (ψ.dag * φ : ℂ) := by
  simp only [bra_mul_ket_eq, Ket.dag_vec, reshapeKet_vec]
  exact (Fintype.sum_equiv (reshapeIdx dE dR)
    (fun i => conj (ψ.vec i) * φ.vec i)
    (fun p => conj (ψ.vec ((reshapeIdx dE dR).symm p)) *
        φ.vec ((reshapeIdx dE dR).symm p))
    (fun i => by simp)).symm

/-- The reshaped overlap norm equals the original overlap norm. -/
lemma reshapeKet_overlap_norm_eq {dE dR : ℕ}
    (ψ φ : Ket ((dE * dR) * (dE * dR))) :
    ‖((reshapeKet ψ).dag * reshapeKet φ : ℂ)‖ = ‖(ψ.dag * φ : ℂ)‖ := by
  rw [reshapeKet_overlap_eq]

/-- **Iterated partial-trace identity for the reshape.**

For any `ψ : Ket ((dE * dR) * (dE * dR))`, the `partialTraceB` of the
reshaped outer product on the new carrier `dE * (dR * (dE * dR))`
(tracing over the right factor of size `dR * (dE * dR)`) equals the
iterated partial trace of the original outer product (first tracing the
right `(dE * dR)` block, then the `dR` factor inside the remaining
`(dE * dR)` block). -/
lemma reshapeKet_partialTraceB_iterated_eq {dE dR : ℕ}
    (ψ : Ket ((dE * dR) * (dE * dR))) :
    partialTraceB ((reshapeKet ψ) * (reshapeKet ψ).dag) =
      partialTraceB (partialTraceB (ψ * ψ.dag)) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, ket_mul_bra_apply, Ket.dag_vec, reshapeKet_vec]
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv finProdFinEquiv
  intro x
  obtain ⟨r, p⟩ := x
  obtain ⟨⟨e', r'⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp [reshapeIdx_symm_apply]

end Quantum.TensorProducts

end -- noncomputable section
