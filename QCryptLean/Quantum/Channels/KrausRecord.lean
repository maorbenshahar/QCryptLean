import Mathlib.Analysis.Complex.Basic

/-!
# Coherent records of Kraus families

Stacking a complete Kraus family into an outcome register gives a Stinespring isometry.
The coherent record preserves the completeness sum as its Gram matrix.
-/

open Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Stack a finite Kraus family coherently into an additional outcome register. -/
def recordKraus {dIn dOut : ℕ} {Xo : Type} [Fintype Xo]
    (K : Xo → Matrix (Fin dOut) (Fin dIn) ℂ) :
    Matrix (Fin (dOut * Fintype.card Xo)) (Fin dIn) ℂ :=
  Matrix.of fun i j =>
    K ((Fintype.equivFin Xo).symm (finProdFinEquiv.symm i).2) (finProdFinEquiv.symm i).1 j

/-- Canonical coordinates for the output register paired with the Kraus outcome. -/
def recordEquiv (dOut : ℕ) (Xo : Type) [Fintype Xo] :
    Fin dOut × Xo ≃ Fin (dOut * Fintype.card Xo) :=
  ((Equiv.refl (Fin dOut)).prodCongr (Fintype.equivFin Xo)).trans finProdFinEquiv

@[simp] theorem recordKraus_apply_recordEquiv {dIn dOut : ℕ} {Xo : Type} [Fintype Xo]
    (K : Xo → Matrix (Fin dOut) (Fin dIn) ℂ) (a : Fin dOut) (x : Xo) (j : Fin dIn) :
    recordKraus K (recordEquiv dOut Xo (a, x)) j = K x a j := by
  simp only [recordKraus, recordEquiv, Matrix.of_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, Equiv.symm_apply_apply]

/-- A complete Kraus family has an isometric coherent record. -/
theorem recordKraus_conjTranspose_mul_self {dIn dOut : ℕ} {Xo : Type} [Fintype Xo]
    (K : Xo → Matrix (Fin dOut) (Fin dIn) ℂ) (hK : ∑ x, (K x)ᴴ * K x = 1) :
    (recordKraus K)ᴴ * recordKraus K = 1 := by
  rw [← hK]
  ext j j'
  rw [Matrix.mul_apply, ← Equiv.sum_comp (recordEquiv dOut Xo), Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [Matrix.conjTranspose_apply, recordKraus_apply_recordEquiv, Matrix.sum_apply,
    Matrix.mul_apply]

/-- `recordEquiv` on a pair, in the `finProdFinEquiv` form the digit lemma reads. -/
theorem recordEquiv_apply (dOut : ℕ) (Xo : Type) [Fintype Xo] (t : Fin dOut) (x : Xo) :
    recordEquiv dOut Xo (t, x) = finProdFinEquiv (t, Fintype.equivFin Xo x) := rfl

end Quantum.Channels
