import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# Kraus Submatrix Blocks — compressed rows and tensor-id block identities

This file provides entrywise identities for Kraus maps obtained by selecting
rows of a larger Kraus family.  The tensor-id version is used to compare
first-factor channels with their reference-register extensions.

## Main definitions
- This file defines no new data structures.

## Main statements
- `krausMapFintype_submatrix_entry_eq_embed_entry`: a compressed finite-index
  Kraus map is a principal block of the original Kraus map.
- `mapTensorId_krausMapFintype_submatrix_entry_eq_mapTensorId_embed_entry`:
  the corresponding block identity after tensoring with the identity.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Compressing every Kraus operator to selected output rows gives the
corresponding principal block of the original Kraus map. -/
lemma krausMapFintype_submatrix_entry_eq_embed_entry
    {n m out r : ℕ}
    (K : Fin r → Matrix (Fin out) (Fin n) ℂ)
    (embed : Fin m → Fin out)
    (A : Op n) (i j : Fin m) :
    (krausMapFintype (fun k => (K k).submatrix embed (fun x : Fin n => x)) A) i j =
      (krausMapFintype K A) (embed i) (embed j) := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

/-- Tensoring with the identity preserves the compressed-Kraus block
calculation on product indices. -/
lemma mapTensorId_krausMapFintype_submatrix_entry_eq_mapTensorId_embed_entry
    {n m out r k : ℕ} [NeZero n] [NeZero m] [NeZero out] [NeZero k]
    (K : Fin r → Matrix (Fin out) (Fin n) ℂ)
    (embed : Fin m → Fin out)
    (op : Op (n * k))
    (a b : Fin m) (s t : Fin k) :
    mapTensorId
        (krausMapFintype (fun r => (K r).submatrix embed (fun x : Fin n => x)))
        op (finProdFinEquiv (a, s)) (finProdFinEquiv (b, t)) =
      mapTensorId (krausMapFintype K) op
        (finProdFinEquiv (embed a, s)) (finProdFinEquiv (embed b, t)) := by
  have h_as : finProdFinEquiv.symm (finProdFinEquiv (a, s)) = (a, s) :=
    Equiv.symm_apply_apply finProdFinEquiv (a, s)
  have h_bt : finProdFinEquiv.symm (finProdFinEquiv (b, t)) = (b, t) :=
    Equiv.symm_apply_apply finProdFinEquiv (b, t)
  have h_eas : finProdFinEquiv.symm (finProdFinEquiv (embed a, s)) = (embed a, s) :=
    Equiv.symm_apply_apply finProdFinEquiv (embed a, s)
  have h_ebt : finProdFinEquiv.symm (finProdFinEquiv (embed b, t)) = (embed b, t) :=
    Equiv.symm_apply_apply finProdFinEquiv (embed b, t)
  simp only [mapTensorId, Matrix.of_apply, Equiv.toFun_as_coe, h_as, h_bt, h_eas, h_ebt]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [krausMapFintype_submatrix_entry_eq_embed_entry]

end Quantum.Channels

end -- noncomputable section
