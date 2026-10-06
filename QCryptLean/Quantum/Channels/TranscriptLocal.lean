import QCryptLean.Quantum.Channels.Separable
import QCryptLean.Quantum.TensorProducts.ClassicalRegister
import QCryptLean.Quantum.TensorProducts.Gram

/-!
# Transcript-conditioned products of local operations

For each public transcript, a product of independent local Kraus families is more restrictive
than a single shared product-Kraus family. Such maps are separable.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- A complete channel with an independent product of local Kraus families at each transcript.

The complete public transcript is appended to the second factor using canonical reassociation. -/
def IsTranscriptLocalOperation {rA rB sA sB : ℕ} {D : ℕ}
    (Φ : Op (rA * rB) →ₗ[ℂ] Op ((sA * sB) * D)) : Prop :=
  ∃ (mA mB : Fin D → ℕ)
    (A : (t : Fin D) → Fin (mA t) → Matrix (Fin sA) (Fin rA) ℂ)
    (B : (t : Fin D) → Fin (mB t) → Matrix (Fin sB) (Fin rB) ℂ),
    (∀ ρ, (Op.castDimLinear (Nat.mul_assoc sA sB D)) (Φ ρ) =
        ∑ t : Fin D, ∑ i : Fin (mA t), ∑ j : Fin (mB t),
          tensorRect (A t i) (appendIndexKraus sB t * B t j) * ρ *
            (tensorRect (A t i) (appendIndexKraus sB t * B t j))ᴴ) ∧
    (∑ t : Fin D, ∑ i : Fin (mA t), ∑ j : Fin (mB t),
        (tensorRect (A t i) (B t j))ᴴ * tensorRect (A t i) (B t j) = 1)

/-- Finite independent local Kraus families give a transcript-local channel. -/
theorem isTranscriptLocalOperation_of_fintype {rA rB sA sB : ℕ} {D : ℕ}
    (Φ : Op (rA * rB) →ₗ[ℂ] Op ((sA * sB) * D))
    {ιA ιB : Fin D → Type} [∀ t, Fintype (ιA t)] [∀ t, Fintype (ιB t)]
    (A : (t : Fin D) → ιA t → Matrix (Fin sA) (Fin rA) ℂ)
    (B : (t : Fin D) → ιB t → Matrix (Fin sB) (Fin rB) ℂ)
    (hmap : ∀ ρ, (Op.castDimLinear (Nat.mul_assoc sA sB D)) (Φ ρ) =
        ∑ t : Fin D, ∑ i : ιA t, ∑ j : ιB t,
          tensorRect (A t i) (appendIndexKraus sB t * B t j) * ρ *
            (tensorRect (A t i) (appendIndexKraus sB t * B t j))ᴴ)
    (hcomp : ∑ t : Fin D, ∑ i : ιA t, ∑ j : ιB t,
        (tensorRect (A t i) (B t j))ᴴ * tensorRect (A t i) (B t j) = 1) :
    IsTranscriptLocalOperation Φ := by
  refine ⟨fun t => Fintype.card (ιA t), fun t => Fintype.card (ιB t),
    fun t i => A t ((Fintype.equivFin (ιA t)).symm i),
    fun t j => B t ((Fintype.equivFin (ιB t)).symm j), fun ρ => ?_, ?_⟩
  · rw [hmap]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Fintype.sum_equiv (Fintype.equivFin (ιA t)) _ _ fun i => ?_
    refine Fintype.sum_equiv (Fintype.equivFin (ιB t)) _ _ fun j => ?_
    simp only [Equiv.symm_apply_apply]
  · rw [← hcomp]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Fintype.sum_equiv (Fintype.equivFin (ιA t)).symm _ _ fun i => ?_
    exact Fintype.sum_equiv (Fintype.equivFin (ιB t)).symm _ _ fun j => rfl

/-- The public transcript may be indexed by any explicitly equivalent finite type. -/
theorem isTranscriptLocalOperation_of_equiv {rA rB sA sB : ℕ} {D : ℕ} {T : Type} [Fintype T]
    (e : T ≃ Fin D) (Φ : Op (rA * rB) →ₗ[ℂ] Op ((sA * sB) * D))
    {ιA ιB : T → Type} [∀ t, Fintype (ιA t)] [∀ t, Fintype (ιB t)]
    (A : (t : T) → ιA t → Matrix (Fin sA) (Fin rA) ℂ)
    (B : (t : T) → ιB t → Matrix (Fin sB) (Fin rB) ℂ)
    (hmap : ∀ ρ, (Op.castDimLinear (Nat.mul_assoc sA sB D)) (Φ ρ) =
        ∑ t : T, ∑ i : ιA t, ∑ j : ιB t,
          tensorRect (A t i) (appendIndexKraus sB (e t) * B t j) * ρ *
            (tensorRect (A t i) (appendIndexKraus sB (e t) * B t j))ᴴ)
    (hcomp : ∑ t : T, ∑ i : ιA t, ∑ j : ιB t,
        (tensorRect (A t i) (B t j))ᴴ * tensorRect (A t i) (B t j) = 1) :
    IsTranscriptLocalOperation Φ := by
  refine isTranscriptLocalOperation_of_fintype Φ
    (ιA := fun s => ιA (e.symm s)) (ιB := fun s => ιB (e.symm s))
    (fun s i => A (e.symm s) i) (fun s j => B (e.symm s) j) (fun ρ => ?_) ?_
  · rw [hmap, ← Equiv.sum_comp e.symm]
    exact Finset.sum_congr rfl fun s _ => by rw [Equiv.apply_symm_apply]
  · exact (Equiv.sum_comp e.symm _).trans hcomp

/-- Flattening the independent Kraus indices gives a separable channel. -/
theorem isTranscriptLocal_isSeparable {rA rB sA sB : ℕ} {D : ℕ}
    (Φ : Op (rA * rB) →ₗ[ℂ] Op ((sA * sB) * D)) (h : IsTranscriptLocalOperation Φ) :
    IsSeparableOperation (rA := rA) (rB := rB) (sA := sA) (sB := sB * D)
      ((Op.castDimLinear (Nat.mul_assoc sA sB D)).comp Φ) := by
  obtain ⟨mA, mB, A, B, hmap, hcomp⟩ := h
  refine isSeparableOperation_of_fintype (ι := (t : Fin D) × (Fin (mA t) × Fin (mB t))) _
    (fun p => A p.1 p.2.1) (fun p => appendIndexKraus sB p.1 * B p.1 p.2.2) (fun ρ => ?_) ?_
  · rw [LinearMap.comp_apply, hmap, Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
  · rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, tensorRect_appendIndexKraus_isometry]
    exact hcomp

/-- A trivial transcript leaves an independent product of two local Kraus families. -/
theorem isTranscriptLocal_one_apply {rA rB sA sB : ℕ} (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB))
    (h : IsTranscriptLocalOperation (rA := rA) (rB := rB) (sA := sA) (sB := sB) (D := 1)
      ((Op.castDimLinear (Nat.mul_one (sA * sB)).symm).comp Φ)) :
    ∃ (mA mB : ℕ) (A : Fin mA → Matrix (Fin sA) (Fin rA) ℂ)
      (B : Fin mB → Matrix (Fin sB) (Fin rB) ℂ),
      ∀ ρ, Φ ρ = ∑ i, ∑ j, tensorRect (A i) (B j) * ρ * (tensorRect (A i) (B j))ᴴ := by
  obtain ⟨mA, mB, A, B, hmap, -⟩ := h
  refine ⟨mA 0, mB 0, A 0, B 0, fun ρ => ?_⟩
  have hρ := hmap ρ
  rw [LinearMap.comp_apply, Op.castDimLinear_trans, castDimLinear_apply_eq_conj] at hρ
  simp only [Fin.sum_univ_one] at hρ
  have hC : ∀ (i : Fin (mA 0)) (j : Fin (mB 0)),
      tensorRect (A 0 i) (appendIndexKraus sB 0 * B 0 j)
        = castRect (sA * sB) (sA * (sB * 1)) * tensorRect (A 0 i) (B 0 j) := by
    intro i j
    rw [appendIndexKraus_one, ← tensorRect_one_castRect (Nat.mul_one sB).symm, tensorRect_mul,
      Matrix.one_mul]
  simp only [hC, ← conj_mul_conj, ← Matrix.mul_sum, ← Matrix.sum_mul] at hρ
  exact eq_of_castRect_conj_eq (n := (sA * sB)) (m := sA * (sB * 1))
    (by rw [Nat.mul_one]) _ _ hρ

end Quantum.Channels
