import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Pure-State Register Extension Channels — appending normalized kets, Kraus form, casts

This module contains the channel `A ↦ A ⊗ |ψ⟩⟨ψ|`, used to append a fixed
pure classical/quantum register to a channel output, together with its
single-Kraus representation for normalized kets.

## Main definitions
- `appendKetKraus`: single Kraus operator for appending a fixed ket.
- `appendKetLinear`: linear map appending the pure register.

## Main statements
- `appendKetKraus_conjTranspose_mul_self`: the Kraus operator is an isometry.
- `kraus_map_fintype_appendKetKraus`: the single-Kraus map equals `appendKetLinear`.
- `appendKetLinear_isCPTP`: appending a normalized pure register is CPTP.
- `castDimLinear_isCPTP`: casting equal operator dimensions is CPTP.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The single Kraus operator that embeds `|i⟩` as `|i⟩ ⊗ |ψ⟩`. -/
def appendKetKraus {d k : ℕ} (ψ : Ket k) :
    Matrix (Fin (d * k)) (Fin d) ℂ :=
  Matrix.of fun p i =>
    let q := finProdFinEquiv.symm p
    if q.1 = i then ψ.vec q.2 else 0

/-- Append a fixed pure register to the output: `A ↦ A ⊗ |ψ⟩⟨ψ|`. -/
noncomputable def appendKetLinear {d k : ℕ} (ψ : Ket k) :
    Op d →ₗ[ℂ] Op (d * k) where
  toFun A := Op.tensor A (ψ * ψ.dag)
  map_add' A B := by
    simp only [Op.tensor_add_left]
  map_smul' c A := by
    simp only [RingHom.id_apply, Op.tensor_smul_left]

/-- The append-Ket Kraus operator is an isometry for a normalized ket. -/
lemma appendKetKraus_conjTranspose_mul_self {d k : ℕ}
    (ψ : Ket k) (hψ : ψ.dag * ψ = 1) :
    (appendKetKraus (d := d) ψ)ᴴ * appendKetKraus (d := d) ψ =
      (1 : Op d) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, appendKetKraus,
    Matrix.of_apply, Matrix.one_apply]
  rw [show (∑ x : Fin (d * k),
      star (let q := finProdFinEquiv.symm x; if q.1 = i then ψ.vec q.2 else 0) *
        (let q := finProdFinEquiv.symm x; if q.1 = j then ψ.vec q.2 else 0)) =
      ∑ q : Fin d × Fin k,
        star (if q.1 = i then ψ.vec q.2 else 0) *
          (if q.1 = j then ψ.vec q.2 else 0) by
    exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · have hnorm : ∑ x, star (ψ.vec x) * ψ.vec x = 1 := by
        rw [bra_mul_ket_eq] at hψ
        simpa [Ket.dag_vec] using hψ
      simpa using hnorm
    · intro a _ hai
      simp [hai]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · simp only [hij, if_false]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hai : a = i
    · have haj : a ≠ j := by
        intro h
        exact hij (hai.symm.trans h)
      simp [hai, hij]
    · simp [hai]

/-- The append-Ket linear map is the finite Kraus map of `appendKetKraus`. -/
lemma kraus_map_fintype_appendKetKraus {d k : ℕ} (ψ : Ket k) :
    krausMapFintype (fun _ : Unit => appendKetKraus (d := d) ψ) =
      appendKetLinear (d := d) ψ := by
  ext A p q
  simp only [krausMapFintype, appendKetLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (∑ _ : Unit, appendKetKraus (d := d) ψ * A *
      (appendKetKraus (d := d) ψ)ᴴ) =
      appendKetKraus (d := d) ψ * A * (appendKetKraus (d := d) ψ)ᴴ by
    simp]
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    appendKetKraus, Matrix.of_apply, ket_mul_bra_apply, Ket.dag_vec]
  let pp := finProdFinEquiv.symm p
  let qq := finProdFinEquiv.symm q
  have hp : finProdFinEquiv.symm p = pp := rfl
  have hq : finProdFinEquiv.symm q = qq := rfl
  simp only [hp, hq]
  trans ∑ x, (ψ.vec pp.2 * A pp.1 x) *
      star (if qq.1 = x then ψ.vec qq.2 else 0)
  · apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Finset.sum_eq_single pp.1]
    · simp
    · intro y _ hy
      simp [hy.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ pp.1))
  · rw [Finset.sum_eq_single qq.1]
    · simp
      ring
    · intro y _ hy
      simp [hy.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ qq.1))

/-- Appending a normalized pure register is CPTP. -/
theorem appendKetLinear_isCPTP {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (ψ : Ket k) (hψ : ψ.dag * ψ = 1) :
    IsCPTP (⇑(appendKetLinear (d := d) ψ)) := by
  have hK : ∑ _ : Unit,
      (appendKetKraus (d := d) ψ)ᴴ * appendKetKraus (d := d) ψ =
        (1 : Op d) := by
    simpa only [Finset.univ_unique, Finset.sum_singleton] using
      appendKetKraus_conjTranspose_mul_self (d := d) ψ hψ
  have hCPTP :
      IsCPTP (⇑(krausMapFintype (fun _ : Unit => appendKetKraus (d := d) ψ))) :=
    krausMapFintype_isCPTP (fun _ : Unit => appendKetKraus (d := d) ψ) hK
  simpa [kraus_map_fintype_appendKetKraus] using hCPTP

/-- Casting equal operator dimensions is CPTP. -/
theorem castDimLinear_isCPTP {d e : ℕ} [NeZero d] [NeZero e] (h : d = e) :
    IsCPTP (⇑(Op.castDimLinear h)) := by
  subst h
  simpa [Op.castDimLinear, Op.castDim] using id_is_cptp d

end Quantum.Channels

end
