import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Operators.MatrixSqrt

/-!
# Maximally Entangled Operator Core

This module contains the lightweight same-dimension maximally entangled operator
and ket, together with the small collection of positivity, trace, sandwich and
square-root lemmas needed by the same-ancilla purification bridge and by the Petz
recovery examples.

## Main definitions
- `maxEntangledOp`: the unnormalized maximally entangled projector on `ℂᵐ ⊗ ℂᵐ`
- `maxEntangledKet`: the canonical diagonal ket whose outer product is `maxEntangledOp`

## Main statements
- `maxEntangledOp_eq_ketbra`: `maxEntangledOp` is the outer product of `maxEntangledKet`
- `maxEntangledOp_posSemidef`: `Ω` is positive semidefinite (it is an outer product)
- `maxEntangledOp_ne_zero`: `Ω ≠ 0` in nonzero dimension
- `maxEntangledOp_partialTraceA`, `maxEntangledOp_partialTraceB`: both partial traces are `1`
- `maxEntangledOp_sandwich`: `Ω * (M ⊗ 1) * Ω = Tr(M) • Ω`
- `maxEntangledOp_mul_self`: `Ω * Ω = m • Ω`, so `Ω/m` is idempotent
- `sqrt_maxEntangledOp`: `Ω^{1/2} = m^{-1/2} • Ω`
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-- The unnormalised maximally entangled state outer product `|Ψ⟩⟨Ψ|`
    on `ℂᵐ ⊗ ℂᵐ`. -/
noncomputable def maxEntangledOp (m : ℕ) : Op (m * m) :=
  Matrix.of fun i j =>
    let (i₁, i₂) := finProdFinEquiv.symm i
    let (j₁, j₂) := finProdFinEquiv.symm j
    if i₁ = i₂ ∧ j₁ = j₂ then (1 : ℂ) else 0

/-- The canonical maximally entangled ket whose outer product is
    `maxEntangledOp`. -/
noncomputable def maxEntangledKet (m : ℕ) : Ket (m * m) :=
  ⟨fun i =>
    if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 then 1 else 0⟩

/-- The maximally entangled operator is the outer product of the canonical
    maximally entangled ket. -/
lemma maxEntangledOp_eq_ketbra {m : ℕ} :
    maxEntangledOp m = maxEntangledKet m * (maxEntangledKet m).dag := by
  ext i j
  simp only [maxEntangledOp, maxEntangledKet, Matrix.of_apply,
    ket_mul_bra_apply, Ket.dag_vec]
  by_cases hi : i.divNat = i.modNat
  · by_cases hj : j.divNat = j.modNat <;> simp [hi, hj]
  · by_cases hj : j.divNat = j.modNat <;> simp [hi, hj]

/-- The maximally entangled operator is Hermitian. -/
lemma maxEntangledOp_isHermitian (m : ℕ) :
    (maxEntangledOp m).IsHermitian := by
  unfold IsHermitian maxEntangledOp
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply, and_comm]

/-- **The maximally entangled operator is positive semidefinite**: it is the outer
product `|Ψ⟩⟨Ψ|` of `maxEntangledKet`.

For the quadratic-form shape consumed by the `PosSemidefOp` bundle, compose with the
standard bridge `Quantum.Operators.posSemidef_re_quadraticForm_nonneg`. -/
lemma maxEntangledOp_posSemidef (m : ℕ) : (maxEntangledOp m).PosSemidef := by
  rw [maxEntangledOp_eq_ketbra]
  exact ketbra_posSemidef _

/-- `Ω ≠ 0` in nonzero dimension: its `((0,0),(0,0))` entry is `1`. -/
lemma maxEntangledOp_ne_zero (m : ℕ) [NeZero m] : maxEntangledOp m ≠ 0 := by
  intro hzero
  have h : maxEntangledOp m (finProdFinEquiv ((0 : Fin m), (0 : Fin m)))
      (finProdFinEquiv ((0 : Fin m), (0 : Fin m))) = 1 := by
    simp only [maxEntangledOp, Matrix.of_apply,
      Equiv.symm_apply_apply]
    simp
  rw [hzero] at h
  simp at h

/-- `Tr_A[|Ψ⟩⟨Ψ|] = 𝟙`. -/
lemma maxEntangledOp_partialTraceA (m : ℕ) :
    partialTraceA (maxEntangledOp m) = (1 : Op m) := by
  unfold partialTraceA maxEntangledOp
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  simp only [Equiv.symm_apply_apply]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq', Finset.mem_univ, and_self]
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    simp only [ite_eq_right_iff, one_ne_zero]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

/-- `Tr_B[|Ψ⟩⟨Ψ|] = 𝟙`. -/
lemma maxEntangledOp_partialTraceB (m : ℕ) :
    partialTraceB (maxEntangledOp m) = (1 : Op m) := by
  unfold partialTraceB maxEntangledOp
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  simp only [Equiv.symm_apply_apply]
  by_cases hij : i = j
  · subst hij
    simp [Finset.mem_univ, and_self]
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    simp only [ite_eq_right_iff, one_ne_zero]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

/-- Summing a function over indices `j : Fin (m * m)` weighted by the diagonal
indicator `(finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2` collapses to
a sum over `Fin m` along the diagonal pairs `(k, k)`. -/
lemma sum_finProdFinEquiv_diag {m : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin (m * m) → α) :
    ∑ j, (if (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2 then f j else 0) =
    ∑ k : Fin m, f (finProdFinEquiv (k, k)) := by
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
      (fun p : Fin m × Fin m => if p.1 = p.2 then f (finProdFinEquiv p) else 0)
      (by
        intro j
        change _ = if _ then f (finProdFinEquiv (finProdFinEquiv.symm j)) else _
        rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ _)]

/-- General trace identity: `Tr[Ω * (A ⊗ B)] = Tr[A * Bᵀ]`. -/
lemma trace_maxEntangled_mul_tensor {m : ℕ} (A B : Op m) :
    (maxEntangledOp m * (A ⊗ B)).trace = (A * B.transpose).trace := by
  have entry_eq : ∀ i j : Fin (m * m),
      (maxEntangledOp m * (A ⊗ B)) i j =
      if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2
      then ∑ k, A k (finProdFinEquiv.symm j).1 * B k (finProdFinEquiv.symm j).2
      else 0 := by
    intro i j
    simp only [Matrix.mul_apply, maxEntangledOp, Matrix.of_apply, Op.tensor,
      Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]
    rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p =>
      (if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 ∧ p.1 = p.2
        then 1 else 0) *
      (A p.1 (finProdFinEquiv.symm j).1 * B p.2 (finProdFinEquiv.symm j).2))
      (by intro k; simp)]
    rw [Fintype.sum_prod_type]
    by_cases hi : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2
    · simp only [hi, true_and, ite_true]
      simp_rw [ite_mul, one_mul, zero_mul]
      have inner : ∀ p₁ : Fin m, (∑ p₂ : Fin m,
          if p₁ = p₂ then A p₁ (finProdFinEquiv.symm j).1 * B p₂ (finProdFinEquiv.symm j).2
          else 0) = A p₁ (finProdFinEquiv.symm j).1 * B p₁ (finProdFinEquiv.symm j).2 := by
        intro p₁
        rw [Finset.sum_ite_eq Finset.univ p₁]
        simp [Finset.mem_univ]
      simp_rw [inner]
    · simp only [hi, false_and, if_false, zero_mul, Finset.sum_const_zero]
  simp only [trace, Matrix.diag, entry_eq]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p =>
    if p.1 = p.2 then ∑ k, A k p.1 * B k p.2 else 0)
    (by intro i; simp)]
  rw [Fintype.sum_prod_type]
  have collapse : ∀ p₁ : Fin m, (∑ p₂ : Fin m,
      if p₁ = p₂ then ∑ k, A k p₁ * B k p₂ else 0)
        = ∑ k, A k p₁ * B k p₁ := by
    intro p₁
    rw [Finset.sum_ite_eq Finset.univ p₁]
    simp [Finset.mem_univ]
  simp_rw [collapse]
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]

/-- `Tr[Ω * (𝟙 ⊗ B)] = Tr[B]` where `Ω = maxEntangledOp`. -/
lemma trace_maxEntangled_mul_one_tensor {m : ℕ} (B : Op m) :
    (maxEntangledOp m * ((1 : Op m) ⊗ B)).trace = B.trace := by
  rw [trace_maxEntangled_mul_tensor, Matrix.one_mul, Matrix.trace_transpose]

/-- `Tr[Ω * (B ⊗ 𝟙)] = Tr[B]` where `Ω = maxEntangledOp`. -/
lemma trace_maxEntangled_mul_tensor_one {m : ℕ} (B : Op m) :
    (maxEntangledOp m * (B ⊗ (1 : Op m))).trace = B.trace := by
  rw [trace_maxEntangled_mul_tensor, Matrix.transpose_one, Matrix.mul_one]

/-- Entry formula for `Ω * (M ⊗ 1)`: the `(i,j)` entry is `δ_{i₁=i₂} · M_{j₂,j₁}`. -/
private lemma maxEntangledOp_mul_tensor_one_entry {m : ℕ} (M : Op m)
    (i j : Fin (m * m)) :
    (maxEntangledOp m * (M ⊗ (1 : Op m))) i j =
    if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2
    then M (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1
    else 0 := by
  simp only [Matrix.mul_apply, maxEntangledOp, Matrix.of_apply, Op.tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p =>
    (if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 ∧ p.1 = p.2
      then 1 else 0) *
    (M p.1 (finProdFinEquiv.symm j).1 *
      (if p.2 = (finProdFinEquiv.symm j).2 then 1 else 0)))
    (by intro k; simp)]
  rw [Fintype.sum_prod_type]
  simp only [ite_and, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2
  · simp only [hi, ite_true]
    have inner_eq : ∀ x : Fin m, (∑ x_1, if x_1 = (finProdFinEquiv.symm j).2
        then if x = x_1 then M x (finProdFinEquiv.symm j).1 else 0 else 0) =
        if x = (finProdFinEquiv.symm j).2 then M x (finProdFinEquiv.symm j).1 else 0 := by
      intro x
      rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
    simp_rw [inner_eq]
    rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
  · simp only [hi, ite_false]
    apply Finset.sum_eq_zero
    intro _ _
    apply Finset.sum_eq_zero
    intro _ _
    split_ifs <;> rfl

/-- Entry formula for `(M ⊗ 1) · |Ω⟩`: the component at index
`finProdFinEquiv (i, j)` is `M i j`.

This is the ket-side counterpart of `maxEntangledOp_mul_tensor_one_entry` and is
the indispensable index-level computation behind
`Quantum.Metrics.KitaevWatrousPurification.Ket.exists_vec_repr`. -/
lemma maxEntangledKet_tensor_one_apply {d : ℕ} (M : Op d) (i j : Fin d) :
    ((Op.tensor M (1 : Op d)) * maxEntangledKet d).vec
        (finProdFinEquiv (i, j))
      = M i j := by
  rw [op_mul_ket_vec]
  simp only [Matrix.mulVec, dotProduct, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
    maxEntangledKet, Equiv.symm_apply_apply]
  -- Reindex `k : Fin (d * d)` as a pair via `finProdFinEquiv.symm`.
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin d × Fin d =>
      M i p.1 * (if j = p.2 then 1 else 0) *
        (if p.1 = p.2 then (1 : ℂ) else 0))
    (by intro k; simp)]
  rw [Fintype.sum_prod_type]
  -- Inner sum over the second component collapses via `a = b`.
  have inner : ∀ a : Fin d,
      (∑ b : Fin d, M i a * (if j = b then (1 : ℂ) else 0) *
          (if a = b then 1 else 0)) =
      if a = j then M i a else 0 := by
    intro a
    rw [Finset.sum_eq_single a]
    · by_cases h : a = j
      · subst h; simp
      · have hj : j ≠ a := fun h' => h h'.symm
        simp [hj, h]
    · intros b _ hba
      have hab : a ≠ b := fun h => hba h.symm
      simp [hab]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [inner]
  rw [Finset.sum_ite_eq' Finset.univ j (fun a => M i a)]
  simp [Finset.mem_univ]

/-- Entry formula for `(1 ⊗ N) · |Ω⟩`: the component at index
`finProdFinEquiv (i, j)` is `N j i`.

This is the sibling of `maxEntangledKet_tensor_one_apply` used to prove the
ricochet identity `(A ⊗ 1) |Ω⟩ = (1 ⊗ Aᵀ) |Ω⟩` in
`Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet`. -/
lemma maxEntangledKet_one_tensor_apply {d : ℕ} (N : Op d) (i j : Fin d) :
    ((Op.tensor (1 : Op d) N) * maxEntangledKet d).vec
        (finProdFinEquiv (i, j))
      = N j i := by
  rw [op_mul_ket_vec]
  simp only [Matrix.mulVec, dotProduct, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, kroneckerMap_apply, Matrix.one_apply,
    maxEntangledKet, Equiv.symm_apply_apply]
  -- Reindex `k : Fin (d * d)` as a pair via `finProdFinEquiv.symm`.
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin d × Fin d =>
      (if i = p.1 then (1 : ℂ) else 0) * N j p.2 *
        (if p.1 = p.2 then (1 : ℂ) else 0))
    (by intro k; simp)]
  rw [Fintype.sum_prod_type]
  -- Inner sum over the second component collapses via `a = b`.
  have inner : ∀ a : Fin d,
      (∑ b : Fin d, (if i = a then (1 : ℂ) else 0) * N j b *
          (if a = b then 1 else 0)) =
      if i = a then N j a else 0 := by
    intro a
    rw [Finset.sum_eq_single a]
    · by_cases h : i = a
      · simp [h]
      · simp [h]
    · intros b _ hba
      have hab : a ≠ b := fun h => hba h.symm
      simp [hab]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [inner]
  rw [Finset.sum_ite_eq Finset.univ i (fun a => N j a)]
  simp [Finset.mem_univ]

/-- Sandwich identity: `Ω * (M ⊗ 𝟙) * Ω = Tr(M) • Ω`. -/
lemma maxEntangledOp_sandwich {m : ℕ} (M : Op m) :
    maxEntangledOp m * (M ⊗ (1 : Op m)) * maxEntangledOp m = M.trace • maxEntangledOp m := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp_rw [maxEntangledOp_mul_tensor_one_entry]
  by_cases hi : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2
  · simp only [hi, ite_true]
    simp_rw [maxEntangledOp, Matrix.of_apply]
    simp only [hi]
    rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p =>
      M p.2 p.1 * if p.1 = p.2 ∧ (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2
                   then 1 else 0)
      (by intro k; simp)]
    rw [Fintype.sum_prod_type]
    simp only [ite_and, mul_ite, mul_one, mul_zero]
    by_cases hj : (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2
    · simp only [hj, ite_true]
      simp_rw [Finset.sum_ite_eq Finset.univ, Finset.mem_univ, ite_true]
      simp [trace, Matrix.diag]
    · simp [trace, Matrix.diag]
  · simp only [hi, ite_false, zero_mul, Finset.sum_const_zero]
    have hΩ : maxEntangledOp m i j = 0 := by
      simp only [maxEntangledOp, Matrix.of_apply,
        show ¬((finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 ∧ _) from
          fun h => hi h.1, ite_false]
    rw [hΩ, mul_zero]

/-- `Ω · Ω = m · Ω`: the unnormalized maximally entangled operator has `Ω/m`
idempotent.  Immediate from `maxEntangledOp_sandwich` at `M = 1`. -/
lemma maxEntangledOp_mul_self (m : ℕ) :
    maxEntangledOp m * maxEntangledOp m = (m : ℂ) • maxEntangledOp m := by
  have h := maxEntangledOp_sandwich (1 : Op m)
  rw [Op.tensor_one, Matrix.mul_one, Matrix.trace_one, Fintype.card_fin] at h
  exact h

/-- `Ω^{1/2} = m^{-1/2} · Ω`: the positive square root of the unnormalized
maximally entangled operator rescales it, because `Ω/m` is a projection. -/
lemma sqrt_maxEntangledOp (m : ℕ) [NeZero m] :
    CFC.sqrt (maxEntangledOp m) = ((1 / Real.sqrt m : ℝ) : ℂ) • maxEntangledOp m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hcR : (1 / Real.sqrt m : ℝ) * (1 / Real.sqrt m) * (m : ℝ) = 1 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hmR.le]
    field_simp
  have hc : ((1 / Real.sqrt m : ℝ) : ℂ) * ((1 / Real.sqrt m : ℝ) : ℂ) * (m : ℂ) = 1 := by
    rw [show (m : ℂ) = (((m : ℝ)) : ℂ) by norm_cast, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hcR, Complex.ofReal_one]
  have hnn : (0 : ℂ) ≤ ((1 / Real.sqrt m : ℝ) : ℂ) := by
    rw [Complex.le_def]
    refine ⟨?_, by simp⟩
    simp only [Complex.zero_re, Complex.ofReal_re]
    positivity
  refine CFC.sqrt_unique ?_ ((maxEntangledOp_posSemidef m).smul hnn).nonneg
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, maxEntangledOp_mul_self, smul_smul,
    hc, one_smul]

end InfoTheory.DeFinetti
