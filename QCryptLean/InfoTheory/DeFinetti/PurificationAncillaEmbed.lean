import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.InfoTheory.DeFinetti.Measure
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# Zero-padding embedding of the second tensor factor

Definition, purity, partial trace, continuity and strong measurability.  This module
provides a zero-padding embedding
`padDensityOpAncillaB : DensityOp (n*m₁) → DensityOp (n*m₂)`
for `m₁ ≤ m₂`: the input density operator is embedded into the larger ancilla
register by setting the new ancilla indices to zero (block-diagonal padding).

It is used in the BB84 Path-A construction of the per-σ τ-side purification:
the standard `(√ρ ⊗ 𝟙)|Ω⟩` purification of `σ.tensorPowGen n` lives on
`(d^n)*(d^n)`, but the BB84 cascade fixes the ancilla register to a larger
`dimR` (usually `Nat.choose (n + d² - 1, d² - 1)`); zero-padding bridges the
two without affecting the partial trace on the first factor.

## Main definitions
- `InfoTheory.DeFinetti.padOpAncillaB`: entrywise zero-padding on `Op`.
- `InfoTheory.DeFinetti.padDensityOpAncillaB`: zero-padding lifted to density
  operators.

## Main statements
- `padOpAncillaB_isHermitian`, `padOpAncillaB_trace`, `padOpAncillaB_posSemidef`,
  `padOpAncillaB_mul`: structural properties of entrywise padding.
- `padDensityOpAncillaB_isPure`: padding preserves purity (`ρ² = ρ`).
- `padDensityOpAncillaB_partialTraceB`: padding does not affect the marginal
  on the first factor, i.e.
  `(padDensityOpAncillaB h ρ).partialTraceB = ρ.partialTraceB`.
- `padDensityOpAncillaB_continuous`: continuity in `ρ`.
- `padDensityOpAncillaB_purification_tensorPow_stronglyMeasurable`: strong
  measurability of `σ ↦ padDensityOpAncillaB h (purificationDensityOp
  (σ.tensorPowGen n))`, used in the BB84 per-σ τ-side Bochner integral.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-! ### Entrywise zero-padding on `Op` -/

/-- Zero-padding of an operator on `n*m₁` to `n*m₂` (`m₁ ≤ m₂`): nonzero
entries only at indices `(a, k)` with `k.val < m₁`. -/
noncomputable def padOpAncillaB {n m₁ m₂ : ℕ} (_h : m₁ ≤ m₂) (ρ : Op (n * m₁)) :
    Op (n * m₂) :=
  Matrix.of fun i j =>
    let p := finProdFinEquiv.symm i
    let q := finProdFinEquiv.symm j
    if hp : p.2.val < m₁ then
      if hq : q.2.val < m₁ then
        ρ (finProdFinEquiv (p.1, ⟨p.2.val, hp⟩))
          (finProdFinEquiv (q.1, ⟨q.2.val, hq⟩))
      else 0
    else 0

/-- The subset of `Fin m₂` with index value less than `m₁` is the image of
`Fin.castLE h` from `Fin m₁`. -/
lemma image_castLE_eq_filter_lt {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    (Finset.univ : Finset (Fin m₂)).filter (fun k : Fin m₂ => k.val < m₁) =
      (Finset.univ : Finset (Fin m₁)).image (Fin.castLE h) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  refine ⟨fun hk => ⟨⟨k.val, hk⟩, by ext; rfl⟩, ?_⟩
  rintro ⟨k₁, rfl⟩
  exact k₁.is_lt

/-- A sum over `Fin m₂` of a function vanishing outside the first `m₁` indices
collapses to the corresponding sum over `Fin m₁` after lifting via `Fin.castLE h`. -/
lemma sum_eq_sum_castLE {m₁ m₂ : ℕ} {α : Type*} [AddCommMonoid α]
    (h : m₁ ≤ m₂) (f : Fin m₂ → α)
    (hf : ∀ k : Fin m₂, ¬ k.val < m₁ → f k = 0) :
    ∑ k : Fin m₂, f k = ∑ k : Fin m₁, f (Fin.castLE h k) := by
  classical
  rw [show (∑ k : Fin m₂, f k) =
        (∑ k ∈ (Finset.univ : Finset (Fin m₂)).filter (fun k => k.val < m₁), f k) +
        (∑ k ∈ (Finset.univ : Finset (Fin m₂)).filter (fun k => ¬ k.val < m₁), f k) from
      (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun k : Fin m₂ => k.val < m₁) _).symm]
  have hzero :
      (∑ k ∈ (Finset.univ : Finset (Fin m₂)).filter (fun k => ¬ k.val < m₁), f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hf k hk
  rw [hzero, add_zero, image_castLE_eq_filter_lt h,
      Finset.sum_image (fun _ _ _ _ hk => Fin.castLE_injective h hk)]

lemma padOpAncillaB_apply_lift {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (ρ : Op (n * m₁)) (a b : Fin n) (k l : Fin m₁) :
    padOpAncillaB h ρ
        (finProdFinEquiv (a, Fin.castLE h k))
        (finProdFinEquiv (b, Fin.castLE h l)) =
      ρ (finProdFinEquiv (a, k)) (finProdFinEquiv (b, l)) := by
  simp only [padOpAncillaB, Matrix.of_apply, Equiv.symm_apply_apply]
  have hp : (Fin.castLE h k).val < m₁ := k.is_lt
  have hq : (Fin.castLE h l).val < m₁ := l.is_lt
  rw [dif_pos hp, dif_pos hq]
  congr 2

/-- Variant of `padOpAncillaB_apply_lift` taking the index hypotheses directly. -/
lemma padOpAncillaB_apply_lift' {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (ρ : Op (n * m₁))
    (i j : Fin (n * m₂))
    (hi : (finProdFinEquiv.symm i).2.val < m₁)
    (hj : (finProdFinEquiv.symm j).2.val < m₁) :
    padOpAncillaB h ρ i j =
    ρ (finProdFinEquiv ((finProdFinEquiv.symm i).1,
        ⟨(finProdFinEquiv.symm i).2.val, hi⟩))
      (finProdFinEquiv ((finProdFinEquiv.symm j).1,
        ⟨(finProdFinEquiv.symm j).2.val, hj⟩)) := by
  simp only [padOpAncillaB, Matrix.of_apply]
  rw [dif_pos hi, dif_pos hj]

lemma padOpAncillaB_apply_zero_left {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (ρ : Op (n * m₁)) (i j : Fin (n * m₂))
    (hi : ¬ (finProdFinEquiv.symm i).2.val < m₁) :
    padOpAncillaB h ρ i j = 0 := by
  simp only [padOpAncillaB, Matrix.of_apply]
  rw [dif_neg hi]

lemma padOpAncillaB_apply_zero_right {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (ρ : Op (n * m₁)) (i j : Fin (n * m₂))
    (hj : ¬ (finProdFinEquiv.symm j).2.val < m₁) :
    padOpAncillaB h ρ i j = 0 := by
  simp only [padOpAncillaB, Matrix.of_apply]
  by_cases hi : (finProdFinEquiv.symm i).2.val < m₁
  · rw [dif_pos hi, dif_neg hj]
  · rw [dif_neg hi]

/-- Padding preserves Hermiticity. -/
lemma padOpAncillaB_isHermitian {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    {ρ : Op (n * m₁)} (hρ : ρ.IsHermitian) :
    (padOpAncillaB h ρ).IsHermitian := by
  ext i j
  change star (padOpAncillaB h ρ j i) = padOpAncillaB h ρ i j
  simp only [padOpAncillaB, Matrix.of_apply]
  by_cases hi : (finProdFinEquiv.symm i).2.val < m₁
  · by_cases hj : (finProdFinEquiv.symm j).2.val < m₁
    · rw [dif_pos hj, dif_pos hi, dif_pos hi, dif_pos hj]
      have hh := congrFun (congrFun hρ
        (finProdFinEquiv ((finProdFinEquiv.symm i).1,
          ⟨(finProdFinEquiv.symm i).2.val, hi⟩)))
        (finProdFinEquiv ((finProdFinEquiv.symm j).1,
          ⟨(finProdFinEquiv.symm j).2.val, hj⟩))
      simpa [Matrix.conjTranspose, Matrix.transpose] using hh
    · rw [dif_pos hi, dif_neg hj, dif_neg hj]
      simp
  · rw [dif_neg hi]
    by_cases hj : (finProdFinEquiv.symm j).2.val < m₁
    · rw [dif_pos hj, dif_neg hi]; simp
    · rw [dif_neg hj]; simp

/-- Padding preserves the trace. -/
lemma padOpAncillaB_trace {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (ρ : Op (n * m₁)) :
    (padOpAncillaB h ρ).trace = ρ.trace := by
  have h1 : (padOpAncillaB h ρ).trace = (partialTraceB (padOpAncillaB h ρ)).trace :=
    (Quantum.TensorProducts.trace_partialTraceB (padOpAncillaB h ρ)).symm
  have h2 : ρ.trace = (partialTraceB ρ).trace :=
    (Quantum.TensorProducts.trace_partialTraceB ρ).symm
  rw [h1, h2]
  unfold partialTraceB
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.of_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_eq_sum_castLE h
        (fun k => padOpAncillaB h ρ (finProdFinEquiv (i, k)) (finProdFinEquiv (i, k)))
        (fun k hk => padOpAncillaB_apply_zero_left h ρ _ _ (by simpa using hk))]
  apply Finset.sum_congr rfl
  intro k _
  exact padOpAncillaB_apply_lift (n := n) (m₁ := m₁) (m₂ := m₂) h ρ i i k k

/-- Padding preserves trace = 1. -/
lemma padOpAncillaB_trace_one {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    {ρ : Op (n * m₁)} (hρ : ρ.trace = 1) :
    (padOpAncillaB h ρ).trace = 1 := by
  rw [padOpAncillaB_trace, hρ]

/-- General reindexing helper: if `f : Fin (n * m₂) → α` vanishes on indices
whose `Fin m₂`-component is outside the image of `Fin.castLE h`, then summing
`f` over `Fin (n * m₂)` equals summing the lifted values over `Fin (n * m₁)`. -/
lemma sum_castLE_finProdFinEquiv {n m₁ m₂ : ℕ} {α : Type*} [AddCommMonoid α]
    (h : m₁ ≤ m₂) (f : Fin (n * m₂) → α)
    (hf : ∀ I : Fin (n * m₂), ¬ (finProdFinEquiv.symm I).2.val < m₁ → f I = 0) :
    ∑ I : Fin (n * m₂), f I =
      ∑ I' : Fin (n * m₁), f (finProdFinEquiv
        ((finProdFinEquiv.symm I').1, Fin.castLE h (finProdFinEquiv.symm I').2)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f, Fintype.sum_prod_type]
  rw [← Equiv.sum_comp finProdFinEquiv
        (fun I' : Fin (n * m₁) =>
          f (finProdFinEquiv ((finProdFinEquiv.symm I').1,
              Fin.castLE h (finProdFinEquiv.symm I').2))),
      Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact sum_eq_sum_castLE h (fun k => f (finProdFinEquiv (a, k)))
    (fun k hk => hf _ (by simpa using hk))

/-- `padOpAncillaB` applied at lifted indices equals `ρ` at the original indices.
This packages `padOpAncillaB_apply_lift` for the inline embedding form. -/
lemma padOpAncillaB_apply_castLE_embed {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (ρ : Op (n * m₁)) (I' J' : Fin (n * m₁)) :
    padOpAncillaB h ρ
        (finProdFinEquiv ((finProdFinEquiv.symm I').1,
            Fin.castLE h (finProdFinEquiv.symm I').2))
        (finProdFinEquiv ((finProdFinEquiv.symm J').1,
            Fin.castLE h (finProdFinEquiv.symm J').2)) = ρ I' J' := by
  have hI : (finProdFinEquiv
      ((finProdFinEquiv.symm I').1, (finProdFinEquiv.symm I').2)
        : Fin (n * m₁)) = I' := by
    rw [Prod.mk.eta]; exact finProdFinEquiv.apply_symm_apply I'
  have hJ : (finProdFinEquiv
      ((finProdFinEquiv.symm J').1, (finProdFinEquiv.symm J').2)
        : Fin (n * m₁)) = J' := by
    rw [Prod.mk.eta]; exact finProdFinEquiv.apply_symm_apply J'
  conv_rhs => rw [← hI, ← hJ]
  exact padOpAncillaB_apply_lift h ρ _ _ _ _

/-- Key identity: the quadratic form of the zero-padded operator on `x` equals
the quadratic form of the original operator on the restriction of `x` to the
image of the lift. -/
lemma padOpAncillaB_quadraticForm_eq
    {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (ρ : Op (n * m₁)) (x : Fin (n * m₂) → ℂ) :
    quadraticForm (padOpAncillaB h ρ) x =
      quadraticForm ρ
        (fun j : Fin (n * m₁) =>
          x (finProdFinEquiv
              ((finProdFinEquiv.symm j).1, Fin.castLE h (finProdFinEquiv.symm j).2))) := by
  classical
  change dotProduct (star x) ((padOpAncillaB h ρ).mulVec x) =
       dotProduct (star (fun j : Fin (n * m₁) => x (finProdFinEquiv
         ((finProdFinEquiv.symm j).1, Fin.castLE h (finProdFinEquiv.symm j).2))))
         (ρ.mulVec (fun j : Fin (n * m₁) => x (finProdFinEquiv
           ((finProdFinEquiv.symm j).1, Fin.castLE h (finProdFinEquiv.symm j).2))))
  unfold dotProduct
  rw [sum_castLE_finProdFinEquiv (n := n) (m₁ := m₁) (m₂ := m₂) h
    (fun I => star x I * (padOpAncillaB h ρ).mulVec x I) ?_]
  · apply Finset.sum_congr rfl
    intro I' _
    change star x _ * _ =
         star (x _) * ρ.mulVec _ I'
    congr 1
    unfold Matrix.mulVec dotProduct
    rw [sum_castLE_finProdFinEquiv (n := n) (m₁ := m₁) (m₂ := m₂) h
      (fun J => padOpAncillaB h ρ
        (finProdFinEquiv ((finProdFinEquiv.symm I').1,
            Fin.castLE h (finProdFinEquiv.symm I').2)) J * x J) ?_]
    · apply Finset.sum_congr rfl
      intro J' _
      rw [padOpAncillaB_apply_castLE_embed h ρ I' J']
    · intro J hJ
      dsimp only
      rw [padOpAncillaB_apply_zero_right h ρ _ J hJ]
      ring
  · intro I hI
    dsimp only
    have h0 : (padOpAncillaB h ρ).mulVec x I = 0 := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_eq_zero
      intro J _
      dsimp only
      rw [padOpAncillaB_apply_zero_left h ρ I J hI]
      ring
    rw [h0, mul_zero]

/-- Padding preserves positive-semidefiniteness (real-part of quadratic form). -/
lemma padOpAncillaB_posSemidef {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (ρ : PosSemidefOp (n * m₁)) :
    ∀ x : Fin (n * m₂) → ℂ, 0 ≤ (quadraticForm (padOpAncillaB h ρ.toOp) x).re := by
  intro x
  rw [padOpAncillaB_quadraticForm_eq h ρ.toOp x]
  exact ρ.pos_semidef _

/-! ### `padDensityOpAncillaB` -/

/-- Zero-padding embedding of a density operator from `n*m₁` to `n*m₂`,
where `m₁ ≤ m₂`: extends the second tensor factor by zero. -/
noncomputable def padDensityOpAncillaB {n m₁ m₂ : ℕ}
    [NeZero (n * m₁)] [NeZero (n * m₂)]
    (h : m₁ ≤ m₂) (ρ : DensityOp (n * m₁)) :
    DensityOp (n * m₂) :=
  ⟨⟨⟨padOpAncillaB h ρ.toOp,
      padOpAncillaB_isHermitian h ρ.toPosSemidefOp.toHermitianOp.isHermitian⟩,
    padOpAncillaB_posSemidef h ρ.toPosSemidefOp⟩,
   padOpAncillaB_trace_one h ρ.trace_one⟩

@[simp] lemma padDensityOpAncillaB_toOp {n m₁ m₂ : ℕ}
    [NeZero (n * m₁)] [NeZero (n * m₂)]
    (h : m₁ ≤ m₂) (ρ : DensityOp (n * m₁)) :
    (padDensityOpAncillaB h ρ).toOp = padOpAncillaB h ρ.toOp := rfl

/-- Padding distributes over operator multiplication: the convolution sum on
the larger ancilla picks up only the lifted indices, and the off-image entries
contribute zero. -/
lemma padOpAncillaB_mul {n m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (ρ σ : Op (n * m₁)) :
    padOpAncillaB h ρ * padOpAncillaB h σ = padOpAncillaB h (ρ * σ) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (finProdFinEquiv.symm i).2.val < m₁
  · by_cases hj : (finProdFinEquiv.symm j).2.val < m₁
    · rw [padOpAncillaB_apply_lift' h _ i j hi hj, Matrix.mul_apply]
      rw [← Equiv.sum_comp finProdFinEquiv
          (fun k => padOpAncillaB h ρ i k * padOpAncillaB h σ k j),
        Fintype.sum_prod_type]
      rw [← Equiv.sum_comp finProdFinEquiv
          (fun p => ρ (finProdFinEquiv ((finProdFinEquiv.symm i).1,
                       ⟨(finProdFinEquiv.symm i).2.val, hi⟩)) p *
                   σ p (finProdFinEquiv ((finProdFinEquiv.symm j).1,
                       ⟨(finProdFinEquiv.symm j).2.val, hj⟩))),
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_eq_sum_castLE h
            (fun b => padOpAncillaB h ρ i (finProdFinEquiv (a, b)) *
                       padOpAncillaB h σ (finProdFinEquiv (a, b)) j)
            (fun b hb => by
              dsimp only
              rw [padOpAncillaB_apply_zero_right h ρ i (finProdFinEquiv (a, b))
                    (by simpa using hb)]
              ring)]
      apply Finset.sum_congr rfl
      intro k₁ _
      have hk_lt : (finProdFinEquiv.symm
          (finProdFinEquiv (a, Fin.castLE h k₁))).2.val < m₁ := by
        simp [Fin.castLE]
      rw [padOpAncillaB_apply_lift' h ρ i _ hi hk_lt,
          padOpAncillaB_apply_lift' h σ _ j hk_lt hj]
      have h_a_eq : (finProdFinEquiv.symm
          (finProdFinEquiv (a, Fin.castLE h k₁))).1 = a := by
        simp
      have h_k_eq : (⟨(finProdFinEquiv.symm
          (finProdFinEquiv (a, Fin.castLE h k₁))).2.val, hk_lt⟩ : Fin m₁) = k₁ := by
        apply Fin.ext
        simp [Fin.castLE]
      rw [h_a_eq, h_k_eq]
    · rw [padOpAncillaB_apply_zero_right h (ρ * σ) i j hj]
      apply Finset.sum_eq_zero
      intro k _
      rw [padOpAncillaB_apply_zero_right h σ k j hj]
      ring
  · rw [padOpAncillaB_apply_zero_left h (ρ * σ) i j hi]
    apply Finset.sum_eq_zero
    intro k _
    rw [padOpAncillaB_apply_zero_left h ρ i k hi]
    ring

/-- Padding the second factor preserves purity (`ρ * ρ = ρ`). -/
lemma padDensityOpAncillaB_isPure {n m₁ m₂ : ℕ}
    [NeZero (n * m₁)] [NeZero (n * m₂)]
    (h : m₁ ≤ m₂) {ρ : DensityOp (n * m₁)} (hρ : ρ.IsPure) :
    (padDensityOpAncillaB h ρ).IsPure := by
  change (padDensityOpAncillaB h ρ).toOp * (padDensityOpAncillaB h ρ).toOp =
    (padDensityOpAncillaB h ρ).toOp
  rw [padDensityOpAncillaB_toOp, padOpAncillaB_mul,
    show ρ.toOp * ρ.toOp = ρ.toOp from hρ]

/-- Padding the second factor does not affect the partial trace on the first. -/
lemma padDensityOpAncillaB_partialTraceB {n m₁ m₂ : ℕ}
    [NeZero (n * m₁)] [NeZero (n * m₂)]
    (h : m₁ ≤ m₂) (ρ : DensityOp (n * m₁)) :
    ((padDensityOpAncillaB h ρ).partialTraceB).toOp =
      (ρ.partialTraceB).toOp := by
  ext i j
  change partialTraceB (padOpAncillaB h ρ.toOp) i j = partialTraceB ρ.toOp i j
  unfold partialTraceB
  simp only [Matrix.of_apply]
  rw [sum_eq_sum_castLE h
        (fun k => padOpAncillaB h ρ.toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)))
        (fun k hk => padOpAncillaB_apply_zero_left h _ _ _ (by simpa using hk))]
  apply Finset.sum_congr rfl
  intro k _
  exact padOpAncillaB_apply_lift (n := n) (m₁ := m₁) (m₂ := m₂) h ρ.toOp i j k k

/-- Padding is continuous as a map between density operators. -/
lemma padDensityOpAncillaB_continuous {n m₁ m₂ : ℕ}
    [NeZero (n * m₁)] [NeZero (n * m₂)]
    (h : m₁ ≤ m₂) :
    Continuous (padDensityOpAncillaB (n := n) (m₁ := m₁) (m₂ := m₂) h) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun ρ : DensityOp (n * m₁) => padOpAncillaB h ρ.toOp i j)
  simp only [padOpAncillaB, Matrix.of_apply]
  by_cases hi : (finProdFinEquiv.symm i).2.val < m₁
  · by_cases hj : (finProdFinEquiv.symm j).2.val < m₁
    · simp only [dif_pos hi, dif_pos hj]
      exact (continuous_apply _).comp ((continuous_apply _).comp continuous_induced_dom)
    · simp only [dif_pos hi, dif_neg hj]
      exact continuous_const
  · simp only [dif_neg hi]
    exact continuous_const

/-! ### Strong measurability of the per-σ purification function -/

/-- The map `σ ↦ padDensityOpAncillaB h (purificationDensityOp (σ.tensorPowGen n))`
is strongly measurable. -/
lemma padDensityOpAncillaB_purification_tensorPow_stronglyMeasurable
    {d n m₂ : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n * m₂)]
    (h : d ^ n ≤ m₂) :
    MeasureTheory.StronglyMeasurable
      (fun σ : DensityOp d =>
        padDensityOpAncillaB h (purificationDensityOp (σ.tensorPowGen n))) := by
  haveI : NeZero (d ^ n) := Nat.instNeZeroHPow
  haveI : NeZero (d ^ n * d ^ n) := instNeZeroNatHMul
  have hcont : Continuous (fun σ : DensityOp d =>
      padDensityOpAncillaB h (purificationDensityOp (σ.tensorPowGen n))) :=
    (padDensityOpAncillaB_continuous h).comp
      (purificationDensityOp_continuous.comp tensorPowGen_continuous)
  have hind : Topology.IsInducing
      (fun ρ : DensityOp (d ^ n * m₂) => ρ.toOp) := Topology.IsInducing.mk rfl
  haveI : TopologicalSpace.PseudoMetrizableSpace (Op (d ^ n * m₂)) :=
    show TopologicalSpace.PseudoMetrizableSpace
        (Fin (d ^ n * m₂) → Fin (d ^ n * m₂) → ℂ) from inferInstance
  haveI : SecondCountableTopology (Op (d ^ n * m₂)) :=
    show SecondCountableTopology
        (Fin (d ^ n * m₂) → Fin (d ^ n * m₂) → ℂ) from inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace (DensityOp (d ^ n * m₂)) :=
    hind.pseudoMetrizableSpace
  haveI : SecondCountableTopology (DensityOp (d ^ n * m₂)) :=
    hind.secondCountableTopology
  haveI : SecondCountableTopologyEither (DensityOp d) (DensityOp (d ^ n * m₂)) :=
    secondCountableTopologyEither_of_right _ _
  exact hcont.stronglyMeasurable

/-- A rank bound permits purification on any larger nonempty ancillary register. -/
lemma densityOp_purification_exists_of_rank_le {m r : ℕ} [NeZero m] [NeZero r]
    (ρ : DensityOp m) (hr : Matrix.rank ρ.toOp ≤ r) :
    ∃ ψ : DensityOp (m * r), ψ.IsPure ∧ partialTraceB ψ.toOp = ρ.toOp := by
  haveI : NeZero (Matrix.rank ρ.toOp) := ⟨(densityOp_rank_pos ρ).ne'⟩
  obtain ⟨ψ, hpure, hmarg⟩ := densityOp_purification_exists_at_rank ρ
  refine ⟨padDensityOpAncillaB hr ψ, padDensityOpAncillaB_isPure hr hpure, ?_⟩
  exact (padDensityOpAncillaB_partialTraceB hr ψ).trans hmarg

end InfoTheory.DeFinetti

end
