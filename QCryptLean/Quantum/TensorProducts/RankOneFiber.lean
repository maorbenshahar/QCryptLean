import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Rank-one operators on a bipartite register: slices, marginal, and fiber Cauchy–Schwarz

A vector `φ` on `A ⊗ C` (dimension `dA * dC`, `A` major under `finProdFinEquiv`) is determined by
its **`C`-slices** `χ_a := φ(a, ·)`. This file records the three index computations that turn the
rank-one operator `|φ⟩⟨φ| = vecMulVec φ (star φ)` and its `C`-marginal into slice coordinates:

* `quadraticForm_vecMulVec_star`: `⟨v| |φ⟩⟨φ| |v⟩ = ‖⟨v, φ⟩‖²`.
* `dotProduct_star_eq_sum_bipartiteSlice`: `⟨v, φ⟩ = ∑_a ⟨η_a, χ_a⟩` (slice decomposition of the
  inner product).
* `partialTraceA_vecMulVec_star`: `Tr_A |φ⟩⟨φ| = ∑_a |χ_a⟩⟨χ_a|` (the marginal identity).
* `quadraticForm_one_tensor_eq_sum_bipartiteSlice`: `⟨v| 1_A ⊗ σ |v⟩ = ∑_a ⟨η_a| σ |η_a⟩`.

together with the discrete Cauchy–Schwarz inequality `normSq_sum_le_card_mul_sum_normSq`
(`‖∑_{i ∈ s} f i‖² ≤ |s| · ∑_{i ∈ s} ‖f i‖²`) against the all-ones vector.

These are the atoms of the rank-one **fiber domination** `|φ⟩⟨φ| ≼ K · (1_A ⊗ Tr_A |φ⟩⟨φ|)` for a
`φ` whose nonzero `A`-slices number at most `K`.  That theorem is
`Quantum.TensorProducts.vecMulVec_opLe_card_smul_one_tensor_partialTraceA` in
`QCryptLean.Quantum.Operators.RankOneOrder`, which is where it sits next to the
non-bipartite operator Cauchy–Schwarz inequality it shares its proof idea with.
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.TensorProducts

variable {dA dC : ℕ}

/-! ### Slices of a bipartite vector -/

/-- The `C`-slice of a bipartite vector `φ` on `A ⊗ C` at the Alice index `a`: the `dC`-block
`c ↦ φ(a, c)` of `φ` under the `A`-major encoding `finProdFinEquiv`. -/
def bipartiteSlice (φ : Fin (dA * dC) → ℂ) (a : Fin dA) : Fin dC → ℂ :=
  fun c => φ (finProdFinEquiv (a, c))

@[simp]
lemma bipartiteSlice_apply (φ : Fin (dA * dC) → ℂ) (a : Fin dA) (c : Fin dC) :
    bipartiteSlice φ a c = φ (finProdFinEquiv (a, c)) := rfl

/-- A bipartite vector whose slice at `a` vanishes identically. -/
lemma bipartiteSlice_eq_zero {φ : Fin (dA * dC) → ℂ} {a : Fin dA}
    (h : ∀ c : Fin dC, φ (finProdFinEquiv (a, c)) = 0) : bipartiteSlice φ a = 0 := by
  funext c
  simpa using h c

/-- The inner product `⟨v, φ⟩` of two bipartite vectors is the sum of the inner products of their
slices. -/
lemma dotProduct_star_eq_sum_bipartiteSlice (φ v : Fin (dA * dC) → ℂ) :
    star v ⬝ᵥ φ = ∑ a : Fin dA, star (bipartiteSlice v a) ⬝ᵥ bipartiteSlice φ a := by
  simp only [dotProduct, bipartiteSlice, Pi.star_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := dA) (n := dC)), Fintype.sum_prod_type]

/-! ### Rank-one quadratic forms -/

/-- **The quadratic form of a rank-one operator.** `⟨v| |φ⟩⟨φ| |v⟩ = ‖⟨v, φ⟩‖²`. -/
lemma quadraticForm_vecMulVec_star {n : ℕ} (φ v : Fin n → ℂ) :
    quadraticForm (Matrix.vecMulVec φ (star φ)) v = (Complex.normSq (star v ⬝ᵥ φ) : ℂ) := by
  have hmv : (Matrix.vecMulVec φ (star φ)).mulVec v = fun i => φ i * (star φ ⬝ᵥ v) := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc]
  have hconj : star φ ⬝ᵥ v = conj (star v ⬝ᵥ φ) := by
    simp [dotProduct, map_sum, mul_comm]
  have hdot : star v ⬝ᵥ (fun i => φ i * (star φ ⬝ᵥ v)) = (star v ⬝ᵥ φ) * (star φ ⬝ᵥ v) := by
    simp [dotProduct, Finset.sum_mul, mul_assoc]
  unfold quadraticForm
  rw [hmv, hdot, hconj, Complex.mul_conj]

/-- **The quadratic form of a sum of rank-one operators.** -/
lemma quadraticForm_sum_vecMulVec_star {ι : Type*} [Fintype ι] {n : ℕ}
    (u : ι → Fin n → ℂ) (x : Fin n → ℂ) :
    quadraticForm (∑ b, Matrix.vecMulVec (u b) (star (u b))) x =
      ((∑ b, Complex.normSq (star x ⬝ᵥ u b) : ℝ) : ℂ) := by
  have hsum : quadraticForm (∑ b, Matrix.vecMulVec (u b) (star (u b))) x =
      ∑ b, quadraticForm (Matrix.vecMulVec (u b) (star (u b))) x := by
    simp only [quadraticForm, Matrix.sum_mulVec, dotProduct_sum]
  rw [hsum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun b _ => quadraticForm_vecMulVec_star (u b) x

/-! ### The `C`-marginal of a rank-one bipartite operator -/

/-- **The marginal identity.** The `C`-marginal of the rank-one operator `|φ⟩⟨φ|` on `A ⊗ C` is the
sum of the rank-one operators built from the `C`-slices of `φ`:
`Tr_A |φ⟩⟨φ| = ∑_a |χ_a⟩⟨χ_a|`. -/
lemma partialTraceA_vecMulVec_star (φ : Fin (dA * dC) → ℂ) :
    partialTraceA (Matrix.vecMulVec φ (star φ)) =
      ∑ a : Fin dA, Matrix.vecMulVec (bipartiteSlice φ a) (star (bipartiteSlice φ a)) := by
  ext i j
  simp [partialTraceA, Matrix.vecMulVec_apply, Matrix.sum_apply, bipartiteSlice]

/-! ### Quadratic forms of `1_A ⊗ σ` -/

/-- `(1_A ⊗ σ) *ᵥ v` restricted to the `a`-block is `σ *ᵥ η_a`, where `η_a` is the `a`-slice. -/
lemma one_tensor_mulVec_apply (σ : Op dC) (v : Fin (dA * dC) → ℂ) (a : Fin dA) (c : Fin dC) :
    (Op.tensor (1 : Op dA) σ).mulVec v (finProdFinEquiv (a, c)) =
      σ.mulVec (bipartiteSlice v a) c := by
  simp only [mulVec, dotProduct, Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, Equiv.symm_apply_apply, bipartiteSlice]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := dA) (n := dC)), Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  simp

/-- **Slice decomposition of the `1_A ⊗ σ` quadratic form.** `⟨v| 1_A ⊗ σ |v⟩ = ∑_a ⟨η_a| σ |η_a⟩`,
the sum over Alice indices of the `σ`-quadratic forms of the `C`-slices of `v`. -/
lemma quadraticForm_one_tensor_eq_sum_bipartiteSlice (σ : Op dC) (v : Fin (dA * dC) → ℂ) :
    quadraticForm (Op.tensor (1 : Op dA) σ) v =
      ∑ a : Fin dA, quadraticForm σ (bipartiteSlice v a) := by
  simp only [quadraticForm, dotProduct]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := dA) (n := dC)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [one_tensor_mulVec_apply]
  rfl

/-! ### Discrete Cauchy–Schwarz against the all-ones vector -/

/-- **Finset Cauchy–Schwarz against the all-ones vector:** `‖∑_{i ∈ s} f i‖² ≤ |s| · ∑_{i ∈ s}
‖f i‖²`. This is the fiber-counting step: a sum of `|s|` complex numbers has squared modulus at
most `|s|` times the sum of their squared moduli, with equality iff they are all equal. -/
lemma normSq_sum_le_card_mul_sum_normSq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) ≤ (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  calc
    Complex.normSq (∑ i ∈ s, f i) = ‖∑ i ∈ s, f i‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
          simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
    _ = (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
          simp [Complex.normSq_eq_norm_sq]

/-- **The fiber Cauchy–Schwarz core.** For a square array `w` of complex numbers whose *diagonal* is
supported on a finset `S` of size at most `K`, the squared modulus of the diagonal sum is at most
`K` times the total sum of squared moduli:

  `‖∑_a w a a‖² ≤ K · ∑_a ∑_b ‖w a b‖²`.

Cauchy–Schwarz over the `≤ K`-element support `S` gives `‖∑_{a ∈ S} w a a‖² ≤ |S| · ∑_{a ∈ S}
‖w a a‖²`, and the diagonal terms are among the nonnegative terms of the full double sum. The bound
is exactly tight (take `w` diagonal with `|S| = K` equal entries and all off-diagonal entries
zero). -/
lemma normSq_sum_diag_le_card_mul_sum_normSq {n : ℕ} (w : Fin n → Fin n → ℂ)
    (S : Finset (Fin n)) (hsupp : ∀ a, a ∉ S → w a a = 0) {K : ℕ} (hK : S.card ≤ K) :
    Complex.normSq (∑ a, w a a) ≤ (K : ℝ) * ∑ a, ∑ b, Complex.normSq (w a b) := by
  classical
  have hdiag : ∑ a, w a a = ∑ a ∈ S, w a a :=
    (Finset.sum_subset (Finset.subset_univ S) fun a _ ha => hsupp a ha).symm
  have hdiag_le : ∑ a ∈ S, Complex.normSq (w a a) ≤ ∑ a, ∑ b, Complex.normSq (w a b) :=
    calc ∑ a ∈ S, Complex.normSq (w a a)
        ≤ ∑ a, Complex.normSq (w a a) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun a _ _ => Complex.normSq_nonneg _
      _ ≤ ∑ a, ∑ b, Complex.normSq (w a b) :=
          Finset.sum_le_sum fun a _ =>
            Finset.single_le_sum (f := fun b => Complex.normSq (w a b))
              (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have hnonneg : (0 : ℝ) ≤ ∑ a ∈ S, Complex.normSq (w a a) :=
    Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  calc Complex.normSq (∑ a, w a a)
      = Complex.normSq (∑ a ∈ S, w a a) := by rw [hdiag]
    _ ≤ (S.card : ℝ) * ∑ a ∈ S, Complex.normSq (w a a) := normSq_sum_le_card_mul_sum_normSq S _
    _ ≤ (K : ℝ) * ∑ a ∈ S, Complex.normSq (w a a) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hnonneg
    _ ≤ (K : ℝ) * ∑ a, ∑ b, Complex.normSq (w a b) :=
        mul_le_mul_of_nonneg_left hdiag_le (by positivity)

end Quantum.TensorProducts

end
