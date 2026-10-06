import QCryptLean.Quantum.TensorProducts.RankOneFiber

/-!
# Operator Cauchy–Schwarz: Löwner domination for rank-one operators

Two forms of the same estimate, both obtained by testing against a vector and applying the
discrete Cauchy–Schwarz inequality.

**Sums.** For a finite family of vectors `v : ι → (Fin n → ℂ)` indexed by a finset `s`, the
rank-one operator of the **sum** is dominated, in the operator-semidefinite (Löwner) order, by
`|s|` times the **sum** of the rank-one operators:

  `|∑_{i ∈ s} vᵢ⟩⟨∑_{i ∈ s} vᵢ|  ⪯  |s| · ∑_{i ∈ s} |vᵢ⟩⟨vᵢ|`.

Rank-one operators are written in the library's canonical spelling `Matrix.vecMulVec x (star x)`
(entry `(i, j) ↦ xᵢ · conj xⱼ`); no new rank-one definition is introduced.

Tested against a vector `x`, the inequality is the discrete Cauchy–Schwarz estimate
`‖∑_{i ∈ s} cᵢ‖² ≤ |s| · ∑_{i ∈ s} ‖cᵢ‖²` for `cᵢ = ⟨x, vᵢ⟩`
(`Quantum.TensorProducts.normSq_sum_le_card_mul_sum_normSq`), combined with the rank-one
quadratic-form identity `⟨x| |v⟩⟨v| |x⟩ = ‖⟨x, v⟩‖²`
(`Quantum.TensorProducts.quadraticForm_vecMulVec_star`).

Sharpness and degenerate cases.

* `|s| = 1` is an equality, and for pairwise orthogonal `vᵢ` tested against a single `vⱼ` the
  bound is attained up to the factor `|s|`; the factor cannot be improved in general (take all
  `vᵢ` equal to one unit vector `u` and test at `x = u`: the two sides are `|s|²` and `|s| · |s|`).
* `s = ∅` gives `0 ⪯ 0`.
* No positivity, normalization or linear-independence hypothesis is needed, and `σ` in the
  scaling corollary is an arbitrary operator.

This is the operator core of Bouman–Fehr, *Sampling in a Quantum Population, and Applications*
([arXiv:0907.4246v5](https://arxiv.org/abs/0907.4246), Lemma 1, proof in Appendix C): the
"`|J| ρ^mix_WE ≥ ρ_WE`" step, which the paper obtains from exactly this Cauchy–Schwarz estimate
applied blockwise.  The min-entropy consequence lives in
`QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SuperpositionPenalty`.

**Bipartite fibers.** The same estimate applied to the `A`-slices of a vector `φ` on `A ⊗ C`
gives the *fiber domination*

  `|φ⟩⟨φ|  ⪯  K · (1_A ⊗ Tr_A |φ⟩⟨φ|)`

whenever at most `K` of the `A`-slices of `φ` are nonzero.  This is the named theorem that
`RankOneFiber.lean` prepares the index computations for; the sole extra
ingredient is that Cauchy–Schwarz is applied to the *diagonal* `∑_a ⟨η_a, χ_a⟩` of a matrix of
slice overlaps, which is `normSq_sum_diag_le_card_mul_sum_normSq`.

## Main statements

* `Quantum.Operators.quadraticForm_ofReal_smul_re` — real-scalar quadratic-form rescaling.
* `Quantum.Operators.quadraticForm_sum_vecMulVec_self_star_re` — the quadratic form of a finset
  sum of rank-one operators is the sum of the squared overlaps.
* `Quantum.Operators.vecMulVec_sum_opLe_card_smul_sum_vecMulVec` — **operator Cauchy–Schwarz.**
* `Quantum.Operators.vecMulVec_sum_opLe_smul_of_sum_opLe_smul` — the scaling corollary: a Löwner
  bound `∑ᵢ |vᵢ⟩⟨vᵢ| ⪯ t · σ` upgrades to `|∑ᵢ vᵢ⟩⟨∑ᵢ vᵢ| ⪯ (|s| · t) · σ`.
* `Quantum.TensorProducts.vecMulVec_opLe_card_smul_one_tensor_partialTraceA` — **rank-one fiber
  domination** `|φ⟩⟨φ| ⪯ K · (1_A ⊗ Tr_A |φ⟩⟨φ|)` for a `φ` with at most `K` nonzero `A`-slices.
-/

open Matrix Quantum.TensorProducts
open scoped BigOperators ComplexOrder

noncomputable section

namespace Quantum.Operators

variable {n : ℕ} {ι : Type*}

/-- Rescaling a quadratic form by a **real** scalar, read on real parts:
`Re ⟨x| (c • A) |x⟩ = c · Re ⟨x| A |x⟩`.  This is `quadraticForm_smul` with the imaginary part of
`Complex.ofReal c` eliminated, the form in which the Löwner order consumes scalars. -/
lemma quadraticForm_ofReal_smul_re (c : ℝ) (A : Op n) (x : Fin n → ℂ) :
    (quadraticForm ((Complex.ofReal c) • A) x).re = c * (quadraticForm A x).re := by
  rw [quadraticForm_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Rescaling the vector of a rank-one operator rescales the operator by the squared modulus:
`|c·v⟩⟨c·v| = ‖c‖² · |v⟩⟨v|`.  This is the step that turns a flat measurement overlap into a
uniform factor in front of a dephased block. -/
lemma vecMulVec_smul_self_star (c : ℂ) (x : Fin n → ℂ) :
    Matrix.vecMulVec (c • x) (star (c • x)) =
      (Complex.ofReal (Complex.normSq c)) • Matrix.vecMulVec x (star x) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, Matrix.smul_apply,
    smul_eq_mul, star_mul']
  rw [← Complex.mul_conj c]
  simp only [Complex.star_def]
  ring

/-- The quadratic form of a finset sum of rank-one operators is the sum of the squared overlaps:
`Re ⟨x| ∑_{i ∈ s} |vᵢ⟩⟨vᵢ| |x⟩ = ∑_{i ∈ s} ‖⟨x, vᵢ⟩‖²`. -/
lemma quadraticForm_sum_vecMulVec_self_star_re (s : Finset ι) (v : ι → Fin n → ℂ)
    (x : Fin n → ℂ) :
    (quadraticForm (∑ i ∈ s, Matrix.vecMulVec (v i) (star (v i))) x).re =
      ∑ i ∈ s, Complex.normSq (star x ⬝ᵥ v i) := by
  have hsplit : quadraticForm (∑ i ∈ s, Matrix.vecMulVec (v i) (star (v i))) x =
      ∑ i ∈ s, quadraticForm (Matrix.vecMulVec (v i) (star (v i))) x := by
    simp only [quadraticForm, Matrix.sum_mulVec, dotProduct_sum]
  rw [hsplit, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [quadraticForm_vecMulVec_star, Complex.ofReal_re]

/-- **Operator Cauchy–Schwarz.** The rank-one operator of a finite sum is dominated in the Löwner
order by the cardinality of the index set times the sum of the rank-one operators:

  `|∑_{i ∈ s} vᵢ⟩⟨∑_{i ∈ s} vᵢ|  ⪯  |s| · ∑_{i ∈ s} |vᵢ⟩⟨vᵢ|`.

Testing at `x` reduces this to `‖∑_{i ∈ s} ⟨x, vᵢ⟩‖² ≤ |s| · ∑_{i ∈ s} ‖⟨x, vᵢ⟩‖²`.  No hypothesis
on the family `v` is required; `s = ∅` and `|s| = 1` are the trivial and the equality case. -/
theorem vecMulVec_sum_opLe_card_smul_sum_vecMulVec (s : Finset ι) (v : ι → Fin n → ℂ) :
    opLe (Matrix.vecMulVec (∑ i ∈ s, v i) (star (∑ i ∈ s, v i)))
      ((Complex.ofReal (s.card : ℝ)) • ∑ i ∈ s, Matrix.vecMulVec (v i) (star (v i))) := by
  intro x
  rw [quadraticForm_vecMulVec_star, Complex.ofReal_re, quadraticForm_ofReal_smul_re,
    quadraticForm_sum_vecMulVec_self_star_re, dotProduct_sum]
  exact normSq_sum_le_card_mul_sum_normSq s fun i => star x ⬝ᵥ v i

/-- **Scaling corollary of operator Cauchy–Schwarz.**  If the sum of the rank-one operators is
Löwner-dominated by `t · σ` for a nonnegative real `t` and an arbitrary operator `σ`, then the
rank-one operator of the sum is dominated by `(|s| · t) · σ`:

  `∑_{i ∈ s} |vᵢ⟩⟨vᵢ| ⪯ t · σ  ⟹  |∑_{i ∈ s} vᵢ⟩⟨∑_{i ∈ s} vᵢ| ⪯ (|s| · t) · σ`.

The scalars are written with `Complex.ofReal`, matching the convention of the min-entropy
feasibility predicate, so this is exactly the scaling hypothesis of the dimension penalty.  At
`|s| = 1` the conclusion is the hypothesis.

Only `|s| ≥ 0` is used, so — unlike the sign-carrying feasibility predicate — **no** hypothesis
`0 ≤ t` is needed here; the statement holds for every real `t` and every operator `σ`. -/
theorem vecMulVec_sum_opLe_smul_of_sum_opLe_smul (s : Finset ι) (v : ι → Fin n → ℂ) (σ : Op n)
    {t : ℝ}
    (hmix : opLe (∑ i ∈ s, Matrix.vecMulVec (v i) (star (v i))) ((Complex.ofReal t) • σ)) :
    opLe (Matrix.vecMulVec (∑ i ∈ s, v i) (star (∑ i ∈ s, v i)))
      ((Complex.ofReal ((s.card : ℝ) * t)) • σ) := by
  intro x
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hstep := vecMulVec_sum_opLe_card_smul_sum_vecMulVec s v x
  have hmixx := hmix x
  rw [quadraticForm_ofReal_smul_re] at hstep hmixx
  rw [quadraticForm_ofReal_smul_re, mul_assoc]
  exact hstep.trans (mul_le_mul_of_nonneg_left hmixx hcard)

end Quantum.Operators

/-! ## The bipartite fiber domination -/

namespace Quantum.TensorProducts

open Quantum.Operators

variable {dA dC : ℕ}

/-- **Rank-one fiber domination.**  Let `φ` be a vector on `A ⊗ C` whose `C`-slices `χ_a` vanish
outside a finset `S` of Alice indices with `|S| ≤ K`.  Then

  `|φ⟩⟨φ|  ⪯  K · (1_A ⊗ Tr_A |φ⟩⟨φ|)`

in the Löwner order.  Tested at `v` with slices `η_a`, the left side is
`‖∑_a ⟨η_a, χ_a⟩‖²` and the right side is `K · ∑_a ∑_b ‖⟨η_a, χ_b⟩‖²`, so the statement is
Cauchy–Schwarz applied to the diagonal of the slice-overlap matrix, discarding the off-diagonal
terms of the right-hand side.

The factor `K` counts the *occupied fibers*, not the Alice dimension, so the bound is useful
exactly when `φ` is supported on few branches — the situation of a superposition with a small
number of terms.  It is tight: for `φ` with `K` orthonormal equal-weight slices and `v = φ`, both
sides are `K` times the squared norm of a single slice.  `S = ∅` forces `φ = 0` on every slice
and both sides vanish. -/
theorem vecMulVec_opLe_card_smul_one_tensor_partialTraceA (φ : Fin (dA * dC) → ℂ)
    (S : Finset (Fin dA)) (hsupp : ∀ a, a ∉ S → bipartiteSlice φ a = 0) {K : ℕ}
    (hK : S.card ≤ K) :
    opLe (Matrix.vecMulVec φ (star φ))
      ((Complex.ofReal (K : ℝ)) •
        Op.tensor (1 : Op dA) (partialTraceA (Matrix.vecMulVec φ (star φ)))) := by
  intro v
  -- Left side: the squared modulus of the diagonal of the slice-overlap matrix.
  rw [quadraticForm_vecMulVec_star, Complex.ofReal_re,
    dotProduct_star_eq_sum_bipartiteSlice φ v, quadraticForm_ofReal_smul_re,
    partialTraceA_vecMulVec_star,
    quadraticForm_one_tensor_eq_sum_bipartiteSlice, Complex.re_sum]
  -- Right side: the full sum of squared slice overlaps.
  have hblock : ∀ a : Fin dA,
      (quadraticForm (∑ b : Fin dA,
          Matrix.vecMulVec (bipartiteSlice φ b) (star (bipartiteSlice φ b)))
        (bipartiteSlice v a)).re =
        ∑ b : Fin dA, Complex.normSq (star (bipartiteSlice v a) ⬝ᵥ bipartiteSlice φ b) := by
    intro a
    simpa using
      quadraticForm_sum_vecMulVec_self_star_re (Finset.univ : Finset (Fin dA))
        (fun b => bipartiteSlice φ b) (bipartiteSlice v a)
  rw [Finset.sum_congr rfl fun a _ => hblock a]
  refine normSq_sum_diag_le_card_mul_sum_normSq
    (fun a b => star (bipartiteSlice v a) ⬝ᵥ bipartiteSlice φ b) S (fun a ha => ?_) hK
  change star (bipartiteSlice v a) ⬝ᵥ bipartiteSlice φ a = 0
  rw [hsupp a ha, dotProduct_zero]

end Quantum.TensorProducts

end
