import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilation

/-!
# Tensor products and tensor powers of rank-one projective measurements

`RankOneProjectiveBasis` (`MeasurementDilation.lean`) packages an orthonormal basis of `ℂ^d`
together with its resolution of the identity, and carries the measurement-dilation and
overlap-constant API of the entropic uncertainty layer.  This file closes that API under tensor
products, which is what an `n`-round (i.i.d.) uncertainty relation needs: the overlap constant is
*multiplicative* and the preparation quality `q = log₂(1/c)` is therefore *additive*.

## Main definitions

* `RankOneProjectiveBasis.trivial` — the one-dimensional basis of `ℂ^1`, the empty tensor power;
* `RankOneProjectiveBasis.tensor` — the product basis `{|x₁⟩ ⊗ |x₂⟩}` of `ℂ^{d₁} ⊗ ℂ^{d₂}`;
* `RankOneProjectiveBasis.tensorPow` — the `n`-fold power `P^{⊗n}` on `ℂ^{dⁿ}`, little-endian
  (`P^{⊗(k+1)} = P^{⊗k} ⊗ P`, matching the reduction `d^(k+1) = d^k * d` of `Nat.pow`, so the
  recursion needs no dimension cast).

## Main statements

* `RankOneProjectiveBasis.proj_tensor` — a product-index projector factors,
  `(P₁ ⊗ P₂).proj (i, j) = P₁.proj i ⊗ P₂.proj j`, so a product measurement reads each factor's
  outcome independently; `proj_tensorPow_succ` is the one-round peel;
* `RankOneProjectiveBasis.overlapConst_tensor` — `c(P₁⊗P₂, Q₁⊗Q₂) = c(P₁,Q₁)·c(P₂,Q₂)`;
* `RankOneProjectiveBasis.overlapConst_tensorPow` — `c(P^{⊗n}, Q^{⊗n}) = c(P,Q)ⁿ`;
* `RankOneProjectiveBasis.preparationQuality_tensorPow` — `q(P^{⊗n}, Q^{⊗n}) = n · q(P,Q)`.

The last statement is the `n`-round input of a finite-key rate: each of the `n` rounds contributes
one copy of the per-round preparation quality.  For the mutually-unbiased qubit pair `q = 1` and
hence `q_n = n` (see `ConcreteMeasurementBases.lean`, where `c(Z, X^{⊗n}) = 2^{-n}` is computed
directly for the Walsh–Hadamard basis; the two routes agree).

## Multiplicativity engine

Both overlap-constant facts rest on the separable-product law for `Finset.sup'`
(`sup'_mul_of_nonneg`): for nonnegative `f, g`, the maximum of `f p₁ · g p₂` over the product index
factorizes as `(max f)·(max g)`.  Mathlib has no `sup'_mul`, so it is proved here by antisymmetry
(`Finset.sup'_le` one way, the argmax witness `Finset.exists_mem_eq_sup'` the other).  The tensor
inner product factorizes as a product of the component inner products
(`bra_tensor_mul_ket_tensor`), whose squared modulus is a product of nonnegative reals, so the
overlap-constant `sup'` splits after reindexing the pair space
`Fin(d₁d₂)² ≃ (Fin d₁)² × (Fin d₂)²`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## `Finset.sup'` separable-product and reindexing helpers
-/

/-- **Separable-product law for `Finset.sup'`.** For nonnegative `f : A → ℝ` and `g : B → ℝ`, the
maximum of the separable product `f p.1 · g p.2` over the finite product index equals the product of
the two maxima. Both directions are proved by hand (Mathlib has no `sup'_mul`): `≤` from
`Finset.sup'_le` and monotonicity of multiplication on the nonnegative reals; `≥` by exhibiting the
argmax pair via `Finset.exists_mem_eq_sup'`. -/
private lemma sup'_mul_of_nonneg {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → ℝ) (g : B → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b) :
    (Finset.univ.sup' Finset.univ_nonempty (fun p : A × B => f p.1 * g p.2))
      = (Finset.univ.sup' Finset.univ_nonempty f) * (Finset.univ.sup' Finset.univ_nonempty g) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    have h1 : f p.1 ≤ Finset.univ.sup' Finset.univ_nonempty f :=
      Finset.le_sup' f (Finset.mem_univ p.1)
    have h2 : g p.2 ≤ Finset.univ.sup' Finset.univ_nonempty g :=
      Finset.le_sup' g (Finset.mem_univ p.2)
    exact mul_le_mul h1 h2 (hg p.2) (le_trans (hf p.1) h1)
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty g
    rw [ha, hb]
    exact Finset.le_sup' (fun p : A × B => f p.1 * g p.2) (Finset.mem_univ (a, b))

/-- **`Finset.sup'` over `univ` is invariant under reindexing by an equivalence.** Reindexes a
maximum over all of `α` into a maximum over all of `β` along `e : β ≃ α`. Proved by antisymmetry
using surjectivity of `e` (no dependent rewrite of the nonemptiness witness). -/
private lemma sup'_univ_reindex {α β : Type*} {M : Type*} [SemilatticeSup M]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : β ≃ α) (g : α → M) :
    Finset.univ.sup' Finset.univ_nonempty g
      = Finset.univ.sup' Finset.univ_nonempty (fun b => g (e b)) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    calc g a = g (e (e.symm a)) := by rw [Equiv.apply_symm_apply]
      _ ≤ _ := Finset.le_sup' (fun b => g (e b)) (Finset.mem_univ (e.symm a))
  · apply Finset.sup'_le
    intro b _
    exact Finset.le_sup' g (Finset.mem_univ (e b))

namespace RankOneProjectiveBasis

variable {d d₁ d₂ : ℕ}

/-!
## The trivial one-dimensional basis (`P^{⊗0}`)
-/

/-- **The trivial rank-one projective basis on `ℂ^1`.** The single unit vector `|0⟩ = (1)`; it is
the base case `P^{⊗0}` of the tensor power (`d^0 = 1`). Orthonormality and completeness are the
`Fin 1` degenerate resolution of the identity. -/
def trivial : RankOneProjectiveBasis 1 where
  vec := stdKet 1
  orthonormal := stdKet_braket 1
  complete := stdKet_complete 1

@[simp] lemma trivial_vec (i : Fin 1) : trivial.vec i = stdKet 1 i := rfl

/-!
## The binary tensor product `P₁ ⊗ P₂`
-/

/-- **Tensor product of two rank-one projective bases.** The basis vectors are the tensor products
`|x₁⟩ ⊗ |x₂⟩` indexed by `x = (x₁, x₂)` through `finProdFinEquiv`; orthonormality follows from
`bra_tensor_mul_ket_tensor` (the inner product factorizes) and completeness from the tensor
resolution `(Σ|x₁⟩⟨x₁|) ⊗ (Σ|x₂⟩⟨x₂|) = 1 ⊗ 1 = 1`. -/
def tensor (P₁ : RankOneProjectiveBasis d₁) (P₂ : RankOneProjectiveBasis d₂) :
    RankOneProjectiveBasis (d₁ * d₂) where
  vec := fun k => P₁.vec (finProdFinEquiv.symm k).1 ⊗ P₂.vec (finProdFinEquiv.symm k).2
  orthonormal := by
    intro i j
    rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor, P₁.orthonormal, P₂.orthonormal]
    by_cases h : i = j
    · subst h; simp
    · rw [ite_eq_right h]
      have hne : (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 ∨
          (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
        by_contra hc
        push Not at hc
        exact h (finProdFinEquiv.symm.injective (Prod.ext_iff.mpr hc))
      rcases hne with h1 | h2
      · rw [ite_eq_right h1, zero_mul]
      · rw [ite_eq_right h2, mul_zero]
  complete := by
    have step : ∀ k : Fin (d₁ * d₂),
        (P₁.vec (finProdFinEquiv.symm k).1 ⊗ P₂.vec (finProdFinEquiv.symm k).2) *
            (P₁.vec (finProdFinEquiv.symm k).1 ⊗ P₂.vec (finProdFinEquiv.symm k).2).dag
          = (P₁.vec (finProdFinEquiv.symm k).1 * (P₁.vec (finProdFinEquiv.symm k).1).dag) ⊗
            (P₂.vec (finProdFinEquiv.symm k).2 * (P₂.vec (finProdFinEquiv.symm k).2).dag) := by
      intro k; rw [ketbra_tensor']
    simp only [step]
    rw [← Op.tensor_one (n := d₁) (m := d₂), ← P₁.complete, ← P₂.complete,
      Op.tensor_finsetSum_left]
    rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin d₁ × Fin d₂ =>
        (P₁.vec p.1 * (P₁.vec p.1).dag) ⊗ (P₂.vec p.2 * (P₂.vec p.2).dag)),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Op.tensor_finsetSum_right]

@[simp] lemma tensor_vec (P₁ : RankOneProjectiveBasis d₁) (P₂ : RankOneProjectiveBasis d₂)
    (k : Fin (d₁ * d₂)) :
    (P₁.tensor P₂).vec k =
      P₁.vec (finProdFinEquiv.symm k).1 ⊗ P₂.vec (finProdFinEquiv.symm k).2 :=
  rfl

/-- **The projector of a tensor basis at a product index is the operator tensor of the factors'
projectors:** `(P₁ ⊗ P₂).proj (finProdFinEquiv (i, j)) = P₁.proj i ⊗ P₂.proj j`.

The basis vector at `finProdFinEquiv (i, j)` is `|i⟩ ⊗ |j⟩` (`Equiv.symm_apply_apply`), and the
ket-bra of a tensor of kets is the tensor of the ket-bras (`ketbra_tensor'`). This is the fact that
lets a product measurement read off each factor's outcome independently. -/
theorem proj_tensor (P₁ : RankOneProjectiveBasis d₁) (P₂ : RankOneProjectiveBasis d₂)
    (i : Fin d₁) (j : Fin d₂) :
    (P₁.tensor P₂).proj (finProdFinEquiv (i, j)) = Op.tensor (P₁.proj i) (P₂.proj j) := by
  simp only [proj, tensor, Equiv.symm_apply_apply]
  rw [ketbra_tensor']

/-!
## Multiplicativity of the overlap constant under tensoring
-/

/-- **Factorization of the tensor cross-overlap.** `|⟨x₁x₂|z₁z₂⟩|²` splits as
`|⟨x₁|z₁⟩|²·|⟨x₂|z₂⟩|²`, since the tensor inner product factorizes (`bra_tensor_mul_ket_tensor`)
and `Complex.normSq` is multiplicative. -/
private lemma normSq_tensor_overlap (P₁ Q₁ : RankOneProjectiveBasis d₁)
    (P₂ Q₂ : RankOneProjectiveBasis d₂) (x z : Fin (d₁ * d₂)) :
    Complex.normSq (((P₁.tensor P₂).vec x).dag * (Q₁.tensor Q₂).vec z)
      = Complex.normSq ((P₁.vec (finProdFinEquiv.symm x).1).dag * Q₁.vec (finProdFinEquiv.symm z).1)
        * Complex.normSq
            ((P₂.vec (finProdFinEquiv.symm x).2).dag * Q₂.vec (finProdFinEquiv.symm z).2) := by
  change Complex.normSq
      ((P₁.vec (finProdFinEquiv.symm x).1 ⊗ P₂.vec (finProdFinEquiv.symm x).2).dag *
        (Q₁.vec (finProdFinEquiv.symm z).1 ⊗ Q₂.vec (finProdFinEquiv.symm z).2)) = _
  rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor, Complex.normSq_mul]

/-- **The overlap constant is separably multiplicative under tensoring:**
`c(P₁⊗P₂, Q₁⊗Q₂) = c(P₁,Q₁)·c(P₂,Q₂)`. The tensor cross-overlap factorizes
(`normSq_tensor_overlap`), so after reindexing the pair space
`Fin(d₁d₂)² ≃ (Fin d₁)²×(Fin d₂)²` the maximum splits by the separable-product law
`sup'_mul_of_nonneg` (`Complex.normSq_nonneg` supplies the nonnegativity). -/
theorem overlapConst_tensor [NeZero d₁] [NeZero d₂]
    (P₁ Q₁ : RankOneProjectiveBasis d₁) (P₂ Q₂ : RankOneProjectiveBasis d₂) :
    overlapConst (P₁.tensor P₂) (Q₁.tensor Q₂) = overlapConst P₁ Q₁ * overlapConst P₂ Q₂ := by
  rw [overlapConst, overlapConst, overlapConst,
    ← sup'_mul_of_nonneg
      (fun p : Fin d₁ × Fin d₁ => Complex.normSq ((P₁.vec p.1).dag * Q₁.vec p.2))
      (fun p : Fin d₂ × Fin d₂ => Complex.normSq ((P₂.vec p.1).dag * Q₂.vec p.2))
      (fun _ => Complex.normSq_nonneg _) (fun _ => Complex.normSq_nonneg _),
    sup'_univ_reindex
      ((Equiv.prodProdProdComm (Fin d₁) (Fin d₁) (Fin d₂) (Fin d₂)).trans
        (finProdFinEquiv.prodCongr finProdFinEquiv))]
  congr 1
  funext q
  rw [normSq_tensor_overlap]
  simp only [Equiv.trans_apply, Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.symm_apply_apply]

/-!
## The `n`-fold tensor power `P^{⊗n}`
-/

/-- **`n`-fold tensor power** `P^{⊗n} : RankOneProjectiveBasis (d^n)`, little-endian
`P^{⊗(k+1)} = P^{⊗k} ⊗ P`. The recursion matches `Nat.pow`'s reduction `d^(k+1) = d^k * d`, so no
dimension cast is needed; the base `P^{⊗0}` is the `trivial` basis on `ℂ^1` (`d^0 = 1`). -/
def tensorPow (P : RankOneProjectiveBasis d) (n : ℕ) : RankOneProjectiveBasis (d ^ n) :=
  match n with
  | 0 => trivial
  | k + 1 => (P.tensorPow k).tensor P

/-- **One-step peel of the tensor power:** `P^{⊗(n+1)} = P^{⊗n} ⊗ P` (little-endian; definitional,
since `Nat.pow`'s reduction `d^(n+1) = d^n * d` needs no dimension cast). -/
theorem tensorPow_succ (P : RankOneProjectiveBasis d) (n : ℕ) :
    P.tensorPow (n + 1) = (P.tensorPow n).tensor P := rfl

/-- **The tensor-power projector factors off its last round:** the projector of `P^{⊗(n+1)}` at a
product index `finProdFinEquiv (i, j)` is the operator tensor of the `P^{⊗n}` projector at `i` and
the single-factor projector at `j`. Instance of `proj_tensor` at the peel `tensorPow_succ`. -/
theorem proj_tensorPow_succ (P : RankOneProjectiveBasis d) (n : ℕ)
    (i : Fin (d ^ n)) (j : Fin d) :
    (P.tensorPow (n + 1)).proj (finProdFinEquiv (i, j))
      = Op.tensor ((P.tensorPow n).proj i) (P.proj j) :=
  proj_tensor (P.tensorPow n) P i j

/-- The overlap constant of the `trivial` one-dimensional basis with itself is `1`: the single
cross-overlap is `|⟨0|0⟩|² = 1`. This is the base case of `overlapConst_tensorPow`. -/
lemma overlapConst_trivial : overlapConst trivial trivial = 1 := by
  have hconst :
      (fun p : Fin 1 × Fin 1 => Complex.normSq ((trivial.vec p.1).dag * trivial.vec p.2))
        = fun _ => (1 : ℝ) := by
    funext p
    obtain ⟨a, b⟩ := p
    fin_cases a; fin_cases b
    change Complex.normSq ((stdKet 1 0).dag * stdKet 1 0) = 1
    simp [stdKet_braket]
  rw [overlapConst, hconst]
  exact Finset.sup'_const _ _

/-- **The overlap constant multiplies over tensor powers:** `c(P^{⊗n}, Q^{⊗n}) = c(P,Q)ⁿ`. By
induction on `n` from `overlapConst_tensor`, with base case `overlapConst_trivial = 1`. The
little-endian recursion `P^{⊗(k+1)} = P^{⊗k} ⊗ P` reduces definitionally against `d^(k+1) = d^k·d`,
so the inductive step consumes `overlapConst_tensor` up to definitional equality with no cast. -/
theorem overlapConst_tensorPow [NeZero d] (P Q : RankOneProjectiveBasis d) (n : ℕ) :
    overlapConst (P.tensorPow n) (Q.tensorPow n) = (overlapConst P Q) ^ n := by
  induction n with
  | zero => rw [pow_zero (P.overlapConst Q)]; exact overlapConst_trivial
  | succ k ih =>
    have h := overlapConst_tensor (P.tensorPow k) (Q.tensorPow k) P Q
    rw [ih] at h
    rw [pow_succ (P.overlapConst Q) k]; exact h

/-- **The preparation quality is additive over tensor powers:** `q(P^{⊗n}, Q^{⊗n}) = n·q(P,Q)`.
Immediate from `overlapConst_tensorPow` (`cⁿ`) and `Real.log_pow` (`log(cⁿ) = n·log c`); positivity
of `c` is not needed. This is the `n`-round preparation quality a finite-key rate consumes: each
of the `n` rounds contributes one copy of the per-round value. -/
theorem preparationQuality_tensorPow [NeZero d] (P Q : RankOneProjectiveBasis d) (n : ℕ) :
    (P.tensorPow n).preparationQuality (Q.tensorPow n) = (n : ℝ) * P.preparationQuality Q := by
  unfold preparationQuality
  rw [overlapConst_tensorPow, Real.log_pow]
  ring

end RankOneProjectiveBasis

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
