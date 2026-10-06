import QCryptLean.Quantum.TensorProducts.QuadraticForm

/-!
# Dimension-cast kets and tensor-power normalization

Generic ket facts, stated over generic `Ket`/`NormKet` objects: the pointwise value of a
dimension-cast ket, prefix factoring of a scalar-weighted sum of casts of `a ⊗ (g t)` with a
shared left factor, and normalization of the tensor power of a normalized reference vector.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- Pointwise value of a dimension-cast ket. -/
theorem ket_cast_vec {n m : ℕ} (h : n = m) (ψ : Ket n) (i : Fin m) :
    (Ket.cast h ψ).vec i = ψ.vec (Fin.cast h.symm i) := by
  subst h; rfl

/-- **Prefix factoring.** A scalar-weighted sum of casts of `a ⊗ (g t)` (with the
*same* left factor `a`) equals the single cast of `a ⊗ (∑ t, c t • g t)`. This is the
only nontrivial algebraic step in `lem:symspacebin` for the no-permutation encoding:
the shared first tensor factor `θ_pow` is pulled out of the membership sum. -/
theorem ket_cast_tensor_smul_sum {p q N : ℕ} (h : p * q = N) (a : Ket p)
    (T : Finset ℕ) (c : ℕ → ℂ) (g : ℕ → Ket q) :
    ∑ t ∈ T, c t • (Ket.cast h (Quantum.TensorProducts.Ket.tensor a (g t))).vec
      = (Ket.cast h
          (Quantum.TensorProducts.Ket.tensor a
            ⟨∑ t ∈ T, c t • (g t).vec⟩)).vec := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Quantum.TensorProducts.ket_cast_vec, smul_eq_mul,
    Quantum.TensorProducts.Ket.tensor]
  rcases hfpe : finProdFinEquiv.symm (Fin.cast h.symm k) with ⟨i, l⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t _ => by ring)

/-- The `(n−r)`-fold tensor power of a normalized reference vector is normalized:
`‖θ^{⊗(n−r)}‖ = 1`. Proved via `quadraticForm_tensorPowVec_of_entrywise_prod` with the
identity operator, whose tensor-power quadratic form is `(‖θ‖²)^{n−r} = 1`. -/
theorem tensorPowVec_isNormalized {d k : ℕ} [NeZero d] [NeZero (d ^ k)]
    (θ : NormKet d) :
    (⟨Quantum.TensorProducts.tensorPowVec θ.toKet.vec⟩ : Ket (d ^ k)).IsNormalized := by
  classical
  have hM : ∀ f g : Fin k → Fin d,
      (1 : Op (d ^ k)) (finFunctionFinEquiv f) (finFunctionFinEquiv g) =
        ∏ x : Fin k, (1 : Op d) (f x) (g x) := by
    intro f g
    by_cases hfg : f = g
    · subst hfg; simp
    · rw [Matrix.one_apply, if_neg (fun hcontra => hfg (finFunctionFinEquiv.injective hcontra))]
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hfg
      exact (Finset.prod_eq_zero (Finset.mem_univ x) (by rw [Matrix.one_apply, if_neg hx])).symm
  have hone : quadraticForm (1 : Op d) θ.toKet.vec = 1 := by
    have hn := θ.normalized
    unfold Ket.IsNormalized at hn
    rw [bra_mul_ket_eq] at hn
    simp only [Ket.dag_vec, starRingEnd_apply] at hn
    unfold quadraticForm
    rw [Matrix.one_mulVec, dotProduct]
    simp only [Pi.star_apply]
    exact hn
  have hq := quadraticForm_tensorPowVec_of_entrywise_prod
    (1 : Op d) (1 : Op (d ^ k)) hM θ.toKet.vec
  rw [hone, one_pow] at hq
  unfold Ket.IsNormalized
  rw [bra_mul_ket_eq]
  simp only [Ket.dag_vec, starRingEnd_apply]
  have hqf : quadraticForm (1 : Op (d ^ k))
      (Quantum.TensorProducts.tensorPowVec θ.toKet.vec) = 1 := hq
  unfold quadraticForm at hqf
  rw [Matrix.one_mulVec, dotProduct] at hqf
  simp only [Pi.star_apply] at hqf
  exact hqf

end Quantum.TensorProducts

end -- noncomputable section
