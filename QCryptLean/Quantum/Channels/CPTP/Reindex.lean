import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Reindexing along an index equivalence is CPTP

The register-generic reindex-channel primitive, realized by the single generalized-permutation
Kraus operator `reindexIsometry e`, an isometry.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate

noncomputable section

namespace Quantum.Channels

/-- The generalized-permutation isometry of an index reindex `e : Fin a ≃ Fin b`. -/
private def reindexIsometry {a b : ℕ} (e : Fin a ≃ Fin b) : Matrix (Fin b) (Fin a) ℂ :=
  Matrix.of fun i j => if i = e j then (1 : ℂ) else 0

private lemma reindexIsometry_conjTranspose_mul {a b : ℕ} (e : Fin a ≃ Fin b) :
    (reindexIsometry e)ᴴ * reindexIsometry e = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, reindexIsometry, Matrix.of_apply, apply_ite star,
    star_one, star_zero]
  rw [Finset.sum_eq_single (e j)]
  · simp [Matrix.one_apply, e.injective.eq_iff]
  · intro x _ hx; simp [(hx : x ≠ e j)]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma reindexIsometry_mul_apply {a b : ℕ} (e : Fin a ≃ Fin b)
    (M : Op a) (i : Fin b) (l : Fin a) :
    (reindexIsometry e * M) i l = M (e.symm i) l := by
  rw [Matrix.mul_apply]
  simp only [reindexIsometry, Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp
  · intro k _ hk
    have : i ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma reindexIsometry_mul_mul_conjTranspose {a b : ℕ} (e : Fin a ≃ Fin b)
    (M : Op a) :
    reindexIsometry e * M * (reindexIsometry e)ᴴ = Matrix.reindex e e M := by
  ext i i'
  rw [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp_rw [reindexIsometry_mul_apply e M i]
  simp only [Matrix.conjTranspose_apply, reindexIsometry, Matrix.of_apply, apply_ite star,
    star_one, star_zero]
  rw [Finset.sum_eq_single (e.symm i')]
  · simp
  · intro l _ hl
    have : i' ≠ e l := fun h => hl (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Reindexing along an index equivalence `e : Fin a ≃ Fin b` is CPTP.** Realized by the single
    generalized-permutation Kraus operator `reindexIsometry e`, an isometry. -/
theorem reindexLinearEquiv_isCPTP {a b : ℕ} [NeZero a] [NeZero b] (e : Fin a ≃ Fin b) :
    IsCPTP (⇑(Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) := by
  have hK : (∑ i : Fin 1, (![reindexIsometry e] i)ᴴ * (![reindexIsometry e] i)) = (1 : Op a) := by
    simp [reindexIsometry_conjTranspose_mul]
  let K : KrausRepresentation a b := ⟨1, ![reindexIsometry e], hK⟩
  have hK_apply : ∀ M : Op a, K.applyOp M = Matrix.reindex e e M := by
    intro M
    change ∑ i : Fin 1, ![reindexIsometry e] i * M * (![reindexIsometry e] i)ᴴ =
      Matrix.reindex e e M
    simp [reindexIsometry_mul_mul_conjTranspose]
  have h := K.is_cptp
  have heq : K.applyOp = (fun M : Op a => Matrix.reindex e e M) := funext hK_apply
  rw [heq] at h
  exact h

end Quantum.Channels

end
