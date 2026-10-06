import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Operators.BraKet.Basic

/-!
# Block-diagonal embedding of ket families

This low-level module provides the generic linear-algebra bridge needed to lift a
*per-block* sum-of-ketbra representation to the reindexed block-diagonal joint
space.  It is the reusable kernel underlying the weight-cap purified-distance
route of Renner's `thm:Hmincondrep`, but contains **no** Renner-specific content
and sits low in the import graph (only the tensor-product / bra-ket layer).

Given a reindexing equivalence `e : (Fin dB × B) ≃ Fin d` (the same kind produced
by `CQState.toJointDensity`), the embedding of a block-`b` ket `u : Ket dB` into
the joint space is `blockKetInclusion e b u`, supported on block `b` only.  The
two facts that make this canonical are:

* `blockKetInclusion_dag_mul_same`: the inclusion is an isometry on each block,
  `⟨ι_b u | ι_b u'⟩ = ⟨u | u'⟩`;
* `reindex_blockDiagonal_eq_sum_blockKetInclusion_ketbra`: if each block operator
  is a sum-of-ketbra `Σ_k u_{b,k} u_{b,k}†`, then the reindexed block-diagonal
  operator is the joint sum-of-ketbra `Σ_{b,k} (ι_b u_{b,k})(ι_b u_{b,k})†`.

Together these let a domination-free vector-family Uhlmann bound be applied to two
block-diagonal joint densities, reading the family overlap back as the per-block
overlap sum.
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.TensorProducts

/-- **Square-root scaling of a ketbra.** For a nonnegative real `c`, scaling a
ket by `√c` turns its ketbra into `c` times the original ketbra: this is the
algebraic identity that lets a `√(weight)`-scaled vector family reproduce a
`weight`-weighted sum-of-projectors. -/
lemma sqrt_smul_ketbra {dB : ℕ} (c : ℝ) (hc : 0 ≤ c) (ψ : Ket dB) :
    (((Real.sqrt c : ℂ) • ψ) * ((Real.sqrt c : ℂ) • ψ).dag : Op dB)
      = (c : ℂ) • (ψ * ψ.dag : Op dB) := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.smul_vec, Pi.smul_apply, smul_eq_mul, Ket.dag_vec,
    Matrix.smul_apply, map_mul]
  rw [Complex.conj_ofReal]
  have : (Real.sqrt c : ℂ) * ψ.vec i * ((Real.sqrt c : ℂ) * conj (ψ.vec j))
      = ((Real.sqrt c : ℂ) * (Real.sqrt c : ℂ)) * (ψ.vec i * conj (ψ.vec j)) := by ring
  rw [this, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

variable {dB d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

/-- Embed a block-`b` ket `u : Ket dB` into the joint space `Fin d` via the
reindexing equivalence `e : (Fin dB × B) ≃ Fin d`.  The joint vector is supported
only on the block `b`: its entry at `p` is `u.vec i` when `e.symm p = (i, b)` and
`0` otherwise. -/
def blockKetInclusion (e : (Fin dB × B) ≃ Fin d) (b : B) (u : Ket dB) : Ket d :=
  ⟨fun p => if (e.symm p).2 = b then u.vec (e.symm p).1 else 0⟩

omit [Fintype B] in
@[simp]
lemma blockKetInclusion_vec (e : (Fin dB × B) ≃ Fin d) (b : B) (u : Ket dB)
    (p : Fin d) :
    (blockKetInclusion e b u).vec p =
      if (e.symm p).2 = b then u.vec (e.symm p).1 else 0 := rfl

omit [Fintype B] in
/-- **Block isometry.** The inclusion of two block-`b` kets has the same overlap
as the original kets: the embedding is norm-preserving on each block. -/
lemma blockKetInclusion_dag_mul_same [Finite B] (e : (Fin dB × B) ≃ Fin d) (b : B)
    (u u' : Ket dB) :
    ((blockKetInclusion e b u).dag * blockKetInclusion e b u' : ℂ)
      = ((u).dag * u' : ℂ) := by
  cases nonempty_fintype B
  rw [bra_mul_ket_eq, bra_mul_ket_eq, ← Equiv.sum_comp e
      (fun p => (blockKetInclusion e b u).dag.vec p * (blockKetInclusion e b u').vec p),
    Fintype.sum_prod_type_right]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro b' _ hb'
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp only [Ket.dag_vec, blockKetInclusion_vec, Equiv.symm_apply_apply, ite_eq_right hb',
      mul_zero, map_zero]
  · intro hb; exact absurd (Finset.mem_univ b) hb
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Ket.dag_vec, blockKetInclusion_vec, Equiv.symm_apply_apply, ite_true]

/-- **Block-diagonal sum-of-ketbra embedding.** If each block operator is a
sum-of-ketbra `Σ_k u_{b,k} u_{b,k}†`, then the reindexed block-diagonal operator
is the joint sum-of-ketbra over all `(b, k)` of the embedded vectors. -/
lemma reindex_blockDiagonal_eq_sum_blockKetInclusion_ketbra
    {K : Type*} [Fintype K]
    (e : (Fin dB × B) ≃ Fin d) (u : B → K → Ket dB) :
    Matrix.reindex e e
        (Matrix.blockDiagonal (fun b => ∑ k, ((u b k) * (u b k).dag : Op dB)))
      = ∑ b : B, ∑ k : K,
          (blockKetInclusion e b (u b k)) * (blockKetInclusion e b (u b k)).dag := by
  ext p q
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, ket_mul_bra_apply, Ket.dag_vec, blockKetInclusion_vec]
  rw [Finset.sum_eq_single (e.symm p).2]
  · by_cases h : (e.symm p).2 = (e.symm q).2
    · rw [ite_eq_left h]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [ite_eq_left rfl, ite_eq_left h.symm]
    · rw [ite_eq_right h]
      refine (Finset.sum_eq_zero (fun k _ => ?_)).symm
      rw [ite_eq_left rfl, ite_eq_right (fun hc => h hc.symm), map_zero, mul_zero]
  · intro b' _ hb'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [ite_eq_right (Ne.symm hb'), zero_mul]
  · intro hb; exact absurd (Finset.mem_univ _) hb

end Quantum.TensorProducts

end -- noncomputable section
