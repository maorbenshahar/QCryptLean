import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Operators.BraKet.Basic

/-!
# Generic vector-family purification

This is a low-level, reusable kernel for building a purifying ket from a finite
family of (unnormalized) vectors on a system `d`, carried by an orthonormal
ancilla `anc` that labels the family.  Given `v : Fin anc → Ket d`, the purifying
ket is

  `purifyVectorFamily v = Σ_k v_k ⊗ |k⟩`

whose entry at the tensor index `(i, k)` is `(v k).vec i`.  Two facts make this
the canonical purification building block:

* `partialTraceB_purifyVectorFamily_ketbra`:
  `Tr_B (Ψ Ψ†) = Σ_k v_k v_k†`, i.e. the reduced state is the sum-of-ketbra
  `Σ_k |v_k⟩⟨v_k|`;
* `purifyVectorFamily_dag_mul`:
  `⟨Ψ_v | Ψ_w⟩ = Σ_k ⟨v_k | w_k⟩`, the live overlap of two such purifications
  collapses on the orthonormal ancilla labels to the family-wise overlap sum.

Combined with `SubDensityOp.livePurificationOverlap_re_le_fidelity` these give a
domination-free Uhlmann lower bound on the fidelity of two sum-of-ketbra
operators in terms of their family overlap.  The module sits low in the import
graph (only the tensor-product / bra-ket layer) so it can be reused without
pulling in any high-level state machinery.
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.TensorProducts

variable {d anc : ℕ}

/-- The purifying ket of a vector family `v : Fin anc → Ket d`, equal to
`Σ_k v_k ⊗ |k⟩`.  Its entry at the tensor index whose `finProdFinEquiv.symm`
decomposition is `(i, k)` is `(v k).vec i`. -/
def purifyVectorFamily (v : Fin anc → Ket d) : Ket (d * anc) :=
  ⟨fun idx => (v (finProdFinEquiv.symm idx).2).vec (finProdFinEquiv.symm idx).1⟩

@[simp]
lemma purifyVectorFamily_vec (v : Fin anc → Ket d) (idx : Fin (d * anc)) :
    (purifyVectorFamily v).vec idx =
      (v (finProdFinEquiv.symm idx).2).vec (finProdFinEquiv.symm idx).1 := rfl

/-- **Family overlap collapse.** The live overlap of two vector-family
purifications equals the sum of the family-wise overlaps. -/
lemma purifyVectorFamily_dag_mul (v w : Fin anc → Ket d) :
    ((purifyVectorFamily v).dag * purifyVectorFamily w : ℂ)
      = ∑ k, ((v k).dag * (w k) : ℂ) := by
  rw [bra_mul_ket_eq]
  -- ∑ idx, conj(Ψv idx) * Ψw idx, reindex idx ↔ (i,k)
  rw [← Equiv.sum_comp finProdFinEquiv
      (fun idx => (purifyVectorFamily v).dag.vec idx * (purifyVectorFamily w).vec idx)]
  simp only [Ket.dag, purifyVectorFamily_vec, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bra_mul_ket_eq]

/-- **Reduced-state identity.** The partial trace (over the ancilla `B`) of the
ketbra of a vector-family purification is the sum-of-ketbra
`Σ_k |v_k⟩⟨v_k|`. -/
lemma partialTraceB_purifyVectorFamily_ketbra (v : Fin anc → Ket d) :
    partialTraceB (purifyVectorFamily v * (purifyVectorFamily v).dag)
      = ∑ k, ((v k) * (v k).dag : Op d) := by
  ext i j
  rw [partialTraceB]
  simp only [Matrix.of_apply]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [ket_mul_bra_apply, purifyVectorFamily_vec, Ket.dag,
    Equiv.symm_apply_apply]

end Quantum.TensorProducts

end -- noncomputable section
