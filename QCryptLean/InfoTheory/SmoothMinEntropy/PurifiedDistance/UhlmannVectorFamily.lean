import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.UhlmannSubNormalized
import QCryptLean.Quantum.TensorProducts.VectorFamilyPurification

/-!
# Vector-family Uhlmann lower bound (domination-free)

This module packages the generic vector-family purification kernel
(`Quantum.TensorProducts.purifyVectorFamily`) with the sub-normalized live-branch
Uhlmann bound (`SubDensityOp.livePurificationOverlap_re_le_fidelity`) into a
single, reusable lower bound:

If two sub-density operators `ρ, σ : SubDensityOp d` are sum-of-ketbra
`ρ = Σ_k |v_k⟩⟨v_k|` and `σ = Σ_k |w_k⟩⟨w_k|` for vector families
`v, w : Fin anc → Ket d` on a common label set, then the real part of the
family-wise overlap sum lower-bounds the ordinary fidelity of the marginals:

  `Re (Σ_k ⟨v_k | w_k⟩) ≤ fidelity ρ σ`.

No operator domination is used — only that both states are represented as
sum-of-ketbra over the *same* ancilla labels.  This is the domination-free
Uhlmann tool needed by the weight-cap purified-distance route in the Renner
`thm:Hmincondrep` chain.
-/

open Quantum.Operators Quantum.TensorProducts

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Domination-free vector-family Uhlmann lower bound.** If `ρ` and `σ` are
sum-of-ketbra over a common label set `Fin anc`, then the real part of the
family-wise overlap sum is at most the ordinary fidelity of their PSD
marginals. -/
theorem SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d) (v w : Fin anc → Ket d)
    (hρ : ρ.toOp = ∑ k, ((v k) * (v k).dag : Op d))
    (hσ : σ.toOp = ∑ k, ((w k) * (w k).dag : Op d)) :
    (∑ k, ((v k).dag * (w k) : ℂ)).re ≤
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  have hψ : Quantum.TensorProducts.partialTraceB
      (purifyVectorFamily v * (purifyVectorFamily v).dag) = ρ.toOp := by
    rw [partialTraceB_purifyVectorFamily_ketbra, hρ]
  have hφ : Quantum.TensorProducts.partialTraceB
      (purifyVectorFamily w * (purifyVectorFamily w).dag) = σ.toOp := by
    rw [partialTraceB_purifyVectorFamily_ketbra, hσ]
  have h := SubDensityOp.livePurificationOverlap_re_le_fidelity ρ σ
    (purifyVectorFamily v) (purifyVectorFamily w) hψ hφ
  rwa [purifyVectorFamily_dag_mul] at h

/-- **Domination-free vector-family Uhlmann lower bound over an arbitrary finite
label set.** Same as `SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra` but with
the family indexed by an arbitrary `Fintype` `L` (composed with `Fintype.equivFin`
so the underlying kernel still sees a `Fin`-indexed family). This is the form
consumed by the weight-cap route, whose natural label set is the spectral-triple
product `(xs, x, z)`. -/
theorem SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra_fintype
    {d : ℕ} [NeZero d] {L : Type*} [Fintype L] [Nonempty L]
    (ρ σ : SubDensityOp d) (v w : L → Ket d)
    (hρ : ρ.toOp = ∑ l, ((v l) * (v l).dag : Op d))
    (hσ : σ.toOp = ∑ l, ((w l) * (w l).dag : Op d)) :
    (∑ l, ((v l).dag * (w l) : ℂ)).re ≤
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  have : NeZero (Fintype.card L) := ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin L with he
  have hρ' : ρ.toOp = ∑ k, ((v (e.symm k)) * (v (e.symm k)).dag : Op d) := by
    rw [hρ, ← Equiv.sum_comp e.symm]
  have hσ' : σ.toOp = ∑ k, ((w (e.symm k)) * (w (e.symm k)).dag : Op d) := by
    rw [hσ, ← Equiv.sum_comp e.symm]
  have h := SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra ρ σ
    (fun k => v (e.symm k)) (fun k => w (e.symm k)) hρ' hσ'
  rw [← Equiv.sum_comp e.symm (fun l => ((v l).dag * (w l) : ℂ))]
  exact h

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
