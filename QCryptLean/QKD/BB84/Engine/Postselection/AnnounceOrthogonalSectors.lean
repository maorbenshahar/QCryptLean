import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# Orthogonal announced-permutation sectors — trace-norm additivity

The retained-Eve announcement `announceLinearEveVisible n ℓ eveDim π` appends the orthogonal
rank-one projector `permAnnounceProjector n π = |π⟩⟨π|` on the `n.factorial`-dimensional public
permutation-announcement register (`QKD.BB84.Model.PermAnnounceRegister`).  Distinct permutations
`π`
land in mutually orthogonal sectors, so for any operator family `F : Equiv.Perm (Fin n) → Op (…)`
the trace norm of the announced sum is additive:
`‖Σ_π announceLinearEveVisible π (F π)‖₁ = Σ_π ‖announceLinearEveVisible π (F π)‖₁`.

This is the covariance-free orthogonal-sector trace-norm additivity used by the Bell
permutation-twirl WLOG endpoint to collapse the real−ideal CKR difference onto its
identity-permutation summand.

## Source / authority
Renner 2005 (`arXiv:quant-ph/0512258v2`, §6.5) de Finetti symmetrization (orthogonal announcement
registers); Christandl–König–Renner 2009 (`arXiv:0809.3019`, main.tex:268–:401 (\emph{Main Result}:
Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328)), block-diagonal
trace-norm step. -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Metrics
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- The public announcement projector is the rank-one matrix unit at the permutation's index. -/
lemma permAnnounceProjector_eq_single' (n : ℕ) (perm : Equiv.Perm (Fin n)) :
    permAnnounceProjector n perm =
      Matrix.single (permAnnounceIndexEquiv n perm)
        (permAnnounceIndexEquiv n perm) (1 : ℂ) := by
  ext i j
  by_cases hi : (permAnnounceIndexEquiv n perm) = i
  · by_cases hj : (permAnnounceIndexEquiv n perm) = j
    · simp [permAnnounceProjector, Matrix.single_apply, hi]
    · simp [permAnnounceProjector, Matrix.single_apply, hi]
  · by_cases hj : (permAnnounceIndexEquiv n perm) = j
    · simp [permAnnounceProjector, Matrix.single_apply, hj]
    · simp [permAnnounceProjector, hi, hj]

/-! ### Trace norm of a tensor with an arbitrary rank-one diagonal projector -/

/-- Trace norm of `A ⊗ |j⟩⟨j|` equals trace norm of `A` for any basis index `j`.

Realized as the `Fin k`-block-diagonal sum whose family is `A` at `j` and `0` elsewhere;
`Quantum.Metrics.traceNorm_blockDiagonal_sum` then gives `‖A‖₁`. -/
lemma traceNorm_tensor_single_diag {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (A : Op d) (j : Fin k) :
    traceNorm (A ⊗ (Matrix.single j j 1 : Op k)) = traceNorm A := by
  classical
  have hfam :
      A ⊗ (Matrix.single j j 1 : Op k) =
        ∑ i : Fin k, (if i = j then A else 0) ⊗ (Matrix.single i i 1 : Op k) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [ite_eq_right hij]
      ext a b; simp [Op.tensor, Matrix.zero_apply]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hfam, traceNorm_blockDiagonal_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; rw [ite_eq_right hij]; exact traceNorm_zero
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ### `mapTensorId` of "append a rank-one diagonal projector" -/

/-- The factor-swap equivalence `Fin ((a*c)*k) ≃ Fin ((a*k)*c)` that exchanges the inner
projector register `c` with the outer identity register `k`, keeping the base register `a`
fixed.  Built from `finProdFinEquiv` reassociation. -/
def tensorSwapInnerEquiv (a c k : ℕ) : Fin ((a * c) * k) ≃ Fin ((a * k) * c) :=
  (finProdFinEquiv.symm : Fin ((a * c) * k) ≃ Fin (a * c) × Fin k).trans
  (((finProdFinEquiv.symm.prodCongr (Equiv.refl (Fin k))) :
      Fin (a * c) × Fin k ≃ (Fin a × Fin c) × Fin k).trans
  ((Equiv.prodAssoc (Fin a) (Fin c) (Fin k)).trans
  (((Equiv.refl (Fin a)).prodCongr (Equiv.prodComm (Fin c) (Fin k))).trans
  ((Equiv.prodAssoc (Fin a) (Fin k) (Fin c)).symm.trans
  ((finProdFinEquiv.prodCongr (Equiv.refl (Fin c))).trans
  (finProdFinEquiv : Fin (a * k) × Fin c ≃ Fin ((a * k) * c)))))))

/-- The linear "append a fixed rank-one diagonal projector" map `A ↦ A ⊗ |j⟩⟨j|`. -/
def appendSingleLinear {a k : ℕ} (j : Fin k) : Op a →ₗ[ℂ] Op (a * k) where
  toFun A := A ⊗ (Matrix.single j j 1 : Op k)
  map_add' x y := by simp [Op.tensor_add_left]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [Op.tensor_smul_left]

/-- `mapTensorId (appendSingleLinear j) M` is the swap-reindexing of `M ⊗ |j⟩⟨j|`. -/
lemma mapTensorId_appendSingleLinear {a c k : ℕ} [NeZero a] [NeZero c] [NeZero k]
    [NeZero (a * c)] (j : Fin c) (M : Op (a * k)) :
    mapTensorId (appendSingleLinear (a := a) j) M =
      (M ⊗ (Matrix.single j j 1 : Op c)).submatrix
        (tensorSwapInnerEquiv a c k) (tensorSwapInnerEquiv a c k) := by
  ext p q
  rw [mapTensorId_apply_eq_apply_block]
  simp only [appendSingleLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Quantum.TensorProducts.Op_tensor_apply_finProd, Matrix.submatrix_apply,
    Quantum.TensorProducts.Op_tensor_apply_finProd]
  simp only [Matrix.of_apply]
  congr 1 <;> simp [tensorSwapInnerEquiv, Equiv.prodCongr, Equiv.prodComm, Equiv.prodAssoc]

/-! ### Trace norm under `mapTensorId` of a castDim reindex -/

/-- `mapTensorId` of a dimension cast preserves trace norm: the cast `Op.castDimLinear h`
is CPTP with the CPTP left inverse `Op.castDimLinear h.symm`, so its `mapTensorId` extension
is a trace-norm isometry (`le_antisymm` of the two contractivities). -/
lemma traceNorm_mapTensorId_castDimLinear {d d2 k : ℕ} [NeZero d] [NeZero d2] [NeZero k]
    (h : d = d2) (W : Op (d * k)) :
    traceNorm (mapTensorId (Op.castDimLinear h) W) = traceNorm W := by
  have hcast : IsCPTP (⇑(Op.castDimLinear h)) := castDimLinear_isCPTP h
  have hcast' : IsCPTP (⇑(Op.castDimLinear h.symm)) := castDimLinear_isCPTP h.symm
  have hinv : (Op.castDimLinear h.symm).comp (Op.castDimLinear h) = LinearMap.id := by
    apply LinearMap.ext
    intro A
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Op.castDimLinear,
      LinearMap.coe_mk, AddHom.coe_mk]
    cases h
    rfl
  apply le_antisymm
  · exact traceNorm_mapTensorId_cptp_contractive (Op.castDimLinear h) hcast W
  · calc traceNorm W
        = traceNorm (mapTensorId ((Op.castDimLinear h.symm).comp (Op.castDimLinear h)) W) := by
          rw [hinv]
          congr 1
          ext p q
          simp only [mapTensorId, Matrix.of_apply, LinearMap.id_coe, id_eq,
            Matrix.single_apply, ite_and, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          congr 1 <;> exact (finProdFinEquiv.apply_symm_apply _).symm
      _ = traceNorm (mapTensorId (Op.castDimLinear h.symm)
            (mapTensorId (Op.castDimLinear h) W)) := by
          rw [mapTensorId_comp]
      _ ≤ traceNorm (mapTensorId (Op.castDimLinear h) W) :=
          traceNorm_mapTensorId_cptp_contractive (Op.castDimLinear h.symm) hcast' _

/-! ### Per-term factorization and the orthogonal-sector additivity bridge -/

end QKD.BB84.Engine

end
