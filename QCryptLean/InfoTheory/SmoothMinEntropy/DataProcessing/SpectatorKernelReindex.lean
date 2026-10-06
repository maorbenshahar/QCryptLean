import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.RegisterSwapBridge
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernelBlockRef
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening

/-!
# Reindexing announced spectator registers

Quantum-register equivalences commute with the classical announcement kernels and their block-
diagonal references. The resulting state and reference transports preserve smooth min-entropy.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The register equivalence `1_c ⊗ e` -/

/-- **The register equivalence `1_c ⊗ e`**, `Fin (c · a) ≃ Fin (c · b)` induced by
`e : Fin a ≃ Fin b` acting on the **low** digits only.

`finProdFinEquiv` puts the first component in the high digits, so this is the identity on the
spectator factor `Fin c` and `e` on the register being re-described.  Built exactly like
`swapTensorEquiv` (`PureCoreUncertainty.lean`). -/
def tensorRightCongrEquiv (c : ℕ) {a b : ℕ} (e : Fin a ≃ Fin b) : Fin (c * a) ≃ Fin (c * b) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl (Fin c)) e).trans finProdFinEquiv)

@[simp] lemma tensorRightCongrEquiv_apply {c a b : ℕ} (e : Fin a ≃ Fin b)
    (p : Fin c) (i : Fin a) :
    tensorRightCongrEquiv c e (finProdFinEquiv (p, i)) = finProdFinEquiv (p, e i) := by
  simp [tensorRightCongrEquiv]

@[simp] lemma tensorRightCongrEquiv_symm_apply {c a b : ℕ} (e : Fin a ≃ Fin b)
    (p : Fin c) (j : Fin b) :
    (tensorRightCongrEquiv c e).symm (finProdFinEquiv (p, j)) = finProdFinEquiv (p, e.symm j) := by
  rw [Equiv.symm_apply_eq, tensorRightCongrEquiv_apply, Equiv.apply_symm_apply]

/-- **The spectator factor is untouched.**  `1_c ⊗ e` reindexes `A ⊗ M` to `A ⊗ (e · M · e⁻¹)`. -/
lemma reindex_tensorRightCongrEquiv_tensor {c a b : ℕ} (e : Fin a ≃ Fin b) (A : Op c) (M : Op a) :
    Matrix.reindex (tensorRightCongrEquiv c e) (tensorRightCongrEquiv c e) (Op.tensor A M) =
      Op.tensor A (Matrix.reindex e e M) := by
  ext I J
  obtain ⟨pi, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨qj, rfl⟩ := finProdFinEquiv.surjective J
  obtain ⟨p, i⟩ := pi
  obtain ⟨q, j⟩ := qj
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, tensorRightCongrEquiv_symm_apply,
    tensorRightCongrEquiv_symm_apply, Op_tensor_apply_finProd, Op_tensor_apply_finProd,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]

/-- The heterogeneous sub-density reindex of a tensor leaves the spectator factor alone. -/
lemma SubDensityOp.reindexHetero_tensorRightCongr_tensor {c a b : ℕ} (e : Fin a ≃ Fin b)
    (A : SubDensityOp c) (M : SubDensityOp a) :
    SubDensityOp.reindexHetero (tensorRightCongrEquiv c e) (A.tensor M) =
      A.tensor (SubDensityOp.reindexHetero e M) := by
  apply SubDensityOp.ext
  rw [SubDensityOp.reindexHetero_toOp]
  exact reindex_tensorRightCongrEquiv_tensor e A.toOp M.toOp

/-- **The transport commutes with attaching the announce kernel.**

Reindexing the low register of an announced state is the same as announcing on the reindexed state:
the announced block never meets the register being re-described. -/
theorem CQState.reindexQHetero_tensorRightCongr_tensorLeftKernel
    {X : Type*} [Fintype X] {a b dC : ℕ} (e : Fin a ≃ Fin b)
    (ρ : CQState X a) (K : X → SubDensityOp dC) :
    CQState.reindexQHetero (tensorRightCongrEquiv dC e) (ρ.tensorLeftKernel K) =
      (CQState.reindexQHetero e ρ).tensorLeftKernel K := by
  refine CQState.ext_stateMap (funext fun x => ?_)
  exact SubDensityOp.reindexHetero_tensorRightCongr_tensor e (K x) (ρ.stateMap x)

/-! ## The announced reference transports blockwise -/

/-- Reindexing the low register of `Σ_p |p⟩⟨p| ⊗ ν_p` reindexes each block. -/
lemma reindexHetero_blockDiagRefOp {a b dC : ℕ} (e : Fin a ≃ Fin b)
    (ν : Fin dC → SubDensityOp a) :
    Matrix.reindex (tensorRightCongrEquiv dC e) (tensorRightCongrEquiv dC e) (blockDiagRefOp ν) =
      blockDiagRefOp (fun p => SubDensityOp.reindexHetero e (ν p)) := by
  rw [blockDiagRefOp, blockDiagRefOp, ← Matrix.reindexLinearEquiv_apply ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.reindexLinearEquiv_apply, reindex_tensorRightCongrEquiv_tensor]
  rfl

/-- The reindexed block family is still sub-normalised: a reindex preserves the trace. -/
lemma sum_reindexHetero_trace_le_one {a b dC : ℕ} (e : Fin a ≃ Fin b)
    (ν : Fin dC → SubDensityOp a) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    ∑ p : Fin dC, (SubDensityOp.reindexHetero e (ν p)).trace ≤ 1 := by
  have h : ∀ p : Fin dC, (SubDensityOp.reindexHetero e (ν p)).trace = (ν p).trace := by
    intro p
    change ((Matrix.reindex e e (ν p).toOp).trace).re = ((ν p).toOp.trace).re
    rw [Matrix.trace_reindex_self]
  simp_rw [h]
  exact hν

/-- **The announced pair transports as a pair.** -/
theorem SubDensityOp.reindexHetero_tensorRightCongr_blockDiagRef {a b dC : ℕ} (e : Fin a ≃ Fin b)
    (ν : Fin dC → SubDensityOp a) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    SubDensityOp.reindexHetero (tensorRightCongrEquiv dC e) (blockDiagRef ν hν) =
      blockDiagRef (fun p => SubDensityOp.reindexHetero e (ν p))
        (sum_reindexHetero_trace_le_one e ν hν) := by
  apply SubDensityOp.ext
  rw [SubDensityOp.reindexHetero_toOp, blockDiagRef_toOp, blockDiagRef_toOp]
  exact reindexHetero_blockDiagRefOp e ν

/-- Extended smooth entropy is invariant under this simultaneous register reindexing. -/
theorem smoothMinEntropy_reindexQHetero_tensorRightCongr_tensorLeftKernel_blockDiagRef
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {a b dC : ℕ}
    [NeZero (dC * a)] [NeZero (dC * b)] (e : Fin a ≃ Fin b) (ε : ℝ)
    (ρ : CQState X a) (K : X → SubDensityOp dC)
    (ν : Fin dC → SubDensityOp a) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    smoothMinEntropy ε ((CQState.reindexQHetero e ρ).tensorLeftKernel K)
        (blockDiagRef (fun p => SubDensityOp.reindexHetero e (ν p))
          (sum_reindexHetero_trace_le_one e ν hν)) =
      smoothMinEntropy ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν) := by
  rw [← CQState.reindexQHetero_tensorRightCongr_tensorLeftKernel e ρ K,
    ← SubDensityOp.reindexHetero_tensorRightCongr_blockDiagRef e ν hν]
  exact smoothMinEntropy_reindexQHetero (tensorRightCongrEquiv dC e) ε _ _


/-- Reindexing the quantum part of a left-kernel state and its block-diagonal reference
preserves signed smooth min-entropy. -/
theorem smoothMinEntropyReal_reindexQHetero_tensorRightCongr_tensorLeftKernel_blockDiagRef
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {a b dC : ℕ}
    [NeZero (dC * a)] [NeZero (dC * b)] (e : Fin a ≃ Fin b) (ε : ℝ)
    (ρ : CQState X a) (K : X → SubDensityOp dC)
    (ν : Fin dC → SubDensityOp a) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    smoothMinEntropyReal ε ((CQState.reindexQHetero e ρ).tensorLeftKernel K)
        (blockDiagRef (fun p => SubDensityOp.reindexHetero e (ν p))
          (sum_reindexHetero_trace_le_one e ν hν)) =
      smoothMinEntropyReal ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν) := by
  rw [← CQState.reindexQHetero_tensorRightCongr_tensorLeftKernel e ρ K,
    ← SubDensityOp.reindexHetero_tensorRightCongr_blockDiagRef e ν hν]
  exact smoothMinEntropyReal_reindexQHetero (tensorRightCongrEquiv dC e) ε _ _

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
