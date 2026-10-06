import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.Transport
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty
import QCryptLean.Quantum.TensorProducts.CastDim

/-!
# Quantum-register reindexing

Heterogeneous quantum-register equivalences preserve smooth min-entropy when the CQ state and
reference are reindexed together. Tensor swaps and register rotations are special cases.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The heterogeneous blockwise quantum reindex -/

/-- On a single dimension the heterogeneous sub-density reindex is `SubDensityOp.reindex`. -/
lemma SubDensityOp.reindexHetero_eq_reindex {n : ℕ} (e : Fin n ≃ Fin n) (ρ : SubDensityOp n) :
    SubDensityOp.reindexHetero e ρ = SubDensityOp.reindex e ρ := rfl

/-- On a single dimension the heterogeneous CQ reindex is `CQState.reindexQ`. -/
lemma CQState.reindexQHetero_eq_reindexQ {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) :
    CQState.reindexQHetero e ρ = CQState.reindexQ e ρ := rfl

/-! ## The tensor-factor swap -/

/-- The swap sends the reference `A ⊗ B` to `B ⊗ A`. -/
lemma SubDensityOp.reindexHetero_swapTensorEquiv_tensor {a b : ℕ}
    (A : SubDensityOp a) (B : SubDensityOp b) :
    SubDensityOp.reindexHetero (swapTensorEquiv a b) (A.tensor B) = B.tensor A := by
  apply SubDensityOp.ext
  rw [SubDensityOp.reindexHetero_toOp]
  exact reindex_swapTensorEquiv_tensor A.toOp B.toOp

/-- The swap sends a blockwise-product CQ state `x ↦ A x ⊗ B x` to `x ↦ B x ⊗ A x`. -/
lemma CQState.reindexQHetero_swapTensorEquiv_stateMap_toOp {X : Type*} [Fintype X] {a b : ℕ}
    (ρ : CQState X (a * b)) (A : X → Op a) (B : X → Op b)
    (h : ∀ x, (ρ.stateMap x).toOp = Op.tensor (A x) (B x)) (x : X) :
    ((CQState.reindexQHetero (swapTensorEquiv a b) ρ).stateMap x).toOp =
      Op.tensor (B x) (A x) := by
  change Matrix.reindex (swapTensorEquiv a b) (swapTensorEquiv a b) (ρ.stateMap x).toOp = _
  rw [h x]
  exact reindex_swapTensorEquiv_tensor (A x) (B x)

/-! ## Moving the leading factor past a pair -/

/-- The dimension cast undoes the inverse dimension transport. -/
private lemma castDim_eqRec_symm_op {n m : ℕ} (h : n = m) (u : Op m) :
    Op.castDim h (h.symm ▸ u) = u := by subst h; rfl

/-- **The leading-register rotation** `Fin (c · (a · b)) ≃ Fin (a · (b · c))`.

It sends the register layout `C ⊗ (A ⊗ B)` to `A ⊗ (B ⊗ C)`: the leading factor `C` is moved to
the trailing slot while the relative order of `A` and `B` is preserved.  Concretely it is the
two-factor swap of `c` against `a · b`, followed by the reassociation `(a · b) · c = a · (b · c)`.

This is the orientation move required when an announcement register occupying the high digits has
to be turned into a *trailing* ancilla while a surviving system register `A` is exposed in the
high digits. -/
def rotateLeadTensorEquiv (c a b : ℕ) : Fin (c * (a * b)) ≃ Fin (a * (b * c)) :=
  (swapTensorEquiv c (a * b)).trans (finCongr (Nat.mul_assoc a b c))

/-- The leading-register rotation evaluated on a triple tensor: `C ⊗ (A ⊗ B) ↦ A ⊗ (B ⊗ C)`. -/
lemma reindex_rotateLeadTensorEquiv_tensor {a b c : ℕ} (C : Op c) (A : Op a) (B : Op b) :
    Matrix.reindex (rotateLeadTensorEquiv c a b) (rotateLeadTensorEquiv c a b)
        (Op.tensor C (Op.tensor A B)) = Op.tensor A (Op.tensor B C) := by
  rw [rotateLeadTensorEquiv, Matrix.reindex_trans_apply, reindex_swapTensorEquiv_tensor,
    ← Op.castDim_eq_reindex_finCongr, ← Op.tensor_assoc, castDim_eqRec_symm_op]

/-- The leading-register rotation on a reference operator: `C ⊗ (A ⊗ B) ↦ A ⊗ (B ⊗ C)`. -/
lemma SubDensityOp.reindexHetero_rotateLeadTensorEquiv_tensor {a b c : ℕ}
    (C : SubDensityOp c) (A : SubDensityOp a) (B : SubDensityOp b) :
    SubDensityOp.reindexHetero (rotateLeadTensorEquiv c a b) (C.tensor (A.tensor B)) =
      A.tensor (B.tensor C) := by
  apply SubDensityOp.ext
  rw [SubDensityOp.reindexHetero_toOp]
  exact reindex_rotateLeadTensorEquiv_tensor C.toOp A.toOp B.toOp

/-- Extended smooth entropy is invariant under this simultaneous register reindexing. -/
theorem smoothMinEntropy_reindexQHetero {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} [NeZero n] [NeZero m] (e : Fin n ≃ Fin m) (ε : ℝ)
    (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy ε (CQState.reindexQHetero e ρ) (SubDensityOp.reindexHetero e σ) =
      smoothMinEntropy ε ρ σ := by
  have h : n = m := by simpa using Fintype.card_congr e
  subst h
  rw [CQState.reindexQHetero_eq_reindexQ, SubDensityOp.reindexHetero_eq_reindex]
  exact smoothMinEntropy_reindexQ e ε ρ σ

/-- Extended smooth entropy is invariant under this simultaneous register reindexing. -/
theorem smoothMinEntropy_reindexQHetero_swapTensor {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {a b : ℕ} [NeZero (a * b)] [NeZero (b * a)] (ε : ℝ)
    (ρ : CQState X (a * b)) (σ : SubDensityOp (a * b)) :
    smoothMinEntropy ε (CQState.reindexQHetero (swapTensorEquiv a b) ρ)
        (SubDensityOp.reindexHetero (swapTensorEquiv a b) σ) =
      smoothMinEntropy ε ρ σ :=
  smoothMinEntropy_reindexQHetero (swapTensorEquiv a b) ε ρ σ

/-- Extended smooth entropy is invariant under this simultaneous register reindexing. -/
theorem smoothMinEntropy_reindexQHetero_rotateLead {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {a b c : ℕ} [NeZero (c * (a * b))] [NeZero (a * (b * c))] (ε : ℝ)
    (ρ : CQState X (c * (a * b))) (σ : SubDensityOp (c * (a * b))) :
    smoothMinEntropy ε (CQState.reindexQHetero (rotateLeadTensorEquiv c a b) ρ)
        (SubDensityOp.reindexHetero (rotateLeadTensorEquiv c a b) σ) =
      smoothMinEntropy ε ρ σ :=
  smoothMinEntropy_reindexQHetero (rotateLeadTensorEquiv c a b) ε ρ σ


/-- Reindexing between equivalent quantum dimensions preserves signed smooth min-entropy when
applied to both state and reference. -/
theorem smoothMinEntropyReal_reindexQHetero {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} [NeZero n] [NeZero m] (e : Fin n ≃ Fin m) (ε : ℝ)
    (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropyReal ε (CQState.reindexQHetero e ρ) (SubDensityOp.reindexHetero e σ) =
      smoothMinEntropyReal ε ρ σ := by
  have h : n = m := by simpa using Fintype.card_congr e
  subst h
  rw [CQState.reindexQHetero_eq_reindexQ, SubDensityOp.reindexHetero_eq_reindex]
  exact smoothMinEntropyReal_reindexQ e ε ρ σ

/-- Swapping the tensor factors of state and reference preserves signed smooth min-entropy. -/
theorem smoothMinEntropyReal_reindexQHetero_swapTensor {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {a b : ℕ} [NeZero (a * b)] [NeZero (b * a)] (ε : ℝ)
    (ρ : CQState X (a * b)) (σ : SubDensityOp (a * b)) :
    smoothMinEntropyReal ε (CQState.reindexQHetero (swapTensorEquiv a b) ρ)
        (SubDensityOp.reindexHetero (swapTensorEquiv a b) σ) =
      smoothMinEntropyReal ε ρ σ :=
  smoothMinEntropyReal_reindexQHetero (swapTensorEquiv a b) ε ρ σ

/-- Rotating the leading tensor factor in state and reference preserves signed smooth
min-entropy. -/
theorem smoothMinEntropyReal_reindexQHetero_rotateLead {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {a b c : ℕ} [NeZero (c * (a * b))] [NeZero (a * (b * c))] (ε : ℝ)
    (ρ : CQState X (c * (a * b))) (σ : SubDensityOp (c * (a * b))) :
    smoothMinEntropyReal ε (CQState.reindexQHetero (rotateLeadTensorEquiv c a b) ρ)
        (SubDensityOp.reindexHetero (rotateLeadTensorEquiv c a b) σ) =
      smoothMinEntropyReal ε ρ σ :=
  smoothMinEntropyReal_reindexQHetero (rotateLeadTensorEquiv c a b) ε ρ σ

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
