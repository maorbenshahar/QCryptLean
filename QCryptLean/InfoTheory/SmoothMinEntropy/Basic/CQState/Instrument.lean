import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.OfBlocks
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Channels.CPTP.IdTensorRect
import QCryptLean.Math.Combinatorics.FinProductEquiv

/-!
# Joint CQ operators and completely positive instruments

`cqJointLinearMap` assembles the diagonal blocks in quantum-first order.
`CQState.ofInstrument` and `CQState.ofInstrumentExtension` construct subnormalized CQ states
from a completely positive instrument whose total output weight is at most one.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Embed an operator-valued family as the diagonal blocks of a joint operator. -/
def cqJointLinearMap (X : Type*) [Fintype X] [DecidableEq X] (b : ℕ) :
    (X → Op b) →ₗ[ℂ] Op (b * Fintype.card X) where
  toFun f := Matrix.reindex (cqJointEquiv X b) (cqJointEquiv X b)
    (Matrix.blockDiagonal f)
  map_add' f g := by simp only [Matrix.blockDiagonal_add, Matrix.reindex_add]
  map_smul' c f := by
    simp only [Matrix.blockDiagonal_smul, Matrix.reindex_smul, RingHom.id_apply]

/-- The CQ joint-density construction is the linear diagonal-block embedding. -/
lemma CQState.toJointDensity_toOp_eq_cqJointLinearMap
    {X : Type*} [Fintype X] [DecidableEq X] {b : ℕ}
    (ρ : CQState X b) :
    ρ.toJointDensity.toOp = cqJointLinearMap X b (fun x => (ρ.stateMap x).toOp) := rfl

/-- Matrix entries of the joint operator in quantum--classical coordinates. -/
@[simp] lemma cqJointLinearMap_apply_cqJointEquiv {X : Type*} [Fintype X] [DecidableEq X] {b : ℕ}
    (f : X → Op b) (i j : Fin b) (x y : X) :
    cqJointLinearMap X b f (cqJointEquiv X b (i, x)) (cqJointEquiv X b (j, y)) =
      if x = y then f x i j else 0 := by
  simp [cqJointLinearMap, Matrix.reindex_apply, Matrix.blockDiagonal_apply]

/-- Assemble the classical output blocks of a linear instrument into one map. -/
def jointInstrumentMap {X : Type*} [Fintype X] [DecidableEq X] {a b : ℕ}
    (L : X → Op a →ₗ[ℂ] Op b) : Op a →ₗ[ℂ] Op (b * Fintype.card X) :=
  (cqJointLinearMap X b).comp (LinearMap.pi L)

/-- Applying the joint instrument embeds its output blocks. -/
@[simp] lemma jointInstrumentMap_apply {X : Type*} [Fintype X] [DecidableEq X]
    {a b : ℕ} (L : X → Op a →ₗ[ℂ] Op b) (A : Op a) :
    jointInstrumentMap L A = cqJointLinearMap X b (fun x => L x A) := rfl

/-- Move an untouched reference past the classical register in the quantum-first
CQ convention: `(B X) R ≃ (B R) X`. -/
def jointReferenceEquiv (X : Type*) [Fintype X] (b r : ℕ) :
    Fin ((b * Fintype.card X) * r) ≃ Fin ((b * r) * Fintype.card X) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr (cqJointEquiv X b).symm (Equiv.refl _)) |>.trans
    (Equiv.prodAssoc _ _ _) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm X (Fin r))) |>.trans
    (Equiv.prodAssoc _ _ _).symm |>.trans
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)) |>.trans
    (cqJointEquiv X (b * r))

/-- The register permutation sends `(B, X, R)` to `(B, R, X)`. -/
@[simp] lemma jointReferenceEquiv_apply (X : Type*) [Fintype X] (b r : ℕ)
    (i : Fin b) (x : X) (k : Fin r) :
    jointReferenceEquiv X b r (finProdFinEquiv (cqJointEquiv X b (i, x), k)) =
      cqJointEquiv X (b * r) (finProdFinEquiv (i, k), x) := by
  simp [jointReferenceEquiv]

/-- The inverse permutation restores the classical register before the reference. -/
@[simp] lemma jointReferenceEquiv_symm_apply (X : Type*) [Fintype X] (b r : ℕ)
    (i : Fin b) (k : Fin r) (x : X) :
    (jointReferenceEquiv X b r).symm
        (cqJointEquiv X (b * r) (finProdFinEquiv (i, k), x)) =
      finProdFinEquiv (cqJointEquiv X b (i, x), k) := by
  simp [jointReferenceEquiv]

/-- Tensoring a joint instrument with a reference is the joint operator of the
individually tensored blocks, up to the prescribed register permutation. -/
lemma cqJointLinearMap_mapTensorId {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {a b r : ℕ} [NeZero a] [NeZero b] [NeZero r]
    (L : X → Op a →ₗ[ℂ] Op b) (A : Op (a * r)) :
    cqJointLinearMap X (b * r) (fun x => mapTensorId (L x) A) =
      Matrix.reindex (jointReferenceEquiv X b r) (jointReferenceEquiv X b r)
        (mapTensorId (jointInstrumentMap L) A) := by
  ext p q
  obtain ⟨⟨ik, x⟩, rfl⟩ := (cqJointEquiv X (b * r)).surjective p
  obtain ⟨⟨jl, y⟩, rfl⟩ := (cqJointEquiv X (b * r)).surjective q
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ik
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective jl
  rw [cqJointLinearMap_apply_cqJointEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, jointReferenceEquiv_symm_apply,
    mapTensorId_apply_eq_apply_block, Equiv.symm_apply_apply,
    jointInstrumentMap_apply, cqJointLinearMap_apply_cqJointEquiv]

/-- Joint diagonal-block embedding commutes with relabelling the quantum register. -/
lemma cqJointLinearMap_reindex {X : Type*} [Fintype X] [DecidableEq X] {a b : ℕ}
    (e : Fin a ≃ Fin b) (f : X → Op a) :
    cqJointLinearMap X b (fun x => Matrix.reindex e e (f x)) =
      Matrix.reindex (Equiv.finProdCongrExt e (Fintype.card X))
        (Equiv.finProdCongrExt e (Fintype.card X))
        (cqJointLinearMap X a f) := by
  ext p q
  obtain ⟨⟨i, x⟩, rfl⟩ := (cqJointEquiv X b).surjective p
  obtain ⟨⟨j, y⟩, rfl⟩ := (cqJointEquiv X b).surjective q
  simp [cqJointLinearMap, cqJointEquiv, Equiv.finProdCongrExt,
    Matrix.reindex_apply, Matrix.blockDiagonal_apply]

/-- Apply a completely positive instrument with total weight at most one. -/
def CQState.ofInstrument {X : Type*} [Fintype X] {a b : ℕ} [NeZero a] [NeZero b]
    (L : X → Op a →ₗ[ℂ] Op b) (hL : ∀ x, IsCompletelyPositive ⇑(L x))
    (hw : ∀ ρ : DensityOp a, ∑ x, (L x ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp a) : CQState X b :=
  CQState.ofBlocks (fun x => L x ρ.toOp)
    (fun x => cp_linear_preserves_posSemidef (L x) (hL x) ρ.toOp
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)) (hw ρ)

/-- The blocks of the instrument state are the instrument outputs. -/
@[simp] lemma CQState.ofInstrument_stateMap_toOp
    {X : Type*} [Fintype X] {a b : ℕ} [NeZero a] [NeZero b]
    (L : X → Op a →ₗ[ℂ] Op b) (hL : ∀ x, IsCompletelyPositive ⇑(L x))
    (hw : ∀ ρ : DensityOp a, ∑ x, (L x ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp a) (x : X) :
    ((CQState.ofInstrument L hL hw ρ).stateMap x).toOp = L x ρ.toOp := rfl

/-- Apply a completely positive instrument while leaving a reference register untouched. -/
def CQState.ofInstrumentExtension {X : Type*} [Fintype X] {a b r : ℕ}
    [NeZero a] [NeZero b] [NeZero r]
    (L : X → Op a →ₗ[ℂ] Op b) (hL : ∀ x, IsCompletelyPositive ⇑(L x))
    (hw : ∀ ρ : DensityOp a, ∑ x, (L x ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp (a * r)) : CQState X (b * r) :=
  CQState.ofBlocks (fun x => mapTensorId (L x) ρ.toOp)
    (fun x => mapTensorId_posSemidef (L x) ρ.toOp
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) (hL x)) (by
        simp only [trace_mapTensorId]
        exact hw ρ.partialTraceB)

/-- The extended instrument blocks retain the reference by tensoring with the identity. -/
@[simp] lemma CQState.ofInstrumentExtension_stateMap_toOp
    {X : Type*} [Fintype X] {a b r : ℕ} [NeZero a] [NeZero b] [NeZero r]
    (L : X → Op a →ₗ[ℂ] Op b) (hL : ∀ x, IsCompletelyPositive ⇑(L x))
    (hw : ∀ ρ : DensityOp a, ∑ x, (L x ρ.toOp).trace.re ≤ 1)
    (ρ : DensityOp (a * r)) (x : X) :
    ((CQState.ofInstrumentExtension L hL hw ρ).stateMap x).toOp =
      mapTensorId (L x) ρ.toOp := rfl

end InfoTheory.SmoothMinEntropy
