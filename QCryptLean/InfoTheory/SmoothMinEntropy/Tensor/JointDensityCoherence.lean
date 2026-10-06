import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct

/-!
# CQ Tensor Joint-Density Coherence — Kronecker/blockDiagonal swaps, CQ tensor, reindex equivalence

Matrix-level helpers used by the universal-permutation tensor-coherence
identity for `CQState.toJointDensity`, consumed elsewhere in the smooth-min-entropy
tensor development
(via `tensor_toJointDensity_purifiedDistance_eq`). The work is split out
into its own file to keep the high-level
SDP/min-entropy reasoning inspectable and avoid mixing low-level
Kronecker / `blockDiagonal` bookkeeping with the smooth-entropy layer.

## Main lemmas

* `Matrix.kronecker_blockDiagonal_blockDiagonal_swap`: pure entrywise identity
  that the Kronecker of two block-diagonal matrices, indexed over types `X`
  and `Y` respectively, equals — up to the canonical "swap inner two factors"
  reindexing — a block-diagonal indexed by `X × Y` whose block at `(x, y)` is
  the Kronecker of the constituent blocks. (The "H1" matrix-level helper.)
* `kroneckerMap_reindex_reindex`, `blockDiagonal_reindex_blocks`: routine
  pull-out / push-in identities for `Matrix.reindex` interacting with
  Kronecker products and `blockDiagonal`.
* `CQState.tensor`, `CQState.tensor_sum_trace`: the binary CQ-state tensor
  product and the trace factorization used by the smooth-Hmin tensor
  superadditivity proof.
* `tensorJointReindexEquiv`: the universal "rebracketing" permutation of
  `Fin (n * n' * card (X × X'))` that translates between the two natural
  index encodings (via `Fintype.equivFin (X × X')` vs. via
  `Fintype.equivFin X × Fintype.equivFin X'`).
* `CQState.tensor_toJointDensity_toOp_eq_reindex`: the universal-permutation
  tensor coherence — the joint density of the CQ tensor product equals, at
  the matrix level, a `Matrix.reindex` (by `tensorJointReindexEquiv`) of the
  dimension-cast operator tensor of the factor joint densities.

The strict matrix-equality form (without a permutation) is **infeasible**
because it would compare the arbitrary `Fintype.equivFin` choices on `X × X'`
versus on `X` and `X'` separately. The universal-permutation form above is
exactly what the purified-distance consumer
(`tensor_toJointDensity_purifiedDistance_eq`, elsewhere in the smooth-min-entropy tensor
development)
needs, since `purifiedDistance` is invariant under reindex by an equiv
(see `purifiedDistance_reindex`).
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open scoped Kronecker

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- "Swap inner two factors" equiv used when expressing the Kronecker product
of two block-diagonal matrices as a single block-diagonal matrix indexed over
the Cartesian product of the two block-index types.

This is a thin wrapper around `Equiv.prodProdProdComm` capturing the specific
type signature we use. -/
def middleSwap (n n' : ℕ) (X Y : Type*) :
    (Fin n × Fin n') × (X × Y) ≃ (Fin n × X) × (Fin n' × Y) :=
  Equiv.prodProdProdComm (Fin n) (Fin n') X Y

/-- **H1 (pure `Matrix` lemma).** Kronecker of two block-diagonal matrices is
the reindexing (via `middleSwap`) of a block-diagonal whose blocks are
Kroneckers.

For `A : X → Matrix (Fin n) (Fin n) ℂ` and `B : Y → Matrix (Fin n') (Fin n') ℂ`
(with `DecidableEq` on the index types):
`(blockDiagonal A) ⊗ₖ (blockDiagonal B)
  = reindex middleSwap middleSwap (blockDiagonal (fun p => A p.1 ⊗ₖ B p.2))`
where `middleSwap : (Fin n × X) × (Fin n' × Y) ≃ (Fin n × Fin n') × (X × Y)`.

Mathlib does not provide this directly; the closest analogues
(`Matrix.kronecker_diagonal`, `Matrix.diagonal_kronecker`) handle only the
fully-diagonal case. -/
lemma kronecker_blockDiagonal_blockDiagonal_swap
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {n n' : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℂ)
    (B : Y → Matrix (Fin n') (Fin n') ℂ) :
    Matrix.kroneckerMap (· * ·) (Matrix.blockDiagonal A) (Matrix.blockDiagonal B)
      = Matrix.reindex (middleSwap n n' X Y) (middleSwap n n' X Y)
          (Matrix.blockDiagonal
            (fun p : X × Y => Matrix.kroneckerMap (· * ·) (A p.1) (B p.2))) := by
  ext ⟨⟨a, x⟩, ⟨a', y⟩⟩ ⟨⟨b, u⟩, ⟨b', v⟩⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.blockDiagonal_apply, middleSwap]
  by_cases hxy : x = u ∧ y = v
  · obtain ⟨hx, hy⟩ := hxy
    subst hx; subst hy
    simp
  · push_neg at hxy
    by_cases hx : x = u
    · have hy : y ≠ v := hxy hx
      subst hx
      simp [hy]
    · simp [hx]

/-- **Pure `Matrix` lemma.** Kronecker product of two `Matrix.reindex`-ed
square matrices equals the `Matrix.reindex` (along the product equiv) of the
Kronecker product of the originals. Composes Mathlib's `kroneckerMap_reindex_left`
and `kroneckerMap_reindex_right`. -/
lemma kroneckerMap_reindex_reindex
    {α : Type*} [Mul α] {l n l' n' : Type*}
    (e₁ : l ≃ l') (e₂ : n ≃ n')
    (A : Matrix l l α) (B : Matrix n n α) :
    Matrix.kroneckerMap (· * ·) (Matrix.reindex e₁ e₁ A) (Matrix.reindex e₂ e₂ B) =
      Matrix.reindex (Equiv.prodCongr e₁ e₂) (Equiv.prodCongr e₁ e₂)
        (Matrix.kroneckerMap (· * ·) A B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_apply]

/-- **Pure `Matrix` lemma.** `blockDiagonal` of pointwise-reindexed blocks
equals the `reindex` (extending the inner-index equiv by the identity on the
block index) of `blockDiagonal`. -/
lemma blockDiagonal_reindex_blocks
    {β : Type*} [Zero β]
    {X m m' : Type*} [DecidableEq X] (e : m ≃ m')
    (M : X → Matrix m m β) :
    Matrix.blockDiagonal (fun x => Matrix.reindex e e (M x)) =
      Matrix.reindex (Equiv.prodCongr e (Equiv.refl X))
        (Equiv.prodCongr e (Equiv.refl X)) (Matrix.blockDiagonal M) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.blockDiagonal_apply_eq, Matrix.submatrix_apply,
      Matrix.blockDiagonal_apply_eq]
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hxy,
      Matrix.blockDiagonal_apply_ne _ _ _ hxy]

end InfoTheory.SmoothMinEntropy

/-! ### CQ tensor product helpers

`CQState.tensor` is defined in `TensorProduct.lean` (namespace
InfoTheory.SmoothMinEntropy). The lemma below adds the trace-factorization
identity used elsewhere and by `purifiedDistance_tensor_subadditive`. -/

namespace InfoTheory.SmoothMinEntropy

/-- The total trace of a CQ tensor product factorizes as the product of the
component total traces. Used by the smooth-Hmin tensor superadditivity proof
to lift normalization (and positive weight) from the factors to the tensor. -/
lemma CQState.tensor_sum_trace {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} (ρ : CQState X n) (ρ' : CQState X' n') :
    ∑ p : X × X', ((CQState.tensor ρ ρ').stateMap p).trace =
      (∑ x : X, (ρ.stateMap x).trace) *
        (∑ x' : X', (ρ'.stateMap x').trace) := by
  change ∑ p : X × X', ((ρ.stateMap p.1).tensor (ρ'.stateMap p.2)).trace = _
  calc
    ∑ p : X × X', ((ρ.stateMap p.1).tensor (ρ'.stateMap p.2)).trace
        = ∑ p : X × X', (ρ.stateMap p.1).trace * (ρ'.stateMap p.2).trace := by
          apply Finset.sum_congr rfl
          intro p _
          exact SubDensityOp.tensor_trace _ _
    _   = (∑ x : X, (ρ.stateMap x).trace) *
            (∑ x' : X', (ρ'.stateMap x').trace) := by
          rw [Fintype.sum_prod_type]
          simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Universal-permutation form of the CQ-tensor joint-density coherence

The strict matrix-equality form (asserting that
`(CQState.tensor ρ ρ').toJointDensity` is *literally*
`SubDensityOp.castDim _ (SubDensityOp.tensor ρ.toJointDensity ρ'.toJointDensity)`)
is infeasible: the LHS uses `Fintype.equivFin (X × X')` to encode the
Cartesian-product classical register into `Fin (card (X × X'))`, while the
RHS encodes the product through `(Fintype.equivFin X).prodCongr
(Fintype.equivFin X')` followed by `finProdFinEquiv`. Both are equivs into
the same `Fin _`, but they differ by an arbitrary permutation of
`X × X'`, and `blockDiagonal` is *not* invariant under such relabellings
when the family of blocks is non-constant.

What does hold (and is what `tensor_toJointDensity_purifiedDistance_eq` needs)
is a coherence *up to a permutation* of `Fin (n * n' * card (X × X'))`,
**universal** in `ρ ρ'`.

The permutation is just the relabelling between the two natural enumerations
of `(Fin n × Fin n') × (X × X')` by `Fin (n * n' * card (X × X'))`:
* the LHS encoding through `Fintype.equivFin (X × X')`,
* the RHS encoding through `(Fintype.equivFin X).prodCongr (Fintype.equivFin X')`.

Both are equivs into the same `Fin _`; their composition is a finite-type
permutation, even though the individual `Fintype.equivFin` choices are
`Trunc.out`-opaque. -/

/-- The universal "rebracketing" permutation of `Fin (n * n' * card (X × X'))`
that translates between the LHS index-decoding (via `Fintype.equivFin (X × X')`)
and the RHS index-decoding (via `Fintype.equivFin X × Fintype.equivFin X'`).

Independent of `ρ ρ'` — this is type-level data only. -/
noncomputable def tensorJointReindexEquiv
    (X X' : Type*) [Fintype X] [Fintype X']
    (n n' : ℕ)
    (h_dim : n * Fintype.card X * (n' * Fintype.card X') =
             n * n' * Fintype.card (X × X') := by
      rw [Fintype.card_prod]; ring) :
    Fin (n * n' * Fintype.card (X × X')) ≃ Fin (n * n' * Fintype.card (X × X')) :=
  let E_LHS : (Fin n × Fin n') × (X × X') ≃ Fin (n * n' * Fintype.card (X × X')) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl (X × X'))).trans <|
      (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin (X × X'))).trans finProdFinEquiv
  let E_RHS : (Fin n × Fin n') × (X × X') ≃ Fin (n * n' * Fintype.card (X × X')) :=
    (((InfoTheory.SmoothMinEntropy.middleSwap n n' X X').trans
        (Equiv.prodCongr
          ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans finProdFinEquiv)
          ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X')).trans finProdFinEquiv))).trans
      finProdFinEquiv).trans (finCongr h_dim)
  E_RHS.symm.trans E_LHS

/-- **Matrix-level coherence (universal-permutation form).**

The joint density of the CQ tensor product equals — at the matrix level — a
`Matrix.reindex` of the (dimension-cast) operator tensor of the factor joint
densities, where the reindex permutation `tensorJointReindexEquiv` is
universal in `ρ ρ'`.

The proof composes:
* `CQState.toJointDensity_toOp_eq_reindex_blockDiagonal` — LHS as a reindex of
  a blockDiagonal of the (Op-level) tensor blocks,
* `Op.tensor` definitional unfolding — each Op-tensor block as a reindex of a
  Kronecker product,
* `blockDiagonal_reindex_blocks` — pull the inner reindex out of blockDiagonal,
* `kroneckerMap_reindex_reindex` — push reindexes through Kronecker on the
  RHS factor side,
* `kronecker_blockDiagonal_blockDiagonal_swap` — the H1 helper that turns a
  Kronecker of blockDiagonals into a blockDiagonal-of-Kroneckers (up to
  `middleSwap`),
* `SubDensityOp.castDim_toOp_eq_reindex` — express the dimension cast as a
  reindex along `finCongr`.
* `Matrix.submatrix_submatrix` and `Equiv.self_trans_symm` — collapse the
  three reindex stacks into a single reindex by `tensorJointReindexEquiv`. -/
lemma CQState.tensor_toJointDensity_toOp_eq_reindex
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    {n n' : ℕ}
    (h_dim : n * Fintype.card X * (n' * Fintype.card X') =
             n * n' * Fintype.card (X × X') := by
      rw [Fintype.card_prod]; ring)
    (ρ : CQState X n) (ρ' : CQState X' n') :
    (CQState.tensor ρ ρ').toJointDensity.toOp =
      Matrix.reindex
          (tensorJointReindexEquiv X X' n n' h_dim)
          (tensorJointReindexEquiv X X' n n' h_dim)
        (SubDensityOp.castDim h_dim
            (SubDensityOp.tensor ρ.toJointDensity ρ'.toJointDensity)).toOp := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  -- Unfold each block: ((ρ.tensor ρ').stateMap p).toOp = Op.tensor (...) = reindex of kronecker.
  change (Matrix.reindex
        (((Equiv.refl (Fin (n * n'))).prodCongr (Fintype.equivFin (X × X'))).trans finProdFinEquiv)
        (((Equiv.refl (Fin (n * n'))).prodCongr (Fintype.equivFin (X × X'))).trans finProdFinEquiv))
      (Matrix.blockDiagonal (fun p : X × X' =>
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (ρ.stateMap p.1).toOp (ρ'.stateMap p.2).toOp))) = _
  rw [InfoTheory.SmoothMinEntropy.blockDiagonal_reindex_blocks]
  -- Now the RHS: rewrite castDim and Op.tensor of factor toJointDensity.toOp's
  rw [SubDensityOp.castDim_toOp_eq_reindex]
  change _ = (Matrix.reindex _ _) ((Matrix.reindex _ _)
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) ρ.toJointDensity.toOp ρ'.toJointDensity.toOp)))
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
    CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
    InfoTheory.SmoothMinEntropy.kroneckerMap_reindex_reindex,
    InfoTheory.SmoothMinEntropy.kronecker_blockDiagonal_blockDiagonal_swap]
  -- Both sides are now `reindex E E BD_pair` for different `E`, where
  -- BD_pair is the canonical block-diagonal of Kronecker blocks.
  -- It remains to show the two equiv stacks compose to equal results.
  -- Collapse all reindex stacks via `submatrix_submatrix`.
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  -- The remaining goal is an equality of `BD_pair.submatrix f f = BD_pair.submatrix g g`.
  -- It holds because both `f` and `g` equal the symm-direction of the same equiv
  -- (`tensorJointReindexEquiv` is constructed to make this so).
  unfold tensorJointReindexEquiv
  congr 1 <;> {
    funext x
    simp only [Function.comp_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.trans_apply, Equiv.symm_apply_apply]
  }

end InfoTheory.SmoothMinEntropy

end -- noncomputable
