import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistanceReindex

/-!
# Partition / permutation infrastructure for `SubDensityOp.tensorFinProd`

Generic, reusable lemmas relating a register permutation of a finite tensor
product `SubDensityOp.tensorFinProd` to a permutation of its factor family.  This
is the index/tensor algebra behind reorganizing a non-contiguous subset of tensor
factors into a contiguous block (e.g. gathering the key rounds of a sifted BB84
string before the PE rounds), via the quantum-register-reindex invariance of
the smooth min-entropy (`smoothMinEntropy_reindexQ`).

## Main statements
- `SubDensityOp.tensorFinProd_reindex_perm`: a register permutation of a finite
  tensor product equals the tensor product with the factor family permuted.
- `SubDensityOp.tensor_assoc`: associativity of the binary `SubDensityOp` tensor
  product up to the dimension-reassociation cast.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Forward (round-major) entry formula for `SubDensityOp.tensorFinProd`: at a
`finFunctionFinEquiv` index without `Fin.rev`, the factor at position `k` is
`f (Fin.rev k)`; this is the entry formula of `SubDensityOp.tensorFinProd_toOp`. -/
lemma SubDensityOp.tensorFinProd_toOp_entry_prod_fwd {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (f : Fin n → SubDensityOp d) (a b : Fin n → Fin d) :
    (SubDensityOp.tensorFinProd n f).toOp (finFunctionFinEquiv a) (finFunctionFinEquiv b) =
      ∏ k : Fin n, (f (Fin.rev k)).toOp (a k) (b k) := by
  rw [SubDensityOp.tensorFinProd_toOp, tensorFamily_apply_finFunctionFinEquiv]

/-- The conjugate of a permutation by index-reversal, used to align the
round-major `finFunctionFinEquiv` convention with the `Fin.rev` of the
`tensorFinProd` recursion. -/
def revConj {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans (σ.trans Fin.revPerm)

@[simp] lemma revConj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    revConj σ i = (σ i.rev).rev := rfl

/-- The register permutation of `Fin (d ^ n)` induced by a permutation `σ` of the
`n` tensor positions, through the round-major encoding `finFunctionFinEquiv`.
The index-reversal conjugation aligns this with the `tensorFinProd` convention so
that `tensorFinProd_reindex_perm` reads cleanly as `f ∘ σ`. -/
noncomputable def registerPerm (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fin (d ^ n) ≃ Fin (d ^ n) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.arrowCongr (revConj σ) (Equiv.refl (Fin d))).trans finFunctionFinEquiv)

/-- The inverse of `registerPerm d n σ` acts on the round-major index function by
postcomposition with `revConj σ`. -/
lemma registerPerm_symm_apply (d n : ℕ) (σ : Equiv.Perm (Fin n)) (K : Fin (d ^ n)) :
    (registerPerm d n σ).symm K =
      finFunctionFinEquiv ((finFunctionFinEquiv.symm K) ∘ (revConj σ)) := by
  simp only [registerPerm, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.arrowCongr_symm, Equiv.refl_symm]
  rfl

/-- **Register permutation ↔ factor permutation.**  A register permutation of a
finite tensor product equals the tensor product with its factor family permuted
(by `σ.symm`):
`reindex (registerPerm d n σ) (tensorFinProd n f) = tensorFinProd n (f ∘ σ.symm)`. -/
theorem SubDensityOp.tensorFinProd_reindex_perm {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (σ : Equiv.Perm (Fin n)) (f : Fin n → SubDensityOp d) :
    SubDensityOp.reindex (registerPerm d n σ) (SubDensityOp.tensorFinProd n f) =
      SubDensityOp.tensorFinProd n (f ∘ σ.symm) := by
  apply SubDensityOp.ext
  ext I J
  have hentry : (SubDensityOp.reindex (registerPerm d n σ) (SubDensityOp.tensorFinProd n f)).toOp I
      J
      = (SubDensityOp.tensorFinProd n f).toOp ((registerPerm d n σ).symm I)
          ((registerPerm d n σ).symm J) := by
    simp only [SubDensityOp.reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hentry, registerPerm_symm_apply, registerPerm_symm_apply]
  set aI := finFunctionFinEquiv.symm I with haI
  set aJ := finFunctionFinEquiv.symm J with haJ
  rw [SubDensityOp.tensorFinProd_toOp_entry_prod_fwd]
  have hRHS : (SubDensityOp.tensorFinProd n (f ∘ σ.symm)).toOp I J =
      (SubDensityOp.tensorFinProd n (f ∘ σ.symm)).toOp (finFunctionFinEquiv aI)
        (finFunctionFinEquiv aJ) := by
    rw [haI, haJ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [hRHS, SubDensityOp.tensorFinProd_toOp_entry_prod_fwd]
  rw [← Equiv.prod_comp (revConj σ.symm)
    (fun k => (f k.rev).toOp ((aI ∘ revConj σ) k) ((aJ ∘ revConj σ) k))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [Function.comp_apply, revConj_apply, Fin.rev_rev, Equiv.apply_symm_apply]

/-! ### Associativity of the `SubDensityOp` tensor product -/

/-- Associativity of the `SubDensityOp` tensor product, up to the dimension-reassociation cast. -/
lemma SubDensityOp.tensor_assoc {a b c : ℕ}
    (X : SubDensityOp a) (Y : SubDensityOp b) (Z : SubDensityOp c) :
    SubDensityOp.castDim (Nat.mul_assoc a b c).symm (X.tensor (Y.tensor Z)) =
      (X.tensor Y).tensor Z := by
  apply SubDensityOp.ext
  ext I J
  rw [SubDensityOp.castDim_toOp_cast]
  change (X.toOp ⊗ (Y.toOp ⊗ Z.toOp)) (Fin.cast _ I) (Fin.cast _ J) =
    ((X.toOp ⊗ Y.toOp) ⊗ Z.toOp) I J
  rw [← Op.tensor_assoc, matrix_eqRec_apply]

/-! ### Append (block split) of `SubDensityOp.tensorFinProd` -/

/-- **Index split for the register reindex `d^(a+b) ≅ d^a · d^b`.**  The flat
register index of the round-major encoding `finFunctionFinEquiv (α ∘ Fin.rev)` of
the coefficient family `α : Fin (a+b) → Fin d`, cast across `d^a · d^b = d^(a+b)`,
splits under `finProdFinEquiv` into the high block (first `a` coefficients) and
the low block (last `b` coefficients), each in its own round-major `Fin.rev`
encoding.  The `tensorFinProd` recursion makes the first factor the most
significant, so the first-`a` block is the high (`.1`) `finProdFinEquiv` factor. -/
private lemma finProdFinEquiv_cast_ffe_rev_split {d a b : ℕ} [NeZero d]
    (α : Fin (a + b) → Fin d) (h : d ^ a * d ^ b = d ^ (a + b)) :
    Fin.cast h.symm (finFunctionFinEquiv (α ∘ Fin.rev)) =
      finProdFinEquiv
        (finFunctionFinEquiv ((α ∘ Fin.castAdd b) ∘ Fin.rev),
         finFunctionFinEquiv ((α ∘ Fin.natAdd a) ∘ Fin.rev)) := by
  apply Fin.ext
  rw [Fin.val_cast, finProdFinEquiv_apply_val, finFunctionFinEquiv_apply_val,
      finFunctionFinEquiv_apply_val, finFunctionFinEquiv_apply_val]
  -- Reindex the LHS sum `∑_{p} (α (rev p)) d^p` by `p ↦ rev p`.
  rw [← Equiv.sum_comp Fin.revPerm
        (fun p => ((α ∘ Fin.rev) p).val * d ^ (p : ℕ))]
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev]
  -- Now LHS = ∑_{q} (α q) d^{rev q}; split at `a`.
  rw [Fin.sum_univ_add, add_comm]
  congr 1
  · -- the last-`b` block (the low `.2` factor)
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev, Fin.val_natAdd]
    congr 2
    omega
  · -- the first-`a` block (the high `.1` factor), carrying the `d ^ b` weight
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev, Fin.val_castAdd]
    rw [mul_left_comm, ← pow_add]
    congr 2
    omega

/-- **Block split (append) of `SubDensityOp.tensorFinProd`.**  The finite tensor
product over `a + b` factors of a family obtained by appending `f1` (the first `a`
factors) and `f2` (the last `b` factors) equals — up to the register reassociation
`d^a · d^b = d^(a+b)` — the binary tensor product of the two sub-products.  The
first-`a` block is the high (`.1`) tensor factor, matching the most-significant
position convention of the `tensorFinProd` recursion. -/
theorem SubDensityOp.tensorFinProd_append {d a b : ℕ} [NeZero d]
    (f1 : Fin a → SubDensityOp d) (f2 : Fin b → SubDensityOp d) :
    SubDensityOp.castDim (pow_add d a b).symm
      ((SubDensityOp.tensorFinProd a f1).tensor (SubDensityOp.tensorFinProd b f2)) =
      SubDensityOp.tensorFinProd (a + b) (Fin.append f1 f2) := by
  have : NeZero (d ^ a) := NeZero.pow
  have : NeZero (d ^ b) := NeZero.pow
  have : NeZero (d ^ (a + b)) := NeZero.pow
  set h0 : d ^ a * d ^ b = d ^ (a + b) := (pow_add d a b).symm with hh0
  apply SubDensityOp.ext
  ext I J
  set α : Fin (a + b) → Fin d := (finFunctionFinEquiv.symm I) ∘ Fin.rev with hα
  set β : Fin (a + b) → Fin d := (finFunctionFinEquiv.symm J) ∘ Fin.rev with hβ
  have hrev : (Fin.rev : Fin (a + b) → Fin (a + b)) ∘ Fin.rev = id := by funext i; simp
  have hI : finFunctionFinEquiv (α ∘ Fin.rev) = I := by
    rw [hα, Function.comp_assoc, hrev]; simp
  have hJ : finFunctionFinEquiv (β ∘ Fin.rev) = J := by
    rw [hβ, Function.comp_assoc, hrev]; simp
  rw [← hI, ← hJ]
  -- RHS: the round-major entry formula for `tensorFinProd (a+b) (append f1 f2)`.
  rw [SubDensityOp.tensorFinProd_toOp_entry_prod_rev]
  -- LHS: drop the `castDim`, expose the Kronecker product, split the index.
  rw [SubDensityOp.castDim_toOp_cast]
  change ((SubDensityOp.tensorFinProd a f1).toOp ⊗ (SubDensityOp.tensorFinProd b f2).toOp)
      (Fin.cast h0.symm (finFunctionFinEquiv (α ∘ Fin.rev)))
      (Fin.cast h0.symm (finFunctionFinEquiv (β ∘ Fin.rev))) = _
  rw [finProdFinEquiv_cast_ffe_rev_split α h0, finProdFinEquiv_cast_ffe_rev_split β h0,
      Quantum.TensorProducts.Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply]
  rw [SubDensityOp.tensorFinProd_toOp_entry_prod_rev,
      SubDensityOp.tensorFinProd_toOp_entry_prod_rev, Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.append_left]; rfl
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.append_right]; rfl

/-- **Count split of `SubDensityOp.tensorFinProd`.**  A finite tensor product over
`nK + nP` factors splits — up to the register reassociation `d^nK · d^nP = d^(nK+nP)`
— into the product over the first `nK` factors and the product over the last `nP`
factors.  This is `tensorFinProd_append` read on the canonical `castAdd`/`natAdd`
restriction of the family. -/
theorem SubDensityOp.tensorFinProd_split {d nK nP : ℕ} [NeZero d]
    (h : Fin (nK + nP) → SubDensityOp d) :
    SubDensityOp.tensorFinProd (nK + nP) h =
      SubDensityOp.castDim (pow_add d nK nP).symm
        ((SubDensityOp.tensorFinProd nK (h ∘ Fin.castAdd nP)).tensor
          (SubDensityOp.tensorFinProd nP (h ∘ Fin.natAdd nK))) := by
  have hh : Fin.append (h ∘ Fin.castAdd nP) (h ∘ Fin.natAdd nK) = h := by
    funext k; refine Fin.addCases ?_ ?_ k <;> intro i <;> simp
  rw [SubDensityOp.tensorFinProd_append, hh]

/-- **Count cast of `SubDensityOp.tensorFinProd`.**  Re-indexing the factor count
along a numeric equality `m = n` of the index range is the register dimension
cast. -/
theorem SubDensityOp.tensorFinProd_castIndex {d m n : ℕ} [NeZero d]
    (hmn : m = n) (f : Fin n → SubDensityOp d) :
    SubDensityOp.tensorFinProd m (f ∘ Fin.cast hmn) =
      SubDensityOp.castDim (by rw [hmn]) (SubDensityOp.tensorFinProd n f) := by
  subst hmn; rfl

/-- **Sorted block split of `SubDensityOp.tensorFinProd`.**  Permuting the register of a
finite tensor product by `registerPerm d n σ.symm` reorders its factors by `σ`, and the
reordered product splits at `nK` (with `nK + nP = n`) into the product over the first `nK`
permuted factors and the product over the last `nP`.  Composes
`tensorFinProd_reindex_perm` (register permutation ↔ factor permutation),
`tensorFinProd_split`, and the factor-count cast.  This is the operator backbone for gathering
a non-contiguous round subset (selected by a permutation `σ`, e.g. `bb84PeSelSort peSel`) into a
contiguous leading block. -/
theorem SubDensityOp.tensorFinProd_sortSplit {d n : ℕ} [NeZero d]
    (g : Fin n → SubDensityOp d) (σ : Equiv.Perm (Fin n)) (nK nP : ℕ) (hn : nK + nP = n) :
    SubDensityOp.reindex (registerPerm d n σ.symm) (SubDensityOp.tensorFinProd n g) =
      SubDensityOp.castDim (by rw [← pow_add, hn])
        ((SubDensityOp.tensorFinProd nK (fun i => g (σ (Fin.cast hn (Fin.castAdd nP i))))).tensor
          (SubDensityOp.tensorFinProd nP (fun j => g (σ (Fin.cast hn (Fin.natAdd nK j)))))) := by
  subst hn
  rw [SubDensityOp.tensorFinProd_reindex_perm]
  simp only [Equiv.symm_symm]
  rw [SubDensityOp.tensorFinProd_split]
  rfl

/-- The inverse of a `registerPerm` is the `registerPerm` of the inverse permutation, so the two
reindexes cancel. -/
lemma subDensityOp_reindex_registerPerm_cancel {d n : ℕ} (σ : Equiv.Perm (Fin n))
    (ρ : SubDensityOp (d ^ n)) :
    SubDensityOp.reindex (registerPerm d n σ)
        (SubDensityOp.reindex (registerPerm d n σ.symm) ρ) = ρ := by
  have hcomp : ∀ K : Fin (d ^ n),
      (registerPerm d n σ.symm).symm ((registerPerm d n σ).symm K) = K := by
    intro K
    rw [registerPerm_symm_apply, registerPerm_symm_apply, Equiv.symm_apply_apply,
      show ((finFunctionFinEquiv.symm K ∘ revConj σ) ∘ revConj σ.symm) =
          finFunctionFinEquiv.symm K from by
        funext k
        simp only [Function.comp_apply, revConj_apply, Fin.rev_rev, Equiv.apply_symm_apply],
      Equiv.apply_symm_apply]
  apply SubDensityOp.ext
  ext I J
  change (SubDensityOp.reindex (registerPerm d n σ.symm) ρ).toOp
      ((registerPerm d n σ).symm I) ((registerPerm d n σ).symm J) = ρ.toOp I J
  change ρ.toOp ((registerPerm d n σ.symm).symm ((registerPerm d n σ).symm I))
      ((registerPerm d n σ.symm).symm ((registerPerm d n σ).symm J)) = ρ.toOp I J
  rw [hcomp, hcomp]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
