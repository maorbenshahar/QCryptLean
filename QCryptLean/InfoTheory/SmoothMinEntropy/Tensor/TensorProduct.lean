import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalizedCastDim
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.TensorFamily

/-!
# Sub-Normalized Tensor Products — binary and finite products of sub-density operators and CQ states

Tensor-product operations for `SubDensityOp` and `CQState`, including binary
products, the one-dimensional trivial state, and finite tensor products. Dimension
casts, which the finite product uses to regroup registers, are in
`SubNormalizedCastDim.lean`.

## Main definitions
- `SubDensityOp.tensor`: tensor product of two sub-density operators.
- `SubDensityOp.trivialOne`: the unique one-dimensional sub-density operator of trace one.
- `SubDensityOp.tensorFinProd`: finite tensor product of a family of sub-density operators.
- `CQState.tensor`: binary tensor product of two CQ states with classical
  register the Cartesian product `X × X'`.

## Main statements
- `SubDensityOp.tensor_trace`: trace of a binary tensor product.
- `SubDensityOp.tensorFinProd_trace`: trace of a finite tensor product.
- `SubDensityOp.tensorFinProd_toOp`: the underlying operator of a finite tensor product is the
  tensor family `Quantum.TensorProducts.tensorFamily` of the reversed family; the recursion puts
  `f 0` on the high digit.
- `SubDensityOp.tensorFinProd_const_toOp`: a constant family's finite tensor product is the
  operator tensor power `Quantum.TensorProducts.Op.tensorPow`.
- `SubDensityOp.tensorFinProd_toOp_entry_prod_rev`: entrywise product formula for
  finite tensor products.
- `SubDensityOp.tensorFinProd_posDef`: positive-definite factors have a positive-definite finite
  tensor product.
- `sum_tensor_stateMap_trace_eq_mul`: block-trace sum factorizes over a CQ
  tensor product.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The trace of a sub-density operator has zero imaginary part. -/
lemma SubDensityOp.trace_im_eq_zero {n : ℕ} (ρ : SubDensityOp n) :
    ρ.toOp.trace.im = 0 :=
  (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).trace_nonneg.2.symm

/-- Tensor product of two sub-density operators.

    If `ρ : SubDensityOp n` and `σ : SubDensityOp m`, then `ρ.toOp ⊗ σ.toOp` is PSD,
    Hermitian, and has trace `Tr(ρ) · Tr(σ) ≤ 1`. -/
noncomputable def SubDensityOp.tensor {n m : ℕ} (ρ : SubDensityOp n) (σ : SubDensityOp m) :
    SubDensityOp (n * m) where
  toOp := ρ.toOp ⊗ σ.toOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Op.tensor_conjTranspose, ρ.isHermitian, σ.isHermitian]
  pos_semidef := Op.tensor_posSemidef ρ.toOp σ.toOp ρ.isHermitian σ.isHermitian
    ρ.pos_semidef σ.pos_semidef
  trace_le_one := by
    rw [Op.trace_tensor, Complex.mul_re, ρ.trace_im_eq_zero, σ.trace_im_eq_zero,
        mul_zero, sub_zero]
    exact mul_le_one₀ ρ.trace_le_one σ.trace_nonneg σ.trace_le_one

/-- Trace of a sub-density tensor product equals the product of traces. -/
lemma SubDensityOp.tensor_trace {n m : ℕ} (ρ : SubDensityOp n) (σ : SubDensityOp m) :
    (ρ.tensor σ).trace = ρ.trace * σ.trace := by
  unfold SubDensityOp.tensor SubDensityOp.trace
  simp only
  rw [Op.trace_tensor]
  simp [Complex.mul_re, ρ.trace_im_eq_zero, σ.trace_im_eq_zero]

/-- The tensor product of two positive-definite sub-density operators is
positive-definite. Bridges `Matrix.PosDef.kronecker` (Mathlib) to the
project-internal `Op.tensor`/`SubDensityOp.tensor` definition. -/
lemma SubDensityOp.tensor_posDef {n m : ℕ}
    (ρ : SubDensityOp n) (σ : SubDensityOp m)
    (hρ : ρ.toOp.PosDef) (hσ : σ.toOp.PosDef) :
    (SubDensityOp.tensor ρ σ).toOp.PosDef := by
  change (ρ.toOp ⊗ σ.toOp).PosDef
  unfold Quantum.TensorProducts.Op.tensor
  rw [Matrix.reindex_apply]
  exact (Matrix.PosDef.kronecker hρ hσ).submatrix finProdFinEquiv.symm.injective

/-- The sub-density operator on `ℂ^1` induced by `DensityOp.trivial`. -/
noncomputable def SubDensityOp.trivialOne : SubDensityOp 1 :=
  DensityOp.toSubDensityOp DensityOp.trivial

/-- The trace of `SubDensityOp.trivialOne` is 1. -/
lemma SubDensityOp.trivialOne_trace : SubDensityOp.trivialOne.trace = 1 := by
  simp [SubDensityOp.trivialOne, SubDensityOp.trace, DensityOp.toSubDensityOp,
        DensityOp.trivial, Matrix.trace, Finset.univ_unique, Fin.default_eq_zero]

/-- N-fold tensor product of a family of sub-density operators.

    For `f : Fin n → SubDensityOp d`, produces a `SubDensityOp (d ^ n)` by induction:
    - n = 0: `SubDensityOp.trivialOne` on `ℂ^1 = ℂ^(d^0)`.
    - n = k+1: `(f 0).tensor (tensorFinProd k (f ∘ Fin.succ))`, cast from `d * d^k`
      to `d^(k+1)`. -/
noncomputable def SubDensityOp.tensorFinProd {d : ℕ} [NeZero d]
    (n : ℕ) (f : Fin n → SubDensityOp d) : SubDensityOp (d ^ n) :=
  match n with
  | 0 => SubDensityOp.castDim (by simp) SubDensityOp.trivialOne
  | k + 1 =>
      SubDensityOp.castDim (by ring)
        ((f 0).tensor (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)))

/-- Trace of the empty tensor product is 1. -/
lemma SubDensityOp.tensorFinProd_zero_trace {d : ℕ} [NeZero d]
    (f : Fin 0 → SubDensityOp d) :
    (SubDensityOp.tensorFinProd 0 f).trace = 1 := by
  simp [SubDensityOp.tensorFinProd, SubDensityOp.castDim_trace, SubDensityOp.trivialOne_trace]

/-- Trace of the n-fold tensor product is the product of individual traces. -/
lemma SubDensityOp.tensorFinProd_trace {d : ℕ} [NeZero d]
    (n : ℕ) (f : Fin n → SubDensityOp d) :
    (SubDensityOp.tensorFinProd n f).trace = ∏ i : Fin n, (f i).trace := by
  induction n with
  | zero => simp [SubDensityOp.tensorFinProd, SubDensityOp.castDim_trace,
                  SubDensityOp.trivialOne_trace]
  | succ k ih =>
      simp only [SubDensityOp.tensorFinProd, SubDensityOp.castDim_trace,
                 SubDensityOp.tensor_trace, ih (f ∘ Fin.succ), Function.comp]
      rw [Fin.prod_univ_succ]

/-- **The finite tensor product is a reversed tensor family.** Its recursion puts `f 0` on the
first (high-digit) tensor factor, while `tensorFamily` puts site `0` on the low digit, so the
underlying operator is the tensor family of `fun k => f (Fin.rev k)`. -/
lemma SubDensityOp.tensorFinProd_toOp {d : ℕ} [NeZero d] (n : ℕ) (f : Fin n → SubDensityOp d) :
    (SubDensityOp.tensorFinProd n f).toOp = tensorFamily fun k => (f (Fin.rev k)).toOp := by
  induction n with
  | zero =>
      rw [tensorFamily_zero]
      ext i j
      obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
      simp [SubDensityOp.tensorFinProd, SubDensityOp.castDim_toOp, SubDensityOp.trivialOne,
        DensityOp.toSubDensityOp, DensityOp.trivial, Op.castDim_apply]
  | succ n ih =>
      rw [tensorFamily_comp_rev_castSucc (fun j => (f j).toOp), tensorRect_square,
        ← Op.castDim_eq_reindex_finCongr, ← ih fun j => f j.succ]
      exact SubDensityOp.castDim_toOp _ _

/-- The finite tensor product of a constant family is the operator tensor power:
`(tensorFinProd n (fun _ => σ)).toOp = σ.toOp^{⊗n}`. -/
lemma SubDensityOp.tensorFinProd_const_toOp {d : ℕ} [NeZero d] (σ : SubDensityOp d) (n : ℕ) :
    (SubDensityOp.tensorFinProd n (fun _ => σ)).toOp = Op.tensorPow σ.toOp n := by
  rw [SubDensityOp.tensorFinProd_toOp, Op.tensorPow_eq_tensorFamily]

/-- Entry formula for the finite tensor product of a family of sub-density operators.

The recursive definition of `tensorFinProd` places `f 0` in the leading tensor
factor, while `finFunctionFinEquiv` stores that leading factor in the last
coordinate.  Consequently the canonical entry formula uses `Fin.rev` on the
flat tensor index. -/
lemma SubDensityOp.tensorFinProd_toOp_entry_prod_rev {d n : ℕ}
    [NeZero d] [NeZero (d ^ n)]
    (f : Fin n → SubDensityOp d) (a b : Fin n → Fin d) :
    (SubDensityOp.tensorFinProd n f).toOp
        (finFunctionFinEquiv (a ∘ Fin.rev))
        (finFunctionFinEquiv (b ∘ Fin.rev)) =
      ∏ k : Fin n, (f k).toOp (a k) (b k) := by
  rw [SubDensityOp.tensorFinProd_toOp, tensorFamily_apply_finFunctionFinEquiv]
  exact Fintype.prod_equiv Fin.revPerm _ _ fun k => rfl

/-- A finite tensor product of positive-definite sub-density operators is positive definite. -/
lemma SubDensityOp.tensorFinProd_posDef {d : ℕ} [NeZero d] (m : ℕ) (f : Fin m → SubDensityOp d)
    (hf : ∀ i, (f i).toOp.PosDef) : (SubDensityOp.tensorFinProd m f).toOp.PosDef := by
  rw [SubDensityOp.tensorFinProd_toOp]
  exact Matrix.PosDef.tensorFamily fun k => hf (Fin.rev k)

/-- **Constant-reference tensorization of the operator order.**

If each factor `f j` is dominated, in the PSD operator order, by the common
scalar `c` times a fixed reference `g`, then the finite tensor product
`tensorFinProd n f` is dominated by `c ^ n` times the `n`-fold tensor power of
`g` (which is `tensorFinProd n (fun _ => g)`). This is the constant-reference
analogue of the maximally-mixed product bound used for BB84, and its inductive
step uses only the definitional `succ` recursion of `tensorFinProd`. -/
lemma SubDensityOp.tensorFinProd_opLe_pow_const {d : ℕ} [NeZero d]
    (g : SubDensityOp d) (n : ℕ) (f : Fin n → SubDensityOp d)
    {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, opLe (f j).toOp ((c : ℂ) • g.toOp)) :
    opLe (SubDensityOp.tensorFinProd n f).toOp
      (((c ^ n : ℝ) : ℂ) •
        (SubDensityOp.tensorFinProd n (fun _ => g)).toOp) := by
  induction n with
  | zero =>
      simp only [pow_zero, Complex.ofReal_one, one_smul]
      intro v
      exact le_refl _
  | succ k ih =>
      haveI hk : NeZero (d ^ k) := NeZero.pow
      haveI hkk : NeZero (d * d ^ k) :=
        ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne (d ^ k))⟩
      have ih' := ih (f ∘ Fin.succ) (fun j => hdom j.succ)
      have h0 := hdom 0
      -- PSD facts
      have hf0_psd : (f 0).toOp.PosSemidef :=
        posSemidefOp_implies_mathlib (f 0).toPosSemidefOp
      have hrest_psd :
          (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toOp.PosSemidef :=
        posSemidefOp_implies_mathlib
          (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toPosSemidefOp
      have hg_psd : g.toOp.PosSemidef :=
        posSemidefOp_implies_mathlib g.toPosSemidefOp
      have hgrest_psd :
          (SubDensityOp.tensorFinProd k (fun _ => g)).toOp.PosSemidef :=
        posSemidefOp_implies_mathlib
          (SubDensityOp.tensorFinProd k (fun _ => g)).toPosSemidefOp
      have hcg_psd : (((c : ℂ) • g.toOp)).PosSemidef := by
        simpa using hg_psd.smul (a := (c : ℂ)) (by exact_mod_cast hc)
      have hck_psd :
          ((((c ^ k : ℝ) : ℂ) •
            (SubDensityOp.tensorFinProd k (fun _ => g)).toOp)).PosSemidef := by
        simpa using hgrest_psd.smul (a := ((c ^ k : ℝ) : ℂ))
          (by exact_mod_cast pow_nonneg hc k)
      -- Binary tensor monotonicity.
      have h_tensor :
          opLe ((f 0).toOp ⊗ (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toOp)
            (((c : ℂ) • g.toOp) ⊗
              (((c ^ k : ℝ) : ℂ) •
                (SubDensityOp.tensorFinProd k (fun _ => g)).toOp)) :=
        opLe_tensor_psd hf0_psd.isHermitian hcg_psd hrest_psd
          hck_psd.isHermitian h0 ih'
      -- Simplify the RHS scalar.
      have hpow_cast : ((c ^ (k + 1) : ℝ) : ℂ) = (c : ℂ) * ((c ^ k : ℝ) : ℂ) := by
        push_cast; rw [pow_succ]; ring
      have h_rhs_eq :
          ((c : ℂ) • g.toOp) ⊗
              (((c ^ k : ℝ) : ℂ) •
                (SubDensityOp.tensorFinProd k (fun _ => g)).toOp) =
            ((c ^ (k + 1) : ℝ) : ℂ) •
              ((g.tensor (SubDensityOp.tensorFinProd k (fun _ => g))).toOp) := by
        rw [Op.smul_tensor_smul, hpow_cast]
        rfl
      rw [h_rhs_eq] at h_tensor
      have hLHS_eq :
          (f 0).toOp ⊗ (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toOp =
            ((f 0).tensor (SubDensityOp.tensorFinProd k (f ∘ Fin.succ))).toOp := rfl
      rw [hLHS_eq] at h_tensor
      -- Cast both sides up to dimension `d ^ (k + 1)`.
      have hcast_lhs :
          (SubDensityOp.tensorFinProd (k + 1) f).toOp =
            (SubDensityOp.castDim (by ring : d * d ^ k = d ^ (k + 1))
              ((f 0).tensor
                (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)))).toOp := rfl
      have hcast_rhs :
          (SubDensityOp.tensorFinProd (k + 1) (fun _ => g)).toOp =
            (SubDensityOp.castDim (by ring : d * d ^ k = d ^ (k + 1))
              (g.tensor
                (SubDensityOp.tensorFinProd k (fun _ => g)))).toOp := rfl
      rw [hcast_lhs, hcast_rhs]
      exact SubDensityOp.opLe_castDim_toOp_smul (by ring : d * d ^ k = d ^ (k + 1))
        ((f 0).tensor (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)))
        (((c ^ (k + 1) : ℝ) : ℂ))
        (g.tensor (SubDensityOp.tensorFinProd k (fun _ => g)))
        h_tensor

/-- **Block-trace sum factorizes over a tensor of CQ-state blocks.**
    Trace multiplicativity (`SubDensityOp.tensor_trace`) lifted to a sum over
    the product index `X × X'`: the total trace of the block-wise tensor
    factors as the product of the factor totals. -/
lemma sum_tensor_stateMap_trace_eq_mul
    {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} (ρ : CQState X n) (ρ' : CQState X' n') :
    ∑ p : X × X', ((ρ.stateMap p.1).tensor (ρ'.stateMap p.2)).trace =
      (∑ x : X, (ρ.stateMap x).trace) *
        (∑ x' : X', (ρ'.stateMap x').trace) := by
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

/-- **CQ-state tensor product.**

    For `ρ : CQState X n` and `ρ' : CQState X' n'`, the product
    `ρ.tensor ρ' : CQState (X × X') (n * n')` has block-wise structure
    `(stateMap (x, x')) = (ρ.stateMap x).tensor (ρ'.stateMap x')`.

    This is the CQ analogue of the operator-level `SubDensityOp.tensor`.
    The classical register is the Cartesian product `X × X'`; the
    quantum register has dimension `n * n'`. -/
noncomputable def CQState.tensor {X X' : Type*} [Fintype X] [Fintype X']
    {n n' : ℕ} (ρ : CQState X n) (ρ' : CQState X' n') :
    CQState (X × X') (n * n') where
  stateMap p := (ρ.stateMap p.1).tensor (ρ'.stateMap p.2)
  weight_le_one := by
    calc
      ∑ p : X × X', ((ρ.stateMap p.1).tensor (ρ'.stateMap p.2)).trace
          = (∑ x : X, (ρ.stateMap x).trace) *
              (∑ x' : X', (ρ'.stateMap x').trace) :=
            sum_tensor_stateMap_trace_eq_mul ρ ρ'
      _   ≤ 1 * 1 :=
            mul_le_mul ρ.weight_le_one ρ'.weight_le_one
              (Finset.sum_nonneg (fun x _ => (ρ'.stateMap x).trace_nonneg))
              zero_le_one
      _   = 1 := one_mul 1

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
