import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Metrics.KitaevWatrousContraction
import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# SWAP Bridge: Connecting mapTensorId and mapIdTensor

This file provides SWAP operator infrastructure to bridge between `mapTensorId` (Φ⊗id)
and `mapIdTensor` (id⊗Φ) for the Kitaev-Watrous theorem.

## Motivation

The cross-side factorization in `WatrousFactorization.lean`
(`watrous_A_side_douglas_factorization`, `watrous_B_side_douglas_factorization`)
produces `Op.tensor A₀ 1 = A₀⊗I`, but
`mapTensorId Φ = Φ⊗id` does NOT commute with `A₀⊗I`. We need to bridge to
`mapIdTensor Φ = id⊗Φ`, which DOES commute with `A₀⊗I`.

The SWAP operator implements this bridge: it exchanges the two tensor factors,
allowing us to convert between the two orderings while preserving trace norm.

## Main results

- `swapEquiv`, `swapOp`: SWAP operator on Op(n*n)
- `swapOp_mul_self`, `swapOp_isUnitary`: SWAP is self-inverse and unitary
- `swapOp_tensor`: SWAP * (A⊗B) * SWAP = B⊗A
- `swapOp_traceNorm`: trace norm is SWAP-invariant
- `traceNorm_mapTensorId_eq_mapIdTensor`: bridge between mapTensorId and mapIdTensor
- `mapIdTensor_left_tensor_mul`, `mapIdTensor_right_tensor_mul`: (A⊗I) commutes with id⊗Φ
- `contraction_absorption_calc_idTensor`: Hölder chain for (A₀⊗I) * (id⊗Φ)(σ) * (B₀⊗I)

## References

- Watrous (2018) "Theory of Quantum Information", Section 3.3
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Quantum.Metrics.TraceNormHoelder
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Quantum.Metrics.SwapBridge

-- ============================================================================
-- Section 1: SWAP Equivalence
-- ============================================================================

/-- The equivalence that swaps two tensor factors: (i,j) ↦ (j,i). -/
def swapEquiv (n : ℕ) : Fin (n * n) ≃ Fin (n * n) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

-- ============================================================================
-- Section 2: SWAP Operator
-- ============================================================================

/-- The SWAP operator on Op(n*n) that exchanges the two tensor factors.
    SWAP|i,j⟩ = |j,i⟩. This is a permutation matrix, hence unitary and self-inverse. -/
def swapOp (n : ℕ) : Op (n * n) :=
  Matrix.of fun p q => if swapEquiv n p = q then (1 : ℂ) else 0

-- ============================================================================
-- Section 3: Basic SWAP properties
-- ============================================================================

/-- SWAP is self-inverse: SWAP * SWAP = I. -/
lemma swapOp_mul_self (n : ℕ) [NeZero n] : swapOp n * swapOp n = 1 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.one_apply, swapOp, Matrix.of_apply]
  simp only [ite_mul, one_mul, zero_mul]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hinv : swapEquiv n (swapEquiv n p) = p := by
    have : (swapEquiv n).symm = swapEquiv n := by
      ext x
      simp [swapEquiv, Equiv.trans_apply, Equiv.prodComm_apply]
    rw [← this]
    exact (swapEquiv n).symm_apply_apply p
  rw [hinv]

/-- SWAP is self-adjoint: SWAPᴴ = SWAP. -/
lemma swapOp_conjTranspose (n : ℕ) : (swapOp n)ᴴ = swapOp n := by
  ext p q
  simp only [conjTranspose_apply, swapOp, Matrix.of_apply]
  have hsymm : (swapEquiv n).symm = swapEquiv n := by
    ext x
    simp [swapEquiv, Equiv.trans_apply, Equiv.prodComm_apply]
  split_ifs with h1 h2 h2
  · simp
  · exfalso; apply h2; rw [← hsymm, ← h1]
    exact (swapEquiv n).symm_apply_apply q
  · exfalso; apply h1; rw [← hsymm, ← h2]
    exact (swapEquiv n).symm_apply_apply p
  · simp

/-- SWAP is unitary: SWAPᴴ * SWAP = I. -/
lemma swapOp_isUnitary (n : ℕ) [NeZero n] : (swapOp n)ᴴ * swapOp n = 1 := by
  rw [swapOp_conjTranspose, swapOp_mul_self]

-- ============================================================================
-- Section 4: SWAP and tensor product
-- ============================================================================

/-- SWAP conjugation exchanges tensor factors: SWAP * (A⊗B) * SWAP = B⊗A. -/
lemma swapOp_tensor {n : ℕ} [NeZero n] (A : Op n) (B : Op n) :
    swapOp n * Op.tensor A B * swapOp n = Op.tensor B A := by
  ext p q
  simp only [Matrix.mul_apply, swapOp, Matrix.of_apply, Op.tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [show ∀ x : Fin (n * n),
    ((swapEquiv n) x = q) = (x = (swapEquiv n).symm q) from
    fun x => propext (Equiv.apply_eq_iff_eq_symm_apply (swapEquiv n))]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsymm : (swapEquiv n).symm = swapEquiv n := by
    ext x
    simp [swapEquiv, Equiv.trans_apply, Equiv.prodComm_apply]
  rw [hsymm]
  have key : ∀ (x : Fin (n * n)),
      (finProdFinEquiv.symm (swapEquiv n x)).1 = (finProdFinEquiv.symm x).2 ∧
      (finProdFinEquiv.symm (swapEquiv n x)).2 =
        (finProdFinEquiv.symm x).1 := by
    intro x
    simp [swapEquiv, Equiv.trans_apply, Equiv.prodComm_apply]
  obtain ⟨h1p, h2p⟩ := key p
  obtain ⟨h1q, h2q⟩ := key q
  rw [h1p, h2p, h1q, h2q]
  ring

/-- SWAP conjugation permutes entries: (SWAP*X*SWAP)(p,q) = X(swap p, swap q). -/
lemma swapOp_conj_entry (n : ℕ) [NeZero n] (X : Op (n * n)) (p q : Fin (n * n)) :
    (swapOp n * X * swapOp n) p q = X (swapEquiv n p) (swapEquiv n q) := by
  simp only [Matrix.mul_apply, swapOp, Matrix.of_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [show ∀ x : Fin (n * n),
    ((swapEquiv n) x = q) = (x = (swapEquiv n).symm q) from
    fun x => propext (Equiv.apply_eq_iff_eq_symm_apply (swapEquiv n))]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsymm : (swapEquiv n).symm = swapEquiv n := by
    ext x
    simp [swapEquiv, Equiv.trans_apply, Equiv.prodComm_apply]
  rw [hsymm]

-- ============================================================================
-- Section 5: SWAP preserves PSD, trace, trace norm
-- ============================================================================

/-- SWAP conjugation preserves positive semidefiniteness. -/
lemma swapOp_posSemidef {n : ℕ} [NeZero n] (σ : Op (n * n)) (hσ : σ.PosSemidef) :
    (swapOp n * σ * swapOp n).PosSemidef := by
  rw [show swapOp n * σ * swapOp n = (swapOp n)ᴴ * σ * swapOp n from by
    rw [swapOp_conjTranspose]]
  exact hσ.conjTranspose_mul_mul_same (swapOp n)

/-- SWAP conjugation preserves trace. -/
lemma swapOp_trace {n : ℕ} [NeZero n] (σ : Op (n * n)) :
    (swapOp n * σ * swapOp n).trace = σ.trace := by
  rw [Matrix.trace_mul_cycle, swapOp_mul_self, Matrix.one_mul]

/-- SWAP conjugation preserves trace norm. -/
lemma swapOp_traceNorm {n : ℕ} [NeZero n] (X : Op (n * n)) :
    traceNorm (swapOp n * X * swapOp n) = traceNorm X := by
  haveI : NeZero (n * n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  calc traceNorm (swapOp n * X * swapOp n)
      = traceNorm (X * swapOp n) := by
        rw [Matrix.mul_assoc]
        exact traceNorm_unitary_mul_left _ _ (swapOp_isUnitary n)
    _ = traceNorm X :=
        traceNorm_mul_unitary_right _ _ (swapOp_isUnitary n)
          (by rw [swapOp_conjTranspose, swapOp_mul_self])

-- ============================================================================
-- Section 6: Bridge between mapTensorId and mapIdTensor
-- ============================================================================

/-- Bridge: mapTensorId Φ X can be computed via mapIdTensor with swapped
    inputs/outputs. Since swap_{m,n} would need a non-square swap, we state
    the trace-norm equality which is what we actually need. -/
lemma traceNorm_mapTensorId_eq_mapIdTensor {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * n)) :
    traceNorm (mapTensorId Φ X) =
      traceNorm (mapIdTensor Φ (swapOp n * X * swapOp n)) := by
  haveI : NeZero (n * n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  haveI : NeZero (n * m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  -- The reindexing equivalence swapping (a,s) ↔ (s,a) between Fin(m*n) and Fin(n*m)
  let e : Fin (m * n) ≃ Fin (n * m) :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin m) (Fin n)).trans finProdFinEquiv)
  -- Step 1: entry-level equality — mapTensorId is a reindexing of mapIdTensor
  have h_sub : mapTensorId Φ X =
      (mapIdTensor Φ (swapOp n * X * swapOp n)).submatrix e e := by
    ext p q
    simp only [mapTensorId, mapIdTensor, Matrix.of_apply, Matrix.submatrix_apply]
    -- Both sides are ∑ i j, Φ(E_ij) a b * (matrix entry)
    -- Use congr to split the product, then close each part by simp
    congr 1; ext i; congr 1; ext j
    simp only [swapOp_conj_entry, swapEquiv, e,
      Equiv.trans_apply, Equiv.prodComm_apply,
      finProdFinEquiv_symm_apply, Prod.swap_prod_mk,
      Equiv.symm_apply_apply]
  -- Step 2: traceNorm is invariant under reindexing by an equivalence
  rw [h_sub]
  exact traceNorm_submatrix_equiv _ e

-- ============================================================================
-- Section 7: PSD bridge
-- ============================================================================

/-- If mapTensorId Φ is bounded on PSD inputs, then mapIdTensor Φ is too. -/
lemma mapIdTensor_psd_bound_of_mapTensorId {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (σ : Op (n * n)) (hσ : σ.PosSemidef) (hσ_tr : σ.trace.re ≤ 1) :
    traceNorm (mapIdTensor Φ σ) ≤ B := by
  haveI : NeZero (n * n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  -- Set ρ := SWAP * σ * SWAP, which is PSD with same trace
  set ρ := swapOp n * σ * swapOp n with hρ_def
  -- ρ is PSD
  have hρ_psd : ρ.PosSemidef := swapOp_posSemidef σ hσ
  -- Tr(ρ) = Tr(σ), so Tr(ρ).re ≤ 1
  have hρ_tr : ρ.trace.re ≤ 1 := by
    rw [swapOp_trace σ]; exact hσ_tr
  -- By hypothesis: traceNorm(mapTensorId Φ ρ) ≤ B
  have h1 := hPSD ρ hρ_psd hρ_tr
  -- By Lemma 1: traceNorm(mapTensorId Φ ρ) = traceNorm(mapIdTensor Φ (SWAP*ρ*SWAP))
  rw [traceNorm_mapTensorId_eq_mapIdTensor] at h1
  -- SWAP*(SWAP*σ*SWAP)*SWAP = σ (by self-inverse)
  have h_cancel : swapOp n * ρ * swapOp n = σ := by
    rw [hρ_def]
    have h_assoc : swapOp n * (swapOp n * σ * swapOp n) * swapOp n =
        swapOp n * swapOp n * σ * (swapOp n * swapOp n) := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, swapOp_mul_self, one_mul, mul_one]
  rw [h_cancel] at h1
  exact h1

-- ============================================================================
-- Section 8: mapIdTensor commutation with Op.tensor A₀ 1
-- ============================================================================

/-- mapIdTensor on a tensor product: (id⊗Φ)(C ⊗ D) = C ⊗ Φ(D).
    Analogue of `mapTensorId_tensor` for the right-factor map. -/
private lemma mapIdTensor_tensor {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (C : Op n) (D : Op n) :
    mapIdTensor Φ (Op.tensor C D) = Op.tensor C (Φ D) := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, kroneckerMap_apply]
  simp only [Equiv.symm_apply_apply]
  -- LHS: ∑ i j, Φ(E_{ij}) a b * (C(s,t) * D(i,j)) = C(s,t) * Φ(D) a b
  -- Use linearity of Φ to rewrite the RHS
  have hD_decomp : D = ∑ i, ∑ j, D i j • single i j 1 := by
    ext r c; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact if_neg (fun ⟨h1, _⟩ => hi h1)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  -- Rewrite RHS using linearity
  conv_rhs =>
    rw [hD_decomp, map_sum]
    simp only [map_sum, LinearMap.map_smul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  -- Both sides are now double sums; show summands agree
  congr 1; ext i; congr 1; ext j; simp; ring

/-- single basis matrix as pure tensor (for mapIdTensor proofs):
    `single (e(i,s)) (e(j,t)) 1 = (single i j 1) ⊗ (single s t 1)` -/
private lemma single_eq_tensor' {n : ℕ}
    (i j s t : Fin n) :
    single (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))
      (1 : ℂ) =
      Op.tensor (single i j 1) (single s t 1) := by
  ext r c
  simp only [single_apply, Op.tensor, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have heq_r : finProdFinEquiv (i, s) = r ↔
      (finProdFinEquiv.symm r).1 = i ∧
      (finProdFinEquiv.symm r).2 = s := by
    constructor
    · intro h; subst h; simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm r = (i, s) :=
        Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv r, this]
  have heq_c : finProdFinEquiv (j, t) = c ↔
      (finProdFinEquiv.symm c).1 = j ∧
      (finProdFinEquiv.symm c).2 = t := by
    constructor
    · intro h; subst h; simp [Equiv.symm_apply_apply]
    · intro ⟨h1, h2⟩
      have : finProdFinEquiv.symm c = (j, t) :=
        Prod.ext h1 h2
      rw [← Equiv.apply_symm_apply finProdFinEquiv c, this]
  simp only [heq_r, heq_c, and_assoc]
  split_ifs <;> simp_all

/-- mapIdTensor commutation: (A⊗I) on the left commutes with (id⊗Φ). -/
lemma mapIdTensor_left_tensor_mul {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (A : Op n) (Y : Op (n * n)) :
    mapIdTensor Φ (Op.tensor A (1 : Op n) * Y) =
      Op.tensor A (1 : Op m) * mapIdTensor Φ Y := by
  -- Package both sides as ℂ-linear maps
  let FL : Op (n * n) →ₗ[ℂ] Op (n * m) :=
    { toFun := fun Z => mapIdTensor Φ (Op.tensor A (1 : Op n) * Z)
      map_add' := fun x y => by
        rw [mul_add, mapIdTensor_add_basic]
      map_smul' := fun c x => by
        rw [mul_smul_comm, mapIdTensor_smul_basic, RingHom.id_apply] }
  let FR : Op (n * n) →ₗ[ℂ] Op (n * m) :=
    { toFun := fun Z => Op.tensor A (1 : Op m) * mapIdTensor Φ Z
      map_add' := fun x y => by
        rw [mapIdTensor_add_basic, mul_add]
      map_smul' := fun c x => by
        rw [mapIdTensor_smul_basic, mul_smul_comm, RingHom.id_apply] }
  -- Reduce to showing FL = FR on basis elements
  change FL Y = FR Y
  have h_eq : FL = FR := by
    apply (Matrix.stdBasis ℂ (Fin (n * n)) (Fin (n * n))).ext
    intro ⟨r, c⟩
    simp only [Matrix.stdBasis_eq_single, FL, FR,
      LinearMap.coe_mk, AddHom.coe_mk]
    -- Decompose basis element as pure tensor
    rw [show r = finProdFinEquiv
          ((finProdFinEquiv.symm r).1,
           (finProdFinEquiv.symm r).2) from
          (finProdFinEquiv.apply_symm_apply r).symm,
        show c = finProdFinEquiv
          ((finProdFinEquiv.symm c).1,
           (finProdFinEquiv.symm c).2) from
          (finProdFinEquiv.apply_symm_apply c).symm,
        single_eq_tensor']
    rw [Op.tensor_mul, one_mul, mapIdTensor_tensor,
        mapIdTensor_tensor, Op.tensor_mul, one_mul]
  exact DFunLike.congr_fun h_eq Y

/-- mapIdTensor commutation: (A⊗I) on the right commutes with (id⊗Φ). -/
lemma mapIdTensor_right_tensor_mul {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (A : Op n) (Y : Op (n * n)) :
    mapIdTensor Φ (Y * Op.tensor A (1 : Op n)) =
      mapIdTensor Φ Y * Op.tensor A (1 : Op m) := by
  let FL : Op (n * n) →ₗ[ℂ] Op (n * m) :=
    { toFun := fun Z => mapIdTensor Φ (Z * Op.tensor A (1 : Op n))
      map_add' := fun x y => by
        rw [add_mul, mapIdTensor_add_basic]
      map_smul' := fun c x => by
        rw [smul_mul_assoc, mapIdTensor_smul_basic, RingHom.id_apply] }
  let FR : Op (n * n) →ₗ[ℂ] Op (n * m) :=
    { toFun := fun Z => mapIdTensor Φ Z * Op.tensor A (1 : Op m)
      map_add' := fun x y => by
        rw [mapIdTensor_add_basic, add_mul]
      map_smul' := fun c x => by
        rw [mapIdTensor_smul_basic, smul_mul_assoc, RingHom.id_apply] }
  change FL Y = FR Y
  have h_eq : FL = FR := by
    apply (Matrix.stdBasis ℂ (Fin (n * n)) (Fin (n * n))).ext
    intro ⟨r, c⟩
    simp only [Matrix.stdBasis_eq_single, FL, FR,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [show r = finProdFinEquiv
          ((finProdFinEquiv.symm r).1,
           (finProdFinEquiv.symm r).2) from
          (finProdFinEquiv.apply_symm_apply r).symm,
        show c = finProdFinEquiv
          ((finProdFinEquiv.symm c).1,
           (finProdFinEquiv.symm c).2) from
          (finProdFinEquiv.apply_symm_apply c).symm,
        single_eq_tensor']
    rw [Op.tensor_mul, mul_one, mapIdTensor_tensor,
        mapIdTensor_tensor, Op.tensor_mul, mul_one]
  exact DFunLike.congr_fun h_eq Y

-- ============================================================================
-- Section 9: Operator norm for A⊗I
-- ============================================================================

private lemma opNorm_conj_linearIsometryEquiv_eq
    {m n : Type} [Fintype m] [Fintype n]
    (U : EuclideanSpace ℂ m ≃ₗᵢ[ℂ] EuclideanSpace ℂ n)
    (T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ‖(U.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (T.comp U.toContinuousLinearMap)‖ = ‖T‖ := by
  -- Post-composing with the isometry `U.symm` and pre-composing with the isometric
  -- equivalence `U` both preserve the operator norm.
  exact (LinearIsometry.norm_toContinuousLinearMap_comp U.symm.toLinearIsometry).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv T U)

private lemma opNorm_reindex_eq {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : n ≃ m) (M : Matrix n n ℂ) :
    ‖Matrix.reindex e e M‖ = ‖M‖ := by
  -- Relabelling coordinates along `e` is an isometry of Euclidean spaces.
  let U : EuclideanSpace ℂ m ≃ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
  -- Pass to Euclidean operators and conjugate the operator of `M` by `U` on the right-hand side.
  rw [cstar_norm_def, cstar_norm_def,
    ← opNorm_conj_linearIsometryEquiv_eq U (toEuclideanCLM (n := n) (𝕜 := ℂ) M)]
  -- As an operator, the reindexed matrix is `M` conjugated by `U`.
  refine congrArg (‖·‖) ?_
  ext x i
  -- Reading off `U.symm` leaves `(reindex e e M *ᵥ x) i = (M *ᵥ U x) (e.symm i)`, which is
  -- `submatrix_mulVec_equiv` because `U x = x ∘ e` by definition.
  simp only [ContinuousLinearMap.comp_apply, ofLp_toEuclideanCLM, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, U, LinearIsometryEquiv.piLpCongrLeft_symm,
    Equiv.symm_symm, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  exact congrFun (Matrix.submatrix_mulVec_equiv M x.ofLp e.symm e.symm) i

/-- Tensoring an operator on the right with the identity does not increase its L2 operator norm. -/
lemma opNorm_tensor_one_right_le {n k : ℕ} [NeZero n] [NeZero k] (A : Op n) :
    ‖Op.tensor A (1 : Op k)‖ ≤ ‖A‖ := by
  let e : Fin (k * n) ≃ Fin (n * k) :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin k) (Fin n)).trans finProdFinEquiv)
  have h_tensor : Op.tensor A (1 : Op k) =
      Matrix.reindex e e (Op.tensor (1 : Op k) A) := by
    ext p q
    simp [e, Op.tensor, finProdFinEquiv_symm_apply]
    ring
  rw [h_tensor, opNorm_reindex_eq]
  exact Quantum.Metrics.KitaevWatrousContraction.opNorm_tensor_one_le (d := k) A

-- ============================================================================
-- Section 10: Holder chain for the mapIdTensor version
-- ============================================================================

/-- Holder chain for (A₀⊗I) * mapIdTensor Φ σ * (B₀⊗I), bounded by B. -/
lemma contraction_absorption_calc_idTensor {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hPSD : ∀ (σ : Op (n * n)), σ.PosSemidef → σ.trace.re ≤ 1 →
      traceNorm (mapIdTensor Φ σ) ≤ B)
    (A₀ B₀ : Op n) (σ : Op (n * n))
    (hσ_psd : σ.PosSemidef) (hσ_tr : σ.trace.re ≤ 1)
    (hA₀ : ‖A₀‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1) :
    traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ * Op.tensor B₀ (1 : Op m)) ≤ B := by
  haveI : NeZero (n * n) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n)⟩
  haveI : NeZero (n * m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  -- Right Holder: traceNorm(M * (B₀⊗I)) ≤ traceNorm(M) * ‖B₀⊗I‖
  have h_right : traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ *
      Op.tensor B₀ (1 : Op m)) ≤
    traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ) *
      ‖Op.tensor B₀ (1 : Op m)‖ :=
    traceNorm_mul_le_traceNorm_mul_opNorm _ _
  -- Left Holder: traceNorm((A₀⊗I) * M) ≤ ‖A₀⊗I‖ * traceNorm(M)
  have h_left : traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ) ≤
    ‖Op.tensor A₀ (1 : Op m)‖ * traceNorm (mapIdTensor Φ σ) :=
    TraceNormHoelder.traceNorm_mul_le_opNorm_mul_traceNorm _ _
  -- Tensor norm bounds
  have hA₀' : ‖Op.tensor A₀ (1 : Op m)‖ ≤ ‖A₀‖ := opNorm_tensor_one_right_le A₀
  have hB₀' : ‖Op.tensor B₀ (1 : Op m)‖ ≤ ‖B₀‖ := opNorm_tensor_one_right_le B₀
  -- PSD bound
  have hσ_bound : traceNorm (mapIdTensor Φ σ) ≤ B := hPSD σ hσ_psd hσ_tr
  -- Combine
  have htn_nn : 0 ≤ traceNorm (mapIdTensor Φ σ) := by
    unfold traceNorm; exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  calc traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ * Op.tensor B₀ (1 : Op m))
      ≤ traceNorm (Op.tensor A₀ (1 : Op m) * mapIdTensor Φ σ) *
          ‖Op.tensor B₀ (1 : Op m)‖ := h_right
    _ ≤ (‖Op.tensor A₀ (1 : Op m)‖ * traceNorm (mapIdTensor Φ σ)) *
          ‖Op.tensor B₀ (1 : Op m)‖ := by
        apply mul_le_mul_of_nonneg_right h_left (norm_nonneg _)
    _ ≤ (‖A₀‖ * traceNorm (mapIdTensor Φ σ)) * ‖B₀‖ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hA₀' htn_nn) hB₀'
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) htn_nn)
    _ ≤ (1 * B) * 1 := by
        apply mul_le_mul (mul_le_mul hA₀ hσ_bound htn_nn (by linarith))
          hB₀ (norm_nonneg _) (mul_nonneg (by linarith) hB)
    _ = B := by ring

end Quantum.Metrics.SwapBridge
