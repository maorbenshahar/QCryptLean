import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.Channels.CPTP.SubstateExtraction
import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Quantum Substate Extraction — Kraus maps, CP maps, Alberti-Uhlmann theorem

Infrastructure for the quantum substate extraction theorem (Alberti-Uhlmann 1982):
given PSD domination of partial traces, construct a CP trace-non-increasing map
that converts a purification into the dominated operator. Also defines the
`mapIdTensor` (id ⊗ Φ) construction and Kraus map infrastructure (built on
`Quantum.Channels.krausMapFintype`, `FintypeKraus.lean`).

Trace-norm contractivity and CPTP preservation for tensored maps are in
`Contractivity.lean`.

## Main definitions

- `mapIdTensor`: tensor `id_H ⊗ Φ` acting on `Op (k * n)`

## Main statements

- `substate_map_exists`: Alberti-Uhlmann quantum Radon-Nikodym theorem —
  PSD domination of partial traces yields a CP TNI map
- `krausMapFintype_castOutput`: output-dimension casts commute with `krausMapFintype`
- `krausMapFintype_tni_of_sum_le_one`: `Σ K†K ≤ I` implies trace-non-increasing
- `krausMapFintype_sum_le_one_of_tni`: converse of the above

## References

- Alberti, Uhlmann (1982) "Stochasticity and Partial Order"
- Christandl, König, Renner (2009) arXiv:0809.3019
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Local restatement of `Quantum.Channels.matrix_douglas_factorization`, with the matrix
    dimensions used in this file. -/
private lemma douglas_factorization_local {nH nK nR : ℕ} {numV : ℕ}
    (A : Fin numV → Matrix (Fin nH) (Fin nK) ℂ)
    (B : Matrix (Fin nH) (Fin nR) ℂ)
    (h_dom : (B * Bᴴ - ∑ k, A k * (A k)ᴴ).PosSemidef) :
    ∃ C : Fin numV → Matrix (Fin nR) (Fin nK) ℂ,
      (∀ k, A k = B * C k) ∧
      ((1 : Op nR) -
        ∑ k, C k * (C k)ᴴ).PosSemidef :=
  matrix_douglas_factorization A B h_dom

/-!
## Sub-lemmas for the CKR per-operator bound
-/

/-- Tensor a linear map with the identity on the left factor.

    `mapIdTensor Φ` acts on operators on `H ⊗ A` by leaving the `H` factor
    unchanged and applying `Φ` on the `A` factor entrywise. This is the
    right-factor analogue of `mapTensorId`. -/
noncomputable def mapIdTensor {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m)
    (X : Op (k * n)) : Op (k * m) :=
  let e_in : Fin k × Fin n ≃ Fin (k * n) := finProdFinEquiv
  let e_out : Fin k × Fin m ≃ Fin (k * m) := finProdFinEquiv
  Matrix.of fun p q =>
    let (s, a) := e_out.symm p
    let (t, b) := e_out.symm q
    ∑ i : Fin n, ∑ j : Fin n,
      Φ (single i j 1) a b * X (e_in (s, i)) (e_in (t, j))

/-- **No-signaling for the Alice marginal**: any trace-preserving map applied to Bob's tensor
factor leaves Alice's reduced state exactly unchanged. -/
theorem partialTraceB_mapIdTensor_of_tracePreserving {k n m : ℕ}
    [NeZero k] [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (hΦ : IsTracePreserving ⇑Φ) (W : Op (k * n)) :
    partialTraceB (mapIdTensor Φ W) = partialTraceB W := by
  ext s t
  simp only [partialTraceB, Matrix.of_apply, mapIdTensor, Equiv.toFun_as_coe,
    Equiv.symm_apply_apply]
  -- LHS: ∑ a, ∑ i, ∑ j, Φ(E_ij) a a · W (s,i) (t,j); collapse ∑ₐ Φ(E_ij) a a = Tr Φ(E_ij) = δ_ij.
  have htr : ∀ i j : Fin n,
      (∑ a : Fin m, Φ (Matrix.single i j 1) a a) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have h1 : (∑ a : Fin m, Φ (Matrix.single i j 1) a a) = (Φ (Matrix.single i j 1)).trace := by
      simp [Matrix.trace, Matrix.diag]
    rw [h1, hΦ]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.trace, Matrix.diag, Matrix.single_apply]
    · simp only [Matrix.trace, Matrix.diag, Matrix.single_apply, hij]
      simp only [Finset.sum_boole, ↓reduceIte, Nat.cast_eq_zero, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff, Finset.mem_univ, not_and, forall_const, forall_eq', ne_eq]
      exact fun h => hij h.symm
  calc (∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n,
        Φ (Matrix.single i j 1) a a * W (finProdFinEquiv (s, i)) (finProdFinEquiv (t, j)))
      = ∑ i : Fin n, ∑ j : Fin n,
          (∑ a : Fin m, Φ (Matrix.single i j 1) a a) *
            W (finProdFinEquiv (s, i)) (finProdFinEquiv (t, j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (if i = j then (1 : ℂ) else 0) *
            W (finProdFinEquiv (s, i)) (finProdFinEquiv (t, j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [htr]
    _ = ∑ i : Fin n, W (finProdFinEquiv (s, i)) (finProdFinEquiv (t, i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Finset.sum_ite_eq, ite_mul]

/-!
## Kraus map infrastructure for substate extraction

`krausMapFintype_castOutput` and `krausMapFintype_tni_of_sum_le_one` below are `Fin r`-specific
facts about `krausMapFintype` (`FintypeKraus.lean`); `krausMapFintype_isCompletelyPositive` and
`krausMapFintype_trace_eq` (used below) also live in `FintypeKraus.lean`.
-/

/-- `krausMapFintype` commutes with output-dimension casts of Kraus representations.

Transporting a `KrausRepresentation` along `h : m = m'` only transports the
resulting operator by the same dimension equality. -/
lemma krausMapFintype_castOutput {n m m' : ℕ}
    (h : m = m') (kr : KrausRepresentation n m)
    (A : Op n) :
    krausMapFintype (kr.castOutput h).operators A =
      h ▸ (krausMapFintype kr.operators A) := by
  subst h
  rfl

/-- A Kraus map with Σ K†K ≤ I is trace-non-increasing on PSD inputs. -/
theorem krausMapFintype_tni_of_sum_le_one {n m : ℕ} [NeZero n] {r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (hK : ((1 : Op n) - ∑ k, (K k)ᴴ * K k).PosSemidef) :
    ∀ A : Op n, A.PosSemidef → (krausMapFintype K A).trace.re ≤ A.trace.re := by
  intro A hA
  set M := ∑ k, (K k)ᴴ * K k with hM_def
  rw [krausMapFintype_trace_eq, ← hM_def]
  have h_split_re : (M * A).trace.re = A.trace.re - ((1 - M) * A).trace.re := by
    have h1 : M * A + (1 - M) * A = A := by rw [sub_mul, one_mul, add_sub_cancel]
    have h2 := congr_arg Matrix.trace h1
    rw [Matrix.trace_add] at h2
    have h3 := congr_arg Complex.re h2
    rw [Complex.add_re] at h3; linarith
  rw [h_split_re]
  linarith [Quantum.Operators.trace_mul_psd_nonneg (1 - M) A hK hA]

/-- CP linear map has Kraus decomposition: T(A) = ∑_k K_k A K_k† for some operators K_k.
    Adapts `cptp_eq_kraus_sum` — the Kraus extraction uses only CP + linearity, not TP. -/
lemma cp_linear_eq_kraus_sum {n m : ℕ} [NeZero n] [NeZero m]
    (T : Op n →ₗ[ℂ] Op m) (hT_cp : IsCompletelyPositive ⇑T) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin m) (Fin n) ℂ),
      ∀ A, T A = ∑ k, K k * A * (K k)† := by
  -- Decompose PSD Choi matrix
  unfold IsCompletelyPositive at hT_cp
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hT_cp
  obtain ⟨r, v, hv⟩ := hT_cp
  -- Define Kraus operators K_k(a, i) = v_k(finProdFinEquiv(i, a))
  set K : Fin r → Matrix (Fin m) (Fin n) ℂ :=
    fun k => Matrix.of fun a i => v k (finProdFinEquiv (i, a))
  refine ⟨r, K, ?_⟩
  intro A; ext a b
  -- Both sides reduce to ∑_k ∑_i ∑_j K_k(a,i) * A(i,j) * star(K_k(b,j))
  -- RHS: expand matrix multiplication
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K, Matrix.of_apply]
  -- LHS: expand via linearity + Choi matrix
  -- T(A) = T(∑_i ∑_j A(i,j) • E_ij) = ∑_i ∑_j A(i,j) • T(E_ij) by linearity
  set E := fun i j : Fin n => Matrix.of fun r c =>
    if r = i ∧ c = j then (1:ℂ) else 0 with hE_def
  -- Decompose A
  have hA_decomp : A = ∑ i, ∑ j, A i j • E i j := by
    ext r c; simp only [E, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact if_neg (fun ⟨h1, _⟩ => hi h1.symm)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2.symm))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  -- Apply linearity to get entry-wise sum
  have hT_entry : T A a b = ∑ i, ∑ j, A i j *
      ChoiMatrix n m (⇑T) (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
    conv_lhs => rw [hA_decomp, map_sum T]
    simp_rw [map_sum T, T.map_smul,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext i; congr 1; ext j
    congr 1
    simp only [E, ChoiMatrix, Matrix.of_apply, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
  rw [hT_entry, hv]
  -- Simplify LHS: push sum application inside
  simp only [vecMulVec, Pi.star_apply]
  have h_push : ∀ i j : Fin n,
      (∑ k, Matrix.of fun x_2 y => v k x_2 * star (v k y))
        (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      ∑ k, v k (finProdFinEquiv (i, a)) * star (v k (finProdFinEquiv (j, b))) :=
    fun i j => Matrix.sum_apply _ _ Finset.univ _
  simp_rw [h_push]
  -- Reorder sums and match terms
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have reorder : ∀ (f : Fin n → Fin n → Fin r → ℂ),
      ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ b, ∑ a, f a b k := by
    intro f
    calc ∑ a, ∑ b, ∑ k, f a b k
        = ∑ a, ∑ k, ∑ b, f a b k := by
          congr 1; ext a; exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, f a b k := Finset.sum_comm
      _ = ∑ k, ∑ b, ∑ a, f a b k := by
          congr 1; ext k; exact Finset.sum_comm
  rw [reorder]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- Trace of M · |v⟩⟨v| equals the quadratic form ⟨v|M|v⟩. -/
private lemma trace_mul_vecMulVec_star {d : ℕ}
    (M : Op d) (v : Fin d → ℂ) :
    (M * vecMulVec v (star v)).trace = star v ⬝ᵥ M.mulVec v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec, Pi.star_apply,
    mulVec, dotProduct, Matrix.of_apply]
  conv_rhs => arg 2; ext i; rw [Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

/-- Converse of `krausMapFintype_tni_of_sum_le_one`: if a Kraus map is trace-non-increasing
    on PSD inputs, then Σ K†K ≤ I (operator inequality). -/
lemma krausMapFintype_sum_le_one_of_tni {n m : ℕ} [NeZero n] {r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (hK_tni : ∀ A : Op n, A.PosSemidef → (krausMapFintype K A).trace.re ≤ A.trace.re) :
    ((1 : Op n) - ∑ k, (K k)ᴴ * K k).PosSemidef := by
  set M := ∑ k, (K k)ᴴ * K k with hM_def
  -- (1 - M) is Hermitian
  have hM_herm : M.IsHermitian := by
    rw [hM_def, Matrix.IsHermitian, Matrix.conjTranspose_sum]
    congr 1; ext1 k
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hIM_herm : (1 - M).IsHermitian := Matrix.isHermitian_one.sub hM_herm
  -- Use dotProduct characterization
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hIM_herm, fun v => ?_⟩
  -- Need: 0 ≤ star v ⬝ᵥ (1 - M).mulVec v
  -- Key: Tr(krausMapFintype K (|v⟩⟨v|)) = Tr(M · |v⟩⟨v|) and Tr(|v⟩⟨v|) = star v ⬝ᵥ v
  set A := vecMulVec v (star v) with hA_def
  have hA_psd : A.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  -- Trace calculation: (krausMapFintype K A).trace = (M * A).trace
  have h_trace_eq : (krausMapFintype K A).trace = (M * A).trace := by
    rw [krausMapFintype_trace_eq, ← hM_def]
  -- Tr(M · |v⟩⟨v|) = ⟨v|M|v⟩
  have h_MA := trace_mul_vecMulVec_star M v
  -- Tr(|v⟩⟨v|) = ⟨v|v⟩
  have h_IA : A.trace = star v ⬝ᵥ v := by
    rw [hA_def]; simp only [Matrix.trace, Matrix.diag, vecMulVec, dotProduct, Pi.star_apply,
      Matrix.of_apply]; congr 1; ext i; ring
  -- From TNI: Tr(krausMapFintype K A).re ≤ Tr(A).re
  have h_le := hK_tni A hA_psd
  rw [h_trace_eq, h_MA, h_IA] at h_le
  -- ⟨v|(1-M)|v⟩ = ⟨v|v⟩ - ⟨v|M|v⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  -- Since (1-M) is Hermitian, ⟨v|(1-M)|v⟩ is real (im = 0)
  have h_real := quadraticForm_hermitian_conj_eq_self (1 - M) hIM_herm v
  unfold quadraticForm at h_real
  have h_im : (star v ⬝ᵥ (1 - M).mulVec v).im = 0 := by
    have := congr_arg Complex.im h_real
    simp [Complex.conj_im] at this; linarith
  rw [Complex.nonneg_iff]
  constructor
  · -- Re part: (star v ⬝ᵥ v - star v ⬝ᵥ M.mulVec v).re ≥ 0
    rw [Complex.sub_re]; linarith
  · -- Im part: follows from Hermiticity
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at h_im
    exact h_im.symm

/-- A pure density operator is a rank-1 projector: τ = |ψ⟩⟨ψ| for some
    unit vector ψ. This uses the spectral decomposition: τ being PSD,
    Hermitian, idempotent (τ² = τ), and trace-1 forces exactly one
    eigenvalue to be 1 and the rest 0.

    The vector ψ is the eigenvector corresponding to eigenvalue 1. -/
lemma pure_density_eq_vecMulVec {n : ℕ} [NeZero n]
    (τ : DensityOp n) (hτ : τ.IsPure) :
    ∃ ψ : Fin n → ℂ,
      τ.toOp = vecMulVec ψ (star ψ) ∧ star ψ ⬝ᵥ ψ = 1 := by
  -- Spectral decomposition setup
  have hH := τ.toPosSemidefOp.toHermitianOp.isHermitian
  set ev := hH.eigenvalues
  set U := (↑hH.eigenvectorUnitary : Op n)
  have hτ_spec : τ.toOp = U * Matrix.diagonal (Complex.ofReal ∘ ev) * Uᴴ := by
    have := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this; exact this
  have hUU : Uᴴ * U = 1 := by
    simpa [star_eq_conjTranspose] using
      UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  -- Step 1: eigenvalues are idempotent (from τ² = τ)
  have hev_idem : ∀ i, ev i * ev i = ev i := by
    intro i
    set e := hH.eigenvectorBasis i
    set w : Fin n → ℂ := ↑e
    have h_eig : τ.toOp *ᵥ w = (ev i : ℂ) • w :=
      hH.mulVec_eigenvectorBasis i
    have h_sq : (τ.toOp * τ.toOp) *ᵥ w =
        ((ev i : ℂ) * (ev i : ℂ)) • w := by
      rw [← Matrix.mulVec_mulVec, h_eig,
          Matrix.mulVec_smul, h_eig, smul_smul]
    rw [hτ] at h_sq; rw [h_eig] at h_sq
    have hv_ne : w ≠ 0 := by
      intro h
      exact hH.eigenvectorBasis.orthonormal.ne_zero i
        (by ext j; exact congr_fun h j)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv_ne
    have h_comp := congr_fun h_sq k
    simp only [Pi.smul_apply, smul_eq_mul] at h_comp
    have h_eq := mul_right_cancel₀ hk h_comp
    have : (ev i : ℂ) = ((ev i * ev i : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]; exact h_eq
    exact_mod_cast this.symm
  -- Step 2: eigenvalues ∈ {0, 1}
  have hev_01 : ∀ i, ev i = 0 ∨ ev i = 1 := by
    intro i
    have h1 := hev_idem i
    have : ev i * (ev i - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · left; exact h
    · right; linarith
  -- Step 3: exactly one eigenvalue equals 1 (from trace = 1)
  have hev_sum_r : ∑ i, ev i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues; rw [τ.trace_one] at h
    have : (∑ i, ev i : ℂ) = 1 := h.symm
    exact_mod_cast this
  have ⟨j, hj⟩ : ∃ j, ev j = 1 := by
    by_contra h; push Not at h
    have : ∀ i, ev i = 0 := fun i =>
      (hev_01 i).resolve_right (h i)
    simp [this] at hev_sum_r
  have hj_uniq : ∀ k, k ≠ j → ev k = 0 := by
    intro k hk; rcases hev_01 k with h | h
    · exact h
    · exfalso
      have h_nn : ∀ i, 0 ≤ ev i := fun i => by
        rcases hev_01 i with h0 | h1 <;> simp [*]
      have : ∑ i, ev i ≥ ev j + ev k := by
        calc ∑ i, ev i
            = ev j + ∑ i ∈ Finset.univ.erase j, ev i :=
              (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
          _ ≥ ev j + ev k := by
              gcongr
              exact Finset.single_le_sum (fun i _ => h_nn i)
                (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
      linarith [show ev j + ev k = 2 from by rw [hj, h]; ring]
  -- Step 4: diagonal matrix has a single 1
  have hD_single : Matrix.diagonal (Complex.ofReal ∘ ev) =
      Matrix.diagonal (fun i => if i = j then 1 else 0) := by
    congr 1; ext i; simp only [Function.comp]
    rcases eq_or_ne i j with rfl | hne
    · simp [hj]
    · simp [hj_uniq i hne, hne]
  -- Step 5: τ = vecMulVec ψ (star ψ) where ψ is the j-th column of U
  set ψ := fun a => U a j with hψ_def
  refine ⟨ψ, ?_, ?_⟩
  · -- τ.toOp = vecMulVec ψ (star ψ)
    rw [hτ_spec, hD_single]
    ext a b
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
      mul_one, mul_zero, Matrix.conjTranspose_apply, vecMulVec,
      Matrix.of_apply, Pi.star_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ite_mul, zero_mul, hψ_def]
  · -- star ψ ⬝ᵥ ψ = 1
    simp only [dotProduct, Pi.star_apply, hψ_def,
      ← Matrix.conjTranspose_apply]
    rw [show ∑ x, Uᴴ j x * U x j = (Uᴴ * U) j j from by
      simp [Matrix.mul_apply]]
    rw [hUU]; simp

/-!
### Helpers for substate extraction

The proof of `substate_from_purification_vec` is decomposed into:
1. `mapIdTensor_krausMapFintype_vecMulVec_eq` — identity relating
   `mapIdTensor (krausMapFintype K)` on a rank-1 operator to a sum of rank-1 operators.
2. `substate_core_kraus_exist` — core Douglas-type factorization: given PSD
   vectors v_j with partial trace ≤ α·σ and purification ψ of σ, construct
   Kraus operators K_j with TNI condition and v_j = √α · (I_H ⊗ K_j)ψ.
-/

/-- The vector in `H ⊗ K` obtained by applying a Kraus operator `Kk : nK × nR`
    to the `R`-factor of a vector `ψ` in `H ⊗ R`. Entry-wise:
    `(krausVec Kk ψ)(s,a) = Σ_r Kk(a,r) · ψ(s,r)`. -/
def krausVec {nH nK nR : ℕ}
    (Kk : Matrix (Fin nK) (Fin nR) ℂ) (ψ : Fin (nH * nR) → ℂ) :
    Fin (nH * nK) → ℂ :=
  fun p =>
    let (s, a) := finProdFinEquiv.symm p
    ∑ r : Fin nR, Kk a r * ψ (finProdFinEquiv (s, r))

/-- Reshaping `krausVec Kk ψ` gives `reshapeVec ψ * Kkᵀ`. -/
private lemma reshapeVec_krausVec {nH nK nR : ℕ}
    (Kk : Matrix (Fin nK) (Fin nR) ℂ) (ψ : Fin (nH * nR) → ℂ) :
    reshapeVec (krausVec Kk ψ) = reshapeVec ψ * Kkᵀ := by
  ext s a
  simp only [reshapeVec_apply, Matrix.mul_apply, Matrix.transpose_apply]
  show (krausVec Kk ψ) (finProdFinEquiv (s, a)) = _
  unfold krausVec
  have h_eq := finProdFinEquiv.symm_apply_apply (s, a)
  have h1 : (finProdFinEquiv.symm (finProdFinEquiv (s, a))).1 = s :=
    congr_arg Prod.fst h_eq
  have h2 : (finProdFinEquiv.symm (finProdFinEquiv (s, a))).2 = a :=
    congr_arg Prod.snd h_eq
  simp only [Equiv.toFun_as_coe, h1, h2]
  congr 1; ext r; ring

/-- `mapIdTensor (krausMapFintype K)` applied to a rank-1 operator `|ψ⟩⟨ψ|` equals
    the sum `Σ_k |w_k⟩⟨w_k|` where `w_k = krausVec (K k) ψ`.

    This is a direct computation: expanding `mapIdTensor` and `krausMapFintype`
    on matrix units and distributing yields the stated sum of outer products. -/
private lemma mapIdTensor_krausMapFintype_vecMulVec_eq {nH nK nR : ℕ}
    [NeZero nH] [NeZero nK] [NeZero nR]
    {r : ℕ} (K : Fin r → Matrix (Fin nK) (Fin nR) ℂ) (ψ : Fin (nH * nR) → ℂ) :
    mapIdTensor (krausMapFintype K) (vecMulVec ψ (star ψ)) =
      ∑ k, vecMulVec (krausVec (K k) ψ) (star (krausVec (K k) ψ)) := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, vecMulVec_apply, Pi.star_apply,
    Matrix.sum_apply, krausVec]
  -- Normalize Equiv coercion notation
  simp only [Equiv.toFun_as_coe]
  -- Unfold krausMapFintype to get explicit sum
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Matrix.sum_apply]
  -- Each term: (K_k * single_ij * K_k†)(a,b) = K_k(a,i) * conj(K_k(b,j))
  simp_rw [show ∀ (i j : Fin nR) (k : Fin r),
      (K k * single i j (1:ℂ) * (K k)ᴴ)
        (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 =
      K k (finProdFinEquiv.symm p).2 i * star (K k (finProdFinEquiv.symm q).2 j) from by
    intro i j k
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero,
      Matrix.conjTranspose_apply, ite_and]
    simp [Finset.sum_ite_eq, Finset.mem_univ]]
  -- Both sides equal Σ_k Σ_r Σ_r' K_k(a,r)·conj(K_k(b,r'))·ψ(s,r)·conj(ψ(t,r'))
  -- LHS: distribute inner Kraus sum, then reorder to Σ_k Σ_x Σ_x1
  conv_lhs =>
    arg 2; ext x; arg 2; ext x1; rw [Finset.sum_mul]  -- expand Σ_k2(...) * (...)
  conv_lhs =>
    arg 2; ext x; rw [Finset.sum_comm]  -- swap x1 and k2
  conv_lhs =>
    rw [Finset.sum_comm]  -- swap x and k2
  -- RHS: expand star(Σ...) and distribute, stay in order Σ_k Σ_i Σ_j
  conv_rhs =>
    arg 2; ext k; rw [Finset.sum_mul]  -- distribute (Σ_i ...) * star(...)
    arg 2; ext i; rw [star_sum, Finset.mul_sum]  -- distribute star and expand
    arg 2; ext j; rw [star_mul']  -- push star into product
  -- Now both sides: Σ_k:r, Σ_i:nR, Σ_j:nR, terms
  congr 1; ext k; congr 1; ext i; congr 1; ext j; ring

/-- **Core Douglas-type factorization for substate extraction.**

    Given PSD decomposition vectors `v_j` of `ρ` and purification vector `ψ`
    of `σ` with the operator inequality `Tr_K(ρ) ≤ α · Tr_R(|ψ⟩⟨ψ|)`,
    there exist Kraus operators `K_j` such that:
    1. `Σ_j K_j† K_j ≤ I` (trace non-increasing condition)
    2. `v_j = √α · krausVec (K_j) ψ` (reconstruction per vector)

    The construction uses the pseudo-inverse of the purification matrix
    `Ψ_{h,r} = ψ_{(h,r)}`: each `K_j` is obtained by "dividing" the
    reshaped `v_j` by `Ψ` in the H-factor. The substate condition ensures
    `range(V_j) ⊆ range(Ψ)`, making the factorization well-defined.

    Reference: Douglas (1966) range factorization, Alberti-Uhlmann (1982). -/
private lemma substate_core_kraus_exist {nH nK nR : ℕ}
    [NeZero nH] [NeZero nK] [NeZero nR]
    {numV : ℕ} (v : Fin numV → (Fin (nH * nK) → ℂ))
    (ψ : Fin (nH * nR) → ℂ) (α : ℝ) (hα : 0 < α)
    (h_sub : (((α : ℂ) • partialTraceB (vecMulVec ψ (star ψ))) -
              partialTraceB (∑ j, vecMulVec (v j) (star (v j)))).PosSemidef) :
    ∃ K : Fin numV → Matrix (Fin nK) (Fin nR) ℂ,
      ((1 : Op nR) - ∑ k, (K k)ᴴ * K k).PosSemidef ∧
      ∀ k, v k = (↑(Real.sqrt α) : ℂ) • krausVec (K k) ψ := by
  -- Step 1: Rewrite substate condition in matrix form
  -- partialTraceB(|v⟩⟨v|) = V V† where V = reshapeVec v
  rw [partialTraceB_vecMulVec_eq_mul_conjTranspose,
      partialTraceB_sum_vecMulVec_eq] at h_sub
  -- Convert α • (Ψ Ψ†) to (√α·Ψ)(√α·Ψ)†
  have hα_eq : (α : ℂ) • (reshapeVec ψ * (reshapeVec ψ)ᴴ) =
      ((↑(Real.sqrt α) : ℂ) • reshapeVec ψ) *
      ((↑(Real.sqrt α) : ℂ) • reshapeVec ψ)ᴴ := by
    rw [Matrix.conjTranspose_smul]
    have h_star : star (↑(Real.sqrt α) : ℂ) = ↑(Real.sqrt α) := by
      simp [Complex.conj_ofReal]
    rw [h_star]
    ext i j; simp only [Matrix.smul_apply, Matrix.mul_apply,
      smul_eq_mul, Finset.mul_sum]
    congr 1; ext k
    have hsq : (↑(Real.sqrt α) : ℂ) * ↑(Real.sqrt α) = (α : ℂ) := by
      simp [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hα)]
    rw [← hsq]; ring
  rw [hα_eq] at h_sub
  -- Step 2: Apply Douglas factorization
  -- A_k = V_k : Matrix nH nK, B = √α·Ψ : Matrix nH nR
  -- → C_k : Matrix nR nK with V_k = B·C_k and (I - Σ C_k C_k†).PSD
  obtain ⟨C, hC_factor, hC_psd⟩ :=
    douglas_factorization_local
      (fun k => reshapeVec (v k))
      ((↑(Real.sqrt α) : ℂ) • reshapeVec ψ)
      h_sub
  -- Step 3: Set K_k = C_kᵀ : Matrix nK nR
  refine ⟨fun k => (C k)ᵀ, ?_, ?_⟩
  · -- TNI: (I - Σ_k K_k† K_k).PSD where K_k = C_kᵀ
    -- (C_kᵀ)† * C_kᵀ = (C_k * C_k†)ᵀ
    have h_sum_eq : ∑ k, ((C k)ᵀ)ᴴ * (C k)ᵀ =
        (∑ k, C k * (C k)ᴴ)ᵀ := by
      rw [Matrix.transpose_sum]; congr 1; ext1 k
      exact conjTranspose_transpose_mul_transpose (C k)
    rw [h_sum_eq]
    exact posSemidef_one_sub_transpose _ hC_psd
  · -- Reconstruction: v_k = √α · krausVec (C_kᵀ) ψ
    intro k
    -- From Douglas: reshapeVec(v_k) = (√α · Ψ) · C_k
    have hVk := hC_factor k
    -- reshapeVec(krausVec C_kᵀ ψ) = Ψ · (C_kᵀ)ᵀ = Ψ · C_k
    have h_kraus : reshapeVec (krausVec (C k)ᵀ ψ) =
        reshapeVec ψ * C k := by
      rw [reshapeVec_krausVec, Matrix.transpose_transpose]
    -- reshapeVec(v_k) = reshapeVec(√α · krausVec C_kᵀ ψ)
    have h_eq : reshapeVec (v k) =
        reshapeVec ((↑(Real.sqrt α) : ℂ) • krausVec (C k)ᵀ ψ) := by
      rw [reshapeVec_smul, h_kraus]
      -- Need: reshapeVec(v_k) = √α • (reshapeVec ψ * C_k)
      -- hVk: reshapeVec(v_k) = (√α • reshapeVec ψ) * C_k
      -- These differ by smul_mul_assoc on non-square matrices
      rw [hVk]
      ext i j; simp only [Matrix.smul_apply, Matrix.mul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
    -- Injectivity of reshapeVec
    have h_inj := congr_arg unreshapeVec h_eq
    simp only [unreshapeVec_reshapeVec] at h_inj
    exact h_inj

/-- **Core Kraus construction from purification vector.**

    Given a PSD operator ρ on H ⊗ K with Tr_K(ρ) ≤ α · σ (operator inequality),
    and a vector ψ ∈ H ⊗ R (not necessarily normalized) satisfying
    `partialTraceB (|ψ⟩⟨ψ|) = σ`,
    there exist Kraus operators K with Σ K†K ≤ I and
    ρ = α · (id_H ⊗ krausMapFintype K)(|ψ⟩⟨ψ|).

    Proved by combining:
    - PSD decomposition: `ρ = Σ_j |v_j⟩⟨v_j|`
    - Core factorization: `v_j = √α · krausVec(K_j, ψ)` with TNI
    - Identity:
      `mapIdTensor (krausMapFintype K) (|ψ⟩⟨ψ|) = Σ_k |krausVec(K_k, ψ)⟩⟨krausVec(K_k, ψ)|`

    Reference: Alberti-Uhlmann (1982), Berta-Lemm-Wilde (2021). -/
lemma substate_from_purification_vec {nH nK nR : ℕ}
    [NeZero nH] [NeZero nK] [NeZero nR]
    (ρ : Op (nH * nK)) (hρ_psd : ρ.PosSemidef)
    (σ : Op nH)
    (α : ℝ) (hα_pos : 0 < α)
    (hρ_sub : (((α : ℂ) • σ) - partialTraceB ρ).PosSemidef)
    (ψ : Fin (nH * nR) → ℂ)
    (hψ_purifies : partialTraceB (vecMulVec ψ (star ψ)) = σ) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin nK) (Fin nR) ℂ),
      ((1 : Op nR) - ∑ k, (K k)ᴴ * K k).PosSemidef ∧
      ρ = (α : ℂ) •
        mapIdTensor (krausMapFintype K) (vecMulVec ψ (star ψ)) := by
  -- Step 1: PSD decomposition ρ = Σ_j |v_j⟩⟨v_j|
  obtain ⟨numV, v, hρ_eq⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ_psd
  -- Step 2: Reformulate substate condition in terms of decomposition vectors
  have h_sub : (((α : ℂ) • partialTraceB (vecMulVec ψ (star ψ))) -
      partialTraceB (∑ j, vecMulVec (v j) (star (v j)))).PosSemidef := by
    rw [hψ_purifies, ← hρ_eq]; exact hρ_sub
  -- Step 3: Core factorization gives Kraus operators
  obtain ⟨K, hK_tni, hK_vec⟩ := substate_core_kraus_exist v ψ α hα_pos h_sub
  -- Step 4: Assembly
  refine ⟨numV, K, hK_tni, ?_⟩
  -- Rewrite ρ using PSD decomposition
  rw [hρ_eq]
  -- Rewrite mapIdTensor using the rank-1 identity
  rw [mapIdTensor_krausMapFintype_vecMulVec_eq K ψ]
  -- Goal: Σ_j |v_j⟩⟨v_j| = α • Σ_k |w_k⟩⟨w_k| where v_j = √α · w_j
  rw [Finset.smul_sum]
  congr 1; ext k
  rw [hK_vec k]
  -- |c • w⟩⟨c • w| = c * conj(c) • |w⟩⟨w| where c = √α
  -- star distributes over smul: star(c • w) = conj(c) • star(w)
  rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  -- Need: √α * conj(√α) = α (as ℂ), so the scalar prefactors match
  simp [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hα_pos)]

/-- **Direct Kraus construction for substate extraction.**

    Given PSD ρ on H ⊗ K with Tr_K(ρ) ≤ α · σ_H, and pure τ on H ⊗ R
    purifying σ_H, there exist Kraus operators K with Σ K†K ≤ I and
    ρ = α · (id_H ⊗ krausMapFintype K)(τ).

    Proved by combining `pure_density_eq_vecMulVec` (pure state → rank-1)
    and `substate_from_purification_vec` (core construction from vector).

    Reference: Alberti-Uhlmann (1982), Berta-Lemm-Wilde (2021). -/
lemma substate_kraus_operators_exist {nH nK nR : ℕ} [NeZero nH] [NeZero nK] [NeZero nR]
    (ρ : Op (nH * nK)) (hρ_psd : ρ.PosSemidef) (σH : DensityOp nH)
    (α : ℝ) (hα_pos : 0 < α)
    (hρ_sub : (((α : ℂ) • σH.toOp) - partialTraceB ρ).PosSemidef)
    (τ : DensityOp (nH * nR)) (hτ_pure : τ.IsPure)
    (hτ_purifies : τ.partialTraceB = σH) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin nK) (Fin nR) ℂ),
      ((1 : Op nR) - ∑ k, (K k)ᴴ * K k).PosSemidef ∧
      ρ = (α : ℂ) • mapIdTensor (krausMapFintype K) τ.toOp := by
  -- Step 1: Extract purification vector from pure state τ
  obtain ⟨ψ, hψ_eq, hψ_norm⟩ := pure_density_eq_vecMulVec τ hτ_pure
  -- Step 2: Connect DensityOp.partialTraceB with Op-level partialTraceB
  have h_ptr : partialTraceB τ.toOp = σH.toOp := by
    change (τ.partialTraceB).toOp = σH.toOp; rw [hτ_purifies]
  -- Step 3: Get purification condition on ψ
  have hψ_purifies : partialTraceB (vecMulVec ψ (star ψ)) = σH.toOp := by
    rw [← hψ_eq]; exact h_ptr
  -- Step 4: Apply core construction
  obtain ⟨r, K, hK_sum, hK_recon⟩ := substate_from_purification_vec ρ hρ_psd
    σH.toOp
    α hα_pos hρ_sub
    ψ hψ_purifies
  -- Step 5: Rewrite using τ.toOp = vecMulVec ψ (star ψ)
  exact ⟨r, K, hK_sum, by rw [hψ_eq]; exact hK_recon⟩

/-- **Abstract existence of CP TNI map for substate extraction**
    (Alberti-Uhlmann / quantum Radon-Nikodym):

    Given PSD ρ on H ⊗ K with Tr_K(ρ) ≤ α · σ_H, and pure τ on H ⊗ R
    purifying σ_H, there exists a completely positive, trace-non-increasing
    linear map T : End(R) → End(K) such that ρ = α · (id_H ⊗ T)(τ).

    This is the core mathematical content of the substate extraction theorem.
    The Kraus form follows from `cp_linear_eq_kraus_sum`.

    Proved by combining `substate_kraus_operators_exist` (direct Kraus construction),
    `krausMapFintype_isCompletelyPositive` (Kraus maps are CP), and
    `krausMapFintype_tni_of_sum_le_one` (Kraus sum ≤ I implies TNI).

    Reference: Alberti-Uhlmann (1982), Berta-Lemm-Wilde (2021). -/
lemma substate_map_exists {nH nK nR : ℕ} [NeZero nH] [NeZero nK] [NeZero nR]
    (ρ : Op (nH * nK)) (hρ_psd : ρ.PosSemidef) (σH : DensityOp nH)
    (α : ℝ) (hα_pos : 0 < α)
    (hρ_sub : (((α : ℂ) • σH.toOp) - partialTraceB ρ).PosSemidef)
    (τ : DensityOp (nH * nR)) (hτ_pure : τ.IsPure)
    (hτ_purifies : τ.partialTraceB = σH) :
    ∃ T : Op nR →ₗ[ℂ] Op nK,
      IsCompletelyPositive T ∧
      (∀ A : Op nR, A.PosSemidef → (T A).trace.re ≤ A.trace.re) ∧
      ρ = (α : ℂ) • mapIdTensor T τ.toOp := by
  -- Get Kraus operators with sum condition and reconstruction
  obtain ⟨r, K, hK_sum, hK_recon⟩ := substate_kraus_operators_exist ρ hρ_psd σH α hα_pos
    hρ_sub τ hτ_pure hτ_purifies
  -- T = krausMapFintype K satisfies all three properties
  exact ⟨krausMapFintype K, krausMapFintype_isCompletelyPositive K,
    krausMapFintype_tni_of_sum_le_one K hK_sum, hK_recon⟩

end Quantum.Channels
