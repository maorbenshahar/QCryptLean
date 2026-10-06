import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# CKR Hermitian Contractivity — PSD preservation, trace contraction, Hermitian `id ⊗ T`

Low-level linear-algebra infrastructure for the CKR postselection argument.
This file contains the core `id ⊗ T` lemmas used when the input is Hermitian:
Kraus-expansion PSD preservation, trace comparison through partial trace, and
the resulting Hermitian trace-norm contractivity theorem.

## Main statements
- `mapIdTensor_preserves_psd`: complete positivity implies PSD preservation for `id ⊗ T`
- `partialTraceA_posSemidef_mathlib`: partial trace preserves Mathlib PSD
- `partialTraceB_posSemidef_mathlib`: the analogous `B`-factor statement
- `partialTraceB_psd_mono`: partial trace preserves PSD monotonicity
- `trace_mapIdTensor_psd_le`: trace contraction for PSD inputs under `id ⊗ T`
- `traceNorm_mapIdTensor_contractive_hermitian`: Hermitian trace-norm contractivity
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- `mapIdTensor` distributes over subtraction. -/
theorem mapIdTensor_sub {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (X Y : Op (k * n)) :
    mapIdTensor Φ (X - Y) = mapIdTensor Φ X - mapIdTensor Φ Y := by
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Matrix.sub_apply]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- **Kraus sum applied to a matrix unit**: For Kraus operators `K_l`,
    `(∑_l K_l * E_ij * K_l†)(a,b) = ∑_l K_l(a,i) * star(K_l(b,j))`. -/
lemma kraus_apply_single {n m r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (i j : Fin n) (a b : Fin m) :
    (∑ l, K l * single i j (1 : ℂ) * (K l)ᴴ) a b = ∑ l, K l a i * star (K l b j) := by
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  have h_KE : ∀ x, (K l * single i j (1 : ℂ)) a x = if x = j then K l a i else 0 := by
    intro x
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hx : x = j
    · subst hx
      simp only [and_true, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun y _ => if_neg (fun ⟨_, h⟩ => hx h.symm)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h_KE, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Collapse a sum over `Fin (k * n)` with an if-condition on the first component. -/
private lemma finProdFinEquiv_sum_ite_left {k n : ℕ}
    (s : Fin k) (f : Fin n → ℂ) (g : Fin (k * n) → ℂ) :
    ∑ r : Fin (k * n),
      (if s = (finProdFinEquiv.symm r).1
        then f (finProdFinEquiv.symm r).2 else 0) * g r =
    ∑ i : Fin n, f i * g (finProdFinEquiv (s, i)) := by
  rw [(Equiv.sum_comp finProdFinEquiv _).symm]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]

/-- Collapse a sum over `Fin (k * n)` with an if-condition on the right. -/
private lemma finProdFinEquiv_sum_ite_right {k n : ℕ}
    (s : Fin k) (f : Fin (k * n) → ℂ) (g : Fin n → ℂ) :
    ∑ c : Fin (k * n),
      f c * (if s = (finProdFinEquiv.symm c).1
        then g (finProdFinEquiv.symm c).2 else 0) =
    ∑ j : Fin n, f (finProdFinEquiv (s, j)) * g j := by
  rw [(Equiv.sum_comp finProdFinEquiv _).symm]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]

/-- `mapIdTensor T` preserves PSD when `T` is completely positive. -/
lemma mapIdTensor_preserves_psd {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m) (hT_cp : IsCompletelyPositive ⇑T)
    (X : Op (k * n)) (hX : X.PosSemidef) :
    (mapIdTensor T X).PosSemidef := by
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum T hT_cp
  have hT_ij : ∀ i j : Fin n, ∀ a b : Fin m,
      T (single i j 1) a b = ∑ l, K l a i * star (K l b j) := by
    intro i j a b
    rw [hK]
    exact kraus_apply_single K i j a b
  set L : Fin r → Matrix (Fin (k * m)) (Fin (k * n)) ℂ := fun l =>
    Matrix.of fun p q =>
      let (s, a) := finProdFinEquiv.symm p
      let (t, i) := finProdFinEquiv.symm q
      if s = t then K l a i else 0
  suffices h_eq : mapIdTensor T X = ∑ l, L l * X * (L l)ᴴ by
    rw [h_eq]
    exact Matrix.posSemidef_sum _ (fun l _ => hX.mul_mul_conjTranspose_same (L l))
  ext p q
  simp only [mapIdTensor, Matrix.of_apply, Matrix.sum_apply, L]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp_rw [hT_ij, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1
  ext l
  conv_rhs => simp only [mul_assoc]
  simp_rw [finProdFinEquiv_sum_ite_left]
  simp_rw [apply_ite star, star_zero]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext x1; rw [← Finset.mul_sum]
  have hCollapse := fun x1 =>
    finProdFinEquiv_sum_ite_right
      (s := (finProdFinEquiv.symm q).1)
      (f := fun c => X (finProdFinEquiv ((finProdFinEquiv.symm p).1, x1)) c)
      (g := fun j => star (K l (finProdFinEquiv.symm q).2 j))
  simp_rw [hCollapse]
  conv_rhs => arg 2; ext x1; rw [Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- `Tr((id ⊗ T) X) = Tr(T(partialTraceA X))`. -/
lemma trace_mapIdTensor_eq {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m) (X : Op (k * n)) :
    (mapIdTensor T X).trace = (T (partialTraceA X)).trace := by
  have T_entry : ∀ (M : Op n) (a b : Fin m),
      T M a b = ∑ i : Fin n, ∑ j : Fin n, M i j * T (single i j 1) a b := by
    intro M a b
    have hM : M = ∑ i, ∑ j, M i j • single i j (1 : ℂ) :=
      (matrix_eq_sum_single M).trans
        (Finset.sum_congr rfl (fun c _ =>
          Finset.sum_congr rfl (fun d _ => by
            ext i j
            simp [single_apply, smul_eq_mul])))
    conv_lhs => rw [hM, map_sum]
    simp_rw [map_sum, T.map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h_entry : ∀ a : Fin m, T (partialTraceA X) a a =
      ∑ s : Fin k, ∑ i : Fin n, ∑ j : Fin n,
        T (single i j 1) a a * X (finProdFinEquiv (s, i)) (finProdFinEquiv (s, j)) := by
    intro a
    rw [T_entry (partialTraceA X) a a]
    simp only [partialTraceA, Matrix.of_apply]
    simp_rw [Finset.sum_mul, mul_comm (T _ _ _)]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2
      ext i
      rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag]
  rw [show (∑ x : Fin m, T (partialTraceA X) x x) =
      ∑ a : Fin m, ∑ s : Fin k, ∑ i : Fin n, ∑ j : Fin n,
        T (single i j 1) a a * X (finProdFinEquiv (s, i)) (finProdFinEquiv (s, j)) from
      Finset.sum_congr rfl (fun a _ => h_entry a)]
  rw [show (∑ x : Fin (k * m), mapIdTensor T X x x) =
      ∑ s : Fin k, ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n,
        T (single i j 1) a a * X (finProdFinEquiv (s, i)) (finProdFinEquiv (s, j)) from by
    calc
      ∑ x : Fin (k * m), mapIdTensor T X x x
          = ∑ sa : Fin k × Fin m,
              mapIdTensor T X (finProdFinEquiv sa) (finProdFinEquiv sa) := by
            exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm
      _ = ∑ s : Fin k, ∑ a : Fin m,
            mapIdTensor T X (finProdFinEquiv (s, a)) (finProdFinEquiv (s, a)) :=
          Fintype.sum_prod_type _
      _ = _ := by
          congr 1
          ext s
          congr 1
          ext a
          simp only [mapIdTensor, Matrix.of_apply]
          simp only [Equiv.symm_apply_apply]]
  exact Finset.sum_comm

/-- Partial trace over the `A`-factor preserves Mathlib PSD. -/
lemma partialTraceA_posSemidef_mathlib {k n : ℕ}
    (X : Op (k * n)) (hX : X.PosSemidef) :
    (partialTraceA X).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hX_dot := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hX).2
  refine ⟨partialTraceA_hermitian X hX.isHermitian, fun x => ?_⟩
  let X_QI : PosSemidefOp (k * n) :=
    { toOp := X
      isHermitian := hX.isHermitian
      pos_semidef := fun v => (Complex.nonneg_iff.mp (hX_dot v)).1 }
  have h_re := partialTraceA_posSemidef X_QI x
  have h_herm := partialTraceA_hermitian X hX.isHermitian
  have h_conj := quadraticForm_hermitian_conj_eq_self (partialTraceA X) h_herm x
  have h_im : (quadraticForm (partialTraceA X) x).im = 0 := by
    have := congr_arg Complex.im h_conj
    simp [Complex.conj_im] at this
    linarith
  rw [Complex.nonneg_iff]
  exact ⟨h_re, h_im.symm⟩

/-- Partial trace over the `B`-factor preserves Mathlib PSD. -/
lemma partialTraceB_posSemidef_mathlib {k n : ℕ}
    (X : Op (k * n)) (hX : X.PosSemidef) :
    (partialTraceB X).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hX_dot := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hX).2
  refine ⟨partialTraceB_hermitian X hX.isHermitian, fun x => ?_⟩
  let X_QI : PosSemidefOp (k * n) :=
    { toOp := X
      isHermitian := hX.isHermitian
      pos_semidef := fun v => (Complex.nonneg_iff.mp (hX_dot v)).1 }
  have h_re := partialTraceB_posSemidef X_QI x
  have h_herm := partialTraceB_hermitian X hX.isHermitian
  have h_conj := quadraticForm_hermitian_conj_eq_self (partialTraceB X) h_herm x
  have h_im : (quadraticForm (partialTraceB X) x).im = 0 := by
    have := congr_arg Complex.im h_conj
    simp [Complex.conj_im] at this
    linarith
  rw [Complex.nonneg_iff]
  exact ⟨h_re, h_im.symm⟩

/-- Partial trace over `B` preserves PSD monotonicity. -/
lemma partialTraceB_psd_mono {n m : ℕ} [NeZero n] [NeZero m]
    (A B : Op (n * m))
    (h : (A - B).PosSemidef) :
    (partialTraceB A - partialTraceB B).PosSemidef := by
  rw [← partialTraceB_sub]
  exact partialTraceB_posSemidef_mathlib _ h

/-- Trace contraction for PSD inputs under `id ⊗ T`. -/
lemma trace_mapIdTensor_psd_le {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_contr : ∀ A : Op n, A.PosSemidef → (T A).trace.re ≤ A.trace.re)
    (X : Op (k * n)) (hX : X.PosSemidef) :
    (mapIdTensor T X).trace.re ≤ X.trace.re := by
  rw [trace_mapIdTensor_eq T X]
  have hPA_psd : (partialTraceA X).PosSemidef := partialTraceA_posSemidef_mathlib X hX
  calc
    (T (partialTraceA X)).trace.re ≤ (partialTraceA X).trace.re := hT_contr _ hPA_psd
    _ = X.trace.re := by rw [trace_partialTraceA]

/-- Hermitian trace-norm contractivity for `id ⊗ T`. -/
theorem traceNorm_mapIdTensor_contractive_hermitian {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (hT_contr : ∀ A : Op n, A.PosSemidef → (T A).trace.re ≤ A.trace.re)
    (A : Op (k * n)) (hA : A.IsHermitian) :
    traceNorm (mapIdTensor T A) ≤ traceNorm A := by
  open Quantum.Metrics in
  obtain ⟨Dp, Dm, hDp, hDm, hDecomp, hNorm⟩ := traceNormHermitian_eq_trace_pos_neg A hA
  have hLinSub : mapIdTensor T A = mapIdTensor T Dp - mapIdTensor T Dm := by
    rw [hDecomp, mapIdTensor_sub]
  have hTDp := mapIdTensor_preserves_psd T hT_cp Dp hDp
  have hTDm := mapIdTensor_preserves_psd T hT_cp Dm hDm
  have hDiff_herm : (mapIdTensor T Dp - mapIdTensor T Dm).IsHermitian :=
    hTDp.isHermitian.sub hTDm.isHermitian
  calc
    traceNorm (mapIdTensor T A) = traceNorm (mapIdTensor T Dp - mapIdTensor T Dm) := by
      rw [hLinSub]
    _ = traceNormHermitian (mapIdTensor T Dp - mapIdTensor T Dm) hDiff_herm := by
      rw [traceNorm_hermitian_eq]
    _ ≤ ((mapIdTensor T Dp).trace + (mapIdTensor T Dm).trace).re := by
      exact traceNormHermitian_le_trace_posSemidef_sub _ _ _ hDiff_herm hTDp hTDm rfl
    _ ≤ (Dp.trace + Dm.trace).re := by
      rw [Complex.add_re, Complex.add_re]
      exact add_le_add
        (trace_mapIdTensor_psd_le T hT_contr Dp hDp)
        (trace_mapIdTensor_psd_le T hT_contr Dm hDm)
    _ = traceNormHermitian A hA := hNorm.symm
    _ = traceNorm A := by rw [traceNorm_hermitian_eq]

end Quantum.Channels
