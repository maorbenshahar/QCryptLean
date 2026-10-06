import QCryptLean.Quantum.TensorProducts.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# PSD Order and Trace Monotonicity — operator-semidefinite ordering and PSD-weighted trace bounds

Operator-semidefinite order helpers derived from PSD trace-product positivity:
for a PSD weight `M`, the map `A ↦ Tr(M · A).re` is monotone in the PSD
order on Hermitian operators.

The semidefinite ordering itself is encapsulated by `Quantum.Operators.opLe`,
defined via the real part of the quadratic form. Two bridge lemmas connect
`opLe` to Mathlib's `Matrix.PosSemidef` and to the induced trace ordering.

## Main definitions

- `Quantum.Operators.opLe`: the operator-semidefinite ordering `A ≤_PSD B`,
  defined as `∀ v, (quadraticForm A v).re ≤ (quadraticForm B v).re`.

## Main statements

- `Matrix.PosSemidef.trace_re_nonneg`: the real part of the trace of a PSD
  operator is nonnegative.
- `Quantum.Operators.trace_mul_psd_nonneg`: the real part of the trace of a
  product of two PSD matrices is nonnegative.
- `Quantum.Operators.quadraticForm_sub`: additivity of the quadratic form
  under subtraction of operators.
- `Quantum.Operators.quadraticForm_conjTranspose_eq_star`,
  `Quantum.Operators.quadraticForm_conjTranspose_re`: the quadratic form of an
  adjoint is the conjugate of the original quadratic form, and hence has the same real part.
- `Quantum.Operators.quadraticForm_im_of_isHermitian`: the quadratic form
  of a Hermitian operator is real-valued.
- `Quantum.Operators.posSemidef_sub_of_quadraticForm_re_le`: if `A` and `B`
  are Hermitian and `∀ v, (quadraticForm A v).re ≤ (quadraticForm B v).re`,
  then `Matrix.PosSemidef (B - A)`.
- `Quantum.Operators.posSemidef_of_isHermitian_of_quadraticForm_re_nonneg`:
  an Hermitian operator whose quadratic form has nonnegative real part on
  every vector is positive-semidefinite.
- `Quantum.Operators.trace_mul_le_of_quadraticForm_re_le`: the induced
  trace monotonicity `(M * A).trace.re ≤ (M * B).trace.re`.
- `Quantum.Operators.opLe.posSemidef_sub`: bridge from `opLe` to `PosSemidef`.
- `Quantum.Operators.trace_mul_le_of_opLe`: PSD-weighted trace monotonicity
  in terms of `opLe`.
- `Quantum.Operators.opLe_trans`, `Quantum.Operators.opLe_smul_nonneg`: the two
  elementary order laws (transitivity, nonnegative real rescaling).
- `Quantum.Operators.opLe_castDim_iff`, `Quantum.Operators.opLe_castDim`: the order is invariant
  under a dimension cast.
- `Quantum.Operators.opLe_mulVec_eq_zero_of_psd`, `Quantum.Operators.opLe_ker_le_of_psd`,
  `Quantum.Operators.opLe_mul_right_eq_zero_of_psd`,
  `Quantum.Operators.opLe_mul_left_eq_zero_of_psd`: Löwner domination contains the support,
  in vector, kernel-submodule and matrix-annihilator form.
- `Quantum.Operators.partialTraceB_opLe_of_smul_one_opLe`,
  `Quantum.Operators.opLe_smul_partialTraceB_of_identityFloor`: an identity floor
  on a joint reference pushes through `Tr_R` and upgrades a feasibility bound
  `ρ ⪯ s·1_E` to domination by the marginal reference at scale `s/(c·dR)`.
-/

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder MatrixOrder

/-- **Trace nonnegativity for PSD operators.** The real part of the trace of
a positive-semidefinite operator is nonnegative. -/
lemma _root_.Matrix.PosSemidef.trace_re_nonneg {n : ℕ}
    {A : Op n} (hA : A.PosSemidef) : 0 ≤ A.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hi : 0 ≤ (A i i : ℂ) := hA.diag_nonneg
  rw [Complex.nonneg_iff] at hi
  exact hi.1

/-- The real trace of a PSD matrix times a nonnegative real diagonal is nonnegative. -/
lemma trace_mul_diagonal_nonneg {n : ℕ} (M : Op n) (hM : M.PosSemidef)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ (M * diagonal (fun i => (d i : ℂ))).trace.re := by
  have h_trace : (M * diagonal (fun i => (d i : ℂ))).trace = ∑ i, M i i * (d i : ℂ) := by
    simp only [trace, diag, mul_apply, diagonal_apply, mul_ite, mul_zero]
    congr 1
    ext i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [h_trace, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (psd_diag_re_nonneg M hM i) (hd i)

/-- Cyclically move a trailing conjugate transpose across a matrix trace. -/
lemma trace_mul_conjTranspose_cycle_re {n : ℕ}
    (A U D : Op n) :
    (A * (U * D * Uᴴ)).trace.re = ((Uᴴ * A * U) * D).trace.re := by
  simpa only [mul_assoc] using congrArg Complex.re (trace_mul_comm Uᴴ (A * U * D)).symm

/-- The real trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_psd_nonneg {n : ℕ} (A B : Op n)
    (hA : Matrix.PosSemidef A) (hB : Matrix.PosSemidef B) :
    0 ≤ (A * B).trace.re := by
  let hBH := hB.isHermitian
  let U : Op n := hBH.eigenvectorUnitary
  let D : Op n := diagonal (RCLike.ofReal ∘ hBH.eigenvalues)
  have hSpec : B = U * D * Uᴴ := by
    have h := hBH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    exact h
  rw [hSpec]
  rw [trace_mul_conjTranspose_cycle_re]
  have hUAU_psd : (Uᴴ * A * U).PosSemidef := hA.conjTranspose_mul_mul_same U
  have hD_eq : D = diagonal (fun i => (hBH.eigenvalues i : ℂ)) := rfl
  rw [hD_eq]
  exact trace_mul_diagonal_nonneg (Uᴴ * A * U) hUAU_psd hBH.eigenvalues hB.eigenvalues_nonneg

/-- The quadratic form is additive under subtraction of operators:
`⟨v|(B - A)|v⟩ = ⟨v|B|v⟩ - ⟨v|A|v⟩`. -/
lemma quadraticForm_sub {n : ℕ} (A B : Op n) (v : Fin n → ℂ) :
    quadraticForm (B - A) v = quadraticForm B v - quadraticForm A v := by
  unfold quadraticForm
  simp only [Matrix.sub_mulVec, dotProduct_sub]

/-- The quadratic form of an adjoint is the conjugate of the original quadratic form. -/
lemma quadraticForm_conjTranspose_eq_star {n : ℕ} (A : Op n) (v : Fin n → ℂ) :
    quadraticForm Aᴴ v = star (quadraticForm A v) := by
  unfold quadraticForm
  simp only [dotProduct, mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul', star_star]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- Taking an adjoint preserves the real part of every quadratic form. -/
lemma quadraticForm_conjTranspose_re {n : ℕ} (A : Op n) (v : Fin n → ℂ) :
    (quadraticForm Aᴴ v).re = (quadraticForm A v).re := by
  rw [quadraticForm_conjTranspose_eq_star]
  exact Complex.conj_re _

/-- If `A` is Hermitian then its quadratic form is real-valued (zero imaginary part). -/
lemma quadraticForm_im_of_isHermitian {n : ℕ} (A : Op n) (hA : A.IsHermitian)
    (v : Fin n → ℂ) : (quadraticForm A v).im = 0 := by
  have hc := quadraticForm_hermitian_conj_eq_self A hA v
  rw [Complex.ext_iff] at hc
  simp only [Complex.conj_re, Complex.conj_im] at hc
  linarith [hc.2]

/-- If `A` and `B` are Hermitian and their real-quadratic-form ordering holds,
then `B - A` is Mathlib-PSD. -/
lemma posSemidef_sub_of_quadraticForm_re_le {n : ℕ} (A B : Op n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (quadraticForm A v).re ≤ (quadraticForm B v).re) :
    Matrix.PosSemidef (B - A) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hB.sub hA, fun v => ?_⟩
  have hqf : star v ⬝ᵥ (B - A).mulVec v = quadraticForm (B - A) v := rfl
  have h_im : (quadraticForm (B - A) v).im = 0 :=
    quadraticForm_im_of_isHermitian _ (hB.sub hA) v
  have h_re : 0 ≤ (quadraticForm (B - A) v).re := by
    rw [quadraticForm_sub]
    simp only [Complex.sub_re]
    linarith [h v]
  rw [hqf, Complex.nonneg_iff]
  exact ⟨h_re, h_im.symm⟩

/-- **PSD criterion via real-valued quadratic form.** An Hermitian operator
whose quadratic form has nonnegative real part on every vector is
positive-semidefinite. -/
lemma posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
    {n : ℕ} {A : Op n} (hA : A.IsHermitian)
    (h : ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm A v).re) :
    A.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hA, fun v => ?_⟩
  have h_im : (quadraticForm A v).im = 0 :=
    quadraticForm_im_of_isHermitian _ hA v
  rw [show star v ⬝ᵥ A.mulVec v = quadraticForm A v from rfl,
      Complex.nonneg_iff]
  exact ⟨h v, h_im.symm⟩

/-- Trace monotonicity for a PSD weight: if `M` is PSD and the Hermitian
operators `A`, `B` satisfy the real-quadratic-form ordering, then
`(M * A).trace.re ≤ (M * B).trace.re`. -/
lemma trace_mul_le_of_quadraticForm_re_le {n : ℕ}
    (M A B : Op n) (hM : Matrix.PosSemidef M)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ v : Fin n → ℂ, (quadraticForm A v).re ≤ (quadraticForm B v).re) :
    (M * A).trace.re ≤ (M * B).trace.re := by
  have h_sub : Matrix.PosSemidef (B - A) :=
    posSemidef_sub_of_quadraticForm_re_le A B hA hB h
  have h_nn : 0 ≤ (M * (B - A)).trace.re :=
    trace_mul_psd_nonneg M (B - A) hM h_sub
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] at h_nn
  exact h_nn

/-! ## The operator-semidefinite order `opLe` -/

/-- The operator-semidefinite ordering on operators: `A ≤_PSD B` iff for every
vector `v`, the real part of the quadratic form of `A` is at most that of `B`.

For Hermitian `A` and `B`, this is equivalent to `B - A` being Mathlib-PSD; see
`opLe.posSemidef_sub`. -/
def opLe {n : ℕ} (A B : Op n) : Prop :=
  ∀ v : Fin n → ℂ, (quadraticForm A v).re ≤ (quadraticForm B v).re

/-- Transitivity of the semidefinite order. -/
lemma opLe_trans {n : ℕ} {A B C : Op n} (hAB : opLe A B) (hBC : opLe B C) : opLe A C :=
  fun v => (hAB v).trans (hBC v)

/-- The semidefinite order is invariant under a dimension cast. -/
theorem opLe_castDim_iff {n m : ℕ} (h : n = m) {A B : Op n} :
    opLe (Op.castDim h A) (Op.castDim h B) ↔ opLe A B := by
  subst h; rfl

/-- A dimension cast preserves the semidefinite order. -/
theorem opLe_castDim {n m : ℕ} (h : n = m) {A B : Op n} (hAB : opLe A B) :
    opLe (Op.castDim h A) (Op.castDim h B) :=
  (opLe_castDim_iff h).2 hAB

/-- Bridge from a PSD difference to the `opLe` ordering. -/
lemma opLe_of_posSemidef_sub {n : ℕ} {A B : Op n}
    (h : (B - A).PosSemidef) : opLe A B := by
  intro v
  have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 v
  rw [Complex.nonneg_iff] at hnn
  have hre := hnn.1
  change 0 ≤ (quadraticForm (B - A) v).re at hre
  rw [quadraticForm_sub, Complex.sub_re, sub_nonneg] at hre
  exact hre

/-- Bridge from the `opLe` predicate to Mathlib's `Matrix.PosSemidef`:
if `A` and `B` are Hermitian and `opLe A B`, then `B - A` is Mathlib-PSD.

This is a direct consequence of `posSemidef_sub_of_quadraticForm_re_le`. -/
lemma opLe.posSemidef_sub {n : ℕ} {A B : Op n}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : opLe A B) :
    Matrix.PosSemidef (B - A) :=
  posSemidef_sub_of_quadraticForm_re_le A B hA hB h

/-- Trace monotonicity via `opLe`: if `M` is Mathlib-PSD, `A` and `B` are
Hermitian, and `opLe A B`, then `(M * A).trace.re ≤ (M * B).trace.re`.

This is the standard PSD-trace-monotonicity fact, restated in terms of the
`opLe` ordering. -/
lemma trace_mul_le_of_opLe {n : ℕ} {M A B : Op n}
    (hM : Matrix.PosSemidef M) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : opLe A B) :
    (M * A).trace.re ≤ (M * B).trace.re :=
  trace_mul_le_of_quadraticForm_re_le M A B hM hA hB h

/-! ### Löwner-order support containment

A fundamental fact of the operator-semidefinite order, currently absent from the
library: a positive-semidefinite operator dominated in the Löwner order has its
support contained in the dominating operator's support.  Equivalently, every vector
annihilated by `B` is annihilated by the smaller PSD operator `A`.  These are the
exact, no-approximation primitives behind any "no orthogonal leak" / range-containment
argument (e.g. the CKR de Finetti reference: the lifted source block lives entirely
inside the support of the correlated marginal). -/

/-- **Löwner domination contains the support: pointwise kernel form.**

If `A` is positive semidefinite and `opLe A B` (i.e. `A ⪯ B`), then every vector in
the kernel of `B` lies in the kernel of `A`: `B *ᵥ v = 0 → A *ᵥ v = 0`.

Note `B` itself need not be PSD; only the Löwner bound `A ⪯ B` and the
positive-semidefiniteness of the smaller operator `A` are used.  The proof is the exact
spectral squeeze: `B *ᵥ v = 0` forces `⟨v|B|v⟩ = 0`, so `0 ≤ ⟨v|A|v⟩ ≤ ⟨v|B|v⟩ = 0`
gives `⟨v|A|v⟩ = 0`, and a PSD operator with vanishing quadratic form annihilates `v`
(`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`). -/
lemma opLe_mulVec_eq_zero_of_psd {n : ℕ} {A B : Op n}
    (hA : A.PosSemidef) (hAB : opLe A B)
    {v : Fin n → ℂ} (hv : B.mulVec v = 0) : A.mulVec v = 0 := by
  have hqB : (quadraticForm B v).re = 0 := by simp [quadraticForm, hv]
  have hAle : (quadraticForm A v).re ≤ 0 := by have := hAB v; rwa [hqB] at this
  have hAge : 0 ≤ (quadraticForm A v).re := posSemidef_re_quadraticForm_nonneg hA v
  have hAre : (quadraticForm A v).re = 0 := le_antisymm hAle hAge
  have hAim : (quadraticForm A v).im = 0 := quadraticForm_im_of_isHermitian A hA.isHermitian v
  exact (hA.dotProduct_mulVec_zero_iff v).mp (Complex.ext hAre hAim)

/-- **Löwner domination contains the support: kernel-submodule form.**

The submodule version of `opLe_mulVec_eq_zero_of_psd`: for `A` positive semidefinite
with `A ⪯ B`, the kernel of the linear map `B.mulVecLin` is contained in the kernel of
`A.mulVecLin`.  Since the support (range) of a Hermitian operator is the orthogonal
complement of its kernel, this is exactly the statement `support A ⊆ support B`: the
range of the smaller operator is contained in the range of the dominating one, with no
orthogonal leak. -/
lemma opLe_ker_le_of_psd {n : ℕ} {A B : Op n}
    (hA : A.PosSemidef) (hAB : opLe A B) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  exact opLe_mulVec_eq_zero_of_psd hA hAB hv

/-- **Löwner domination contains the support: right-annihilator form.**

If `A` is positive semidefinite with `A ⪯ B`, then every matrix annihilated by `B` from the
right is annihilated by `A`: `B * M = 0 → A * M = 0`, for `M` of arbitrary — in particular
rectangular, possibly empty — column shape.  This is `opLe_mulVec_eq_zero_of_psd` applied to
each column of `M`.  As with the vector form, `B` itself need not be positive semidefinite. -/
lemma opLe_mul_right_eq_zero_of_psd {n m : ℕ} {A B : Op n}
    (hA : A.PosSemidef) (hAB : opLe A B)
    {M : Matrix (Fin n) (Fin m) ℂ} (hM : B * M = 0) : A * M = 0 := by
  ext i j
  have hcol : B.mulVec (M.mulVec (Pi.single j 1)) = 0 := by
    rw [Matrix.mulVec_mulVec, hM, Matrix.zero_mulVec]
  have h := congrFun (opLe_mulVec_eq_zero_of_psd hA hAB hcol) i
  rw [Matrix.mulVec_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

/-- **Löwner domination contains the support: left-annihilator form.**

The adjoint of `opLe_mul_right_eq_zero_of_psd`: if `A` is positive semidefinite with
`A ⪯ B`, then every matrix annihilated by `B` from the left is annihilated by `A`,
`M * B = 0 → M * A = 0`. The real quadratic-form order is invariant under taking the
adjoint of its right argument, so `B` need not be Hermitian. -/
lemma opLe_mul_left_eq_zero_of_psd {n m : ℕ} {A B : Op n}
    (hA : A.PosSemidef) (hAB : opLe A B)
    {M : Matrix (Fin m) (Fin n) ℂ} (hM : M * B = 0) : M * A = 0 := by
  have hAB' : opLe A Bᴴ := by
    intro v
    rw [quadraticForm_conjTranspose_re]
    exact hAB v
  have hMB : Bᴴ * Mᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hM
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] using h
  have hright := opLe_mul_right_eq_zero_of_psd hA hAB' hMB
  have h := congrArg Matrix.conjTranspose hright
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.isHermitian.eq, Matrix.conjTranspose_zero] using h

end Quantum.Operators

/-! ## Tensor-product monotonicity for `opLe` -/

namespace Quantum.TensorProducts

open Quantum.Operators
open scoped ComplexOrder MatrixOrder TensorProduct Kronecker

/-- Combined two-sided scalar multiplication on a tensor product. -/
lemma Op.smul_tensor_smul {n m : ℕ} (c d : ℂ) (A : Op n) (B : Op m) :
    ((c • A) ⊗ (d • B) : Op (n * m)) = (c * d) • (A ⊗ B) := by
  rw [Op.tensor_smul_left, Op.tensor_smul_right, smul_smul]

/-- Tensor distributes over subtraction in the left factor. -/
lemma Op.tensor_sub_left {n m : ℕ} (A B : Op n) (C : Op m) :
    ((A - B) ⊗ C : Op (n * m)) = A ⊗ C - B ⊗ C := by
  have h : ((A - B) + B) ⊗ C = (A - B) ⊗ C + B ⊗ C :=
    Op.tensor_add_left (A - B) B C
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- Tensor distributes over subtraction in the right factor. -/
lemma Op.tensor_sub_right {n m : ℕ} (A : Op n) (B C : Op m) :
    (A ⊗ (B - C) : Op (n * m)) = A ⊗ B - A ⊗ C := by
  have h : A ⊗ ((B - C) + C) = A ⊗ (B - C) + A ⊗ C :=
    Op.tensor_add_right A (B - C) C
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- Tensor of two PSD operators is PSD as a Mathlib matrix after reindexing. -/
lemma Op.tensor_posSemidef_mathlib {n m : ℕ} {A : Op n} {B : Op m}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ B).PosSemidef := by
  have hKron : (A ⊗ₖ B).PosSemidef := hA.kronecker hB
  unfold Op.tensor
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hKron

end Quantum.TensorProducts

namespace Quantum.Operators

open Matrix Quantum.TensorProducts
open scoped ComplexOrder MatrixOrder TensorProduct Kronecker

/-- Binary tensor monotonicity for `opLe`. If both right-hand sides are PSD,
the left factors are Hermitian/PSD as needed to form PSD differences, and both
factor inequalities hold, then the tensor product inequality holds. -/
lemma opLe_tensor_psd {n m : ℕ}
    {A B : Op n} {C D : Op m}
    (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.IsHermitian)
    (hAB : opLe A B) (hCD : opLe C D) :
    opLe (A ⊗ C) (B ⊗ D) := by
  apply opLe_of_posSemidef_sub
  have hBA : (B - A).PosSemidef := opLe.posSemidef_sub hA hB.isHermitian hAB
  have hDC : (D - C).PosSemidef := opLe.posSemidef_sub hC.isHermitian hD hCD
  have h1 : (B ⊗ (D - C)).PosSemidef :=
    Quantum.TensorProducts.Op.tensor_posSemidef_mathlib hB hDC
  have h2 : ((B - A) ⊗ C).PosSemidef :=
    Quantum.TensorProducts.Op.tensor_posSemidef_mathlib hBA hC
  have heq : (B ⊗ D) - (A ⊗ C) = (B ⊗ (D - C)) + ((B - A) ⊗ C) := by
    rw [Quantum.TensorProducts.Op.tensor_sub_right,
      Quantum.TensorProducts.Op.tensor_sub_left]
    abel
  rw [heq]
  exact h1.add h2

/-- The quadratic form is linear in the operator under complex scalar multiplication:
`⟨v | (c • A) | v⟩ = c * ⟨v | A | v⟩`. -/
lemma quadraticForm_smul {n : ℕ} (c : ℂ) (A : Op n) (v : Fin n → ℂ) :
    quadraticForm (c • A) v = c * quadraticForm A v := by
  unfold quadraticForm
  rw [Matrix.smul_mulVec c A v, dotProduct_smul]
  rfl

/-- The real-scalar reading of `quadraticForm_smul`:
`⟨v | (t • A) | v⟩ = t · ⟨v | A | v⟩` for a real `t`. -/
lemma quadraticForm_ofReal_smul {n : ℕ} (t : ℝ) (A : Op n) (v : Fin n → ℂ) :
    quadraticForm ((Complex.ofReal t) • A) v = (Complex.ofReal t) * quadraticForm A v :=
  quadraticForm_smul (Complex.ofReal t) A v

/-- Scaling by a nonnegative real preserves the semidefinite order:
`t ≥ 0` and `A ⪯ B` imply `(t : ℂ) • A ⪯ (t : ℂ) • B`. -/
lemma opLe_smul_nonneg {n : ℕ} {A B : Op n} {t : ℝ} (ht : 0 ≤ t) (hAB : opLe A B) :
    opLe ((Complex.ofReal t) • A) ((Complex.ofReal t) • B) := by
  intro v
  rw [quadraticForm_ofReal_smul, quadraticForm_ofReal_smul, Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left (hAB v) ht

/-- The component of a vector on `E ⊗ R` supported on one fixed `R` index. -/
private def referenceBlockSupport {dE dR : ℕ} (r : Fin dR)
    (v : Fin (dE * dR) → ℂ) : Fin (dE * dR) → ℂ :=
  fun p => if (finProdFinEquiv.symm p).2 = r then v p else 0

/-- Insert an `E`-vector into one fixed `R` block of `E ⊗ R`. -/
private def referenceBlockInsert {dE dR : ℕ} (r : Fin dR)
    (x : Fin dE → ℂ) : Fin (dE * dR) → ℂ :=
  fun p => if (finProdFinEquiv.symm p).2 = r
    then x (finProdFinEquiv.symm p).1 else 0

@[simp] private lemma referenceBlockInsert_block_eq_referenceBlockSupport
    {dE dR : ℕ} (r : Fin dR) (v : Fin (dE * dR) → ℂ) :
    referenceBlockInsert r (fun i : Fin dE => v (finProdFinEquiv (i, r))) =
      referenceBlockSupport r v := by
  funext p
  unfold referenceBlockInsert referenceBlockSupport
  split_ifs with hp
  · exact congrArg v (by
      rw [← hp]
      exact Equiv.apply_symm_apply finProdFinEquiv p)
  · rfl

private lemma tensor_right_one_mulVec_apply {dE dR : ℕ} (B : Op dE)
    (v : Fin (dE * dR) → ℂ) (i : Fin dE) (r : Fin dR) :
    (Quantum.TensorProducts.Op.tensor B (1 : Op dR)).mulVec v
        (finProdFinEquiv (i, r)) =
      ∑ j : Fin dE, B i j * v (finProdFinEquiv (j, r)) := by
  simp only [Matrix.mulVec, dotProduct, Quantum.TensorProducts.Op.tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  congr 1
  ext j
  simp only [Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]

private lemma quadraticForm_tensor_right_one_eq_sum_blocks
    {dE dR : ℕ} (B : Op dE) (v : Fin (dE * dR) → ℂ) :
    (quadraticForm (Quantum.TensorProducts.Op.tensor B (1 : Op dR)) v).re =
      ∑ r : Fin dR, (quadraticForm B
        (fun i : Fin dE => v (finProdFinEquiv (i, r)))).re := by
  unfold quadraticForm dotProduct
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Pi.star_apply, tensor_right_one_mulVec_apply]
  rw [Finset.sum_comm]
  simp [Matrix.mulVec, dotProduct]

/-- Tensoring on the right with the identity preserves the quadratic-form
operator order. -/
lemma opLe_tensor_right_one {dE dR : ℕ} {A B : Op dE}
    (hAB : opLe A B) :
    opLe (Quantum.TensorProducts.Op.tensor A (1 : Op dR))
      (Quantum.TensorProducts.Op.tensor B (1 : Op dR)) := by
  intro v
  rw [quadraticForm_tensor_right_one_eq_sum_blocks A v,
    quadraticForm_tensor_right_one_eq_sum_blocks B v]
  exact Finset.sum_le_sum fun r _ =>
    hAB (fun i : Fin dE => v (finProdFinEquiv (i, r)))

private lemma quadraticForm_partialTraceB_eq_sum_referenceBlockInsert
    {dE dR : ℕ} (A : Op (dE * dR)) (x : Fin dE → ℂ) :
    (quadraticForm (Quantum.TensorProducts.partialTraceB A) x).re =
      ∑ k : Fin dR, (quadraticForm A (referenceBlockInsert k x)).re := by
  unfold quadraticForm Quantum.TensorProducts.partialTraceB dotProduct
  simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Pi.star_apply]
  let y : Fin dR → (Fin (dE * dR) → ℂ) := fun k => referenceBlockInsert k x
  have h_expand : (∑ i : Fin dE, star (x i) *
      ∑ j : Fin dE, (∑ k : Fin dR,
        A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))) * x j) =
      ∑ k : Fin dR, (∑ i : Fin dE, ∑ j : Fin dE,
        star (x i) * A (finProdFinEquiv (i, k))
          (finProdFinEquiv (j, k)) * x j) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [h_expand, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h_eq : (∑ i : Fin dE, ∑ j : Fin dE,
      star (x i) * A (finProdFinEquiv (i, k))
        (finProdFinEquiv (j, k)) * x j) =
      quadraticForm A (y k) := by
    unfold quadraticForm dotProduct Matrix.mulVec y referenceBlockInsert
    simp only [Pi.star_apply, star_ite_zero]
    symm
    calc
      ∑ p, (if (finProdFinEquiv.symm p).2 = k
             then star (x (finProdFinEquiv.symm p).1) else 0) *
          ∑ q, A p q * (if (finProdFinEquiv.symm q).2 = k
             then x (finProdFinEquiv.symm q).1 else 0)
          = ∑ il : Fin dE × Fin dR,
              (if il.2 = k then star (x il.1) else 0) *
              ∑ jl : Fin dE × Fin dR,
                A (finProdFinEquiv il) (finProdFinEquiv jl) *
                  (if jl.2 = k then x jl.1 else 0) := by
            trans ∑ p, (if (finProdFinEquiv.symm p).2 = k
                          then star (x (finProdFinEquiv.symm p).1) else 0) *
                ∑ jl : Fin dE × Fin dR, A p (finProdFinEquiv jl) *
                  (if jl.2 = k then x jl.1 else 0)
            · congr 1; ext p; congr 1
              apply Fintype.sum_equiv finProdFinEquiv.symm
              intro q
              simp only [Equiv.apply_symm_apply]
            · apply Fintype.sum_equiv finProdFinEquiv.symm
              intro p
              congr 1
              simp only [Equiv.apply_symm_apply]
      _ = ∑ i : Fin dE, ∑ l : Fin dR,
              (if l = k then star (x i) else 0) *
              ∑ j : Fin dE, ∑ l' : Fin dR,
                A (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l')) *
                  (if l' = k then x j else 0) := by
            conv_lhs =>
              rw [Fintype.sum_prod_type]
              arg 2; ext i
              arg 2; ext l; arg 2
              rw [Fintype.sum_prod_type]
      _ = ∑ i : Fin dE, star (x i) *
              ∑ j : Fin dE,
                A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) * x j := by
            congr 1; ext i
            rw [Finset.sum_eq_single k]
            · rw [if_pos rfl]
              congr 1
              congr 1; ext j
              rw [Finset.sum_eq_single k]
              · rw [if_pos rfl]
              · intro l' _ hl'
                rw [if_neg hl', mul_zero]
              · intro hk; exact (hk (Finset.mem_univ k)).elim
            · intro l _ hl
              rw [if_neg hl, zero_mul]
            · intro hk; exact (hk (Finset.mem_univ k)).elim
      _ = ∑ i : Fin dE, ∑ j : Fin dE,
              star (x i) * A (finProdFinEquiv (i, k))
                (finProdFinEquiv (j, k)) * x j := by
            congr 1; ext i
            rw [Finset.mul_sum]
            congr 1; ext j
            ring
  rw [h_eq]
  rfl

/-- Scalar Cauchy estimate for a finite complex sum. -/
private lemma normSq_sum_le_card_mul_sum_normSq
    {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    Complex.normSq (∑ i, f i) ≤
      (Fintype.card ι : ℝ) * ∑ i, Complex.normSq (f i) := by
  have hnorm : ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := by
    simpa using norm_sum_le (Finset.univ : Finset ι) f
  calc
    Complex.normSq (∑ i, f i)
        = ‖∑ i, f i‖ ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
    _ ≤ (∑ i, ‖f i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ i : ι, (1 : ℝ) ^ 2) * ∑ i, ‖f i‖ ^ 2 := by
          simpa using
            (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
              (fun _ : ι => (1 : ℝ)) (fun i => ‖f i‖))
    _ = (Fintype.card ι : ℝ) * ∑ i, Complex.normSq (f i) := by
          simp [Complex.normSq_eq_norm_sq]

/-- PSD Cauchy/pinching estimate for a finite sum of test vectors. -/
lemma quadraticForm_sum_le_card_mul_sum_quadraticForm
    {ι : Type*} [Fintype ι] {n : ℕ} {A : Op n}
    (hA : A.PosSemidef) (z : ι → Fin n → ℂ) :
    (quadraticForm A (∑ i, z i)).re ≤
      (Fintype.card ι : ℝ) * ∑ i, (quadraticForm A (z i)).re := by
  let R : Op n := CFC.sqrt A
  have hR_psd : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hR_herm : R.IsHermitian := hR_psd.isHermitian
  have hR_sq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hquad : ∀ x : Fin n → ℂ,
      quadraticForm A x = star (R.mulVec x) ⬝ᵥ R.mulVec x := by
    intro x
    rw [← hR_sq]
    unfold quadraticForm
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [Matrix.star_mulVec, hR_herm]
  have hq_re : ∀ x : Fin n → ℂ,
      (quadraticForm A x).re = ∑ k, Complex.normSq ((R.mulVec x) k) := by
    intro x
    rw [hquad x]
    unfold dotProduct
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (star ((R.mulVec x) k) * (R.mulVec x) k).re =
      Complex.normSq ((R.mulVec x) k)
    rw [show star ((R.mulVec x) k) =
      (starRingEnd ℂ) ((R.mulVec x) k) from rfl]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hmul_sum : R.mulVec (∑ i, z i) = ∑ i, R.mulVec (z i) := by
    simpa using Matrix.mulVec_sum R (Finset.univ : Finset ι) z
  calc
    (quadraticForm A (∑ i, z i)).re
        = ∑ k, Complex.normSq ((R.mulVec (∑ i, z i)) k) := hq_re _
    _ = ∑ k, Complex.normSq ((∑ i, R.mulVec (z i)) k) := by
          rw [hmul_sum]
    _ = ∑ k, Complex.normSq (∑ i, (R.mulVec (z i)) k) := by
          simp
    _ ≤ ∑ k, (Fintype.card ι : ℝ) *
          ∑ i, Complex.normSq ((R.mulVec (z i)) k) := by
          apply Finset.sum_le_sum
          intro k _
          exact normSq_sum_le_card_mul_sum_normSq
            (fun i : ι => (R.mulVec (z i)) k)
    _ = (Fintype.card ι : ℝ) *
          ∑ i, ∑ k, Complex.normSq ((R.mulVec (z i)) k) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (Fintype.card ι : ℝ) * ∑ i, (quadraticForm A (z i)).re := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [hq_re]

/-- The block-diagonal quadratic form kept by `referenceBlockSupport` is dominated
by the partial trace tensored with the reference identity. -/
lemma sum_quadraticForm_referenceBlockSupport_le_partialTraceB_tensor_one
    {dE dR : ℕ} [NeZero dE] [NeZero dR] {A : Op (dE * dR)}
    (hA : A.PosSemidef) (v : Fin (dE * dR) → ℂ) :
    (∑ r : Fin dR, (quadraticForm A (referenceBlockSupport r v)).re) ≤
      (quadraticForm
        (Quantum.TensorProducts.Op.tensor
          (Quantum.TensorProducts.partialTraceB A) (1 : Op dR)) v).re := by
  rw [quadraticForm_tensor_right_one_eq_sum_blocks]
  apply Finset.sum_le_sum
  intro r _
  let x : Fin dE → ℂ := fun i => v (finProdFinEquiv (i, r))
  change (quadraticForm A (referenceBlockSupport r v)).re ≤
    (quadraticForm (Quantum.TensorProducts.partialTraceB A) x).re
  rw [quadraticForm_partialTraceB_eq_sum_referenceBlockInsert]
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin dR)),
      0 ≤ (quadraticForm A (referenceBlockInsert k x)).re := by
    intro k _
    have hnn := hA.dotProduct_mulVec_nonneg (referenceBlockInsert k x)
    rw [Complex.nonneg_iff] at hnn
    simpa [quadraticForm] using hnn.1
  have hsingle :
      (quadraticForm A (referenceBlockInsert r x)).re ≤
        ∑ k : Fin dR, (quadraticForm A (referenceBlockInsert k x)).re := by
    simpa using Finset.single_le_sum hnonneg (Finset.mem_univ r)
  simpa [x] using hsingle

/-- A positive operator on `E ⊗ R` is dominated by `dim R` times its
`R`-partial trace tensored with the identity on `R`. -/
theorem opLe_le_card_smul_partialTraceB_tensor_one
    {dE dR : ℕ} [NeZero dE] [NeZero dR] {A : Op (dE * dR)}
    (hA : A.PosSemidef) :
    opLe A
      ((Complex.ofReal (dR : ℝ)) •
        (Quantum.TensorProducts.Op.tensor
          (Quantum.TensorProducts.partialTraceB A) (1 : Op dR))) := by
  intro v
  let z : Fin dR → Fin (dE * dR) → ℂ := fun r => referenceBlockSupport r v
  have hv : (∑ r : Fin dR, z r) = v := by
    funext p
    simp only [z, referenceBlockSupport, Finset.sum_apply,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hsum :=
    quadraticForm_sum_le_card_mul_sum_quadraticForm (A := A) hA z
  have hblock :=
    sum_quadraticForm_referenceBlockSupport_le_partialTraceB_tensor_one
      (A := A) hA v
  have hcard_nonneg : 0 ≤ (dR : ℝ) := by exact_mod_cast Nat.zero_le dR
  have hscalar :
      (quadraticForm
        ((Complex.ofReal (dR : ℝ)) •
          (Quantum.TensorProducts.Op.tensor
            (Quantum.TensorProducts.partialTraceB A) (1 : Op dR))) v).re =
        (dR : ℝ) *
          (quadraticForm
            (Quantum.TensorProducts.Op.tensor
              (Quantum.TensorProducts.partialTraceB A) (1 : Op dR)) v).re := by
    rw [quadraticForm_smul, Complex.mul_re]
    simp
  calc
    (quadraticForm A v).re
        = (quadraticForm A (∑ r : Fin dR, z r)).re := by rw [hv]
    _ ≤ (Fintype.card (Fin dR) : ℝ) *
          ∑ r : Fin dR, (quadraticForm A (z r)).re := hsum
    _ = (dR : ℝ) *
          ∑ r : Fin dR, (quadraticForm A (referenceBlockSupport r v)).re := by
          simp [z]
    _ ≤ (dR : ℝ) *
          (quadraticForm
            (Quantum.TensorProducts.Op.tensor
              (Quantum.TensorProducts.partialTraceB A) (1 : Op dR)) v).re :=
          mul_le_mul_of_nonneg_left hblock hcard_nonneg
    _ = (quadraticForm
          ((Complex.ofReal (dR : ℝ)) •
            (Quantum.TensorProducts.Op.tensor
              (Quantum.TensorProducts.partialTraceB A) (1 : Op dR))) v).re :=
          hscalar.symm

/-- Löwner-monotonicity of the partial trace over `B`.

If `opLe A B` on `E ⊗ R`, then `opLe (partialTraceB A) (partialTraceB B)` on `E`.

Proof: `opLe` is the pointwise quadratic-form inequality; rewriting both sides with
`quadraticForm_partialTraceB_re_eq_sum` turns each side into a finite sum over the
`R`-blocks of the original quadratic form, and `Finset.sum_le_sum` closes it
termwise from `h`.  This is the partial-trace analogue of the standard
operator-monotonicity of a completely positive trace-preserving map. -/
theorem partialTraceB_opLe_of_opLe {dE dR : ℕ} {A B : Op (dE * dR)}
    (h : opLe A B) :
    opLe (Quantum.TensorProducts.partialTraceB A)
      (Quantum.TensorProducts.partialTraceB B) := by
  intro v
  rw [quadraticForm_partialTraceB_re_eq_sum, quadraticForm_partialTraceB_re_eq_sum]
  exact Finset.sum_le_sum (fun k _ => h (rightBlockVector k v))

/-- **An identity floor pushes through the partial trace.**  If `c·1_{E⊗R} ⪯ X` then
`(c · dR)·1_E ⪯ Tr_R X`, because `Tr_R 1_{E⊗R} = dR · 1_E`
(`Quantum.TensorProducts.partialTraceB_one`). -/
theorem partialTraceB_opLe_of_smul_one_opLe {dE dR : ℕ} {X : Op (dE * dR)} {c : ℂ}
    (h : opLe (c • (1 : Op (dE * dR))) X) :
    opLe ((c * (dR : ℂ)) • (1 : Op dE)) (Quantum.TensorProducts.partialTraceB X) := by
  have hmono := partialTraceB_opLe_of_opLe h
  rwa [Quantum.TensorProducts.partialTraceB_smul, Quantum.TensorProducts.partialTraceB_one,
    smul_smul] at hmono

/-- **Marginal domination from an identity floor and a feasibility bound.**

If the joint reference is floored by the identity, `c·1_{E⊗R} ⪯ σ_ER` with `c > 0`,
and `ρ` on `E` is feasible at scale `s`, `ρ ⪯ s·1_E` with `s ≥ 0`, then `ρ` is
dominated by the *marginal* reference at scale `s / (c · dR)`:

`ρ ⪯ (s / (c · dR)) · Tr_R σ_ER`.

The floor is transported through `Tr_R` by `partialTraceB_opLe_of_smul_one_opLe`,
rescaled by `opLe_smul_nonneg`, and chained with feasibility by `opLe_trans`.  No
relation between `ρ` and `σ_ER` is assumed, and no dimension-dependent constant is
hidden: the scale is exactly `s / (c · dR)`. -/
theorem opLe_smul_partialTraceB_of_identityFloor {dE dR : ℕ}
    (sigmaER : Op (dE * dR)) {c s : ℝ} (hc : 0 < c) (hdR : 0 < dR)
    (hfloor : opLe (Complex.ofReal c • (1 : Op (dE * dR))) sigmaER)
    {rho : Op dE} (hs : 0 ≤ s)
    (hfeas : opLe rho (Complex.ofReal s • (1 : Op dE))) :
    opLe rho (Complex.ofReal (s / (c * dR)) •
      Quantum.TensorProducts.partialTraceB sigmaER) := by
  have hdRR : (0 : ℝ) < (dR : ℝ) := by exact_mod_cast hdR
  set t : ℝ := s / (c * dR) with ht_def
  have ht : 0 ≤ t := by rw [ht_def]; positivity
  -- Push the floor through the partial trace, then rescale it by `t ≥ 0`.
  have hmarg : opLe ((Complex.ofReal c * (dR : ℂ)) • (1 : Op dE))
      (Quantum.TensorProducts.partialTraceB sigmaER) :=
    partialTraceB_opLe_of_smul_one_opLe hfloor
  have hscaled := opLe_smul_nonneg ht hmarg
  -- `t · (c · dR) = s`, so the scaled floor is exactly the feasibility scale.
  have hcoeff : Complex.ofReal t * (Complex.ofReal c * (dR : ℂ)) = Complex.ofReal s := by
    have hcd : (c * dR : ℝ) ≠ 0 := by positivity
    rw [show ((dR : ℕ) : ℂ) = ((dR : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ht_def, div_mul_cancel₀ s hcd]
  rw [smul_smul, hcoeff] at hscaled
  exact opLe_trans hfeas hscaled

/-- Change-of-test-vector identity for the sandwich `S * X * S` when `S` is
Hermitian (self-adjoint):

  `⟨v | S X S | v⟩ = ⟨S v | X | S v⟩`.

No hypothesis on `X` is required. -/
lemma quadraticForm_sandwich_self_of_isHermitian {n : ℕ} {S : Op n}
    (hS : S.IsHermitian) (X : Op n) (v : Fin n → ℂ) :
    quadraticForm (S * X * S) v = quadraticForm X (S.mulVec v) := by
  unfold quadraticForm
  -- (S * X * S).mulVec v = S.mulVec (X.mulVec (S.mulVec v))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  -- goal: vecMul (star v) S ⬝ᵥ X.mulVec (S.mulVec v)
  --     = star (S.mulVec v) ⬝ᵥ X.mulVec (S.mulVec v)
  rw [Matrix.star_mulVec, hS]

/-! ## Sandwich monotonicity for `opLe` -/

/-- Sandwich monotonicity of `opLe` by a Hermitian operator: if `S` is Hermitian
and `opLe A B`, then `opLe (S * A * S) (S * B * S)`.

Proof: change of test vector via `quadraticForm_sandwich_self_of_isHermitian`. -/
lemma opLe_sandwich_of_isHermitian {n : ℕ} {S : Op n}
    (hS : S.IsHermitian) {A B : Op n} (h : opLe A B) :
    opLe (S * A * S) (S * B * S) := by
  intro v
  rw [quadraticForm_sandwich_self_of_isHermitian hS A v,
      quadraticForm_sandwich_self_of_isHermitian hS B v]
  exact h (S.mulVec v)

/-- **Spectral inequality (PSD form):** if `A` is positive semidefinite and
`opLe A (t • 1)`, then `opLe (A * A) (t • A)`.

Proof: write `A = √A · √A` (CFC square root); the sandwich monotonicity
`opLe_sandwich_of_isHermitian` applied with `S = √A` gives
`opLe (√A · A · √A) (√A · (t • 1) · √A)`. The LHS is `A · A` and the RHS
simplifies to `t • A` via `mul_smul_comm`/`smul_mul_assoc` and
`CFC.sqrt_mul_sqrt_self`. No sign hypothesis on `t` is needed: the proof is
purely algebraic, manipulating `Complex.ofReal t` only via smul-commutativity. -/
lemma sq_opLe_smul_of_opLe_smul_one {n : ℕ}
    {A : Op n} (hA : A.PosSemidef) {t : ℝ}
    (h : opLe A (Complex.ofReal t • (1 : Op n))) :
    opLe (A * A) (Complex.ofReal t • A) := by
  set R : Op n := CFC.sqrt A
  have hR_psd : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hR_herm : R.IsHermitian := hR_psd.isHermitian
  have hR_sq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hsand := opLe_sandwich_of_isHermitian hR_herm h
  -- hsand : opLe (R * A * R) (R * (Complex.ofReal t • 1) * R)
  -- Rewrite the LHS to A * A
  have hLHS : R * A * R = A * A := by
    calc R * A * R
        = R * (R * R) * R := by rw [hR_sq]
      _ = (R * R) * (R * R) := by simp only [Matrix.mul_assoc]
      _ = A * A := by rw [hR_sq]
  -- Rewrite the RHS to Complex.ofReal t • A
  have hRHS : R * (Complex.ofReal t • (1 : Op n)) * R = Complex.ofReal t • A := by
    calc R * (Complex.ofReal t • (1 : Op n)) * R
        = (Complex.ofReal t • (R * (1 : Op n))) * R := by
            rw [mul_smul_comm]
      _ = Complex.ofReal t • ((R * (1 : Op n)) * R) := by
            rw [smul_mul_assoc]
      _ = Complex.ofReal t • (R * R) := by rw [Matrix.mul_one]
      _ = Complex.ofReal t • A := by rw [hR_sq]
  rw [hLHS, hRHS] at hsand
  exact hsand

/-- **Scalar trace inequality.** If `A` is positive semidefinite and
`opLe A (t • 1)`, then `(A * A).trace.re ≤ t * A.trace.re`.

Proof: combine `sq_opLe_smul_of_opLe_smul_one` with
`trace_mul_le_of_opLe` (PSD weight `M = 1`), and unwrap the
`Complex.ofReal t • A` real-trace coercion via `Complex.smul_re`.
No sign hypothesis on `t` is needed. -/
lemma trace_sq_le_smul_trace_of_opLe_smul_one {n : ℕ}
    {A : Op n} (hA : A.PosSemidef) {t : ℝ}
    (h : opLe A (Complex.ofReal t • (1 : Op n))) :
    (A * A).trace.re ≤ t * A.trace.re := by
  have h_sq := sq_opLe_smul_of_opLe_smul_one hA h
  -- h_sq : opLe (A * A) (Complex.ofReal t • A)
  have hA_herm : A.IsHermitian := hA.isHermitian
  have hAA_herm : (A * A).IsHermitian := by
    change (A * A)ᴴ = A * A
    rw [Matrix.conjTranspose_mul, hA_herm.eq]
  have hsmul_herm : (Complex.ofReal t • A).IsHermitian := by
    have hsa : IsSelfAdjoint (Complex.ofReal t) := by
      change star (Complex.ofReal t) = Complex.ofReal t
      rw [Complex.star_def, Complex.conj_ofReal]
    exact hsa.smul hA_herm
  have h_trace : ((1 : Op n) * (A * A)).trace.re
      ≤ ((1 : Op n) * (Complex.ofReal t • A)).trace.re :=
    trace_mul_le_of_opLe Matrix.PosSemidef.one hAA_herm hsmul_herm h_sq
  rw [Matrix.one_mul, Matrix.one_mul] at h_trace
  -- h_trace : (A * A).trace.re ≤ (Complex.ofReal t • A).trace.re
  have hRHS : (Complex.ofReal t • A).trace.re = t * A.trace.re := by
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hRHS] at h_trace
  exact h_trace

/-- **Kernel inclusion from Löwner domination.** If `A` is positive semidefinite,
`B` is Hermitian, `A ≼ c • B` in the operator order, and a Hermitian `Q` satisfies
`B * Q = 0`, then `A * Q = 0`.

Mathematically: `0 ≼ A ≼ c • B` forces `ker B ⊆ ker A`; applied with `Q` a
projector onto a kernel subspace of `B`, the kernel of `A` swallows it. The proof
sandwiches the domination by `Q`, collapses the right-hand side to `0` using
`B * Q = 0`, and uses a Gram/sqrt argument (`Q A Q = 0 ⟹ √A · Q = 0 ⟹ A Q = 0`). -/
lemma mul_eq_zero_of_opLe_smul {n : ℕ} {A B Q : Op n} {c : ℝ}
    (hA : A.PosSemidef) (hB : B.IsHermitian) (hQ : Q.IsHermitian)
    (hle : opLe A ((c : ℂ) • B)) (hBQ : B * Q = 0) :
    A * Q = 0 := by
  -- (1) `Q * B = 0` by taking adjoints of `B * Q = 0`.
  have hQB : Q * B = 0 := by
    have h := congrArg Matrix.conjTranspose hBQ
    rwa [Matrix.conjTranspose_mul, hB, hQ, Matrix.conjTranspose_zero] at h
  -- (2) Sandwich the domination by `Q`; the right-hand side collapses to `0`.
  have hsand := opLe_sandwich_of_isHermitian hQ hle
  have hrhs : Q * ((c : ℂ) • B) * Q = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, hQB, Matrix.zero_mul, smul_zero]
  rw [hrhs] at hsand
  -- (3) `Q * A * Q` is PSD and `≼ 0`, hence has zero trace, hence is `0`.
  have hQAQ_psd : (Q * A * Q).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same Q
    rwa [hQ] at h
  have hneg : (0 - Q * A * Q).PosSemidef :=
    opLe.posSemidef_sub hQAQ_psd.isHermitian Matrix.isHermitian_zero hsand
  have htr0 : (Q * A * Q).trace = 0 := by
    have h1 : 0 ≤ (Q * A * Q).trace.re := hQAQ_psd.trace_re_nonneg
    have h2 : 0 ≤ (0 - Q * A * Q).trace.re := hneg.trace_re_nonneg
    rw [Matrix.trace_sub, Matrix.trace_zero, Complex.sub_re, Complex.zero_re,
      zero_sub, neg_nonneg] at h2
    exact Complex.ext (le_antisymm h2 h1) (hQAQ_psd.trace_nonneg.2).symm
  have hQAQ0 : Q * A * Q = 0 := hQAQ_psd.trace_eq_zero_iff.mp htr0
  -- (4) Gram/sqrt argument: `√A · Q = 0`, hence `A · Q = 0`.
  set R : Op n := CFC.sqrt A with hRdef
  have hR_psd : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hR_herm : R.IsHermitian := hR_psd.isHermitian
  have hR_sq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hGram : (R * Q)ᴴ * (R * Q) = 0 := by
    rw [Matrix.conjTranspose_mul, hR_herm, hQ, mul_assoc, ← mul_assoc R R Q,
      hR_sq, ← mul_assoc]
    exact hQAQ0
  have hRQ : R * Q = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hGram
  calc A * Q = R * R * Q := by rw [hR_sq]
    _ = R * (R * Q) := by rw [mul_assoc]
    _ = 0 := by rw [hRQ, Matrix.mul_zero]

/-! ## Weyl-block assembly for the operator-semidefinite order

Reusable spectral infrastructure: a Löwner-order analogue of the Weyl 2×2 block bound
`‖[[X,Y],[Yᴴ,Z]]‖ ≤ max(‖X‖,‖Z‖) + ‖Y‖`.  Splitting a Hermitian operator `H` along a
Hermitian idempotent `R` and its complement `1 - R`, an upper Löwner bound on the
`R`-block-plus-off-diagonal part together with a `⪯ 0` bound on the complementary block
yields the global Löwner bound `H ⪯ c • 1`. -/

/-- **Additivity of the operator-semidefinite order `opLe`.**  Termwise domination
`A ⪯ C`, `B ⪯ D` gives domination of the sums `A + B ⪯ C + D` (trivial termwise
quadratic-form addition). -/
lemma opLe_add {n : ℕ} {A B C D : Op n}
    (hAC : opLe A C) (hBD : opLe B D) : opLe (A + B) (C + D) := by
  intro v
  simp only [quadraticForm, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  exact add_le_add (hAC v) (hBD v)

/-- The `opLe` order is preserved under finite sums. -/
lemma opLe_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) {f g : ι → Op n}
    (h : ∀ i ∈ s, opLe (f i) (g i)) : opLe (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => intro v; simp [quadraticForm]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact opLe_add (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Reflexivity of the semidefinite order. -/
lemma opLe_refl {n : ℕ} (A : Op n) : opLe A A := fun _ => le_refl _

/-- Scaling a PSD operator by a nondecreasing pair of reals is `opLe`-monotone. -/
lemma opLe_smul_mono_psd {n : ℕ} {a b : ℝ} {M : Op n} (hab : a ≤ b) (hM : M.PosSemidef) :
    opLe (Complex.ofReal a • M) (Complex.ofReal b • M) := by
  apply opLe_of_posSemidef_sub
  rw [show Complex.ofReal b • M - Complex.ofReal a • M = Complex.ofReal (b - a) • M by
    rw [Complex.ofReal_sub, sub_smul]]
  exact hM.smul (Complex.zero_le_real.mpr (by linarith))

/-- Quadratic form is additive over finite sums of operators. -/
lemma quadraticForm_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Op n)
    (v : Fin n → ℂ) : quadraticForm (∑ i ∈ s, f i) v = ∑ i ∈ s, quadraticForm (f i) v := by
  classical
  induction s using Finset.induction with
  | empty => simp [quadraticForm]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [quadraticForm, Matrix.add_mulVec, dotProduct_add]

/-- **Monotonicity of the scalar-identity Löwner floor.**  If `c ≤ c'` then
`c • 1 ⪯ c' • 1`: the quadratic form of `c • 1` is `c · ‖v‖²` with `‖v‖² ≥ 0`, so the
ordering is termwise by `mul_le_mul_of_nonneg_right`. -/
lemma opLe_smul_one_mono {n : ℕ} {c c' : ℝ} (h : c ≤ c') :
    opLe (Complex.ofReal c • (1 : Op n)) (Complex.ofReal c' • (1 : Op n)) := by
  intro v
  rw [quadraticForm_smul, quadraticForm_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_right h
    (posSemidef_re_quadraticForm_nonneg Matrix.PosSemidef.one v)

/-- **Weyl 2×2-block Löwner upper bound (assembly form), reusable spectral infra.**

For a Hermitian operator `H : Op n` and a Hermitian idempotent `R` (`R * R = R`,
`Rᴴ = R`) with complement `R' := 1 - R`, the operator identity

  `H = R*H*R + R'*H*R' + (R*H*R' + R'*H*R)`

decomposes `H` into the two diagonal Weyl blocks plus the Hermitian off-diagonal part.
If the `R`-block grouped with the full off-diagonal is Löwner-bounded by the scalar floor
`c • 1`, and the complementary `R'`-block is `⪯ 0`, then `H ⪯ c • 1`.

This is the Löwner-order specialization of the Weyl 2×2 block norm bound
`‖[[X,Y],[Yᴴ,Z]]‖ ≤ max(‖X‖,‖Z‖) + ‖Y‖` (here the complementary `R'`-block plays the
role of the `≤ 0` block, so only the *upper* off-diagonal bound is needed).  The
complementary projector `R'` is taken as an explicit parameter constrained by
`R + R' = 1`; instantiate with `R' = 1 - R`.  Kept fully general for reuse as spectral
infrastructure. -/
lemma opLe_smul_one_of_block_decomposition {n : ℕ} {H R R' : Op n} {c : ℝ}
    (hRR' : R + R' = 1)
    (hdiag : opLe (R * H * R + (R * H * R' + R' * H * R))
      (Complex.ofReal c • (1 : Op n)))
    (hzero : opLe (R' * H * R') (0 : Op n)) :
    opLe H (Complex.ofReal c • (1 : Op n)) := by
  have hident :
      (R * H * R + (R * H * R' + R' * H * R)) + R' * H * R' = H := by
    have hexp : (R + R') * H * (R + R')
        = (R * H * R + (R * H * R' + R' * H * R)) + R' * H * R' := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      abel
    rw [← hexp, hRR', Matrix.one_mul, Matrix.mul_one]
  have hstep := opLe_add hdiag hzero
  rwa [hident, add_zero] at hstep

end Quantum.Operators
