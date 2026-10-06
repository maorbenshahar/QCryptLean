import QCryptLean.Quantum.Operators.BraKet.Basic

/-!
# Bra-Ket Projectors — rank-one operators, phase uniqueness, trace identities

This file contains identities for rank-one ket-bra operators `ψ * φ.dag`,
including projector positivity, trace formulas, overlap bounds, and the
global-phase uniqueness of normalized kets with equal projectors.

## Main definitions
- `ketbraPosSemidefOp`: rank-one ket-bra projectors bundled as PSD operators.

## Main statements
- `op_mul_ketbra_mul_conjTranspose`: conjugating a ketbra transforms its ket.
- `ket_eq_mod_phase_of_ketbra_eq`: equal normalized rank-one projectors have
  kets equal up to a global phase.
- `stdKet_complete`: `∑ i, |i⟩⟨i| = 1` for the computational basis, with
  `completeness_2` as its qubit instance.
- `stdKet_ketbra_eq_diagonal`, `sum_diagonal_single`,
  `posSemidef_diagonal_single`, `isIdempotentElem_diagonal_single`: the same
  family read as `Matrix.diagonal (Pi.single i 1)`, which is the form the
  entrywise compression lemmas consume.
- `ketbra_posSemidef`: rank-one ket-bra operators are positive semidefinite.
- `trace_ketbra_mul`: trace of a rank-one projector against an operator.
- `trace_cross_ketbra_mul`: trace of a cross rank-one operator against an
  operator.
- `ket_overlap_norm_le_one`: normalized ket overlaps have modulus at most one.
-/

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-- Conjugating a ketbra by an operator is the ketbra of the transformed ket. -/
theorem op_mul_ketbra_mul_conjTranspose {n : ℕ} (A : Op n) (ψ : Ket n) :
    A * (ψ * ψ.dag) * A† = (A * ψ) * (A * ψ).dag := by
  rw [op_mul_ketbra, ketbra_mul_op]
  congr 1
  ext j
  simp only [Ket.dag_vec, bra_mul_op_vec, Matrix.conjTranspose_apply, op_mul_ket_vec,
    Matrix.mulVec, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- The self bra-ket is the coordinate sum `∑ i, ψᵢ* ψᵢ`. -/
lemma Ket.sum_conj_mul_self_eq_dag_mul_self {n : ℕ} (ψ : Ket n) :
    (∑ i, starRingEnd ℂ (ψ.vec i) * ψ.vec i) = ψ.dag * ψ := by
  rw [bra_mul_ket_eq]
  simp only [Ket.dag_vec]

/-- Equal rank-one projectors recover the second ket after multiplying by the
overlap with a normalized representative. -/
lemma ket_mul_overlap_eq_of_ketbra_eq {n : ℕ} (ψ φ : Ket n)
    (hφ : φ.dag * φ = 1) (hket : ψ * ψ.dag = φ * φ.dag) :
    ∀ j : Fin n, ψ.vec j * (ψ.dag * φ) = φ.vec j := by
  intro j
  rw [bra_mul_ket_eq]
  simp only [Ket.dag_vec]
  rw [Finset.mul_sum]
  have h1 : ∀ k : Fin n,
      ψ.vec j * (starRingEnd ℂ (ψ.vec k) * φ.vec k) =
        φ.vec j * (starRingEnd ℂ (φ.vec k) * φ.vec k) := by
    intro k
    calc
      ψ.vec j * (starRingEnd ℂ (ψ.vec k) * φ.vec k)
          = (ψ.vec j * starRingEnd ℂ (ψ.vec k)) * φ.vec k := by ring
      _ = (φ.vec j * starRingEnd ℂ (φ.vec k)) * φ.vec k := by
        have h_entry := congr_fun₂ hket j k
        simp only [ket_mul_bra_apply, Ket.dag_vec] at h_entry
        rw [h_entry]
      _ = φ.vec j * (starRingEnd ℂ (φ.vec k) * φ.vec k) := by ring
  simp_rw [h1, ← Finset.mul_sum]
  rw [Ket.sum_conj_mul_self_eq_dag_mul_self, hφ, mul_one]

/-- Equal rank-one projectors have unit overlap with a normalized representative. -/
lemma conj_overlap_mul_overlap_of_ketbra_eq {n : ℕ} (ψ φ : Ket n)
    (hφ : φ.dag * φ = 1) (hket : ψ * ψ.dag = φ * φ.dag) :
    starRingEnd ℂ (ψ.dag * φ) * (ψ.dag * φ) = 1 := by
  have hψc := ket_mul_overlap_eq_of_ketbra_eq ψ φ hφ hket
  conv_lhs => arg 2; rw [bra_mul_ket_eq]; simp only [Ket.dag_vec]
  rw [Finset.mul_sum]
  simp_rw [show ∀ k : Fin n,
      starRingEnd ℂ (ψ.dag * φ) *
        (starRingEnd ℂ (ψ.vec k) * φ.vec k) =
      starRingEnd ℂ (ψ.vec k * (ψ.dag * φ)) * φ.vec k from
    fun k => by simp only [map_mul]; ring]
  simp_rw [hψc]
  rw [Ket.sum_conj_mul_self_eq_dag_mul_self, hφ]

/-- Equal rank-one projectors identify a normalized representative up to the
conjugate of its overlap with the other ket. -/
lemma ket_eq_conj_overlap_smul_of_ketbra_eq {n : ℕ} (ψ φ : Ket n)
    (hφ : φ.dag * φ = 1) (hket : ψ * ψ.dag = φ * φ.dag) :
    ∀ j : Fin n, ψ.vec j = starRingEnd ℂ (ψ.dag * φ) * φ.vec j := by
  intro j
  set c := ψ.dag * φ with hc
  change ψ.vec j = starRingEnd ℂ c * φ.vec j
  have hψc : ∀ j, ψ.vec j * c = φ.vec j := by
    simpa [hc] using ket_mul_overlap_eq_of_ketbra_eq ψ φ hφ hket
  have hcc : c * starRingEnd ℂ c = 1 := by
    have h := conj_overlap_mul_overlap_of_ketbra_eq ψ φ hφ hket
    simpa [hc, mul_comm] using h
  calc
    ψ.vec j = ψ.vec j * 1 := (mul_one _).symm
    _ = ψ.vec j * (c * starRingEnd ℂ c) := by rw [hcc]
    _ = (ψ.vec j * c) * starRingEnd ℂ c := by ring
    _ = φ.vec j * starRingEnd ℂ c := by rw [hψc j]
    _ = starRingEnd ℂ c * φ.vec j := by ring

/-- If `conj c * c = 1`, then the conjugate of `c` has norm one. -/
lemma complex_norm_star_eq_one_of_conj_mul_self_eq_one (c : ℂ)
    (h : starRingEnd ℂ c * c = 1) :
    ‖starRingEnd ℂ c‖ = 1 := by
  have h_c_normSq : Complex.normSq c = 1 := by
    have h_mul := Complex.mul_conj c
    have h2 : (Complex.normSq c : ℂ) = 1 := by
      rw [← h_mul, mul_comm]
      exact h
    exact Complex.ofReal_eq_one.mp h2
  have h1 : starRingEnd ℂ c = star c := rfl
  rw [h1, norm_star]
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h_c_normSq
  rcases mul_self_eq_one_iff.mp (by simpa [pow_two] using h2) with hnorm | hnorm
  · exact hnorm
  · have hnonneg : (0 : ℝ) ≤ -1 := by
      simpa [hnorm] using norm_nonneg c
    norm_num at hnonneg

/-- Equality of rank-one projectors identifies normalized kets up to a global
phase. -/
theorem ket_eq_mod_phase_of_ketbra_eq {n : ℕ} [NeZero n] (ψ φ : Ket n)
    (_hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1)
    (hket : ψ * ψ.dag = φ * φ.dag) :
    ∃ θ : ℝ, ∀ i : Fin n,
      ψ.vec i = Complex.exp (Complex.I * θ) * φ.vec i := by
  set c := ψ.dag * φ with hc
  have h_conj_c_mul_c : starRingEnd ℂ c * c = 1 := by
    simpa [hc] using conj_overlap_mul_overlap_of_ketbra_eq ψ φ hφ hket
  have hψ_eq : ∀ j, ψ.vec j = starRingEnd ℂ c * φ.vec j := by
    simpa [hc] using ket_eq_conj_overlap_smul_of_ketbra_eq ψ φ hφ hket
  have h_conj_c_norm : ‖starRingEnd ℂ c‖ = 1 :=
    complex_norm_star_eq_one_of_conj_mul_self_eq_one c h_conj_c_mul_c
  rw [Complex.norm_eq_one_iff] at h_conj_c_norm
  obtain ⟨θ, hθ⟩ := h_conj_c_norm
  exact ⟨θ, fun i => by
    rw [hψ_eq i, ← hθ,
      show (↑θ : ℂ) * Complex.I = Complex.I * ↑θ from mul_comm _ _]⟩

/-- Dimension casts preserve the self inner product of a ket. -/
lemma Ket.cast_dag_mul_cast {n m : ℕ} (h : n = m) (ψ : Ket n) :
    (Ket.cast h ψ).dag * Ket.cast h ψ = ψ.dag * ψ := by
  subst h
  rfl

/-- The ket-bra of a dimension-cast ket is the corresponding operator dimension cast. -/
lemma Ket.cast_mul_dag {n m : ℕ} (h : n = m) (ψ : Ket n) :
    Ket.cast h ψ * (Ket.cast h ψ).dag = Op.castDim h (ψ * ψ.dag) := by
  subst h
  rfl

/-! ## The computational basis: completeness and the diagonal form

The standard-basis projector `|i⟩⟨i|` is the diagonal matrix of the indicator
`Pi.single i 1`, and the family resolves the identity.  Both readings are kept
because the ket-bra form is what measurement arguments consume while the diagonal
form is what the entrywise compression lemmas consume. -/

/-- **Resolution of the identity in the computational basis:** `∑ i, |i⟩⟨i| = 1`. -/
theorem stdKet_complete (n : ℕ) :
    (∑ i, stdKet n i * (stdKet n i).dag) = (1 : Op n) := by
  classical
  ext a b
  rw [Matrix.sum_apply]
  have hterm : ∀ k : Fin n,
      (stdKet n k * (stdKet n k).dag) a b = if k = a then (if k = b then 1 else 0) else 0 := by
    intro k
    simp only [ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, apply_ite, map_one, map_zero]
    split <;> simp
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq' Finset.univ a,
    Matrix.one_apply]
  simp

/-- Completeness relation for qubits: |0⟩⟨0| + |1⟩⟨1| = 1.

The `n = 2` instance of `stdKet_complete`. -/
theorem completeness_2 :
    stdKet 2 0 * (stdKet 2 0).dag + stdKet 2 1 * (stdKet 2 1).dag = (1 : Op 2) := by
  rw [← Fin.sum_univ_two (fun i : Fin 2 => stdKet 2 i * (stdKet 2 i).dag)]
  exact stdKet_complete 2

/-- The standard-basis projector in diagonal form:
`|i⟩⟨i| = diagonal (Pi.single i 1)`.

The diagonal reading is what the entrywise compression lemmas consume. -/
lemma stdKet_ketbra_eq_diagonal {n : ℕ} (i : Fin n) :
    stdKet n i * (stdKet n i).dag = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
  ext a b
  simp only [ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, Matrix.diagonal_apply,
    Pi.single_apply]
  by_cases hab : a = b
  · subst hab; by_cases ha : i = a <;> simp [ha, eq_comm]
  · by_cases ha : i = a <;> simp [hab, ha]

/-- **Resolution of the identity in diagonal form**:
`∑ i, diagonal (Pi.single i 1) = 1`.

The `Matrix.diagonal` reading of `stdKet_complete`. -/
lemma sum_diagonal_single (n : ℕ) :
    ∑ i : Fin n, Matrix.diagonal (Pi.single i (1 : ℂ)) = (1 : Op n) := by
  simp only [← stdKet_ketbra_eq_diagonal]
  exact stdKet_complete n

/-- The standard-basis diagonal projector is idempotent. -/
lemma diagonal_single_mul_self {n : ℕ} (i : Fin n) :
    Matrix.diagonal (Pi.single i (1 : ℂ)) * Matrix.diagonal (Pi.single i (1 : ℂ))
      = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : a = i <;> simp [Pi.single_apply, h]

/-- The standard-basis diagonal projector is an idempotent element, in the form the
square-root API consumes (`Matrix.PosSemidef.sqrt_eq_self_of_isIdempotentElem`). -/
lemma isIdempotentElem_diagonal_single {n : ℕ} (i : Fin n) :
    IsIdempotentElem (Matrix.diagonal (Pi.single i (1 : ℂ)) : Op n) :=
  diagonal_single_mul_self i

/-- Outer product |i⟩⟨j| applied at indices. -/
@[simp] lemma ketbra_std_apply (i j k l : Fin 2) :
    (stdKet 2 i * (stdKet 2 j).dag : Op 2) k l =
    if i = k then (if j = l then 1 else 0) else 0 := by
  simp only [ket_mul_bra_apply, stdKet_apply, Ket.dag_vec]
  by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj]

/-- Conjugate transpose of outer product: (|ψ⟩⟨φ|)† = |φ.dag.dag⟩⟨ψ.dag|. -/
@[simp]
theorem ket_mul_bra_conjTranspose {n : ℕ} (ψ : Ket n) (φ : Bra n) :
    (ψ * φ)† = φ.dag * ψ.dag := by
  ext i j
  simp only [Matrix.conjTranspose_apply, ket_mul_bra_apply, Bra.dag_vec, Ket.dag_vec, star]
  change (starRingEnd ℂ) (ψ.vec j * φ.vec i) =
    (starRingEnd ℂ) (φ.vec i) * (starRingEnd ℂ) (ψ.vec j)
  rw [RingHom.map_mul, mul_comm]

/-- Dagger of standard ket: `(stdKet n i).dag.dag = stdKet n i`. -/
@[simp] lemma stdKet_dag_dag (n : ℕ) (i : Fin n) : (stdKet n i).dag.dag = stdKet n i := by
  ext j
  simp only [Bra.dag_vec, Ket.dag_vec, stdKet_apply]
  by_cases h : i = j <;> simp [h]

/-- Projector onto normalized ket is idempotent: `(ψψ†)^2 = ψψ†`. -/
theorem ketbra_idempotent {n : ℕ} (ψ : Ket n) (h : ψ.dag * ψ = 1) :
    (ψ * ψ.dag) * (ψ * ψ.dag) = ψ * ψ.dag := by
  rw [ketbra_mul_ketbra]
  rw [h]
  simp

/-- Projector onto ket is Hermitian. -/
theorem ketbra_hermitian {n : ℕ} (ψ : Ket n) :
    (ψ * ψ.dag)† = ψ * ψ.dag := by
  rw [ket_mul_bra_conjTranspose]
  simp only [Ket.dag_dag]

/-- A ket-bra projector is the matrix outer product of a ket vector with its conjugate. -/
lemma ket_mul_dag_eq_vecMulVec {n : ℕ} (ψ : Ket n) :
    ψ * ψ.dag = Matrix.vecMulVec ψ.vec (star ψ.vec) := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.dag_vec, Matrix.vecMulVec_apply, Pi.star_apply,
    starRingEnd_apply]

/-- Projector `ψψ†` is positive semidefinite in Mathlib's matrix sense. -/
theorem ketbra_posSemidef {n : ℕ} (ψ : Ket n) : (ψ * ψ.dag).PosSemidef := by
  rw [ket_mul_dag_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star ψ.vec

/-- The standard-basis diagonal projector is positive semidefinite. -/
lemma posSemidef_diagonal_single {n : ℕ} (i : Fin n) :
    (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
  rw [← stdKet_ketbra_eq_diagonal]
  exact ketbra_posSemidef _

/-- The rank-one ket-bra operator bundled as a positive-semidefinite operator. -/
def ketbraPosSemidefOp {n : ℕ} (ψ : Ket n) : PosSemidefOp n where
  toOp := ψ * ψ.dag
  isHermitian := ketbra_hermitian ψ
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg (ketbra_posSemidef ψ) v

/-- Cross term of orthogonal projectors vanishes. -/
theorem ketbra_orthogonal_mul_zero {n : ℕ} (ψ φ : Ket n) (h : ψ.dag * φ = 0) :
    (ψ * ψ.dag) * (φ * φ.dag) = 0 := by
  rw [ketbra_mul_ketbra]
  rw [h]
  simp

/-- Left distributivity of outer product: `(ψ + φ) * χ = ψ * χ + φ * χ`. -/
@[simp]
lemma ket_add_mul_bra {n : ℕ} (ψ φ : Ket n) (χ : Bra n) :
    (ψ + φ) * χ = ψ * χ + φ * χ := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.add_vec, Matrix.add_apply]
  ring

/-- Right distributivity of outer product: `ψ * (φ + χ) = ψ * φ + ψ * χ`. -/
@[simp]
lemma ket_mul_add_bra {n : ℕ} (ψ : Ket n) (φ χ : Bra n) :
    ψ * (φ + χ) = ψ * φ + ψ * χ := by
  ext i j
  simp only [ket_mul_bra_apply, Bra.add_vec, Matrix.add_apply]
  ring

/-- For a ket `ψ` and operator `A`, `Tr(ψψ† A) = ψ† A ψ`. -/
lemma trace_ketbra_mul {n : ℕ} (ψ : Ket n) (A : Op n) :
    ((ψ * ψ.dag) * A).trace = ψ.dag * A * ψ := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec]
  rw [bra_mul_ket_eq]
  simp only [bra_mul_op_vec, Ket.dag_vec]
  congr 1
  ext i
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-- For kets `ψ`, `φ` and an operator `A`, `Tr(|ψ⟩⟨φ| A) = φ† A ψ`. -/
lemma trace_cross_ketbra_mul {n : ℕ} (ψ φ : Ket n) (A : Op n) :
    ((ψ * φ.dag) * A).trace = φ.dag * A * ψ := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec]
  rw [bra_mul_ket_eq]
  simp only [bra_mul_op_vec, Ket.dag_vec]
  congr 1
  ext i
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-- Right multiplication of a bra by the identity operator. -/
lemma bra_mul_one {n : ℕ} (φ : Bra n) :
    φ * (1 : Op n) = φ := by
  ext j
  simp only [bra_mul_op_vec, Matrix.one_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/-- The trace of a ketbra is the squared norm of the ket. -/
lemma ketbra_trace_eq_inner {n : ℕ} (ψ : Ket n) :
    (ψ * ψ.dag : Op n).trace = ψ.dag * ψ := by
  have htrace := trace_ketbra_mul ψ (1 : Op n)
  simpa [Matrix.mul_one, bra_mul_one] using htrace

/-- For normalized kets, the overlap has modulus at most `1`. -/
lemma ket_overlap_norm_le_one {n : ℕ} (ψ φ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) :
    ‖(ψ.dag * φ : ℂ)‖ ≤ 1 := by
  have hψ_sq : ∑ i, ‖ψ.vec i‖ ^ 2 = 1 := by
    have hψ_re : (∑ i, starRingEnd ℂ (ψ.vec i) * ψ.vec i).re = 1 := by
      simpa [bra_mul_ket_eq, Ket.dag_vec] using congrArg Complex.re hψ
    rw [Complex.re_sum] at hψ_re
    have hterm : ∀ i, (starRingEnd ℂ (ψ.vec i) * ψ.vec i).re = ‖ψ.vec i‖ ^ 2 := by
      intro i
      have hnorm : (starRingEnd ℂ (ψ.vec i) * ψ.vec i).re = Complex.normSq (ψ.vec i) := by
        rw [starRingEnd_apply]
        simp only [Complex.star_def, Complex.normSq_apply, Complex.mul_re,
          Complex.conj_re, Complex.conj_im]
        ring
      rw [hnorm, Complex.normSq_eq_norm_sq]
    simpa [hterm] using hψ_re
  have hφ_sq : ∑ i, ‖φ.vec i‖ ^ 2 = 1 := by
    have hφ_re : (∑ i, starRingEnd ℂ (φ.vec i) * φ.vec i).re = 1 := by
      simpa [bra_mul_ket_eq, Ket.dag_vec] using congrArg Complex.re hφ
    rw [Complex.re_sum] at hφ_re
    have hterm : ∀ i, (starRingEnd ℂ (φ.vec i) * φ.vec i).re = ‖φ.vec i‖ ^ 2 := by
      intro i
      have hnorm : (starRingEnd ℂ (φ.vec i) * φ.vec i).re = Complex.normSq (φ.vec i) := by
        rw [starRingEnd_apply]
        simp only [Complex.star_def, Complex.normSq_apply, Complex.mul_re,
          Complex.conj_re, Complex.conj_im]
        ring
      rw [hnorm, Complex.normSq_eq_norm_sq]
    simpa [hterm] using hφ_re
  have htriangle :
      ‖(ψ.dag * φ : ℂ)‖ ≤ ∑ i, ‖ψ.vec i‖ * ‖φ.vec i‖ := by
    calc ‖∑ i, starRingEnd ℂ (ψ.vec i) * φ.vec i‖
        ≤ ∑ i, ‖starRingEnd ℂ (ψ.vec i) * φ.vec i‖ := by
          simpa using norm_sum_le (Finset.univ)
            (fun i => starRingEnd ℂ (ψ.vec i) * φ.vec i)
      _ = ∑ i, ‖ψ.vec i‖ * ‖φ.vec i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, starRingEnd_apply, norm_star]
  calc ‖(ψ.dag * φ : ℂ)‖
      ≤ ∑ i, ‖ψ.vec i‖ * ‖φ.vec i‖ := by
          simpa [bra_mul_ket_eq, Ket.dag_vec] using htriangle
    _ ≤ Real.sqrt (∑ i, ‖ψ.vec i‖ ^ 2) * Real.sqrt (∑ i, ‖φ.vec i‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i => ‖ψ.vec i‖) (fun i => ‖φ.vec i‖)
    _ = 1 := by
        rw [hψ_sq, hφ_sq]
        simp

/-- Scaling two kets by arbitrary scalars scales a bra-ket overlap by the
corresponding conjugate-left scalar factor. -/
lemma ket_scalar_overlap
    {n : ℕ} (ψ ψ₀ φ φ₀ : Ket n) (T : Op n) (α β : ℂ)
    (hψ : ψ = α • ψ₀) (hφ : φ = β • φ₀) :
    φ.dag * T * ψ = (star β * α) * (φ₀.dag * T * ψ₀) := by
  rw [hψ, hφ]
  simp [braop_mul_ket, mul_left_comm, mul_comm]

/-- Trace of a product of two pure-state projectors equals the squared overlap. -/
lemma trace_pure_mul_pure {m : ℕ} (a b : Ket m) :
    ((a * a.dag) * (b * b.dag)).trace = ↑(Complex.normSq (a.dag * b)) := by
  rw [trace_ketbra_mul, bra_mul_ketbra, smul_bra_mul_ket]
  simp only [smul_eq_mul]
  have hconj : b.dag * a = starRingEnd ℂ (a.dag * b) := by
    simp only [bra_mul_ket_eq]
    rw [map_sum]
    congr 1
    ext i
    simp [mul_comm]
  rw [hconj, Complex.normSq_eq_conj_mul_self]
  ring

/-- Trace of a ketbra for a normalized ket is `1`. -/
lemma trace_ketbra_normalized {n : ℕ} (ψ : Ket n) (h : ψ.dag * ψ = 1) :
    (ψ * ψ.dag).trace = 1 := by
  have h1 : ((ψ * ψ.dag) * (1 : Op n)).trace = ψ.dag * (1 : Op n) * ψ :=
    trace_ketbra_mul ψ (1 : Op n)
  simp only [Matrix.mul_one] at h1
  rw [h1]
  rw [braop_mul_ket]
  have h_one : (1 : Op n) * ψ = ψ := by
    ext i
    simp only [op_mul_ket_vec, Matrix.one_mulVec]
  rw [h_one]
  exact h

/-- Quadratic forms of Hermitian operators have zero imaginary part. -/
lemma braOpKet_hermitian_im_zero {n : ℕ} (A : Op n) (hA : A.IsHermitian) (ψ : Ket n) :
    (ψ.dag * (A * ψ)).im = 0 := by
  have h_eq : ψ.dag * (A * ψ) = quadraticForm A ψ.vec := by
    simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
    unfold quadraticForm dotProduct
    rfl
  rw [h_eq]
  have h_conj : (starRingEnd ℂ) (quadraticForm A ψ.vec) = quadraticForm A ψ.vec :=
    quadraticForm_hermitian_conj_eq_self A hA ψ.vec
  set z := quadraticForm A ψ.vec with hz
  have : z.im = -z.im := by
    calc z.im = ((starRingEnd ℂ) z).im := by rw [h_conj]
      _ = -z.im := by rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
  linarith

end  -- noncomputable section

end Quantum.Operators
