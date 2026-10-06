import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Operators.BraKet.Basic
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.PartialTrace

/-!
# Trace Operations for Tensor Products — partial traces, PSD preservation, tensor sandwiches

This file defines partial traces over both factors of a finite-dimensional tensor
product and proves their algebraic, trace, positivity, and tensor-sandwich
properties.

## Main definitions

- `partialTraceA`, `partialTraceB`: trace over the first or second tensor factor
- `rightTensorUnitaryConj`: conjugation by a unitary on the right tensor factor
- `rightBlockVector`, `leftBlockVector`: block-supported test vectors

## Main statements

- `partialTraceB_add`, `partialTraceB_smul`, `partialTraceB_sub`: Linearity
- `partialTraceA_finset_sum`, `partialTraceB_finset_sum`: Distribution over finite sums
- `partialTraceA_hermitian`, `partialTraceB_hermitian`: Hermiticity preservation
- `partialTraceA_tensor_self_eq`, `partialTraceB_tensor_self_eq`: self-tensor
  partial trace identities
- `partialTraceB_one`, `partialTraceA_one`: the partial traces of the identity,
  `Tr_R 1_{E⊗R} = dR · 1_E` and `Tr_E 1_{E⊗R} = dE · 1_R`
- `partialTraceB_dim1_op`: partial trace over a one-dimensional product
- `quadraticForm_partialTraceA_eq_sum`, `quadraticForm_partialTraceB_eq_sum`: block
  decompositions of partial-trace quadratic forms
- `partialTraceA_posSemidef`, `partialTraceB_posSemidef`: PSD preservation
- `trace_partialTraceB`: `Tr(Tr_B(ρ)) = Tr(ρ)`
- `trace_eq_of_partialTraceB_eq`: a partial-trace section preserves trace
- `partialTraceB_sandwich_tensor_one`: tensor-sandwich identity
- `partialTraceA_one_tensor_sandwich`: right-factor sandwich identity
- `partialTraceA_rightTensorUnitaryConj`: right-factor unitary transport for
  `partialTraceA`
- `right_tensor_unitary_conj_paired_fixed_to_canonical`: undoing right-factor
  transport in paired tensor fixedness.
-/

namespace Quantum.TensorProducts

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker ComplexOrder
open Matrix

noncomputable section

/-- Partial trace over the second subsystem (trace out B from A⊗B).
    For ρ : Op (n * m), returns the reduced state on A: Op n.
    Formula: (Tr_B ρ)_{i,j} = ∑_k ρ_{(i,k),(j,k)} -/
def partialTraceB {n m : ℕ} (ρ : Op (n * m)) : Op n :=
  Matrix.of fun i j =>
    ∑ k : Fin m, ρ (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))

/-- Partial trace over the first subsystem (trace out A from A⊗B).
    For ρ : Op (n * m), returns the reduced state on B: Op m.
    Formula: (Tr_A ρ)_{i,j} = ∑_k ρ_{(k,i),(k,j)} -/
def partialTraceA {n m : ℕ} (ρ : Op (n * m)) : Op m :=
  Matrix.of fun i j =>
    ∑ k : Fin n, ρ (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j))

/-- Right-factor unitary conjugation of an operator on `A ⊗ R`. -/
def rightTensorUnitaryConj {n m : ℕ} (W : UnitaryOp m) (M : Op (n * m)) :
    Op (n * m) :=
  Op.tensor (1 : Op n) W.toOp * M * (Op.tensor (1 : Op n) W.toOp)†

/-- Undoing right-factor unitary transport converts paired fixedness by
`U ⊗ U` into canonical fixedness by `U ⊗ W†UW`. -/
lemma right_tensor_unitary_conj_paired_fixed_to_canonical {d : ℕ}
    (P : Op (d * d)) (U : Op d) (W : UnitaryOp d)
    (hfixed :
      Op.tensor U U * rightTensorUnitaryConj W P *
          (Op.tensor U U)† =
        rightTensorUnitaryConj W P) :
    Op.tensor U (W.toOp† * U * W.toOp) * P *
        (Op.tensor U (W.toOp† * U * W.toOp))† =
      P := by
  let A : Op (d * d) := Op.tensor (1 : Op d) W.toOp
  have hAA :
      (Op.tensor (1 : Op d) W.toOp†) * (Op.tensor (1 : Op d) W.toOp) =
        (1 : Op (d * d)) := by
    rw [Op.tensor_mul, Matrix.one_mul, W.unitary_left, Op.tensor_one]
  have hA_left : A† * Op.tensor U U * A = Op.tensor U (W.toOp† * U * W.toOp) := by
    dsimp [A]
    simp only [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul,
      Matrix.one_mul, Matrix.mul_one]
  have hA_right : A† * (Op.tensor U U)† * A =
      (Op.tensor U (W.toOp† * U * W.toOp))† := by
    dsimp [A]
    simp only [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul,
      Matrix.conjTranspose_mul, conjTranspose_conjTranspose, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  have hA_transport :
      A† * rightTensorUnitaryConj W P * A = P := by
    dsimp [A]
    simp only [rightTensorUnitaryConj,
      Op.tensor_conjTranspose, conjTranspose_one, Matrix.mul_assoc]
    rw [hAA]
    rw [← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one]
  calc
    Op.tensor U (W.toOp† * U * W.toOp) * P *
        (Op.tensor U (W.toOp† * U * W.toOp))† =
        (A† * Op.tensor U U * A) * P *
          (A† * (Op.tensor U U)† * A) := by
          rw [hA_left, hA_right]
    _ = A† *
          (Op.tensor U U * (A * P * A†) * (Op.tensor U U)†) * A := by
          simp only [Matrix.mul_assoc]
    _ = A† *
          (Op.tensor U U * rightTensorUnitaryConj W P *
            (Op.tensor U U)†) * A := by
          simp only [A, rightTensorUnitaryConj]
    _ = A† * rightTensorUnitaryConj W P * A := by
          rw [hfixed]
    _ = P := hA_transport

/-- Entrywise form of the raw `▸`-cast of a square matrix indexed by `Fin`. -/
lemma matrix_eqRec_apply {n m : ℕ} (h : n = m)
    (M : Op n) (i j : Fin m) :
    (h ▸ M : Op m) i j =
      M (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h
  rfl

/-- **Iterated `partialTraceB` matches single `partialTraceB` of the
associativity-reshape.**

For `M : Op ((a * b) * c)`, tracing out `c` and then `b` yields the same
`Op a` as tracing out `b * c` directly from the associativity-reshape
`Nat.mul_assoc a b c ▸ M : Op (a * (b * c))`. -/
lemma partialTraceB_partialTraceB_eq_assoc {a b c : ℕ}
    (M : Op (a * b * c)) :
    partialTraceB (partialTraceB M) =
      partialTraceB (Nat.mul_assoc a b c ▸ M) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply]
  rw [← Finset.sum_product']
  refine Fintype.sum_equiv finProdFinEquiv _ _ ?_
  rintro ⟨p, k⟩
  rw [matrix_eqRec_apply]
  have hidx :
      ∀ (i₀ : Fin a),
        finProdFinEquiv (finProdFinEquiv (i₀, p), k) =
          Fin.cast (Nat.mul_assoc a b c).symm
            (finProdFinEquiv (i₀, finProdFinEquiv (p, k))) := by
    intro i₀
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [hidx i, hidx j]

/-- Tracing out the second factor of an operator tensor product multiplies the
first factor by the trace of the second. -/
lemma partialTraceB_tensor_op {n m : ℕ} (A : Op n) (B : Op m) :
    partialTraceB (Op.tensor A B) = B.trace • A := by
  ext i j
  simp [partialTraceB, Matrix.trace, Op.tensor, Finset.mul_sum, mul_comm]

/-- Tracing out the first factor of an operator tensor product multiplies the
second factor by the trace of the first. -/
lemma partialTraceA_tensor_op {n m : ℕ} (A : Op n) (B : Op m) :
    partialTraceA (Op.tensor A B) = A.trace • B := by
  ext i j
  simp [partialTraceA, Matrix.trace, Op.tensor, ← Finset.sum_mul]

/-- **The partial trace of the identity**: tracing out `R` leaves `dR` copies of the
identity, `Tr_R 1_{E⊗R} = dR · 1_E`. -/
theorem partialTraceB_one {n m : ℕ} :
    partialTraceB (1 : Op (n * m)) = (m : ℂ) • (1 : Op n) := by
  have h : (1 : Op (n * m)) = Op.tensor (1 : Op n) (1 : Op m) := Op.tensor_one.symm
  rw [h, partialTraceB_tensor_op, Matrix.trace_one, Fintype.card_fin]

/-- The left counterpart of `partialTraceB_one`: tracing out `E` leaves `dE` copies of
the identity, `Tr_E 1_{E⊗R} = dE · 1_R`. -/
theorem partialTraceA_one {n m : ℕ} :
    partialTraceA (1 : Op (n * m)) = (n : ℂ) • (1 : Op m) := by
  have h : (1 : Op (n * m)) = Op.tensor (1 : Op n) (1 : Op m) := Op.tensor_one.symm
  rw [h, partialTraceA_tensor_op, Matrix.trace_one, Fintype.card_fin]

/-- Partial trace over the second register of a self-tensor:
`partialTraceB (U ⊗ U) = trace(U) • U`. -/
lemma partialTraceB_tensor_self_eq {n : ℕ} (U : Op n) :
    partialTraceB (Op.tensor U U) = U.trace • U := by
  exact partialTraceB_tensor_op U U

/-- Partial trace over the first register of a self-tensor:
`partialTraceA (U ⊗ U) = trace(U) • U`. -/
lemma partialTraceA_tensor_self_eq {n : ℕ} (U : Op n) :
    partialTraceA (Op.tensor U U) = U.trace • U := by
  exact partialTraceA_tensor_op U U

/-- Tensoring a diagonal operator on the left with the identity gives the
corresponding product-index diagonal operator. -/
lemma Op.tensor_diagonal_one {n m : ℕ} (d : Fin n → ℂ) :
    Op.tensor (Matrix.diagonal d) (1 : Op m) =
      Matrix.diagonal (fun p : Fin (n * m) => d (finProdFinEquiv.symm p).1) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [Op.tensor]
  · by_cases hfirst : p.divNat = q.divNat
    · have hsecond : p.modNat ≠ q.modNat := by
        intro hs
        apply hpq
        exact finProdFinEquiv.symm.injective (Prod.ext hfirst hs)
      simp [Op.tensor, hpq, hfirst, hsecond]
    · simp [Op.tensor, hpq, hfirst]

/-- Partial trace over the left factor after sandwiching by a diagonal left
operator tensored with the identity. -/
lemma partialTraceA_sandwich_tensor_diagonal_one {n m : ℕ}
    (d : Fin n → ℂ) (M : Op (n * m)) :
    partialTraceA
        (Op.tensor (Matrix.diagonal d) (1 : Op m) * M *
          Op.tensor (Matrix.diagonal d) (1 : Op m)) =
      Matrix.of fun a b =>
        ∑ k : Fin n, d k * M (finProdFinEquiv (k, a)) (finProdFinEquiv (k, b)) * d k := by
  rw [Op.tensor_diagonal_one d]
  ext a b
  simp only [partialTraceA, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Equiv.symm_apply_apply]

/-- Partial trace over `B` distributes over addition. -/
theorem partialTraceB_add {n m : ℕ} (ρ σ : Op (n * m)) :
    partialTraceB (ρ + σ) = partialTraceB ρ + partialTraceB σ := by
  ext i j
  unfold partialTraceB
  simp only [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- Partial trace over `B` commutes with complex scalar multiplication. -/
theorem partialTraceB_smul {n m : ℕ} (c : ℂ) (ρ : Op (n * m)) :
    partialTraceB (c • ρ) = c • partialTraceB ρ := by
  ext i j
  unfold partialTraceB
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Partial trace over `A` distributes over addition. -/
theorem partialTraceA_add {n m : ℕ} (ρ σ : Op (n * m)) :
    partialTraceA (ρ + σ) = partialTraceA ρ + partialTraceA σ := by
  ext i j
  unfold partialTraceA
  simp only [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

/-- Partial trace over `A` commutes with complex scalar multiplication. -/
theorem partialTraceA_smul {n m : ℕ} (c : ℂ) (ρ : Op (n * m)) :
    partialTraceA (c • ρ) = c • partialTraceA ρ := by
  ext i j
  unfold partialTraceA
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Partial trace over `A` commutes with real scalar multiplication, with the
scalar coerced to complex matrix entries. -/
lemma partialTraceA_real_smul {n m : ℕ} (c : ℝ) (ρ : Op (n * m)) :
    partialTraceA (c • ρ) = (c : ℂ) • partialTraceA ρ := by
  simpa [Complex.real_smul] using partialTraceA_smul (n := n) (m := m) (c := (c : ℂ)) ρ

/-- Partial trace over `B` commutes with real scalar multiplication, with the
scalar coerced to complex matrix entries. -/
lemma partialTraceB_real_smul {n m : ℕ} (c : ℝ) (ρ : Op (n * m)) :
    partialTraceB (c • ρ) = (c : ℂ) • partialTraceB ρ := by
  simpa [Complex.real_smul] using partialTraceB_smul (n := n) (m := m) (c := (c : ℂ)) ρ

/-- Partial trace over `B` distributes over subtraction. -/
theorem partialTraceB_sub {n m : ℕ} [NeZero n] [NeZero m]
    (A B : Op (n * m)) :
    partialTraceB (A - B) = partialTraceB A - partialTraceB B := by
  simp only [sub_eq_add_neg]
  rw [partialTraceB_add]
  congr 1
  rw [show -B = (-1 : ℂ) • B from by simp]
  rw [partialTraceB_smul]
  simp

/-- Partial trace over `B` distributes over finite sums. -/
lemma partialTraceB_finset_sum {n m : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Op (n * m)) :
    partialTraceB (∑ i ∈ s, f i) = ∑ i ∈ s, partialTraceB (f i) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]

/-- Partial trace over `A` distributes over finite sums. -/
lemma partialTraceA_finset_sum {n m : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Op (n * m)) :
    partialTraceA (∑ i ∈ s, f i) = ∑ i ∈ s, partialTraceA (f i) := by
  ext i j
  simp only [partialTraceA, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]

/-- Partial trace over `B` preserves Hermiticity. -/
theorem partialTraceB_hermitian {n m : ℕ} (ρ : Op (n * m)) (h : ρ.IsHermitian) :
    (partialTraceB ρ).IsHermitian := by
  unfold IsHermitian conjTranspose partialTraceB
  ext i j
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrFun (congrFun h (finProdFinEquiv (i, k))) (finProdFinEquiv (j, k))
  unfold conjTranspose at hk
  simp only [Matrix.transpose_apply, Matrix.map_apply] at hk
  exact hk

/-- Partial trace over `A` preserves Hermiticity. -/
theorem partialTraceA_hermitian {n m : ℕ} (ρ : Op (n * m)) (h : ρ.IsHermitian) :
    (partialTraceA ρ).IsHermitian := by
  unfold IsHermitian conjTranspose partialTraceA
  ext i j
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrFun (congrFun h (finProdFinEquiv (k, i))) (finProdFinEquiv (k, j))
  unfold conjTranspose at hk
  simp only [Matrix.transpose_apply, Matrix.map_apply] at hk
  exact hk

/-- The columns of a matrix satisfying `Uᴴ * U = 1` are orthonormal. -/
lemma columns_orthonormal_of_conjTranspose_mul_eq_one {n : ℕ}
    (U : Op n) (hU : Uᴴ * U = 1) (a c : Fin n) :
    ∑ k : Fin n, U k a * star (U k c) = if c = a then 1 else 0 := by
  have h := congrFun (congrFun hU c) a
  simp only [mul_apply, conjTranspose_apply, one_apply] at h
  simpa only [mul_comm] using h

/-- Entry expansion for left-multiplication by an operator tensored with the
identity on the right factor. -/
lemma tensor_one_mul_apply {n m : ℕ}
    (U : Op n) (M : Op (n * m)) (k : Fin n) (i : Fin m) (p : Fin (n * m)) :
    (Op.tensor U (1 : Op m) * M) (finProdFinEquiv (k, i)) p =
      ∑ a : Fin n, U k a * M (finProdFinEquiv (a, i)) p := by
  simp only [Matrix.mul_apply]
  rw [(Fintype.sum_equiv finProdFinEquiv
    (fun ab => (Op.tensor U (1 : Op m)) (finProdFinEquiv (k, i)) (finProdFinEquiv ab) *
      M (finProdFinEquiv ab) p)
    _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [show i ≠ b from fun h => hb h.symm]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Entry expansion for sandwiching by operators tensored with the identity on
the right factor. -/
lemma tensor_one_mul_mul_tensor_one_apply {n m : ℕ}
    (A B : Op n) (M : Op (n * m)) (i j : Fin n) (k l : Fin m) :
    (Op.tensor A (1 : Op m) * M * Op.tensor B (1 : Op m))
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) =
      ∑ a : Fin n, ∑ c : Fin n,
        A i a * M (finProdFinEquiv (a, k)) (finProdFinEquiv (c, l)) * B c j := by
  rw [Matrix.mul_apply]
  simp_rw [tensor_one_mul_apply]
  rw [(Fintype.sum_equiv finProdFinEquiv
    (fun cd => (∑ a, A i a * M (finProdFinEquiv (a, k)) (finProdFinEquiv cd)) *
      (Op.tensor B (1 : Op m)) (finProdFinEquiv cd) (finProdFinEquiv (j, l)))
    _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero]
  simp_rw [Fintype.sum_ite_eq', Finset.sum_mul]
  exact (Finset.sum_comm ..).symm

/-- Entry expansion for conjugating by an operator tensored with the identity
on the right factor. -/
lemma tensor_one_mul_mul_conjTranspose_tensor_one_apply {n m : ℕ}
    (U : Op n) (M : Op (n * m)) (k l : Fin n) (i j : Fin m) :
    (Op.tensor U (1 : Op m) * M * Op.tensor Uᴴ (1 : Op m))
        (finProdFinEquiv (k, i)) (finProdFinEquiv (l, j)) =
      ∑ a : Fin n, ∑ c : Fin n,
        U k a * M (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) *
        star (U l c) := by
  simpa only [conjTranspose_apply] using
    Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply U Uᴴ M k l i j

/-- Partial trace over `A` is invariant under conjugation by `U ⊗ 1`
when `U` is unitary. -/
lemma partialTraceA_tensor_one_unitary_conj {n m : ℕ}
    (U : Op n) (M : Op (n * m)) (hU : Uᴴ * U = 1) :
    partialTraceA (U ⊗ (1 : Op m) * M * (Uᴴ ⊗ (1 : Op m))) = partialTraceA M := by
  have hUU := columns_orthonormal_of_conjTranspose_mul_eq_one U hU
  ext i j
  simp only [partialTraceA, Matrix.of_apply]
  simp_rw [tensor_one_mul_mul_conjTranspose_tensor_one_apply]
  trans ∑ a : Fin n, ∑ c : Fin n,
    (∑ k : Fin n, U k a * star (U k c)) *
      M (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j))
  · rw [Finset.sum_comm]
    congr 1
    funext a
    rw [Finset.sum_comm]
    congr 1
    funext c
    rw [Finset.sum_mul]
    congr 1
    funext k
    ring
  · simp_rw [hUU, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']

end
end Quantum.TensorProducts

namespace Quantum.Operators
open Quantum.TensorProducts
noncomputable section

/-- Partial trace over `B` of a Hermitian operator is Hermitian. -/
def HermitianOp.partialTraceB {n m : ℕ} (ρ : HermitianOp (n * m)) : HermitianOp n :=
  ⟨Quantum.TensorProducts.partialTraceB ρ.toOp, by
    exact partialTraceB_hermitian ρ.toOp ρ.isHermitian⟩

/-- Partial trace over `A` of a Hermitian operator is Hermitian. -/
def HermitianOp.partialTraceA {n m : ℕ} (ρ : HermitianOp (n * m)) : HermitianOp m :=
  ⟨Quantum.TensorProducts.partialTraceA ρ.toOp, by
    exact partialTraceA_hermitian ρ.toOp ρ.isHermitian⟩

end
end Quantum.Operators

namespace Quantum.TensorProducts
open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker ComplexOrder
open Matrix
noncomputable section

/-- The vector on `A ⊗ B` supported on the block with fixed `B` index. -/
def rightBlockVector {n m : ℕ} (k : Fin m) (x : Fin n → ℂ) :
    Fin (n * m) → ℂ :=
  fun p => if (finProdFinEquiv.symm p).2 = k then x (finProdFinEquiv.symm p).1 else 0

/-- The vector on `A ⊗ B` supported on the block with fixed `A` index. -/
def leftBlockVector {n m : ℕ} (k : Fin n) (x : Fin m → ℂ) :
    Fin (n * m) → ℂ :=
  fun p => if (finProdFinEquiv.symm p).1 = k then x (finProdFinEquiv.symm p).2 else 0

/-- The quadratic form on a vector supported in one fixed `B` block is the
corresponding fixed-block double sum. -/
lemma quadraticForm_rightBlockVector_eq_sum {n m : ℕ} (M : Op (n * m))
    (k : Fin m) (x : Fin n → ℂ) :
    quadraticForm M (rightBlockVector k x) =
      ∑ i : Fin n, ∑ j : Fin n,
        star (x i) * M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) * x j := by
  unfold quadraticForm dotProduct mulVec dotProduct rightBlockVector
  simp only [Pi.star_apply, star_ite_zero]
  calc ∑ p, (if (finProdFinEquiv.symm p).2 = k
               then star (x (finProdFinEquiv.symm p).1) else 0) *
           ∑ q, M p q * (if (finProdFinEquiv.symm q).2 = k
                              then x (finProdFinEquiv.symm q).1 else 0)
      = ∑ il : Fin n × Fin m, (if il.2 = k then star (x il.1) else 0) *
          ∑ jl : Fin n × Fin m, M (finProdFinEquiv il) (finProdFinEquiv jl) *
            (if jl.2 = k then x jl.1 else 0) := by
        trans ∑ p, (if (finProdFinEquiv.symm p).2 = k
                    then star (x (finProdFinEquiv.symm p).1) else 0) *
                   ∑ jl : Fin n × Fin m, M p (finProdFinEquiv jl) *
                     (if jl.2 = k then x jl.1 else 0)
        · congr 1; ext p; congr 1
          apply Fintype.sum_equiv finProdFinEquiv.symm
          intro q
          simp only [Equiv.apply_symm_apply]
        · apply Fintype.sum_equiv finProdFinEquiv.symm
          intro p
          congr 1
          simp only [Equiv.apply_symm_apply]
    _ = ∑ i : Fin n, ∑ l : Fin m, (if l = k then star (x i) else 0) *
          ∑ j : Fin n, ∑ l' : Fin m,
            M (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l')) *
              (if l' = k then x j else 0) := by
        conv_lhs =>
          rw [Fintype.sum_prod_type]
          arg 2; ext i
          arg 2; ext l; arg 2
          rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin n, star (x i) *
          ∑ j : Fin n, M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) * x j := by
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
    _ = ∑ i : Fin n, ∑ j : Fin n,
          star (x i) * M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) * x j := by
        congr 1; ext i
        rw [Finset.mul_sum]
        congr 1; ext j
        ring

/-- The quadratic form on a vector supported in one fixed `A` block is the
corresponding fixed-block double sum. -/
lemma quadraticForm_leftBlockVector_eq_sum {n m : ℕ} (M : Op (n * m))
    (k : Fin n) (x : Fin m → ℂ) :
    quadraticForm M (leftBlockVector k x) =
      ∑ i : Fin m, ∑ j : Fin m,
        star (x i) * M (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) * x j := by
  unfold quadraticForm dotProduct mulVec dotProduct leftBlockVector
  simp only [Pi.star_apply, star_ite_zero]
  calc ∑ p, (if (finProdFinEquiv.symm p).1 = k
               then star (x (finProdFinEquiv.symm p).2) else 0) *
           ∑ q, M p q * (if (finProdFinEquiv.symm q).1 = k
                              then x (finProdFinEquiv.symm q).2 else 0)
      = ∑ li : Fin n × Fin m, (if li.1 = k then star (x li.2) else 0) *
          ∑ lj : Fin n × Fin m, M (finProdFinEquiv li) (finProdFinEquiv lj) *
            (if lj.1 = k then x lj.2 else 0) := by
        trans ∑ p, (if (finProdFinEquiv.symm p).1 = k
                    then star (x (finProdFinEquiv.symm p).2) else 0) *
                   ∑ lj : Fin n × Fin m, M p (finProdFinEquiv lj) *
                     (if lj.1 = k then x lj.2 else 0)
        · congr 1; ext p; congr 1
          apply Fintype.sum_equiv finProdFinEquiv.symm
          intro q
          simp only [Equiv.apply_symm_apply]
        · apply Fintype.sum_equiv finProdFinEquiv.symm
          intro p
          congr 1
          simp only [Equiv.apply_symm_apply]
    _ = ∑ l : Fin n, ∑ i : Fin m, (if l = k then star (x i) else 0) *
          ∑ l' : Fin n, ∑ j : Fin m,
            M (finProdFinEquiv (l, i)) (finProdFinEquiv (l', j)) *
              (if l' = k then x j else 0) := by
        conv_lhs =>
          rw [Fintype.sum_prod_type]
          arg 2; ext l
          arg 2; ext i; arg 2
          rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin m, star (x i) *
          ∑ j : Fin m, M (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) * x j := by
        rw [Finset.sum_eq_single k]
        · simp only [↓reduceIte]
          congr 1; ext i
          congr 1
          rw [Finset.sum_eq_single k]
          · simp only [↓reduceIte]
          · intro l' _ hl'
            simp only [hl', ↓reduceIte, Finset.sum_const_zero, mul_zero]
          · intro hk; exact (hk (Finset.mem_univ k)).elim
        · intro l _ hl
          simp only [hl, ↓reduceIte, Finset.sum_const_zero, zero_mul]
        · intro hk; exact (hk (Finset.mem_univ k)).elim
    _ = ∑ i : Fin m, ∑ j : Fin m,
          star (x i) * M (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) * x j := by
        congr 1; ext i
        rw [Finset.mul_sum]
        congr 1; ext j
        ring

/-- The quadratic form of a `B`-partial trace is the sum of quadratic forms on
the fixed-`B` blocks of the original operator. -/
lemma quadraticForm_partialTraceB_eq_sum {n m : ℕ} (M : Op (n * m))
    (x : Fin n → ℂ) :
    quadraticForm (Quantum.TensorProducts.partialTraceB M) x =
      ∑ k : Fin m, quadraticForm M (rightBlockVector k x) := by
  unfold quadraticForm partialTraceB dotProduct
  simp only [Matrix.of_apply, mulVec, dotProduct, Pi.star_apply]
  have h_expand : (∑ i : Fin n, star (x i) *
      ∑ j : Fin n, (∑ k : Fin m, M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))) * x j) =
      ∑ k : Fin m, (∑ i : Fin n, ∑ j : Fin n,
        star (x i) * M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) * x j) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [h_expand]
  apply Finset.sum_congr rfl
  intro k _
  exact (quadraticForm_rightBlockVector_eq_sum M k x).symm

/-- The real part of the quadratic form of a `B`-partial trace is the sum of the
real parts on the fixed-`B` blocks of the original operator. -/
lemma quadraticForm_partialTraceB_re_eq_sum {n m : ℕ} (M : Op (n * m))
    (x : Fin n → ℂ) :
    (quadraticForm (Quantum.TensorProducts.partialTraceB M) x).re =
      ∑ k : Fin m, (quadraticForm M (rightBlockVector k x)).re := by
  rw [quadraticForm_partialTraceB_eq_sum, Complex.re_sum]

/-- The quadratic form of an `A`-partial trace is the sum of quadratic forms on
the fixed-`A` blocks of the original operator. -/
lemma quadraticForm_partialTraceA_eq_sum {n m : ℕ} (M : Op (n * m))
    (x : Fin m → ℂ) :
    quadraticForm (Quantum.TensorProducts.partialTraceA M) x =
      ∑ k : Fin n, quadraticForm M (leftBlockVector k x) := by
  unfold quadraticForm partialTraceA dotProduct
  simp only [Matrix.of_apply, mulVec, dotProduct, Pi.star_apply]
  have h_expand : (∑ i : Fin m, star (x i) *
      ∑ j : Fin m, (∑ k : Fin n, M (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j))) * x j) =
      ∑ k : Fin n, (∑ i : Fin m, ∑ j : Fin m,
        star (x i) * M (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) * x j) := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [h_expand]
  apply Finset.sum_congr rfl
  intro k _
  exact (quadraticForm_leftBlockVector_eq_sum M k x).symm

/-- The real part of the quadratic form of an `A`-partial trace is the sum of the
real parts on the fixed-`A` blocks of the original operator. -/
lemma quadraticForm_partialTraceA_re_eq_sum {n m : ℕ} (M : Op (n * m))
    (x : Fin m → ℂ) :
    (quadraticForm (Quantum.TensorProducts.partialTraceA M) x).re =
      ∑ k : Fin n, (quadraticForm M (leftBlockVector k x)).re := by
  rw [quadraticForm_partialTraceA_eq_sum, Complex.re_sum]

/-- Partial trace over `B` preserves positive semidefiniteness. -/
theorem partialTraceB_posSemidef {n m : ℕ} (ρ : PosSemidefOp (n * m)) :
    ∀ x : Fin n → ℂ, 0 ≤ (quadraticForm (Quantum.TensorProducts.partialTraceB ρ.toOp) x).re := by
  intro x
  rw [quadraticForm_partialTraceB_re_eq_sum]
  apply Finset.sum_nonneg
  intro k _
  exact ρ.pos_semidef (rightBlockVector k x)

/-- A nonzero vector lifts to a nonzero fixed-`B`-block vector on the chosen block. -/
lemma rightBlockVector_ne_zero {n m : ℕ} (k : Fin m) {x : Fin n → ℂ}
    (hx : x ≠ 0) : rightBlockVector k x ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  intro hcontra
  apply hi
  have := congrFun hcontra (finProdFinEquiv (i, k))
  simpa [rightBlockVector] using this

/-- Partial trace over `B` preserves positive definiteness (the traced-out factor
must be nonempty).  For a nonzero `v`, the quadratic form of `Tr_B(M)` at `v`
equals `∑_k ⟨w_k|M|w_k⟩` over the fixed-`B`-block lifts `w_k`; each summand is
nonnegative since `M` is PosDef, and the block at any fixed `k` lifts the nonzero
`v` to a nonzero `w_k`, so that summand is strictly positive. -/
theorem partialTraceB_posDef {n m : ℕ} [NeZero m] {ρ : Op (n * m)}
    (hρ : ρ.PosDef) : (Quantum.TensorProducts.partialTraceB ρ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨partialTraceB_hermitian ρ hρ.isHermitian, ?_⟩
  intro x hx
  -- It suffices to show the quadratic form is real and strictly positive.
  -- The partial trace is Hermitian, so its quadratic form has zero imaginary part.
  have hHerm : (Quantum.TensorProducts.partialTraceB ρ).IsHermitian :=
    partialTraceB_hermitian ρ hρ.isHermitian
  have him : (quadraticForm (Quantum.TensorProducts.partialTraceB ρ) x).im = 0 := by
    have hc := Quantum.Operators.quadraticForm_hermitian_conj_eq_self
      (Quantum.TensorProducts.partialTraceB ρ) hHerm x
    rw [Complex.ext_iff] at hc
    simp only [Complex.conj_re, Complex.conj_im] at hc
    linarith [hc.2]
  -- `Re ⟨x|Tr_B ρ|x⟩ = ∑_k Re ⟨w_k|ρ|w_k⟩` over the fixed-`B`-block lifts `w_k`.
  have hsum :
      (quadraticForm (Quantum.TensorProducts.partialTraceB ρ) x).re =
        ∑ k : Fin m, (quadraticForm ρ (rightBlockVector k x)).re :=
    quadraticForm_partialTraceB_re_eq_sum ρ x
  -- every summand is nonnegative; the `k = 0` block is strictly positive.
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_neZero _⟩⟩
  let k0 : Fin m := ⟨0, Nat.pos_of_neZero _⟩
  have hpos : 0 < (quadraticForm ρ (rightBlockVector k0 x)).re := by
    have hne : rightBlockVector k0 x ≠ 0 := rightBlockVector_ne_zero k0 hx
    simpa [quadraticForm] using hρ.re_dotProduct_pos hne
  have hnonneg : ∀ k : Fin m, 0 ≤ (quadraticForm ρ (rightBlockVector k x)).re := by
    intro k
    exact posSemidef_re_quadraticForm_nonneg hρ.posSemidef (rightBlockVector k x)
  have hre_pos : 0 < (quadraticForm (Quantum.TensorProducts.partialTraceB ρ) x).re := by
    rw [hsum]
    calc (0 : ℝ) < (quadraticForm ρ (rightBlockVector k0 x)).re := hpos
      _ ≤ ∑ k : Fin m, (quadraticForm ρ (rightBlockVector k x)).re :=
          Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ k0)
  -- Repackage `0 < Re z, Im z = 0` into `0 < z` over `ℂ` (ComplexOrder).
  have : (0 : ℂ) < quadraticForm (Quantum.TensorProducts.partialTraceB ρ) x :=
    Complex.lt_def.mpr ⟨by simpa using hre_pos, by simp [him]⟩
  simpa [quadraticForm] using this

/-- Partial trace over `A` preserves positive semidefiniteness. -/
theorem partialTraceA_posSemidef {n m : ℕ} (ρ : PosSemidefOp (n * m)) :
    ∀ x : Fin m → ℂ, 0 ≤ (quadraticForm (Quantum.TensorProducts.partialTraceA ρ.toOp) x).re := by
  intro x
  rw [quadraticForm_partialTraceA_re_eq_sum]
  apply Finset.sum_nonneg
  intro k _
  exact ρ.pos_semidef (leftBlockVector k x)

end
end Quantum.TensorProducts

namespace Quantum.Operators
open Quantum.TensorProducts
noncomputable section

/-- Partial trace over `B` of a positive semidefinite operator is positive semidefinite. -/
def PosSemidefOp.partialTraceB {n m : ℕ} (ρ : PosSemidefOp (n * m)) : PosSemidefOp n :=
  ⟨⟨Quantum.TensorProducts.partialTraceB ρ.toOp, by
      exact partialTraceB_hermitian ρ.toOp ρ.toHermitianOp.isHermitian⟩,
   by exact partialTraceB_posSemidef ρ⟩

/-- Partial trace over `A` of a positive semidefinite operator is positive semidefinite. -/
def PosSemidefOp.partialTraceA {n m : ℕ} (ρ : PosSemidefOp (n * m)) : PosSemidefOp m :=
  ⟨⟨Quantum.TensorProducts.partialTraceA ρ.toOp, by
      exact partialTraceA_hermitian ρ.toOp ρ.toHermitianOp.isHermitian⟩,
   by exact partialTraceA_posSemidef ρ⟩

end
end Quantum.Operators

namespace Quantum.TensorProducts
open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker ComplexOrder
open Matrix
noncomputable section

/-- The trace of a partial trace over `B` equals the original trace. -/
theorem trace_partialTraceB {n m : ℕ} (ρ : Op (n * m)) :
    (partialTraceB ρ).trace = ρ.trace := by
  unfold trace diag partialTraceB
  simp only [Matrix.of_apply]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv finProdFinEquiv
  intro ⟨i, k⟩
  simp

/-- A partial-trace section preserves trace: if tracing out the second subsystem
returns `A`, then the original operator has the same trace as `A`. -/
lemma trace_eq_of_partialTraceB_eq {n m : ℕ}
    (M : Op (n * m)) (A : Op n)
    (hsec : partialTraceB M = A) :
    M.trace = A.trace := by
  rw [← hsec, trace_partialTraceB]

/-- The trace of a partial trace over `A` equals the original trace. -/
theorem trace_partialTraceA {n m : ℕ} (ρ : Op (n * m)) :
    (partialTraceA ρ).trace = ρ.trace := by
  unfold trace diag partialTraceA
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv finProdFinEquiv
  intro ⟨i, k⟩
  simp

end
end Quantum.TensorProducts

namespace Quantum.Operators
open Quantum.TensorProducts
noncomputable section

/-- Partial trace over `B` of a density operator is a density operator. -/
def DensityOp.partialTraceB {n m : ℕ} (ρ : DensityOp (n * m)) : DensityOp n :=
  ⟨ρ.toPosSemidefOp.partialTraceB, by
    change (Quantum.TensorProducts.partialTraceB ρ.toOp).trace = 1
    rw [trace_partialTraceB]
    exact ρ.trace_one⟩

/-- The operator of a density partial trace is the partial trace of its operator. -/
@[simp] theorem DensityOp.partialTraceB_toOp {n m : ℕ} (ρ : DensityOp (n * m)) :
    ρ.partialTraceB.toOp = Quantum.TensorProducts.partialTraceB ρ.toOp := rfl

/-- Casting only the traced-out subsystem does not change `DensityOp.partialTraceB`. -/
theorem DensityOp.partialTraceB_castDim {n m₁ m₂ : ℕ} (h : m₁ = m₂)
    (ρ : DensityOp (n * m₁)) :
    DensityOp.partialTraceB (DensityOp.castDim (congrArg (n * ·) h) ρ) =
      DensityOp.partialTraceB ρ := by
  subst h
  rfl

/-- Partial trace over `A` of a density operator is a density operator. -/
def DensityOp.partialTraceA {n m : ℕ} (ρ : DensityOp (n * m)) : DensityOp m :=
  ⟨ρ.toPosSemidefOp.partialTraceA, by
    change (Quantum.TensorProducts.partialTraceA ρ.toOp).trace = 1
    rw [trace_partialTraceA]
    exact ρ.trace_one⟩

end
end Quantum.Operators

namespace Quantum.TensorProducts
open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker ComplexOrder
open Matrix
noncomputable section

/-- Partial trace over `B` of a product state returns the first factor. -/
theorem partialTraceB_tensor {n m : ℕ} (ρ : DensityOp n) (σ : DensityOp m) :
    (DensityOp.partialTraceB (ρ.tensor σ)).toOp = ρ.toOp := by
  change partialTraceB (Op.tensor ρ.toOp σ.toOp) = ρ.toOp
  rw [partialTraceB_tensor_op, σ.trace_one]
  simp

/-- Partial trace over `A` of a product state returns the second factor. -/
theorem partialTraceA_tensor {n m : ℕ} (ρ : DensityOp n) (σ : DensityOp m) :
    (DensityOp.partialTraceA (ρ.tensor σ)).toOp = σ.toOp := by
  change partialTraceA (Op.tensor ρ.toOp σ.toOp) = σ.toOp
  rw [partialTraceA_tensor_op, ρ.trace_one]
  simp

/-- Partial trace over a one-dimensional product is the identity on `Op (1 * 1)`. -/
lemma partialTraceB_dim1_op (ρ : Op (1 * 1)) :
    partialTraceB ρ = ρ := by
  ext i j
  fin_cases i
  fin_cases j
  have h0 : finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)) = (0 : Fin (1 * 1)) := by
    ext
    simp
  simp [partialTraceB, h0]

/-- Partial trace over a one-dimensional second factor is the only block of the
original operator. -/
theorem partialTraceB_dim1 {n : ℕ} (ρ : DensityOp (n * 1)) :
    (DensityOp.partialTraceB ρ).toOp =
    fun i j => ρ.toOp (finProdFinEquiv (i, 0)) (finProdFinEquiv (j, 0)) := by
  unfold DensityOp.partialTraceB PosSemidefOp.partialTraceB partialTraceB
  ext i j
  simp only [Matrix.of_apply]
  have h_fin1 : Finset.univ (α := Fin 1) = {0} := by rfl
  rw [h_fin1, Finset.sum_singleton]

end

end Quantum.TensorProducts

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker ComplexOrder

namespace Quantum.TensorProducts

open scoped TensorProduct Kronecker

/-- Entrywise form of commuting `partialTraceB` through a tensor-one sandwich. -/
lemma partialTraceB_sandwich_tensor_one_apply {n m : ℕ}
    (A B : Op n) (M : Op (n * m)) (i j : Fin n) :
    partialTraceB (Op.tensor A (1 : Op m) * M * Op.tensor B (1 : Op m)) i j =
      (A * partialTraceB M * B) i j := by
  simp only [partialTraceB, Matrix.of_apply]
  simp_rw [Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc
    (∑ k : Fin m, ∑ a : Fin n, ∑ c : Fin n,
        A i a * M (finProdFinEquiv (a, k)) (finProdFinEquiv (c, k)) * B c j)
        = ∑ c : Fin n, ∑ a : Fin n, ∑ k : Fin m,
            A i a * M (finProdFinEquiv (a, k)) (finProdFinEquiv (c, k)) * B c j := by
          rw [Finset.sum_comm]
          conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
    _ = ∑ c : Fin n,
          (∑ a : Fin n, A i a *
            ∑ k : Fin m, M (finProdFinEquiv (a, k)) (finProdFinEquiv (c, k))) * B c j := by
          congr 1; ext c
          rw [Finset.sum_mul]
          congr 1; ext a
          rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Partial trace over `B` commutes with sandwiching by `A ⊗ 1` and `B ⊗ 1`. -/
lemma partialTraceB_sandwich_tensor_one {n m : ℕ}
    (A B : Op n) (M : Op (n * m)) :
    partialTraceB (Op.tensor A (1 : Op m) * M * Op.tensor B (1 : Op m)) =
      A * partialTraceB M * B := by
  ext i j
  exact partialTraceB_sandwich_tensor_one_apply A B M i j

/-!
### Trailing-factor reassociation infrastructure

Generic plumbing for commuting `partialTraceB` (which traces the trailing tensor factor)
through a dimension-reassociation cast `(Nat.mul_assoc …).symm ▸ ·` that splits a spectator
register `d1 * d2` so that only the trailing `d2` factor is traced and the inner `d1` survives.
-/

/-- Reassociation index identity for `finProdFinEquiv`:
`(p ⊗ q) ⊗ r` and `p ⊗ (q ⊗ r)` agree up to the dimension cast. -/
lemma finProdFinEquiv_assoc_cast {a b c : ℕ} (p : Fin a) (q : Fin b) (r : Fin c) :
    finProdFinEquiv (finProdFinEquiv (p, q), r) =
      Fin.cast (Nat.mul_assoc a b c).symm (finProdFinEquiv (p, finProdFinEquiv (q, r))) := by
  apply Fin.ext
  simp [finProdFinEquiv_apply_val]
  ring

/-- The `Fin.cast`-reassociated nested product index. -/
lemma finProdFinEquiv_cast_assoc {a b c : ℕ} (p : Fin a) (q : Fin b) (r : Fin c) :
    Fin.cast (Nat.mul_assoc a b c) (finProdFinEquiv (finProdFinEquiv (p, q), r)) =
      finProdFinEquiv (p, finProdFinEquiv (q, r)) := by
  rw [finProdFinEquiv_assoc_cast]
  simp

/-- Decomposition of a `Fin.cast`-reassociated index under `finProdFinEquiv.symm`. -/
lemma finProdFinEquiv_symm_cast_assoc {a b c : ℕ} (I : Fin (a * b * c)) :
    finProdFinEquiv.symm (Fin.cast (Nat.mul_assoc a b c) I) =
      ((finProdFinEquiv.symm (finProdFinEquiv.symm I).1).1,
       finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm I).1).2,
         (finProdFinEquiv.symm I).2)) := by
  have hI : Fin.cast (Nat.mul_assoc a b c) I =
      finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm I).1).1,
        finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm I).1).2,
          (finProdFinEquiv.symm I).2)) := by
    conv_lhs => rw [show I = finProdFinEquiv (finProdFinEquiv ((finProdFinEquiv.symm
      (finProdFinEquiv.symm I).1).1, (finProdFinEquiv.symm (finProdFinEquiv.symm I).1).2),
      (finProdFinEquiv.symm I).2) by simp only [Prod.mk.eta, Equiv.apply_symm_apply]]
    rw [finProdFinEquiv_assoc_cast]
    simp
  rw [hI, Equiv.symm_apply_apply]

/-- Cast distributes over operator multiplication. -/
lemma eqRec_op_mul {n m : ℕ} (h : n = m) (X Y : Op n) :
    (h ▸ (X * Y) : Op m) = (h ▸ X) * (h ▸ Y) := by
  subst h; rfl

/-- General tensor associativity up to the dimension-reassociation cast. -/
lemma Op.tensor_assoc {a b c : ℕ} (X : Op a) (Y : Op b) (Z : Op c) :
    (Nat.mul_assoc a b c).symm ▸ Op.tensor X (Op.tensor Y Z) =
      Op.tensor (Op.tensor X Y) Z := by
  ext I J
  rw [matrix_eqRec_apply, Op_tensor_apply_finProd, Op_tensor_apply_finProd,
    Op_tensor_apply_finProd, Op_tensor_apply_finProd,
    finProdFinEquiv_symm_cast_assoc, finProdFinEquiv_symm_cast_assoc]
  simp only [Equiv.symm_apply_apply]
  ring

/-- Reassociating a trailing identity factor `1_{d1·d2}` into `1_{d1} ⊗ 1_{d2}`. -/
lemma Op.tensor_one_assoc {a d1 d2 : ℕ} (N : Op a) :
    (Nat.mul_assoc a d1 d2).symm ▸ Op.tensor N (1 : Op (d1 * d2)) =
      Op.tensor (Op.tensor N (1 : Op d1)) (1 : Op d2) := by
  rw [← Op.tensor_one (n := d1) (m := d2), Op.tensor_assoc]

/-- **Trailing-factor `partialTraceB_sandwich_tensor_one`.**  Conjugation by `A ⊗ 1` and
`B ⊗ 1` acting trivially on the trailing `d2` factor of the spectator `d1 * d2` commutes
with tracing out only that `d2` factor (after the reassociation cast). -/
lemma partialTraceB_sandwich_tensor_one_trailing {p d1 d2 : ℕ}
    (A B : Op p) (M : Op (p * (d1 * d2))) :
    partialTraceB ((Nat.mul_assoc p d1 d2).symm ▸
        (Op.tensor A (1 : Op (d1 * d2)) * M * Op.tensor B (1 : Op (d1 * d2)))) =
      Op.tensor A (1 : Op d1) * partialTraceB ((Nat.mul_assoc p d1 d2).symm ▸ M)
        * Op.tensor B (1 : Op d1) := by
  rw [eqRec_op_mul, eqRec_op_mul, Op.tensor_one_assoc, Op.tensor_one_assoc,
    partialTraceB_sandwich_tensor_one]

/-- Entry expansion for left-multiplication by the identity tensored with an
operator on the right factor. -/
lemma one_tensor_mul_apply {n m : ℕ}
    (U : Op m) (M : Op (n * m)) (k : Fin n) (i : Fin m) (p : Fin (n * m)) :
    (Op.tensor (1 : Op n) U * M) (finProdFinEquiv (k, i)) p =
      ∑ a : Fin m, U i a * M (finProdFinEquiv (k, a)) p := by
  simp only [Matrix.mul_apply]
  rw [(Fintype.sum_equiv finProdFinEquiv
    (fun ab => (Op.tensor (1 : Op n) U) (finProdFinEquiv (k, i)) (finProdFinEquiv ab) *
      M (finProdFinEquiv ab) p)
    _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [show k ≠ l from fun h => hl h.symm]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Entry expansion for sandwiching by identities tensored with operators on
the right factor. -/
lemma one_tensor_mul_mul_one_tensor_apply {n m : ℕ}
    (A B : Op m) (M : Op (n * m)) (k l : Fin n) (i j : Fin m) :
    (Op.tensor (1 : Op n) A * M * Op.tensor (1 : Op n) B)
        (finProdFinEquiv (k, i)) (finProdFinEquiv (l, j)) =
      ∑ a : Fin m, ∑ c : Fin m,
        A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * B c j := by
  rw [Matrix.mul_apply]
  simp_rw [one_tensor_mul_apply]
  rw [(Fintype.sum_equiv finProdFinEquiv
    (fun cd => (∑ a, A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv cd)) *
      (Op.tensor (1 : Op n) B) (finProdFinEquiv cd) (finProdFinEquiv (l, j)))
    _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, Equiv.symm_apply_apply]
  calc
    (∑ x : Fin n, ∑ c : Fin m,
        (∑ a : Fin m, A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (x, c))) *
          ((if x = l then 1 else 0) * B c j))
        = ∑ c : Fin m,
            (∑ a : Fin m, A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c))) *
              B c j := by
          simp
    _ = ∑ a : Fin m, ∑ c : Fin m,
        A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * B c j := by
          rw [← Finset.sum_comm]
          congr 1; ext c
          rw [Finset.sum_mul]

/-- Entrywise form of commuting `partialTraceA` through a one-tensor sandwich. -/
lemma partialTraceA_one_tensor_sandwich_apply {n m : ℕ}
    (A B : Op m) (M : Op (n * m)) (i j : Fin m) :
    partialTraceA (Op.tensor (1 : Op n) A * M * Op.tensor (1 : Op n) B) i j =
      (A * partialTraceA M * B) i j := by
  simp only [partialTraceA, Matrix.of_apply]
  simp_rw [one_tensor_mul_mul_one_tensor_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc
    (∑ k : Fin n, ∑ a : Fin m, ∑ c : Fin m,
        A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (k, c)) * B c j)
        = ∑ c : Fin m, ∑ a : Fin m, ∑ k : Fin n,
            A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (k, c)) * B c j := by
          rw [Finset.sum_comm]
          conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
    _ = ∑ c : Fin m,
          (∑ a : Fin m, A i a *
            ∑ k : Fin n, M (finProdFinEquiv (k, a)) (finProdFinEquiv (k, c))) * B c j := by
          congr 1; ext c
          rw [Finset.sum_mul]
          congr 1; ext a
          rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Partial trace over `A` commutes with sandwiching by `1 ⊗ A` and `1 ⊗ B`. -/
lemma partialTraceA_one_tensor_sandwich {n m : ℕ}
    (A B : Op m) (M : Op (n * m)) :
    partialTraceA (Op.tensor (1 : Op n) A * M * Op.tensor (1 : Op n) B) =
      A * partialTraceA M * B := by
  ext i j
  exact partialTraceA_one_tensor_sandwich_apply A B M i j

/-- `partialTraceA` of a right-factor unitary conjugation is the conjugated
right marginal. -/
lemma partialTraceA_rightTensorUnitaryConj {n m : ℕ}
    (W : UnitaryOp m) (M : Op (n * m)) :
    partialTraceA (rightTensorUnitaryConj W M) =
      W.toOp * partialTraceA M * W.toOp† := by
  unfold rightTensorUnitaryConj
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  exact partialTraceA_one_tensor_sandwich W.toOp W.toOp† M

end Quantum.TensorProducts
