import Mathlib.Data.List.Sort
import Mathlib.Deprecated.Sort
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.FinRange

/-!
# Permutation Representation — Sₙ action on tensor products, Young diagrams, Schur-Weyl

Representation theory for the symmetric group on tensor product spaces,
including Young diagram bookkeeping and block decomposition.

## Main definitions
- `permutationRepresentation`: Unitary representation of Sₙ on (ℂᵈ)^⊗n
- `YoungDiagram`: Partitions of n indexing irreducible representations
- `symmetricProjectorRep`: Projector onto the symmetric subspace

## Main statements
- `permutationRepresentation_mul`: Homomorphism property
- `symmetricSubspace_dimension`: Dimension of the symmetric subspace
- `permutationRepresentation_trace_weighted_sum_commutes_of_commutes`: commutant
  lemma for the character-weighted permutation average

The full Schur-Weyl block-decomposition theorem is *not* formalized in this file. The
`YoungDiagram` type and the `symmetricYoungDiagram` / `YoungDiagram.validForDim` helpers
support the symmetric-subspace bookkeeping (dimension count, trivial-diagram
labelling), not a delivered block-decomposition result.
-/

open Matrix
open scoped Matrix BigOperators ComplexConjugate

/-- Local dagger notation for conjugate transpose. -/
local postfix:max "†" => Matrix.conjTranspose

noncomputable section

namespace Math.RepresentationTheory

/-!
## Permutation Representation

The permutation representation of Sₙ on (ℂᵈ)^⊗n permutes tensor factors:
  U_σ |ψ₁⟩⊗|ψ₂⟩⊗...⊗|ψₙ⟩ = |ψ_{σ⁻¹(1)}⟩⊗|ψ_{σ⁻¹(2)}⟩⊗...⊗|ψ_{σ⁻¹(n)}⟩

This is a unitary representation: U_σ† = U_{σ⁻¹} = U_σ⁻¹.
-/

/-- Index type for d^n dimensional tensor product space.
    We represent indices as functions Fin n → Fin d, encoding which basis
    vector in each tensor factor. -/
abbrev TensorIndex (d n : ℕ) := Fin n → Fin d

/-- The permutation representation matrix on tensor product space.
    U_σ permutes the tensor factors according to σ⁻¹.

    For basis states |i₁⟩⊗|i₂⟩⊗...⊗|iₙ⟩ (represented as function i : Fin n → Fin d):
      U_σ|i⟩ = |i ∘ σ⁻¹⟩

    The matrix element (U_σ)ᵢⱼ = 1 if i = j ∘ σ⁻¹, else 0.
    Equivalently: (U_σ)ᵢⱼ = 1 if i ∘ σ = j, else 0. -/
def permutationRepresentation (d n : ℕ) [NeZero d] (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ :=
  let e := @finFunctionFinEquiv d n
  Matrix.of fun i j =>
    if e.symm i = (e.symm j) ∘ σ.symm then 1 else 0

/-- Helper: (σ₁ * σ₂).symm x = σ₂.symm (σ₁.symm x) -/
private lemma perm_mul_symm_apply {α : Type*} (σ₁ σ₂ : Equiv.Perm α) (x : α) :
    (σ₁ * σ₂).symm x = σ₂.symm (σ₁.symm x) := by
  simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

private lemma perm_inv_symm {α : Type*} (σ : Equiv.Perm α) :
    (σ⁻¹ : Equiv.Perm α).symm = σ := by
  ext x
  simp [Equiv.Perm.inv_def]

/-- Precomposing by the inverse of a product is the same as precomposing by
the two inverses in reverse order. -/
lemma comp_perm_mul_symm {α β : Type*} (f : α → β) (σ₁ σ₂ : Equiv.Perm α) :
    (f ∘ ⇑σ₂.symm) ∘ ⇑σ₁.symm = f ∘ ⇑(σ₁ * σ₂).symm := by
  funext x
  simp only [Function.comp_apply, perm_mul_symm_apply]

/-- Equality after precomposition with a permutation can be moved across the inverse
permutation. -/
lemma eq_comp_perm_symm_iff_comp_perm_eq {α β : Type*} (f g : α → β)
    (σ : Equiv.Perm α) :
    f = g ∘ ⇑σ.symm ↔ f ∘ ⇑σ = g := by
  constructor
  · intro h
    funext x
    have hx := congr_fun h (σ x)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hx
  · intro h
    funext x
    have hx := congr_fun h (σ.symm x)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx

/-- The permutation representation is a group homomorphism:
`U_{σ₁} U_{σ₂} = U_{σ₁σ₂}`. -/
theorem permutationRepresentation_mul (d n : ℕ) [NeZero d]
    (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ₁ * permutationRepresentation d n σ₂ =
    permutationRepresentation d n (σ₁ * σ₂) := by
  ext i j
  simp only [permutationRepresentation, Matrix.mul_apply, Matrix.of_apply]
  set e := @finFunctionFinEquiv d n
  set k₀ := e (e.symm j ∘ ⇑σ₂.symm)
  have hk₀ : e.symm k₀ = e.symm j ∘ ⇑σ₂.symm := by simp [k₀]
  rw [Finset.sum_eq_single k₀]
  · rw [if_pos hk₀, mul_one, hk₀, comp_perm_mul_symm]
  · intro k _ hk
    by_cases h : e.symm k = e.symm j ∘ ⇑σ₂.symm
    · exact absurd (e.symm.injective (h.trans hk₀.symm)) hk
    · simp [h]
  · intro h; exact absurd (Finset.mem_univ k₀) h

/-- The identity permutation gives the identity matrix. -/
theorem permutationRepresentation_one (d n : ℕ) [NeZero d] :
    permutationRepresentation d n 1 = 1 := by
  ext i j
  unfold permutationRepresentation
  simp only [Matrix.of_apply, Matrix.one_apply, Equiv.Perm.one_symm]
  by_cases h : i = j
  · simp [h]
  · simp only [h, ↓reduceIte]
    split_ifs with heq
    · exfalso
      apply h
      have : (@finFunctionFinEquiv d n).symm i = (@finFunctionFinEquiv d n).symm j := heq
      exact (@finFunctionFinEquiv d n).symm.injective this
    · rfl

/-- The inverse permutation gives the inverse (conjugate transpose) matrix.
    Permutation matrices have 0/1 entries; transposing inverts the permutation. -/
theorem permutationRepresentation_inv (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ⁻¹ = (permutationRepresentation d n σ)† := by
  ext i j
  simp only [permutationRepresentation, Matrix.of_apply, Matrix.conjTranspose_apply]
  set e := @finFunctionFinEquiv d n
  have hstar : star (if e.symm j = e.symm i ∘ ⇑σ.symm then (1 : ℂ) else 0) =
    if e.symm j = e.symm i ∘ ⇑σ.symm then 1 else 0 := by split_ifs <;> simp
  rw [hstar]
  suffices key : (e.symm i = e.symm j ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin n)).symm) ↔
      (e.symm j = e.symm i ∘ ⇑σ.symm) by simp only [key]
  rw [perm_inv_symm]
  simpa only [Equiv.symm_symm, eq_comm] using
    (eq_comp_perm_symm_iff_comp_perm_eq (e.symm i) (e.symm j) σ.symm)

/-- The transpose of a permutation representation matrix represents the inverse
permutation. -/
theorem permutationRepresentation_transpose (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation d n σ)ᵀ = permutationRepresentation d n σ⁻¹ := by
  ext i j
  simp only [permutationRepresentation, Matrix.of_apply, Matrix.transpose_apply]
  set e := @finFunctionFinEquiv d n
  suffices key : (e.symm j = e.symm i ∘ ⇑σ.symm) ↔
      (e.symm i = e.symm j ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin n)).symm) by
    simp only [key]
  rw [perm_inv_symm]
  simpa only [eq_comm] using
    (eq_comp_perm_symm_iff_comp_perm_eq (e.symm j) (e.symm i) σ)

/-- The character of the permutation representation is invariant under inversion. -/
theorem permutationRepresentation_trace_inv (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation d n σ⁻¹).trace =
      (permutationRepresentation d n σ).trace := by
  rw [← permutationRepresentation_transpose d n σ, Matrix.trace_transpose]

/-- The permutation representation is unitary: U_σ† U_σ = I and U_σ U_σ† = I.
    Follows from U_{σ⁻¹} = U_σ† and the group homomorphism property. -/
theorem permutationRepresentation_unitary (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    let U := permutationRepresentation d n σ
    U† * U = 1 ∧ U * U† = 1 := by
  constructor
  · -- U† * U = U_{σ⁻¹} * U_σ = U_{σ⁻¹σ} = U_1 = 1
    rw [← permutationRepresentation_inv, permutationRepresentation_mul,
        inv_mul_cancel, permutationRepresentation_one]
  · -- U * U† = U_σ * U_{σ⁻¹} = U_{σσ⁻¹} = U_1 = 1
    rw [← permutationRepresentation_inv, permutationRepresentation_mul,
        mul_inv_cancel, permutationRepresentation_one]

/-- Conjugating a permutation representation by another represented permutation
implements group conjugation. -/
theorem permutationRepresentation_conj (d n : ℕ) [NeZero d]
    (π σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n π * permutationRepresentation d n σ *
      (permutationRepresentation d n π)† =
    permutationRepresentation d n (π * σ * π⁻¹) := by
  rw [← permutationRepresentation_inv, permutationRepresentation_mul,
    permutationRepresentation_mul]

/-- The character of the permutation representation is invariant under group
conjugation. -/
theorem permutationRepresentation_trace_conj (d n : ℕ) [NeZero d]
    (π σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation d n (π * σ * π⁻¹)).trace =
      (permutationRepresentation d n σ).trace := by
  rw [← permutationRepresentation_conj d n π σ]
  calc
    (permutationRepresentation d n π * permutationRepresentation d n σ *
        (permutationRepresentation d n π)†).trace
        = ((permutationRepresentation d n π)† *
            (permutationRepresentation d n π * permutationRepresentation d n σ)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = (permutationRepresentation d n σ).trace := by
      rw [← Matrix.mul_assoc, (permutationRepresentation_unitary d n π).1, Matrix.one_mul]

/-!
## Young Diagrams

Young diagrams (or Young tableaux) are partitions of n that index the
irreducible representations of Sₙ. They also index the irreducible
representations appearing in (ℂᵈ)^⊗n under the joint Sₙ × GL(d) action.
-/

/-- A Young diagram is a partition of n: a non-increasing sequence of
    positive integers summing to n.

    Example: For n=4, the partitions are:
    - [4]: single row of 4 boxes
    - [3,1]: row of 3 + row of 1
    - [2,2]: two rows of 2
    - [2,1,1]: row of 2 + two rows of 1
    - [1,1,1,1]: four rows of 1 -/
structure YoungDiagram (n : ℕ) where
  /-- The parts of the partition (row lengths). -/
  parts : List ℕ
  /-- All parts are positive. -/
  parts_pos : ∀ p ∈ parts, 0 < p
  /-- The parts sum to n. -/
  sum_eq : parts.sum = n
  /-- The parts are sorted in non-increasing order. -/
  parts_sorted : parts.Pairwise (· ≥ ·)

/-- Number of rows in the Young diagram. -/
def YoungDiagram.numRows {n : ℕ} (Y : YoungDiagram n) : ℕ := Y.parts.length

/-- Number of columns (length of first row, or 0 if empty). -/
def YoungDiagram.numCols {n : ℕ} (Y : YoungDiagram n) : ℕ :=
  match Y.parts with
  | [] => 0
  | p :: _ => p

/-- The trivial (single-row) partition [n]. This corresponds to the
    symmetric representation. -/
def YoungDiagram.trivial (n : ℕ) (hn : 0 < n) : YoungDiagram n where
  parts := [n]
  parts_pos := by simp [hn]
  sum_eq := by simp
  parts_sorted := by simp

/-- The sign (single-column) partition [1,1,...,1]. This corresponds to the
    antisymmetric representation. Only valid when d ≥ n (needs n boxes in one column). -/
def YoungDiagram.sign (n : ℕ) : YoungDiagram n where
  parts := List.replicate n 1
  parts_pos := by simp
  sum_eq := by simp [List.sum_replicate]
  parts_sorted := by
    induction n with
    | zero => simp
    | succ k ih =>
      simp only [List.replicate_succ]
      rw [List.pairwise_cons]
      constructor
      · intro b hb
        simp only [List.mem_replicate, ne_eq] at hb
        omega
      · exact ih

/-!
## Schur-Weyl Duality

Schur-Weyl duality describes the decomposition of (ℂᵈ)^⊗n under the
commuting actions of Sₙ (permuting factors) and GL(d,ℂ) (acting on each factor).

The key result is that:
  (ℂᵈ)^⊗n ≅ ⊕_λ V_λ ⊗ W_λ

where:
- λ ranges over Young diagrams with at most d rows and n boxes
- V_λ is the irreducible Sₙ-representation corresponding to λ
- W_λ is the irreducible GL(d,ℂ)-representation corresponding to λ

For quantum information, the important consequence is that permutation-invariant
states are supported on the symmetric subspace (λ = [n]).

This section is mathematical background. Only the symmetric-subspace slice (λ = [n]) is
formalized below (via `symmetricProjectorRep` and `symmetricSubspace_dimension`); the full
`⊕_λ V_λ ⊗ W_λ` decomposition is not a theorem in this file.
-/

/-- Young diagrams with at most d rows (valid for GL(d) representations). -/
def YoungDiagram.validForDim {n : ℕ} (Y : YoungDiagram n) (d : ℕ) : Prop :=
  Y.numRows ≤ d

/-- The symmetric subspace corresponds to the trivial Young diagram [n].
    This is the subspace of states invariant under all permutations. -/
def symmetricYoungDiagram (n : ℕ) (hn : 0 < n) : YoungDiagram n :=
  YoungDiagram.trivial n hn

/-- The symmetric power of `Fin d` has the stars-and-bars cardinality. -/
lemma card_sym_fin_eq_choose (d n : ℕ) [NeZero d] :
    Fintype.card (Sym (Fin d) n) = Nat.choose (n + d - 1) (d - 1) := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [show d + n - 1 = n + d - 1 from by omega]
  exact (Nat.choose_symm_of_eq_add (by omega)).symm

/-- The dimension of the symmetric subspace is C(n+d-1, d-1) = (n+d-1)!/(n!(d-1)!).
    This is the number of ways to distribute n indistinguishable balls into d bins,
    or equivalently, the number of homogeneous polynomials of degree n in d variables.

    Reference: "Stars and bars" combinatorics. -/
theorem symmetricSubspace_dimension (d n : ℕ) [NeZero d] [NeZero n] :
    -- dim(Sym^n(ℂᵈ)) = C(n+d-1, d-1)
    -- The number of symmetric basis states equals the binomial coefficient
    let symDim := Nat.choose (n + d - 1) (d - 1)
    -- This equals the number of ways to choose occupation numbers
    -- (n₁,...,nₐ) with n₁ + ... + nₐ = n and all nᵢ ≥ 0
    symDim = Nat.card {f : Fin d → ℕ // ∑ i, f i = n} := by
  simp only
  haveI : Fintype {f : Fin d → ℕ // ∑ i, f i = n} :=
    Fintype.ofEquiv (Sym (Fin d) n) (Sym.equivNatSumOfFintype (Fin d) n)
  rw [Nat.card_eq_fintype_card,
      ← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin d) n),
      card_sym_fin_eq_choose]

/-!
## The symmetric projector

The symmetric projector `P_sym = (1/n!) Σ_{σ ∈ Sₙ} U_σ` projects onto the trivial
(`λ = [n]`) isotypic component of the Schur–Weyl decomposition: the totally symmetric
subspace `Sym^n(ℂᵈ)`.  It is the one isotypic projector of `(ℂᵈ)^{⊗n}` available in closed
form without the irreducible characters `χ_λ` of the general Young diagram.
-/

/-- The symmetric projector: P_sym = (1/n!) Σ_{σ ∈ Sₙ} U_σ.
    This projects onto the totally symmetric subspace. -/
def symmetricProjectorRep (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ :=
  (1 / (Nat.factorial n : ℂ)) • ∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ

/-- The unnormalized sum of permutation representation matrices is invariant
under left multiplication by any represented permutation. -/
lemma permutationRepresentation_mul_sum (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ *
      (∑ τ : Equiv.Perm (Fin n), permutationRepresentation d n τ) =
    ∑ τ : Equiv.Perm (Fin n), permutationRepresentation d n τ := by
  rw [Finset.mul_sum]
  simp_rw [permutationRepresentation_mul]
  exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)

/-- Squaring the unnormalized symmetric group average multiplies it by `n!`. -/
lemma permutationRepresentation_sum_mul_self (d n : ℕ) [NeZero d] :
    (∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ) *
      (∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ) =
    (Fintype.card (Equiv.Perm (Fin n))) •
      ∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ := by
  rw [Finset.sum_mul]
  simp_rw [permutationRepresentation_mul_sum]
  rw [Finset.sum_const, Finset.card_univ]

/-- The unnormalized symmetric group average is self-adjoint. -/
lemma permutationRepresentation_sum_conjTranspose (d n : ℕ) [NeZero d] :
    (∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ)† =
    ∑ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ := by
  rw [conjTranspose_sum]
  simp_rw [← permutationRepresentation_inv]
  exact Fintype.sum_bijective (·⁻¹) inv_involutive.bijective _ _ (fun _ => rfl)

/-- The symmetric projector is a projector: P² = P and P† = P.
    Idempotence uses left-invariance of the group sum (U_σ · S = S).
    Hermiticity uses that entries are real and relabels σ ↦ σ⁻¹. -/
theorem symmetricProjectorRep_is_projector (d n : ℕ) [NeZero d] [NeZero n] :
    let P := symmetricProjectorRep d n
    P * P = P ∧ P† = P := by
  constructor
  · simp only [symmetricProjectorRep]
    rw [smul_mul_smul_comm, permutationRepresentation_sum_mul_self,
        Fintype.card_perm, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    have hn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  · simp only [symmetricProjectorRep, conjTranspose_smul]
    congr 1
    · rw [star_div₀, star_one, star_natCast]
    · rw [permutationRepresentation_sum_conjTranspose]

/-- Conjugation by a fixed group element is a bijection. -/
lemma mul_conj_bijective {G : Type*} [Group G] (g : G) :
    Function.Bijective (fun x : G => g * x * g⁻¹) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h'
  · intro y
    refine ⟨g⁻¹ * y * g, ?_⟩
    simp [mul_assoc]

/-- The character-weighted sum of permutation representation matrices is
invariant under conjugation by any represented permutation. -/
theorem sum_permRep_trace_smul_conj_eq (d n : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin n)) :
    permutationRepresentation d n π *
      (∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ) *
      (permutationRepresentation d n π)† =
    ∑ σ : Equiv.Perm (Fin n),
      (permutationRepresentation d n σ).trace • permutationRepresentation d n σ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, permutationRepresentation_conj]
  exact Fintype.sum_bijective (fun σ : Equiv.Perm (Fin n) => π * σ * π⁻¹)
    (mul_conj_bijective π) _ _ (fun σ => by rw [permutationRepresentation_trace_conj d n π σ])

/-- The character-weighted sum of permutation representation matrices is fixed by
plain matrix transpose. -/
theorem sum_permRep_trace_smul_transpose (d n : ℕ) [NeZero d] :
    (∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ)ᵀ =
      ∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ := by
  rw [Matrix.transpose_sum]
  simp_rw [Matrix.transpose_smul, permutationRepresentation_transpose]
  exact Fintype.sum_bijective (fun σ : Equiv.Perm (Fin n) => σ⁻¹)
    inv_involutive.bijective _ _ (fun σ => by rw [permutationRepresentation_trace_inv d n σ])

/-- The character-weighted permutation average commutes with every matrix
that commutes with each tensor-factor permutation representation. -/
lemma permutationRepresentation_trace_weighted_sum_commutes_of_commutes
    {d n : ℕ} [NeZero d] [NeZero n]
    (W : Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ)
    (hW : ∀ σ : Equiv.Perm (Fin n),
      W * permutationRepresentation d n σ =
        permutationRepresentation d n σ * W) :
    W * (∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ) =
      (∑ σ : Equiv.Perm (Fin n),
        (permutationRepresentation d n σ).trace • permutationRepresentation d n σ) * W := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro σ _
  calc
    W * ((permutationRepresentation d n σ).trace • permutationRepresentation d n σ)
        = (permutationRepresentation d n σ).trace •
            (W * permutationRepresentation d n σ) := by
          rw [Matrix.mul_smul]
    _ = (permutationRepresentation d n σ).trace •
            (permutationRepresentation d n σ * W) := by
          rw [hW σ]
    _ = ((permutationRepresentation d n σ).trace •
            permutationRepresentation d n σ) * W := by
          rw [Matrix.smul_mul]

/-- The trace of a permutation representation matrix counts tensor basis functions
fixed by that permutation. -/
lemma permutationRepresentation_trace_eq_fixed_card (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation d n σ).trace =
      ((Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f)).card : ℂ) := by
  let e := @finFunctionFinEquiv d n
  have pred_iff : ∀ f : Fin n → Fin d, (f = f ∘ ⇑σ.symm) ↔ (f ∘ ⇑σ = f) :=
    fun f => eq_comp_perm_symm_iff_comp_perm_eq f f σ
  have nat_step : ∑ i : Fin (d ^ n),
      (if e.symm i = e.symm i ∘ ⇑σ.symm then (1 : ℕ) else 0) =
      (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f)).card := by
    rw [Fintype.sum_equiv e.symm
        (fun i => if e.symm i = e.symm i ∘ ⇑σ.symm then (1 : ℕ) else 0)
        (fun f => if f = f ∘ ⇑σ.symm then (1 : ℕ) else 0)
        (fun _ => rfl),
      Finset.sum_boole]
    norm_cast
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact pred_iff f
  simp only [Matrix.trace, Matrix.diag_apply, permutationRepresentation, Matrix.of_apply]
  exact_mod_cast nat_step

/-- The tensor-factor permutation representation has nonzero character: at
least the constant tensor word is fixed by every permutation. -/
lemma permutationRepresentation_trace_ne_zero (d n : ℕ) [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation d n σ).trace ≠ 0 := by
  rw [permutationRepresentation_trace_eq_fixed_card]
  let f : Fin n → Fin d := fun _ => 0
  have hf :
      f ∈ Finset.univ.filter (fun g : Fin n → Fin d => g ∘ ⇑σ = g) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    rfl
  have hcard :
      (Finset.univ.filter (fun g : Fin n → Fin d => g ∘ ⇑σ = g)).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hf
  exact_mod_cast hcard

/-!
## Trace against the permutation representation

The trace of an operator `M` on `(ℂᵈ)^⊗n` against `U_σ` contracts each digit string with its
`σ⁻¹`-permuted copy. For a tensor product of a family of operators this is the cycle-product
identity `Tr((⊗ₖ Aₖ) U_σ) = ∏_{cycles c of σ} Tr(∏_{k ∈ c} Aₖ)` in index form, stated as
`Quantum.TensorProducts.trace_tensorFamily_mul_permutationRepresentation`.
Setting every factor to `1` recovers the character
`Tr U_σ = d^{#cycles}` (`permutationRepresentation_trace_eq_fixed_card`).

Reference: Harrow, "The Church of the Symmetric Subspace" §3;
Christandl–König–Renner 2009, `lem:extractpart`.
-/

/-- **Trace against the permutation representation (general operator).**

For any operator `M` on `(ℂ^d)^{⊗n}`, the trace of `M · U_σ` contracts the row tuple
`f` against its `σ⁻¹`-permuted copy:

  `Tr(M · U_σ) = ∑_{f : Fin n → Fin d} M_{e f, e (f ∘ σ⁻¹)}`,   `e = finFunctionFinEquiv d n`.

`M` need not be a tensor product. In each column `i = e f` of `U_σ` the unique nonzero entry sits
at row `e (f ∘ σ⁻¹)`, so the diagonal sum of `M · U_σ` collapses to a single `M`-entry,
reindexed by `finFunctionFinEquiv`. -/
theorem trace_mul_permutationRepresentation (d n : ℕ) [NeZero d]
    (M : Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ) (σ : Equiv.Perm (Fin n)) :
    (M * permutationRepresentation d n σ).trace
      = ∑ f : Fin n → Fin d,
          M (@finFunctionFinEquiv d n f) (@finFunctionFinEquiv d n (f ∘ σ.symm)) := by
  set e := @finFunctionFinEquiv d n with he
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, permutationRepresentation, Matrix.of_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single (e (f ∘ σ.symm))]
  · rw [Equiv.symm_apply_apply, if_pos rfl, mul_one]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro hcontra; exact hj (by rw [← hcontra, Equiv.apply_symm_apply])
  · intro h; exact absurd (Finset.mem_univ _) h

section PermFunctionAction

local instance permFinAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n) :=
  Equiv.Perm.applyMulAction _

local instance permFunAction (d n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n → Fin d) :=
  arrowAction

local instance permFunOrbitRelDecidable (d n : ℕ) :
    DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r := by
  intro f g
  simp only [MulAction.orbitRel_apply]
  rw [MulAction.mem_orbit_iff]
  exact Fintype.decidableExistsFintype

/-- For the arrow action of permutations on functions, fixed points are exactly
functions satisfying `f ∘ σ = f`. -/
lemma mem_fixedBy_perm_arrow_iff (d n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin d) :
    f ∈ MulAction.fixedBy (Fin n → Fin d) σ ↔ f ∘ ⇑σ = f := by
  rw [MulAction.mem_fixedBy]
  constructor
  · intro hf
    funext k
    have h : f (σ.symm (σ k)) = f (σ k) := congr_fun hf (σ k)
    simp only [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro hf
    funext k
    change f (σ.symm k) = f k
    have h := congr_fun hf (σ.symm k)
    simp only [Function.comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- The fixed-point set of the arrow action has the same cardinality as the
explicit filter of functions satisfying `f ∘ σ = f`. -/
lemma card_fixedBy_perm_arrow_eq_filter_card (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (Fin n → Fin d) σ) =
      (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f)).card := by
  rw [← Fintype.card_coe (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f))]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_fixedBy_perm_arrow_iff d n σ f).mp hf⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact (mem_fixedBy_perm_arrow_iff d n σ f).mpr hf⟩
    left_inv := fun ⟨f, _⟩ => by simp
    right_inv := fun ⟨f, _⟩ => by simp
  }

/-- Two functions `Fin n → Fin d` with permutation-equivalent value lists lie
in the same orbit under permutations of the domain. -/
lemma perm_fun_orbitRel_of_list_ofFn_perm (f g : Fin n → Fin d)
    (hperm : (List.ofFn f).Perm (List.ofFn g)) :
    MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d) f g := by
  apply MulAction.orbitRel_apply.mpr
  rw [MulAction.mem_orbit_iff]
  let σf := Tuple.sort f
  let σg := Tuple.sort g
  have hfmon : Monotone (f ∘ σf) := Tuple.monotone_sort f
  have hgmon : Monotone (g ∘ σg) := Tuple.monotone_sort g
  have hperm2 : (List.ofFn (f ∘ σf)).Perm (List.ofFn (g ∘ σg)) :=
    (Equiv.Perm.ofFn_comp_perm σf f).trans
      (hperm.trans (Equiv.Perm.ofFn_comp_perm σg g).symm)
  have heq : f ∘ σf = g ∘ σg :=
    List.ofFn_injective
      (List.Perm.eq_of_sortedLE hfmon.sortedLE_ofFn hgmon.sortedLE_ofFn hperm2)
  refine ⟨σg.symm.trans σf, funext (fun k => ?_)⟩
  change g ((σg.symm.trans σf)⁻¹ • k) = f k
  rw [Equiv.Perm.smul_def, Equiv.Perm.coe_inv, Equiv.symm_trans_apply, Equiv.symm_symm]
  have h1 := congr_fun heq (σf.symm k)
  simp only [Function.comp, Equiv.apply_symm_apply] at h1
  exact h1.symm

/-- The symmetric multiset of values of a function is unchanged by permuting
the function's domain. -/
lemma sym_ofFn_smul_perm (f : Fin n → Fin d) (σ : Equiv.Perm (Fin n)) :
    (⟨Multiset.ofList (List.ofFn (σ • f)), by simp⟩ : Sym (Fin d) n) =
      ⟨Multiset.ofList (List.ofFn f), by simp⟩ := by
  apply Sym.ext
  simp only [Sym.coe_mk]
  exact Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm σ.symm f)

/-- Two functions lie in the same permutation orbit exactly when they determine
the same symmetric multiset of values. -/
lemma sym_of_fn_eq_iff_perm_fun_orbit_rel (f g : Fin n → Fin d) :
    (⟨Multiset.ofList (List.ofFn f), by simp⟩ : Sym (Fin d) n) =
      ⟨Multiset.ofList (List.ofFn g), by simp⟩ ↔
    MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d) f g := by
  constructor
  · intro h
    apply perm_fun_orbitRel_of_list_ofFn_perm
    have hmultiset :
        Multiset.ofList (List.ofFn f) = Multiset.ofList (List.ofFn g) := by
      simpa only [Sym.coe_mk] using congr_arg Sym.toMultiset h
    exact Multiset.coe_eq_coe.mp hmultiset
  · intro hfg
    have hfg' : f ∈ MulAction.orbit (Equiv.Perm (Fin n)) g :=
      MulAction.orbitRel_apply.mp hfg
    rw [MulAction.mem_orbit_iff] at hfg'
    obtain ⟨σ, hσ⟩ := hfg'
    rw [← hσ]
    exact sym_ofFn_smul_perm g σ

private lemma list_ofFn_get_of_length_eq {α : Type*} (l : List α) {n : ℕ}
    (h : l.length = n) :
    (List.ofFn fun i : Fin n => l.get ⟨i.val, by omega⟩) = l := by
  subst n
  simp

/-- A symmetric multiset is represented by reading off the elements of any
chosen list representative. -/
lemma sym_of_fn_get_to_list_eq {α : Type*} (s : Sym α n) :
    (⟨Multiset.ofList (List.ofFn fun i : Fin n => s.val.toList.get ⟨i.val, by
      have hlen : s.val.toList.length = n := by
        rw [Multiset.length_toList]
        exact_mod_cast s.2
      omega⟩), by simp⟩ : Sym α n) = s := by
  have hlen : s.val.toList.length = n := by
    rw [Multiset.length_toList]
    exact_mod_cast s.2
  apply Sym.ext
  simp only [Sym.coe_mk]
  rw [list_ofFn_get_of_length_eq s.val.toList hlen]
  exact Multiset.coe_toList s.val

/-- Orbits of functions `Fin n → Fin d` under domain permutations are the
same data as multisets of `n` elements of `Fin d`. -/
noncomputable def permFunOrbitsEquivSym (d n : ℕ) :
    Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)) ≃
      Sym (Fin d) n := by
  let toSymFn : (Fin n → Fin d) → Sym (Fin d) n :=
    fun f => ⟨Multiset.ofList (List.ofFn f), by simp⟩
  apply Equiv.ofBijective (Quotient.lift toSymFn (fun f g hfg => by
    simpa only [toSymFn] using (sym_of_fn_eq_iff_perm_fun_orbit_rel f g).mpr hfg))
  constructor
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn with | h f =>
    induction q₂ using Quotient.inductionOn with | h g =>
    simp only [Quotient.lift_mk] at h
    apply Quotient.sound
    exact (sym_of_fn_eq_iff_perm_fun_orbit_rel f g).mp (by simpa only [toSymFn] using h)
  · intro s
    use Quotient.mk _ (fun i : Fin n => s.val.toList.get ⟨i.val, by
      have hlen : s.val.toList.length = n := by
        rw [Multiset.length_toList]
        exact_mod_cast s.2
      omega⟩)
    simpa only [Quotient.lift_mk, toSymFn] using sym_of_fn_get_to_list_eq s

/-- Orbits of functions `Fin n → Fin d` under domain permutations are classified
by multisets of length `n`, hence counted by stars and bars. -/
lemma card_permFunOrbits_eq_choose (d n : ℕ) [NeZero d] [NeZero n]
    [DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r] :
    Fintype.card (Quotient (MulAction.orbitRel
      (Equiv.Perm (Fin n)) (Fin n → Fin d))) =
    Nat.choose (n + d - 1) (d - 1) := by
  rw [show Nat.choose (n + d - 1) (d - 1) = Fintype.card (Sym (Fin d) n) from
    (card_sym_fin_eq_choose d n).symm]
  exact Fintype.card_congr (permFunOrbitsEquivSym d n)

/-- The sum of traces of all permutation representation matrices equals
    n! * C(n+d-1, d-1). Each Tr(U_σ) = d^{c(σ)} (number of cycles), and the
    identity ∑_σ d^{c(σ)} = n! · C(n+d-1,d-1) follows from a double-counting
    argument: count pairs (σ, f) where f : [n] → [d] and f ∘ σ = f. -/
lemma sum_permRep_trace_eq (d n : ℕ) [NeZero d] [NeZero n] :
    ∑ σ : Equiv.Perm (Fin n),
      (permutationRepresentation d n σ).trace =
    (n.factorial : ℂ) * (Nat.choose (n + d - 1) (d - 1) : ℂ) := by
  simp_rw [permutationRepresentation_trace_eq_fixed_card]
  letI : DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r :=
    permFunOrbitRelDecidable d n
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin n)) (Fin n → Fin d)
  rw [show Fintype.card (Equiv.Perm (Fin n)) = n.factorial from
    (Fintype.card_perm).trans (by simp [Fintype.card_fin])] at burnside
  have key : ∑ σ : Equiv.Perm (Fin n),
    (Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑σ = f)).card =
      n.factorial * Nat.choose (n + d - 1) (d - 1) := by
    simp_rw [← card_fixedBy_perm_arrow_eq_filter_card d n]
    rw [burnside, card_permFunOrbits_eq_choose d n, mul_comm]
  exact_mod_cast key

end PermFunctionAction

section PermFunctionActionGeneral

local instance permFinAction' (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n) :=
  Equiv.Perm.applyMulAction _

local instance permFunAction' (β : Type*) (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin n → β) :=
  arrowAction

/-- **Orbit count, arbitrary finite codomain** (generalizes `card_permFunOrbits_eq_choose`
from `Fin d` to any `Fintype β`): the orbits of `Sₙ` acting on `Fin n → β` by domain
permutation are counted by stars-and-bars on `Fintype.card β` symbols. Proved by transporting
through a chosen equivalence `β ≃ Fin (Fintype.card β)`, which is equivariant for the
domain-permutation (`arrowAction`) action since it only postcomposes the codomain. -/
lemma card_permFunOrbits_eq_choose_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) [NeZero n] [NeZero (Fintype.card β)]
    [DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β)).r] :
    Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β))) =
      Nat.choose (n + Fintype.card β - 1) (Fintype.card β - 1) := by
  set d := Fintype.card β with hd
  let e : β ≃ Fin d := Fintype.equivFin β
  letI hdec : DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → Fin d)).r :=
    permFunOrbitRelDecidable d n
  rw [← card_permFunOrbits_eq_choose d n]
  apply Fintype.card_congr
  apply Quotient.congr (Equiv.arrowCongr (Equiv.refl (Fin n)) e)
  intro f g
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, funext fun k => ?_⟩
    have hk : g (σ⁻¹ • k) = f k := congr_fun hσ k
    change e (g (σ⁻¹ • k)) = e (f k)
    rw [hk]
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, funext fun k => ?_⟩
    have hk : e (g (σ⁻¹ • k)) = e (f k) := congr_fun hσ k
    exact e.injective hk

/-- Generalization of `mem_fixedBy_perm_arrow_iff` to an arbitrary codomain `β`. -/
lemma mem_fixedBy_perm_arrow_iff' {β : Type*} (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → β) :
    f ∈ MulAction.fixedBy (Fin n → β) σ ↔ f ∘ ⇑σ = f := by
  rw [MulAction.mem_fixedBy]
  constructor
  · intro hf
    funext k
    have h : f (σ.symm (σ k)) = f (σ k) := congr_fun hf (σ k)
    simp only [Equiv.symm_apply_apply] at h
    exact h.symm
  · intro hf
    funext k
    change f (σ.symm k) = f k
    have h := congr_fun hf (σ.symm k)
    simp only [Function.comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- Generalization of `card_fixedBy_perm_arrow_eq_filter_card` to an arbitrary finite
codomain `β`. -/
lemma card_fixedBy_perm_arrow_eq_filter_card' {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype.card ↑(MulAction.fixedBy (Fin n → β) σ) =
      (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f)).card := by
  rw [← Fintype.card_coe (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f))]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (mem_fixedBy_perm_arrow_iff' n σ f).mp hf⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact (mem_fixedBy_perm_arrow_iff' n σ f).mpr hf⟩
    left_inv := fun ⟨f, _⟩ => by simp
    right_inv := fun ⟨f, _⟩ => by simp
  }

/-- **Burnside sum, arbitrary finite codomain** (generalizes `sum_permRep_trace_eq`'s
combinatorial core to any `Fintype β`): the total number of `σ`-fixed functions
`Fin n → β`, summed over `σ ∈ Sₙ`, is `n! · C(n + |β| - 1, |β| - 1)`. -/
lemma sum_card_fixedBy_perm_fun_eq_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) [NeZero n] [NeZero (Fintype.card β)] :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun f : Fin n → β => f ∘ ⇑σ = f)).card =
      n.factorial * Nat.choose (n + Fintype.card β - 1) (Fintype.card β - 1) := by
  letI : DecidableRel (MulAction.orbitRel (Equiv.Perm (Fin n)) (Fin n → β)).r := by
    intro f g
    simp only [MulAction.orbitRel_apply]
    rw [MulAction.mem_orbit_iff]
    exact Fintype.decidableExistsFintype
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin n)) (Fin n → β)
  rw [show Fintype.card (Equiv.Perm (Fin n)) = n.factorial from
    (Fintype.card_perm).trans (by simp [Fintype.card_fin])] at burnside
  simp_rw [← card_fixedBy_perm_arrow_eq_filter_card' n]
  rw [burnside, card_permFunOrbits_eq_choose_of_fintype n, mul_comm]

end PermFunctionActionGeneral

/-- The trace of the symmetric projector equals the dimension of the symmetric subspace:
    Tr(P_sym) = C(n+d-1, d-1) = dim(Sym^n(ℂᵈ)). -/
lemma symmetricProjectorRep_trace (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjectorRep d n).trace = (Nat.choose (n + d - 1) (d - 1) : ℂ) := by
  unfold symmetricProjectorRep
  rw [Matrix.trace_smul, trace_sum, sum_permRep_trace_eq]
  simp only [one_div, smul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

end Math.RepresentationTheory

end
