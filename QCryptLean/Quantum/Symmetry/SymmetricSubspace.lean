import QCryptLean.Quantum.TensorProducts.TensorFamily
import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Operators.DensityOpTopology

/-!
# Symmetric Subspace — projector, permutation invariance, symmetrization

This module defines the symmetric subspace and permutation invariance
for quantum states, which is crucial for the quantum de Finetti theorem
and collective attack security proofs.

## Main definitions
- `IsPermutationInvariant`: Predicate for permutation-invariant density operators
- `symmetricProjector`: Projector onto the symmetric subspace Sym^n(ℂᵈ)
- `symmetrize`: Symmetrization by averaging over all permutations

## Main statements
- `Quantum.TensorProducts.permutationRepresentation_conj_tensorFamily`: permuting the sites of a
  tensor family by `U_σ` relabels its factors by `σ⁻¹` (`permutationRepresentation_mul_tensorFamily`
  and `tensorFamily_mul_permutationRepresentation` are the intertwining forms, and
  `permutationRepresentation_mulVec_tensorFamilyVec` the product-vector form)
- `Quantum.TensorProducts.trace_tensorFamily_mul_permutationRepresentation`: the cycle trace
  `Tr((⊗ₖ Aₖ) U_σ)` of a tensor family, and its symmetric-projector average
  `trace_tensorFamily_mul_symmetricProjectorRep`
- `Quantum.TensorProducts.Op.commute_tensorPow_permutationRepresentation`: operator tensor powers
  commute with the permutations of the copies (`Op.permutationRepresentation_conj_tensorPow` is
  the conjugation form); `tensorPow_isPermutationInvariant` is the state form
- `symmetricProjector_is_projector`: P_sym is idempotent and Hermitian
- `symmetricSubspace_dim`: dim(Sym^n(ℂᵈ)) = C(n+d-1, d-1)
- `permRep_mul_symmetricProjector`: U_π * P_sym = P_sym (left-invariance)
- `symmetricProjector_mul_permRep`: P_sym * U_π = P_sym (right-invariance)
- `projector_sandwich_oneSided`: PΨP = Ψ implies PΨ = Ψ for projectors P and PSD Ψ
- `symmetric_perm_invariant`: Symmetric-subspace states satisfy U_π Ψ = Ψ
- `symmetrize_contracts_distance`: Symmetrization is trace-distance contractive

## References
- Christandl, König, Mitchison, Renner (2007) "One-and-a-Half Quantum de Finetti
  Theorems", Comm. Math. Phys. 273(2), 473-498
- Harrow (2013) "The church of the symmetric subspace"
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry

-- ============================================================================
-- Pure math lemmas about trace
-- ============================================================================

/-- For any matrix P with P² = P and any matrix A, we have Tr(PAP) = Tr(PA).

    Proof: Tr(PAP) = Tr(P²A) = Tr(PA) using P² = P and trace cyclicity.

    Note: No Hermiticity condition on P (P† = P) and no commutativity condition
    (PA = AP) is required; idempotence alone suffices. -/
lemma trace_sandwich_projector_eq {n : ℕ} (P A : Op n)
    (hP_idem : P * P = P) :
    (P * A * P).trace = (P * A).trace := by
  calc (P * A * P).trace
      = (P * (P * A)).trace := by rw [Matrix.trace_mul_comm (P * A) P]
    _ = ((P * P) * A).trace := by rw [Matrix.mul_assoc]
    _ = (P * A).trace := by rw [hP_idem]

/-!
## Permutation Invariance

A density operator ρ on (ℂᵈ)^⊗n is permutation-invariant if it commutes
with all permutation unitaries: U_σ ρ U_σ† = ρ for all σ ∈ Sₙ.

This is the key symmetry assumption for the quantum de Finetti theorem.
-/

/-- Permutation-invariance predicate for density operators on tensor product space.

    A state ρ on (ℂᵈ)^⊗n is permutation-invariant if for all permutations σ ∈ Sₙ:
      U_σ ρ U_σ† = ρ

    where U_σ is the permutation representation unitary.

    **Physical meaning**: The state looks the same regardless of how we label
    the n subsystems. This is the key symmetry assumption for de Finetti theorems. -/
def IsPermutationInvariant {d n : ℕ} [NeZero d] (ρ : DensityOp (d ^ n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    let U := permutationRepresentation d n σ
    U * ρ.toOp * U† = ρ.toOp

/-- Equivalent characterization: ρ commutes with all permutation unitaries. -/
theorem isPermutationInvariant_iff_commutes {d n : ℕ} [NeZero d]
    (ρ : DensityOp (d ^ n)) :
    IsPermutationInvariant ρ ↔
    ∀ σ : Equiv.Perm (Fin n), permutationRepresentation d n σ * ρ.toOp =
                              ρ.toOp * permutationRepresentation d n σ := by
  constructor
  · intro hinv σ
    have h := hinv σ
    -- U * ρ * U† = ρ implies U * ρ = ρ * U (multiply by U on right)
    have hU := permutationRepresentation_unitary d n σ
    calc permutationRepresentation d n σ * ρ.toOp
        = permutationRepresentation d n σ * ρ.toOp * 1 := by rw [mul_one]
      _ = permutationRepresentation d n σ * ρ.toOp *
            ((permutationRepresentation d n σ)† * permutationRepresentation d n σ) := by rw [hU.1]
      _ = (permutationRepresentation d n σ * ρ.toOp * (permutationRepresentation d n σ)†) *
            permutationRepresentation d n σ := by
              rw [mul_assoc, mul_assoc, mul_assoc]
      _ = ρ.toOp * permutationRepresentation d n σ := by rw [h]
  · intro hcomm σ
    have hU := permutationRepresentation_unitary d n σ
    calc permutationRepresentation d n σ * ρ.toOp * (permutationRepresentation d n σ)†
        = ρ.toOp * permutationRepresentation d n σ * (permutationRepresentation d n σ)† := by
            rw [hcomm σ]
      _ = ρ.toOp * (permutationRepresentation d n σ * (permutationRepresentation d n σ)†) := by
            rw [mul_assoc]
      _ = ρ.toOp * 1 := by rw [hU.2]
      _ = ρ.toOp := by rw [mul_one]

-- Helper lemmas for tensorPowGen_toOp_eq_prod proof

/-- castDim acts on matrix entries by casting indices. -/
lemma castDim_toOp_cast {n m : ℕ} (h : n = m)
    (ρ : DensityOp n) (i j : Fin m) :
    (DensityOp.castDim h ρ).toOp i j =
    ρ.toOp (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

/-- Tensor power entries factor as products in `finFunctionFinEquiv` coordinates:
`(ρ^⊗n)_{e(f), e(g)} = ∏ k, ρ_{f(k), g(k)}`. This is the operator entry formula
`Quantum.TensorProducts.Op.tensorPow_apply_finFunctionFinEquiv` read through
`DensityOp.tensorPowGen_toOp`. -/
theorem tensorPowGen_toOp_eq_prod {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (ρ : DensityOp d) (f g : Fin n → Fin d) :
    (ρ.tensorPowGen n).toOp (@finFunctionFinEquiv d n f) (@finFunctionFinEquiv d n g) =
    ∏ k : Fin n, ρ.toOp (f k) (g k) := by
  rw [DensityOp.tensorPowGen_toOp, Op.tensorPow_apply_finFunctionFinEquiv]

/-- **Helper**: Conjugation by permutation representation permutes tensor indices.

    For any matrix M on (ℂᵈ)^⊗n and permutation τ ∈ Sₙ:
      (U_τ * M * U_τ†)_{i,j} = M_{e(e⁻¹(i) ∘ τ), e(e⁻¹(j) ∘ τ)}

    where e = finFunctionFinEquiv d n. In words: conjugation by U_τ relabels tensor
    indices by composing with τ on the right.

    **Proof sketch**: Expand the matrix product using the definition of
    `permutationRepresentation`. The sum over intermediate indices collapses
    to a single term because U_τ has exactly one nonzero entry per row/column. -/
theorem permRep_conj_entry {d n : ℕ} [NeZero d] (τ : Equiv.Perm (Fin n))
    (M : Op (d ^ n)) (i j : Fin (d ^ n)) :
    (permutationRepresentation d n τ * M * (permutationRepresentation d n τ)†) i j =
    M (@finFunctionFinEquiv d n ((@finFunctionFinEquiv d n).symm i ∘ τ))
      (@finFunctionFinEquiv d n ((@finFunctionFinEquiv d n).symm j ∘ τ)) := by
  set e := @finFunctionFinEquiv d n
  set i' := e (e.symm i ∘ ⇑τ) with hi'_def
  set j' := e (e.symm j ∘ ⇑τ) with hj'_def
  have hei' : e.symm i' = e.symm i ∘ ⇑τ := e.symm_apply_apply _
  have hej' : e.symm j' = e.symm j ∘ ⇑τ := e.symm_apply_apply _
  have hi'_inv : e.symm i = e.symm i' ∘ ⇑τ.symm := by
    rw [hei']; funext x; simp [Function.comp]
  have hj'_inv : e.symm j = e.symm j' ∘ ⇑τ.symm := by
    rw [hej']; funext x; simp [Function.comp]
  -- Factor as (U_τ * M) * U_τ†, expand, use U_τ† = U_{τ⁻¹}
  rw [← permutationRepresentation_inv]
  -- LHS = Σ_l (U_τ * M)_{i,l} * (U_{τ⁻¹})_{l,j}
  -- (U_{τ⁻¹})_{l,j} = 1 iff e⁻¹(l) = e⁻¹(j) ∘ (τ⁻¹).symm = e⁻¹(j) ∘ τ
  -- So the sum collapses to l = j', and similarly the inner product to k = i'.
  -- We prove this by computing (U_τ * M)_{i,l} first, then composing.
  -- Step 1: (U_τ * M)_{i,l} = Σ_k (U_τ)_{i,k} * M_{k,l} = M_{i',l}
  have hUM : ∀ l, (permutationRepresentation d n τ * M) i l = M i' l := by
    intro l
    simp only [Matrix.mul_apply, permutationRepresentation, Matrix.of_apply]
    rw [Finset.sum_eq_single i']
    · rw [if_pos hi'_inv, one_mul]
    · intro k _ hk
      rw [if_neg fun h => hk (e.symm.injective (by
        rw [hi'_inv] at h
        exact funext fun x => by
          have := congr_fun h (τ x); simp [Function.comp] at this; exact this.symm))]
      ring
    · intro h; exact absurd (Finset.mem_univ i') h
  -- Step 2: ((U_τ * M) * U_{τ⁻¹})_{i,j} = Σ_l (U_τ * M)_{i,l} * (U_{τ⁻¹})_{l,j} = M_{i',j'}
  -- Rewrite (A * B * C)_{i,j} = Σ_l (A*B)_{i,l} * C_{l,j}
  rw [show (permutationRepresentation d n τ * M * permutationRepresentation d n τ⁻¹) i j =
    ∑ l, (permutationRepresentation d n τ * M) i l *
         (permutationRepresentation d n τ⁻¹) l j from by
    simp [Matrix.mul_apply, Finset.sum_mul]]
  simp_rw [hUM]
  simp only [permutationRepresentation, Matrix.of_apply]
  rw [show ⇑(τ⁻¹ : Equiv.Perm (Fin n)).symm = ⇑τ from by ext x; simp [Equiv.Perm.inv_def]]
  rw [Finset.sum_eq_single j']
  · rw [if_pos hej', mul_one]
  · intro l _ hl
    rw [if_neg (fun h => hl (e.symm.injective (h.trans hej'.symm)))]
    ring
  · intro h; exact absurd (Finset.mem_univ j') h

/-! ## Permuting the sites of a tensor family -/

/-- **Permuting the sites of a tensor family.** Conjugation by the permutation representation
`U_σ` relabels the factors of `⊗ₖ Aₖ` by `σ⁻¹`. -/
theorem _root_.Quantum.TensorProducts.permutationRepresentation_conj_tensorFamily {d n : ℕ}
    [NeZero d] (A : Fin n → Op d) (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ * tensorFamily A * (permutationRepresentation d n σ)† =
      tensorFamily fun k => A (σ.symm k) := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  rw [permRep_conj_entry]
  simp only [Equiv.symm_apply_apply, tensorFamily_apply_finFunctionFinEquiv, Function.comp_apply]
  exact Fintype.prod_equiv σ _ _ fun k => by simp

/-- The intertwining form of `permutationRepresentation_conj_tensorFamily`:
`U_σ (⊗ₖ Aₖ) = (⊗ₖ A_{σ⁻¹ k}) U_σ`. -/
theorem _root_.Quantum.TensorProducts.permutationRepresentation_mul_tensorFamily {d n : ℕ}
    [NeZero d] (A : Fin n → Op d) (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ * tensorFamily A =
      (tensorFamily fun k => A (σ.symm k)) * permutationRepresentation d n σ := by
  rw [← permutationRepresentation_conj_tensorFamily A σ,
    Matrix.mul_assoc _ _ (permutationRepresentation d n σ),
    (permutationRepresentation_unitary d n σ).1, Matrix.mul_one]

/-- The intertwining form with the permutation on the right:
`(⊗ₖ Aₖ) U_σ = U_σ (⊗ₖ A_{σ k})`. -/
theorem _root_.Quantum.TensorProducts.tensorFamily_mul_permutationRepresentation {d n : ℕ}
    [NeZero d] (A : Fin n → Op d) (σ : Equiv.Perm (Fin n)) :
    tensorFamily A * permutationRepresentation d n σ =
      permutationRepresentation d n σ * tensorFamily fun k => A (σ k) := by
  simpa using (permutationRepresentation_mul_tensorFamily (fun k => A (σ k)) σ).symm

/-- **Permuting the sites of a product vector.** `U_σ (⊗ₖ vₖ) = ⊗ₖ v_{σ⁻¹ k}`: the permutation
representation relabels the factors of a product vector by `σ⁻¹`, as it does for a tensor
family. -/
theorem _root_.Quantum.TensorProducts.permutationRepresentation_mulVec_tensorFamilyVec {d n : ℕ}
    [NeZero d] (v : Fin n → Fin d → ℂ) (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ *ᵥ tensorFamilyVec v =
      tensorFamilyVec fun k => v (σ.symm k) := by
  set e := @finFunctionFinEquiv d n
  funext i
  rw [mulVec, dotProduct, Finset.sum_eq_single (e (e.symm i ∘ σ))]
  · simp only [permutationRepresentation, Matrix.of_apply, tensorFamilyVec_apply]
    rw [if_pos (by funext k; simp [e]), one_mul]
    exact Fintype.prod_equiv σ _ _ fun k => by simp [e]
  · intro j _ hj
    simp only [permutationRepresentation, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro h
    exact hj (e.symm.injective (by rw [Equiv.symm_apply_apply, h]; funext k; simp [e]))
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Conjugating a tensor power by a permutation of its copies leaves it unchanged. -/
theorem _root_.Quantum.TensorProducts.Op.permutationRepresentation_conj_tensorPow {d n : ℕ}
    [NeZero d] (M : Op d) (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation d n σ * Op.tensorPow M n * (permutationRepresentation d n σ)† =
      Op.tensorPow M n := by
  rw [Op.tensorPow_eq_tensorFamily, permutationRepresentation_conj_tensorFamily]

/-- A tensor power commutes with every permutation of its copies. -/
theorem _root_.Quantum.TensorProducts.Op.commute_tensorPow_permutationRepresentation {d n : ℕ}
    [NeZero d] (M : Op d) (σ : Equiv.Perm (Fin n)) :
    Commute (Op.tensorPow M n) (permutationRepresentation d n σ) := by
  rw [Op.tensorPow_eq_tensorFamily]
  exact tensorFamily_mul_permutationRepresentation _ σ

/-- **Tensor-permutation (cycle) trace formula.** The trace of a tensor family against the
permutation representation contracts the factor entries along the permutation:

  `Tr((⊗ₖ Aₖ) U_σ) = ∑_{f : Fin n → Fin d} ∏ₖ (Aₖ)_{f k, f (σ⁻¹ k)}`.

This is the index form of the cycle-product identity `∏_{cycles c of σ} Tr(∏_{k ∈ c} Aₖ)`. With
every `Aₖ = 1` it is the character `Tr U_σ = #{f : f ∘ σ = f}`
(`permutationRepresentation_trace_eq_fixed_card`).

Reference: Harrow, *The Church of the Symmetric Subspace* (arXiv:1308.6595) §3;
Christandl–König–Renner 2009, `lem:extractpart`; Watrous 2018, Theorem 3.51. -/
theorem _root_.Quantum.TensorProducts.trace_tensorFamily_mul_permutationRepresentation {d n : ℕ}
    [NeZero d] (A : Fin n → Op d) (σ : Equiv.Perm (Fin n)) :
    (tensorFamily A * permutationRepresentation d n σ).trace =
      ∑ f : Fin n → Fin d, ∏ k, A k (f k) (f (σ.symm k)) := by
  rw [trace_mul_permutationRepresentation]
  simp only [tensorFamily_apply_finFunctionFinEquiv, Function.comp_apply]

/-- **Symmetric-subspace second moment.** The trace of a tensor family against the symmetric
projector `P_sym = (1/n!) ∑_σ U_σ` is the normalised permutation average of the cycle
contractions of `trace_tensorFamily_mul_permutationRepresentation`. -/
theorem _root_.Quantum.TensorProducts.trace_tensorFamily_mul_symmetricProjectorRep {d n : ℕ}
    [NeZero d] [NeZero n] (A : Fin n → Op d) :
    (tensorFamily A * symmetricProjectorRep d n).trace =
      (1 / (Nat.factorial n : ℂ)) * ∑ σ : Equiv.Perm (Fin n),
        ∑ f : Fin n → Fin d, ∏ k, A k (f k) (f (σ.symm k)) := by
  rw [symmetricProjectorRep, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum,
    Matrix.trace_sum]
  simp only [trace_tensorFamily_mul_permutationRepresentation]

/-- **Symmetric-subspace second moment of a tensor power**, the constant family of
`trace_tensorFamily_mul_symmetricProjectorRep`: `Tr(B^{⊗n} P_sym)` is the permutation average of
the cycle contractions of `B`, `(1/n!) ∑_σ ∏_{cycles c of σ} Tr(B^{|c|})`. -/
theorem _root_.Quantum.TensorProducts.Op.trace_tensorPow_mul_symmetricProjectorRep {d : ℕ}
    [NeZero d] (B : Op d) (n : ℕ) [NeZero n] :
    (Op.tensorPow B n * symmetricProjectorRep d n).trace =
      (1 / (Nat.factorial n : ℂ)) * ∑ σ : Equiv.Perm (Fin n),
        ∑ f : Fin n → Fin d, ∏ k, B (f k) (f (σ.symm k)) := by
  rw [Op.tensorPow_eq_tensorFamily, trace_tensorFamily_mul_symmetricProjectorRep]

/-- Tensor product states σ^⊗n are permutation-invariant for any dimension d.
    This is because permuting identical copies gives the same state. -/
theorem tensorPow_isPermutationInvariant {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (σ : DensityOp d) :
    IsPermutationInvariant (σ.tensorPowGen n) := fun τ => by
  simp only [DensityOp.tensorPowGen_toOp]
  exact Op.permutationRepresentation_conj_tensorPow σ.toOp τ

/-!
## Symmetric Projector

The symmetric projector P_sym = (1/n!) Σ_{σ ∈ Sₙ} U_σ projects onto the
totally symmetric subspace Sym^n(ℂᵈ).
-/

/-- The symmetric projector onto Sym^n(ℂᵈ).

    P_sym = (1/n!) Σ_{σ ∈ Sₙ} U_σ

    This projects onto states that are invariant under ALL permutations
    (not just on average, but exactly). -/
def symmetricProjector (d n : ℕ) [NeZero d] [NeZero n] : Op (d ^ n) :=
  symmetricProjectorRep d n

/-- The symmetric projector is idempotent and Hermitian (i.e., a projector). -/
theorem symmetricProjector_is_projector (d n : ℕ) [NeZero d] [NeZero n] :
    let P := symmetricProjector d n
    P * P = P ∧ P† = P :=
  symmetricProjectorRep_is_projector d n

/-- Dimension of symmetric subspace: dim(Sym^n(ℂᵈ)) = C(n+d-1, d-1).

    This is the trace of the symmetric projector, which equals the
    dimension of the subspace it projects onto.

    **Reference**: "Stars and bars" combinatorics. -/
theorem symmetricSubspace_dim (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjector d n).trace.re = Nat.choose (n + d - 1) (d - 1) := by
  unfold symmetricProjector; rw [symmetricProjectorRep_trace]; simp

/-- If P is a projector (P²=P, P†=P), Ψ is PSD, and PΨP = Ψ, then PΨ = Ψ and ΨP = Ψ.
    Proof: (I-P)Ψ(I-P) is PSD with trace 0, hence zero. Expanding gives PΨ+ΨP = 2Ψ,
    and multiplying by P yields ΨP = Ψ (and PΨ = Ψ by symmetry). -/
lemma projector_sandwich_oneSided {N : ℕ} {P Ψ : Op N}
    (hP_idem : P * P = P) (hP_herm : Pᴴ = P)
    (hΨ_psd : Ψ.PosSemidef) (hPΨP : P * Ψ * P = Ψ) :
    P * Ψ = Ψ ∧ Ψ * P = Ψ := by
  -- Step 1: (I-P)Ψ(I-P) is PSD
  have hQ : (1 - P)ᴴ = 1 - P := by simp [hP_herm]
  have h_psd : ((1 - P) * Ψ * (1 - P)).PosSemidef := by
    rw [show (1 - P) * Ψ * (1 - P) = (1 - P)ᴴ * Ψ * (1 - P) from by rw [hQ]]
    exact hΨ_psd.conjTranspose_mul_mul_same _
  -- Step 2: trace((I-P)Ψ(I-P)) = 0
  have hQ_idem : (1 - P) * (1 - P) = (1 - P) := by
    have : (1 - P) * (1 - P) = 1 - P - P + P * P := by
      simp only [mul_sub, sub_mul, one_mul, mul_one]; abel
    rw [this, hP_idem]; abel
  have h_tr : ((1 - P) * Ψ * (1 - P)).trace = 0 := by
    rw [Matrix.trace_mul_cycle (1 - P) Ψ (1 - P), hQ_idem, sub_mul, one_mul,
        Matrix.trace_sub]
    have : (P * Ψ).trace = Ψ.trace := by
      have hcyc := Matrix.trace_mul_cycle P Ψ P
      rw [hPΨP, hP_idem] at hcyc; exact hcyc.symm
    rw [this, sub_self]
  -- Step 3: (I-P)Ψ(I-P) = 0
  have h_zero : (1 - P) * Ψ * (1 - P) = 0 := h_psd.trace_eq_zero_iff.mp h_tr
  -- Step 4: Expand (I-P)Ψ(I-P) = Ψ - PΨ - ΨP + PΨP
  have h_expand : (1 - P) * Ψ * (1 - P) = Ψ - P * Ψ - Ψ * P + P * Ψ * P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_assoc]; abel
  -- From h_zero: Ψ - PΨ - ΨP + PΨP = 0, substitute PΨP = Ψ
  have h_eq : Ψ - P * Ψ - Ψ * P + Ψ = 0 := by
    have h1 : Ψ - P * Ψ - Ψ * P + P * Ψ * P = 0 := by rw [← h_expand]; exact h_zero
    rwa [hPΨP] at h1
  -- Step 5: Derive PΨ + ΨP = Ψ + Ψ
  have h_sum : P * Ψ + Ψ * P = Ψ + Ψ := by
    have : P * Ψ + Ψ * P - (Ψ + Ψ) = 0 := by
      calc P * Ψ + Ψ * P - (Ψ + Ψ)
          = -(Ψ - P * Ψ - Ψ * P + Ψ) := by abel
        _ = -(0 : Matrix _ _ ℂ) := by rw [h_eq]
        _ = 0 := neg_zero
    exact sub_eq_zero.mp this
  -- Step 6: ΨP = Ψ (multiply h_sum by P from right)
  have hΨP : Ψ * P = Ψ := by
    have h1 : (P * Ψ + Ψ * P) * P = (Ψ + Ψ) * P := by rw [h_sum]
    rw [add_mul, add_mul, hPΨP] at h1
    rw [show Ψ * P * P = Ψ * P from by rw [mul_assoc, hP_idem]] at h1
    symm
    calc Ψ = Ψ + Ψ * P - Ψ * P := by abel
      _ = Ψ * P + Ψ * P - Ψ * P := by rw [h1]
      _ = Ψ * P := by abel
  -- Step 7: PΨ = Ψ (substitute ΨP = Ψ into h_sum)
  have hPΨ : P * Ψ = Ψ := by
    have h1 : P * Ψ + Ψ = Ψ + Ψ := by
      have := h_sum; rwa [hΨP] at this
    calc P * Ψ = P * Ψ + Ψ - Ψ := by abel
      _ = Ψ + Ψ - Ψ := by rw [h1]
      _ = Ψ := by abel
  exact ⟨hPΨ, hΨP⟩

/-- Left-invariance of the group sum: U_π * P_sym = P_sym.
    Proof: U_π * (1/n! · Σ_τ U_τ) = 1/n! · Σ_τ U_{π·τ} = 1/n! · Σ_τ' U_{τ'} = P_sym,
    by reindexing the sum via left-multiplication bijection. -/
lemma permRep_mul_symmetricProjector {d n : ℕ} [NeZero d] [NeZero n]
    (π : Equiv.Perm (Fin n)) :
    permutationRepresentation d n π * symmetricProjector d n = symmetricProjector d n := by
  simp only [symmetricProjector, symmetricProjectorRep]
  rw [mul_smul_comm]
  congr 1
  rw [Finset.mul_sum]
  simp_rw [permutationRepresentation_mul]
  exact Fintype.sum_bijective (π * ·) (Group.mulLeft_bijective π) _ _ (fun _ => rfl)

/-- Right-invariance of the group sum: P_sym * U_π = P_sym. -/
lemma symmetricProjector_mul_permRep {d n : ℕ} [NeZero d] [NeZero n]
    (π : Equiv.Perm (Fin n)) :
    symmetricProjector d n * permutationRepresentation d n π = symmetricProjector d n := by
  simp only [symmetricProjector, symmetricProjectorRep]
  rw [smul_mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  simp_rw [permutationRepresentation_mul]
  exact Fintype.sum_bijective (· * π) (Group.mulRight_bijective π) _ _ (fun _ => rfl)

/-- Permutation invariance for symmetric states: if P_sym * Ψ * P_sym = Ψ, then
    U_π * Ψ = Ψ for all π ∈ S_n. -/
lemma symmetric_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (π : Equiv.Perm (Fin n)) :
    permutationRepresentation d n π * Ψ.toOp = Ψ.toOp := by
  have ⟨hPΨ, _⟩ := projector_sandwich_oneSided
    (symmetricProjector_is_projector d n).1
    (symmetricProjector_is_projector d n).2
    (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp)
    hsym
  calc permutationRepresentation d n π * Ψ.toOp
      = permutationRepresentation d n π * (symmetricProjector d n * Ψ.toOp) := by rw [hPΨ]
    _ = (permutationRepresentation d n π * symmetricProjector d n) * Ψ.toOp := by rw [mul_assoc]
    _ = symmetricProjector d n * Ψ.toOp := by rw [permRep_mul_symmetricProjector]
    _ = Ψ.toOp := hPΨ

/-!
## Commutation Properties of Permutation-Invariant States

Permutation-invariant states commute with the symmetric projector.
This is used in the de Finetti construction; it does NOT imply that
permutation-invariant states have support in the symmetric subspace
(that claim is false — see the counterexample below).
-/

-- A permutation-invariant state need NOT have support in the symmetric subspace: the bound
-- Tr(P_sym ρ P_sym) ≥ 1 - d²/n is FALSE.
-- Counterexample: The maximally mixed state on (ℂ²)^⊗8 gives
--   Tr(P_sym ρ P_sym) = dim(Sym⁸(ℂ²)) / 2⁸ = 9/256 ≈ 0.035,
--   violating the claimed bound of 1 - 4/8 = 0.5.
-- More simply: for d=2, n=2, the singlet |ψ⁻⟩ is permutation-invariant
-- (swap acts as -1, so UρU† = ρ) but lives entirely in the antisymmetric
-- subspace, giving Tr(P_sym ρ P_sym) = 0.
--
-- The CKMR d²/n bound applies to TRACE DISTANCE of reduced states
-- (quantum de Finetti theorem), NOT to symmetric subspace overlap.
-- The `quantum_deFinetti` theorem (`InfoTheory/DeFinetti/Theorem/Main.lean`) states the
-- correct result directly.

-- The following helper lemmas record how permutation-invariant states interact
-- with the symmetric projector and are used throughout the de Finetti
-- development when simplifying projector-trace expressions.

/-- Permutation-invariant ρ commutes with the symmetric projector:
    P_sym * ρ = ρ * P_sym.

    Since P_sym = (1/n!) Σ_σ U_σ and ρ commutes with each U_σ
    (by permutation invariance), ρ commutes with P_sym. -/
lemma perm_invariant_commutes_projector {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    symmetricProjector d n * ρ.toOp = ρ.toOp * symmetricProjector d n := by
  -- Get commutation with individual U_σ from invariance
  have hcomm := (isPermutationInvariant_iff_commutes ρ).mp hinv
  -- Unfold to scalar • sum form
  simp only [symmetricProjector, symmetricProjectorRep]
  -- (c • S) * ρ = c • (S * ρ) and ρ * (c • S) = c • (ρ * S)
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  -- (∑ σ, U_σ) * ρ = ρ * (∑ σ, U_σ) via per-term commutation
  have h_sum_mul : (∑ σ, permutationRepresentation d n σ) * ρ.toOp =
      ∑ σ, permutationRepresentation d n σ * ρ.toOp :=
    Finset.sum_mul Finset.univ _ _
  have h_mul_sum : ρ.toOp * (∑ σ, permutationRepresentation d n σ) =
      ∑ σ, ρ.toOp * permutationRepresentation d n σ :=
    Finset.mul_sum Finset.univ _ _
  rw [h_sum_mul, h_mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => hcomm σ)

/-!
## Symmetrization

Any state can be symmetrized by averaging over all permutations.
This is useful for converting general attacks to collective attacks.
-/

/-- Symmetrize a density operator by averaging over all permutations.

    ρ_sym = (1/n!) Σ_{σ ∈ Sₙ} U_σ ρ U_σ†

    This produces a permutation-invariant state. -/
def symmetrize {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : DensityOp (d ^ n)) : DensityOp (d ^ n) :=
  let c : ℂ := 1 / (Nat.factorial n : ℂ)
  let U := fun σ => permutationRepresentation d n σ
  let S := ∑ σ : Equiv.Perm (Fin n), U σ * ρ.toOp * (U σ)†
  ⟨⟨⟨c • S, by
    -- Hermiticity: (c • S)† = star(c) • S† = c • S
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_sum]
    -- star c = c (real scalar: 1/n!)
    have h_star_c : star c = c := by
      simp [c]
    rw [h_star_c]
    refine congrArg (c • ·) (Finset.sum_congr rfl fun σ _ => ?_)
    -- (U ρ U†)† = U†† (U ρ)† = U (ρ† U†) = U ρ U†
    rw [conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose,
        ρ.toPosSemidefOp.toHermitianOp.isHermitian,
        Matrix.mul_assoc]⟩, by
    -- PSD: ∀ x, 0 ≤ (quadraticForm (c • S) x).re
    intro x
    unfold quadraticForm
    rw [Matrix.smul_mulVec, dotProduct_smul]
    rw [sum_mulVec, dotProduct_sum]
    -- Each term is non-negative
    have h_term : ∀ σ : Equiv.Perm (Fin n),
        0 ≤ (dotProduct (star x)
          ((U σ * ρ.toOp * (U σ)†).mulVec x)).re := by
      intro σ
      -- (U ρ U†)x = U(ρ(U†x))
      rw [← mulVec_mulVec, ← mulVec_mulVec]
      -- ⟨x, U·v⟩ = ⟨U†x, v⟩
      rw [dotProduct_mulVec]
      -- vecMul (star x) (U σ) = star ((U σ)†x)
      have : vecMul (star x) (U σ) =
          star ((U σ)† *ᵥ x) := by
        rw [star_mulVec, conjTranspose_conjTranspose]
      rw [this]
      exact ρ.toPosSemidefOp.pos_semidef _
    -- c.re ≥ 0
    have h_c_nonneg : (0 : ℝ) ≤ c.re := by
      have : c = (↑((1 : ℝ) / (Nat.factorial n : ℝ)) : ℂ) := by
        simp [c]
      rw [this, Complex.ofReal_re]
      positivity
    -- c.im = 0
    have h_c_im : c.im = 0 := by
      have : c = (↑((1 : ℝ) / (Nat.factorial n : ℝ)) : ℂ) := by
        simp [c]
      rw [this, Complex.ofReal_im]
    suffices h : 0 ≤ (∑ i : Equiv.Perm (Fin n),
        star x ⬝ᵥ (U i * ρ.toOp * (U i)ᴴ) *ᵥ x).re by
      rw [smul_eq_mul, Complex.mul_re, h_c_im, zero_mul, sub_zero]
      exact mul_nonneg h_c_nonneg h
    exact Finset.sum_induction _ (fun z : ℂ => (0 : ℝ) ≤ z.re)
      (fun a b ha hb => by simp [Complex.add_re]; linarith)
      (by simp) (fun σ _ => h_term σ)⟩, by
    -- Trace = 1: Tr(c • S) = c * ∑ Tr(U ρ U†) = c * n! = 1
    change (c • S).trace = 1
    rw [Matrix.trace_smul]
    -- Tr(S) = ∑ Tr(U ρ U†)
    have h_trace_sum : S.trace = ∑ σ : Equiv.Perm (Fin n),
        (U σ * ρ.toOp * (U σ)†).trace :=
      Matrix.trace_sum Finset.univ _
    rw [h_trace_sum]
    -- Each Tr(U ρ U†) = Tr(ρ) = 1
    have h_each : ∀ σ : Equiv.Perm (Fin n),
        (U σ * ρ.toOp * (U σ)†).trace = 1 := by
      intro σ
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
          (permutationRepresentation_unitary d n σ).1,
          Matrix.one_mul]
      exact ρ.trace_one
    simp_rw [h_each, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    -- c * n! = (1 / n!) * n! = 1
    rw [smul_eq_mul]
    have h_ne : (Nat.factorial n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos n).ne'
    simp [c, h_ne]⟩

/-- The underlying matrix of a symmetrized state is the uniform average of permutation conjugates.

    `(symmetrize ρ).toOp = (1/n!) • ∑_σ U_σ * ρ.toOp * U_σ†`

    This is the explicit formula underlying all symmetrization computations.
    Used to avoid repeated `change`/`show` unfolding of the nested structure. -/
theorem symmetrize_toOp {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : DensityOp (d ^ n)) :
    (symmetrize ρ).toOp =
      (1 / (Nat.factorial n : ℂ)) •
      ∑ σ : Equiv.Perm (Fin n),
        permutationRepresentation d n σ * ρ.toOp *
        (permutationRepresentation d n σ)† := rfl

/-- Symmetrization produces a permutation-invariant state. -/
theorem symmetrize_isPermutationInvariant {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : DensityOp (d ^ n)) :
    IsPermutationInvariant (symmetrize ρ) := by
  intro σ
  -- Zeta-reduce the let U binding from IsPermutationInvariant
  change permutationRepresentation d n σ * (symmetrize ρ).toOp *
       (permutationRepresentation d n σ)† = (symmetrize ρ).toOp
  -- (symmetrize ρ).toOp = c • ∑ τ, U τ ρ U τ† by definition
  change permutationRepresentation d n σ *
    ((1 / (↑(Nat.factorial n) : ℂ)) •
      ∑ τ : Equiv.Perm (Fin n),
        permutationRepresentation d n τ * ρ.toOp *
        (permutationRepresentation d n τ)†) *
    (permutationRepresentation d n σ)† =
    (1 / (↑(Nat.factorial n) : ℂ)) •
      ∑ τ : Equiv.Perm (Fin n),
        permutationRepresentation d n τ * ρ.toOp *
        (permutationRepresentation d n τ)†
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  -- U σ * (∑ τ, U τ ρ U τ†) * U σ† = ∑ τ, U τ ρ U τ†
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  -- Reassociate, combine permutations, reindex
  simp_rw [← Matrix.mul_assoc, permutationRepresentation_mul,
           Matrix.mul_assoc, ← conjTranspose_mul, permutationRepresentation_mul,
           ← Matrix.mul_assoc]
  exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)

/-- Symmetrization is idempotent: symmetrizing an invariant state does nothing. -/
theorem symmetrize_invariant {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    symmetrize ρ = ρ := by
  -- Reduce to matrix equality via PosSemidefOp.ext
  set s := symmetrize ρ with hs
  suffices h : s.toOp = ρ.toOp by
    rcases s with ⟨p_s, t_s⟩; rcases ρ with ⟨p_r, t_r⟩
    have := PosSemidefOp.ext h; subst this; rfl
  rw [hs]
  -- Unfold symmetrize: (1/n!) ∑_σ U_σ ρ U_σ† = ρ
  change (1 / (↑(Nat.factorial n) : ℂ)) •
    ∑ σ : Equiv.Perm (Fin n),
      permutationRepresentation d n σ * ρ.toOp *
      (permutationRepresentation d n σ)† = ρ.toOp
  -- Each term = ρ.toOp by invariance
  simp_rw [hinv _]
  -- (1/n!) • (n! • ρ.toOp) = ρ.toOp
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.factorial_pos n).ne'

/-- Trace distance does not increase under symmetrization.

    D(symmetrize(ρ), symmetrize(σ)) ≤ D(ρ, σ)

    This is because symmetrization is a CPTP map (quantum channel). -/
theorem symmetrize_contracts_distance {d n : ℕ} [NeZero d] [NeZero n]
    (ρ σ : DensityOp (d ^ n)) :
    Quantum.Metrics.traceDistance (symmetrize ρ).toOp (symmetrize σ).toOp ≤
    Quantum.Metrics.traceDistance ρ.toOp σ.toOp := by
  haveI hdn : NeZero (d ^ n) :=
    ⟨(Nat.pow_pos (NeZero.pos d)).ne'⟩
  set U := Math.RepresentationTheory.permutationRepresentation d n
  rw [Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian,
      Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Quantum.Metrics.traceNorm_hermitian_eq _
        (densityOp_sub_isHermitian (symmetrize ρ) (symmetrize σ)),
      ← Quantum.Metrics.traceNorm_hermitian_eq _ (densityOp_sub_isHermitian ρ σ)]
  have card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  let c_r : ℝ := Real.sqrt (1 / (Nat.factorial n : ℝ))
  let c : ℂ := (c_r : ℂ)
  have h_star_c : star c = c := by
    simp [c, Complex.conj_ofReal]
  have h_c_sq : c * c = (1 / Nat.factorial n : ℂ) := by
    have hpos : (0 : ℝ) ≤ 1 / (Nat.factorial n : ℝ) :=
      div_nonneg zero_le_one (Nat.cast_nonneg _)
    have hr : c_r * c_r = 1 / (Nat.factorial n : ℝ) := Real.mul_self_sqrt hpos
    change (c_r : ℂ) * c_r = 1 / (Nat.factorial n : ℂ)
    rw [← Complex.ofReal_mul, hr, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast]
  let enum : Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
    (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  let K : Quantum.Channels.KrausRepresentation (d ^ n) (d ^ n) :=
  { numOps := Nat.factorial n
    operators := fun i => c • U (enum i)
    completeness := by
      have hU : ∀ τ : Equiv.Perm (Fin n), (U τ)ᴴ * U τ = 1 :=
        fun τ => (Math.RepresentationTheory.permutationRepresentation_unitary d n τ).1
      simp only [conjTranspose_smul, h_star_c]
      simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      have hcongr : ∀ x ∈ (Finset.univ : Finset (Fin n.factorial)),
          (c * c) • ((U (enum x))ᴴ * U (enum x)) =
          (c * c) • (1 : Op (d ^ n)) :=
        fun x _ => by rw [hU (enum x)]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_smul, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h_c_sq,
          mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'),
          one_smul] }
  have hΦ : Quantum.Channels.IsCPTP K.applyOp := K.is_cptp
  -- The Kraus channel `K` is the symmetrization map: `(c U)ρ(c U)† = c² UρU†` and `c² = 1/n!`.
  have hK : ∀ τ : DensityOp (d ^ n), K.applyOp τ.toOp = (symmetrize τ).toOp := by
    intro τ
    change ∑ i : Fin (Nat.factorial n), (c • U (enum i)) * τ.toOp * (c • U (enum i))†
      = (1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n), U π * τ.toOp * (U π)†
    simp only [conjTranspose_smul, h_star_c]
    simp_rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← Finset.smul_sum, h_c_sq]
    -- Reindex the Kraus sum along `enum : Fin n! ≃ Perm (Fin n)`.
    exact congrArg ((1 / (Nat.factorial n : ℂ)) • ·)
      (Fintype.sum_equiv enum _ _ fun _ => rfl)
  have hNorm := Quantum.Channels.cptp_contracts_trace_distance K.applyOp hΦ ρ σ
  rwa [hK ρ, hK σ] at hNorm

/-- The trace of the symmetric projector equals the dimension of the symmetric subspace:
    Tr(P_sym) = C(n+d-1, d-1) = dim(Sym^n(ℂᵈ)). -/
lemma symmetricProjector_trace (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjector d n).trace = (Nat.choose (n + d - 1) (d - 1) : ℂ) := by
  exact Math.RepresentationTheory.symmetricProjectorRep_trace d n

-- ============================================================================
-- Canonical embedding isometry of the symmetric subspace
-- (CKR 2009, arXiv:0809.3019, lem:extractpart / source-replacement)
-- ============================================================================

/-!
## Symmetric-subspace embedding isometry

The CKR post-selection technique (`lem:extractpart`) factors the symmetric
projector `P_sym` on `(ℂᵈ)^{⊗n} ≅ ℂ^{dⁿ}` through an explicit isometry

  `V : ℂ^g → ℂ^{dⁿ}`,    `g = dim Sym^n(ℂᵈ) = C(n+d-1, d-1)`,

with `V†V = 1` and `VV† = P_sym`. Here `V = (symmetricEmbeddingIsometry d n)†`
where `symmetricEmbeddingIsometry d n : Matrix (Fin g) (Fin (dⁿ)) ℂ` is the
matrix whose `g` rows are the eigenvalue-`1` eigenvectors of `P_sym` (i.e. an
orthonormal basis of the symmetric subspace).

The construction is the standard finite-dimensional spectral one: `P_sym` is a
Hermitian `0/1`-projector, so its eigenvalue-`1` eigenspace is exactly the
symmetric subspace, of dimension `g` (`symmetricSubspace_dim`); selecting the
corresponding columns of the spectral unitary yields `V`.
-/

/-- `P_sym` is Hermitian, as a `Matrix.IsHermitian` witness (the second
component of `symmetricProjector_is_projector`). -/
theorem symmetricProjector_isHermitian (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjector d n).IsHermitian :=
  (symmetricProjector_is_projector d n).2

/-- The eigenvalues of `P_sym` lie in `{0, 1}` (it is a Hermitian idempotent). -/
theorem symmetricProjector_eigenvalues_zero_or_one (d n : ℕ) [NeZero d] [NeZero n]
    (i : Fin (d ^ n)) :
    (Quantum.Symmetry.symmetricProjector_isHermitian d n).eigenvalues i = 0 ∨
      (Quantum.Symmetry.symmetricProjector_isHermitian d n).eigenvalues i = 1 := by
  set hH := Quantum.Symmetry.symmetricProjector_isHermitian d n with hH_def
  -- From P² = P, the diagonal of eigenvalues squares to itself.
  have hP_sq : symmetricProjector d n * symmetricProjector d n = symmetricProjector d n :=
    (symmetricProjector_is_projector d n).1
  -- λᵢ² = λᵢ pointwise.
  have h_idem : ∀ i, hH.eigenvalues i * hH.eigenvalues i = hH.eigenvalues i := by
    intro i
    have h_spec := hH.spectral_theorem
    -- Conjugate P² and P: their diagonal forms agree, so eigenvalues are idempotent.
    have h_D_eq : (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
          (diagonal (fun j => ((hH.eigenvalues j : ℝ) : ℂ) * (hH.eigenvalues j : ℝ)))
        = (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
          (diagonal (fun j => ((hH.eigenvalues j : ℝ) : ℂ))) := by
      rw [← diagonal_mul_diagonal, map_mul]
      have : (Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
            (diagonal (fun j => ((hH.eigenvalues j : ℝ) : ℂ)))
          = symmetricProjector d n := by
        rw [show (fun j => ((hH.eigenvalues j : ℝ) : ℂ))
              = (RCLike.ofReal ∘ hH.eigenvalues : Fin (d ^ n) → ℂ) from rfl]
        exact h_spec.symm
      rw [this, hP_sq]
    have h_inj := (Unitary.conjStarAlgAut ℂ (Op (d ^ n))
      hH.eigenvectorUnitary).injective h_D_eq
    have h_entry := congrFun (congrFun h_inj i) i
    simp only [diagonal_apply_eq] at h_entry
    have : ((hH.eigenvalues i : ℝ) * hH.eigenvalues i : ℝ) = (hH.eigenvalues i : ℝ) := by
      have h2 : (((hH.eigenvalues i : ℝ) * hH.eigenvalues i : ℝ) : ℂ)
          = ((hH.eigenvalues i : ℝ) : ℂ) := by push_cast; exact h_entry
      exact_mod_cast h2
    exact this
  have h := h_idem i
  by_cases h0 : hH.eigenvalues i = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    have h_eq : hH.eigenvalues i * (hH.eigenvalues i - 1) = 0 := by ring_nf; linarith [h]
    have h_sub : hH.eigenvalues i - 1 = 0 := by
      rcases mul_eq_zero.mp h_eq with h' | h'
      · exact absurd h' h0
      · exact h'
    linarith

/-- The eigenvalue-`1` index finset of `P_sym`. Its cardinality is
`g = C(n+d-1, d-1)` (`symmetricEmbedding_one_eigenset_card`). -/
def symmetricEmbeddingOneEigenset (d n : ℕ) [NeZero d] [NeZero n] : Finset (Fin (d ^ n)) :=
  Finset.univ.filter (fun i => (Quantum.Symmetry.symmetricProjector_isHermitian d n).eigenvalues i =
      1)

/-- The number of eigenvalue-`1` eigenvectors of `P_sym` equals
`g = dim Sym^n(ℂᵈ) = C(n+d-1, d-1)` — it is the trace of `P_sym`. -/
theorem symmetricEmbedding_one_eigenset_card (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricEmbeddingOneEigenset d n).card = Nat.choose (n + d - 1) (d - 1) := by
  classical
  set hH := Quantum.Symmetry.symmetricProjector_isHermitian d n with hH_def
  -- trace = ∑ eigenvalues = #{eigenvalues = 1}, and trace.re = g.
  have h_tr_re : (symmetricProjector d n).trace.re = Nat.choose (n + d - 1) (d - 1) :=
    symmetricSubspace_dim d n
  have h_tr_sum : (symmetricProjector d n).trace = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) := by
    have := hH.trace_eq_sum_eigenvalues
    simpa using this
  -- The real part of the eigenvalue sum.
  have h_sum_re : (symmetricProjector d n).trace.re = ∑ i, hH.eigenvalues i := by
    rw [h_tr_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  -- ∑ eigenvalues = card of the {=1} set (each eigenvalue is 0 or 1).
  have h_sum_card : (∑ i, hH.eigenvalues i) = (symmetricEmbeddingOneEigenset d n).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => hH.eigenvalues i = 1)]
    have h_one : (∑ i ∈ Finset.univ.filter (fun i => hH.eigenvalues i = 1),
        hH.eigenvalues i)
        = ∑ i ∈ Finset.univ.filter (fun i => hH.eigenvalues i = 1), (1 : ℝ) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      exact hi.2
    have h_zero : (∑ i ∈ Finset.univ.filter (fun i => ¬ hH.eigenvalues i = 1),
        hH.eigenvalues i) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      rcases symmetricProjector_eigenvalues_zero_or_one d n i with h0 | h1
      · exact h0
      · exact absurd h1 hi.2
    rw [h_one, h_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
        symmetricEmbeddingOneEigenset]
  have : ((symmetricEmbeddingOneEigenset d n).card : ℝ) = Nat.choose (n + d - 1) (d - 1) := by
    rw [← h_sum_card, ← h_sum_re, h_tr_re]
  exact_mod_cast this

/-- The explicit selection map `Fin g ↪ Fin (dⁿ)` enumerating the eigenvalue-`1`
indices of `P_sym`, where `g = C(n+d-1, d-1)`. Built from
`Finset.equivFinOfCardEq` applied to `symmetricEmbedding_one_eigenset_card`;
fully constructive (no choice). -/
def symmetricEmbeddingSel (d n : ℕ) [NeZero d] [NeZero n] :
    Fin (Nat.choose (n + d - 1) (d - 1)) → Fin (d ^ n) :=
  fun k => ((symmetricEmbeddingOneEigenset d n).equivFinOfCardEq
    (symmetricEmbedding_one_eigenset_card d n)).symm k

/-- `symmetricEmbeddingSel` is injective: it is the coercion of a bijection onto a
finset. -/
theorem symmetricEmbeddingSel_injective (d n : ℕ) [NeZero d] [NeZero n] :
    Function.Injective (symmetricEmbeddingSel d n) := by
  intro a b hab
  have := Subtype.ext_iff.mpr hab
  exact ((symmetricEmbeddingOneEigenset d n).equivFinOfCardEq
    (symmetricEmbedding_one_eigenset_card d n)).symm.injective (by exact this)

/-- The image of `symmetricEmbeddingSel` is exactly the eigenvalue-`1` set, hence
each selected eigenvalue is `1`. -/
theorem symmetricEmbeddingSel_mem (d n : ℕ) [NeZero d] [NeZero n]
    (k : Fin (Nat.choose (n + d - 1) (d - 1))) :
    (Quantum.Symmetry.symmetricProjector_isHermitian d n).eigenvalues (symmetricEmbeddingSel d n k)
        = 1 := by
  have h : symmetricEmbeddingSel d n k ∈ symmetricEmbeddingOneEigenset d n :=
    ((symmetricEmbeddingOneEigenset d n).equivFinOfCardEq
      (symmetricEmbedding_one_eigenset_card d n)).symm k |>.2
  simp only [symmetricEmbeddingOneEigenset, Finset.mem_filter] at h
  exact h.2

/-- **CKR `lem:extractpart` embedding isometry.**

`symmetricEmbeddingIsometry d n : Matrix (Fin g) (Fin (dⁿ)) ℂ`, `g = C(n+d-1, d-1)`,
is the matrix whose `g` rows are the eigenvalue-`1` eigenvectors of the symmetric
projector `P_sym` on `(ℂᵈ)^{⊗n}`. Its adjoint `V := (symmetricEmbeddingIsometry d n)†`
is the canonical isometric embedding `ℂ^g ↪ ℂ^{dⁿ}` of `Sym^n(ℂᵈ)`, satisfying
`V†V = 1` (`symmetricEmbeddingIsometry_isometry`) and `VV† = P_sym`
(`symmetricEmbeddingIsometry_range`).

Concretely it is the row-submatrix of the (conjugate-transposed) spectral
eigenvector unitary `U = hH.eigenvectorUnitary` selecting the eigenvalue-`1`
indices via `symmetricEmbeddingSel`.

**Reference**: Christandl–König–Renner 2009 (arXiv:0809.3019), `lem:extractpart`. -/
noncomputable def symmetricEmbeddingIsometry (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix (Fin (Nat.choose (n + d - 1) (d - 1))) (Fin (d ^ n)) ℂ :=
  (((Quantum.Symmetry.symmetricProjector_isHermitian d n).eigenvectorUnitary :
      Op (d ^ n))ᴴ).submatrix (symmetricEmbeddingSel d n) id

/-- **CKR `lem:extractpart` (a): isometry condition.**
`V†V = 1`, i.e. `(symmetricEmbeddingIsometry d n) * (symmetricEmbeddingIsometry d n)† = 1`.

The rows of `symmetricEmbeddingIsometry` are orthonormal because they are an
injectively-selected subset of the rows of a unitary (the spectral eigenvector
unitary's columns). -/
theorem symmetricEmbeddingIsometry_isometry (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricEmbeddingIsometry d n) * (symmetricEmbeddingIsometry d n)ᴴ =
      (1 : Op (Nat.choose (n + d - 1) (d - 1))) := by
  set hH := Quantum.Symmetry.symmetricProjector_isHermitian d n with hH_def
  set U : Op (d ^ n) :=
    (hH.eigenvectorUnitary : Op (d ^ n)) with hU_def
  -- iso = (Uᴴ).submatrix sel id ; isoᴴ = U.submatrix id sel
  have h_iso : symmetricEmbeddingIsometry d n
      = Uᴴ.submatrix (symmetricEmbeddingSel d n) id := rfl
  rw [h_iso, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
  -- (Uᴴ).submatrix sel id * U.submatrix id sel = (Uᴴ * U).submatrix sel sel
  rw [← Matrix.submatrix_mul Uᴴ U (symmetricEmbeddingSel d n) id (symmetricEmbeddingSel d n)
        Function.bijective_id]
  -- Uᴴ * U = 1 (unitary)
  have h_unit : Uᴴ * U = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [h_unit]
  -- (1).submatrix sel sel = 1, since sel is injective
  exact Matrix.submatrix_one (symmetricEmbeddingSel d n) (symmetricEmbeddingSel_injective d n)

/-- **CKR `lem:extractpart` (b): range / range projector.**
`VV† = P_sym`, i.e.
`(symmetricEmbeddingIsometry d n)† * (symmetricEmbeddingIsometry d n) = symmetricProjector d n`.

The columns of `V` span exactly the symmetric subspace, so `VV†` is its orthogonal
projector. This follows from the spectral expansion of `P_sym` as the eigenvalue-
weighted sum of rank-one eigenprojectors, restricted to the eigenvalue-`1` set. -/
theorem symmetricEmbeddingIsometry_range (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricEmbeddingIsometry d n)ᴴ * (symmetricEmbeddingIsometry d n) =
      symmetricProjector d n := by
  classical
  set hH := Quantum.Symmetry.symmetricProjector_isHermitian d n with hH_def
  set U : Op (d ^ n) :=
    (hH.eigenvectorUnitary : Op (d ^ n)) with hU_def
  -- Spectral expansion of P_sym as eigenvalue-weighted rank-one eigenprojectors.
  have h_spec_sum : symmetricProjector d n
      = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) • Matrix.vecMulVec
          ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp)) := by
    have h2 := Math.SpectralTheory.conjStarAlgAut_eigenvectorUnitary_diagonal hH
      (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
    rw [← h2]
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  -- Restrict the sum to the eigenvalue-1 set (other terms vanish, λ=1 there).
  have h_restrict : (∑ i, ((hH.eigenvalues i : ℝ) : ℂ) • Matrix.vecMulVec
        ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp)))
      = ∑ i ∈ symmetricEmbeddingOneEigenset d n, Matrix.vecMulVec
        ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => hH.eigenvalues i = 1)]
    have h_one : (∑ i ∈ Finset.univ.filter (fun i => hH.eigenvalues i = 1),
          ((hH.eigenvalues i : ℝ) : ℂ) • Matrix.vecMulVec
            ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp)))
        = ∑ i ∈ symmetricEmbeddingOneEigenset d n, Matrix.vecMulVec
            ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp)) := by
      rw [symmetricEmbeddingOneEigenset]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      rw [hi.2]; simp
    have h_zero : (∑ i ∈ Finset.univ.filter (fun i => ¬ hH.eigenvalues i = 1),
          ((hH.eigenvalues i : ℝ) : ℂ) • Matrix.vecMulVec
            ((hH.eigenvectorBasis i).ofLp) (star ((hH.eigenvectorBasis i).ofLp))) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      rcases symmetricProjector_eigenvalues_zero_or_one d n i with h0 | h1
      · rw [h0]; simp
      · exact absurd h1 hi.2
    rw [h_one, h_zero, add_zero]
  -- isoᴴ * iso, written as a sum over Fin g of rank-one terms, reindexed to S.
  have h_iso : symmetricEmbeddingIsometry d n
      = Uᴴ.submatrix (symmetricEmbeddingSel d n) id := rfl
  have h_isoH : (symmetricEmbeddingIsometry d n)ᴴ
      = U.submatrix id (symmetricEmbeddingSel d n) := by
    rw [h_iso, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
  rw [h_spec_sum, h_restrict, h_isoH, h_iso]
  -- Entrywise: (isoᴴ * iso) a b = ∑_{i∈S} u_i a * conj (u_i b).
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  -- LHS sum is over Fin g via the bijection sel : Fin g ≃ S.
  rw [show (∑ x : Fin (Nat.choose (n + d - 1) (d - 1)),
        U.submatrix id (symmetricEmbeddingSel d n) a x
          * (Uᴴ).submatrix (symmetricEmbeddingSel d n) id x b)
      = ∑ i ∈ symmetricEmbeddingOneEigenset d n,
          U a i * (Uᴴ) i b from ?_]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.vecMulVec_apply]
    rw [hU_def, hH.eigenvectorUnitary_apply a i, Matrix.conjTranspose_apply,
      hH.eigenvectorUnitary_apply b i]
    rw [show star ((hH.eigenvectorBasis i).ofLp) b
          = star ((hH.eigenvectorBasis i).ofLp b) from rfl]
  · -- Reindex ∑_{x:Fin g} via sel onto S = symmetricEmbeddingOneEigenset.
    rw [← Finset.sum_attach (symmetricEmbeddingOneEigenset d n)
        (fun i => U a i * (Uᴴ) i b)]
    refine Fintype.sum_equiv
      ((symmetricEmbeddingOneEigenset d n).equivFinOfCardEq
        (symmetricEmbedding_one_eigenset_card d n)).symm _ _ (fun x => ?_)
    simp only [Matrix.submatrix_apply, id_eq, symmetricEmbeddingSel]

/-- **CKR `lem:extractpart` (c): recovery / conjugation identity.**
For any operator `X` supported on the symmetric subspace (`P_sym X P_sym = X`),
`X = V† (V X V†) V`, where `V† = symmetricEmbeddingIsometry d n` here written as
`X = (symmetricEmbeddingIsometry d n)† * (symmetricEmbeddingIsometry d n * X *
  (symmetricEmbeddingIsometry d n)†) * symmetricEmbeddingIsometry d n`.

A direct consequence of (b) `VVᴴ = P_sym`: substituting it twice turns the right-hand
side into `P_sym X P_sym`, which is `X` by the support hypothesis. -/
theorem symmetricEmbeddingIsometry_recovery (d n : ℕ) [NeZero d] [NeZero n]
    (X : Op (d ^ n))
    (hX_supp : symmetricProjector d n * X * symmetricProjector d n = X) :
    X = (symmetricEmbeddingIsometry d n)ᴴ
        * (symmetricEmbeddingIsometry d n * X * (symmetricEmbeddingIsometry d n)ᴴ)
        * symmetricEmbeddingIsometry d n := by
  set V := symmetricEmbeddingIsometry d n with hV_def
  set P := symmetricProjector d n with hP_def
  have hVV : V * Vᴴ = 1 := symmetricEmbeddingIsometry_isometry d n
  have hVHV : Vᴴ * V = P := symmetricEmbeddingIsometry_range d n
  -- Vᴴ (V X Vᴴ) V = (Vᴴ V) X (Vᴴ V) = P X P = X.
  symm
  calc Vᴴ * (V * X * Vᴴ) * V
      = (Vᴴ * V) * X * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = P * X * P := by rw [hVHV]
    _ = X := hX_supp

/-- **Paired embedding isometry** for the Bose-symmetric sector of `(ℂᵈ ⊗ ℂᵈ)^{⊗n}`.

This is the `d ↦ d²` specialization of `symmetricEmbeddingIsometry`: the symmetric
subspace `Sym^n(ℂ^{d²})` of `(ℂ^{d²})^{⊗n}` is the target register of the CKR
source-replacement on a paired (system ⊗ reference) space `ℂ^d ⊗ ℂ^d ≅ ℂ^{d²}`.
Its dimension is `C(n + d² - 1, d² - 1)`, matching the paired CKR polynomial
dimension. Inherits `V†V = 1`, `VV† = P_sym(d², n)` and the recovery identity from
the general lemmas. -/
noncomputable def symmetricEmbeddingIsometryPaired (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix (Fin (Nat.choose (n + d * d - 1) (d * d - 1))) (Fin ((d * d) ^ n)) ℂ :=
  symmetricEmbeddingIsometry (d * d) n

/-- The paired embedding isometry is an isometry: `V†V = 1`. -/
theorem symmetricEmbeddingIsometryPaired_isometry (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricEmbeddingIsometryPaired d n) * (symmetricEmbeddingIsometryPaired d n)ᴴ =
      (1 : Op (Nat.choose (n + d * d - 1) (d * d - 1))) :=
  symmetricEmbeddingIsometry_isometry (d * d) n

/-- The paired embedding's range projector is the paired symmetric projector
`P_sym(d², n)` on `(ℂ^{d²})^{⊗n}`: `VV† = P_sym`. -/
theorem symmetricEmbeddingIsometryPaired_range (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricEmbeddingIsometryPaired d n)ᴴ * (symmetricEmbeddingIsometryPaired d n) =
      symmetricProjector (d * d) n :=
  symmetricEmbeddingIsometry_range (d * d) n

end Quantum.Symmetry


namespace InfoTheory.DeFinetti

open Quantum.Operators Quantum.TensorProducts

/-- Dimension factoring: d^n = d^k * d^(n-k) when k ≤ n. -/
lemma pow_eq_mul_pow_sub {d n k : ℕ} (hk : k ≤ n) :
    d ^ n = d ^ k * d ^ (n - k) := by
  rw [← pow_add, Nat.add_sub_cancel' hk]

/-- "Paired" permutation invariance for bipartite states on ℂ^{d^n} ⊗ ℂ^{d^n}.

    A state Ψ on d^n * d^n is paired-permutation-invariant if it commutes
    with the simultaneous action (U_σ ⊗ U_σ) for all σ ∈ S_n, where
    U_σ = permutationRepresentation d n σ acts on each tensor factor. -/
def IsPairedPermInvariant {d n : ℕ} [NeZero d]
    (Ψ : DensityOp (d ^ n * d ^ n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    let U := Math.RepresentationTheory.permutationRepresentation d n σ
    Op.tensor U U * Ψ.toOp * (Op.tensor U U)† = Ψ.toOp

/-- Signal-permutation invariance for bipartite states on ℂ^{d^n} ⊗ R with an
    arbitrary reference register of dimension `dimR`.

    A state Ψ on `d^n * dimR` is signal-permutation-invariant if it is invariant
    under permutations of the signal register with the identity on the reference
    register: `(U_σ ⊗ I_R) Ψ (U_σ ⊗ I_R)† = Ψ` for all σ ∈ S_n.

    This is strictly weaker than `IsPairedPermInvariant` (which requires `(U_σ ⊗ U_σ)`
    on both factors and is restricted to `dimR = d^n`), and is the right covariance
    condition for chains that permute only the signal register.

    Note: `IsPairedPermInvariant` does NOT imply `IsSignalPermInvariant` in general.
    The square-root-vectorization purification of a permutation-invariant state satisfies
    `IsPairedPermInvariant` but not `(U ⊗ I) τ (U ⊗ I)† = τ` (for example, at `d = 4`, `n = 2`, with
    the swap permutation).  These are independent properties.
    A `d^n`-ancilla CKR purification can satisfy `IsCKRDeFinettiPurification` at ancilla
    dimension `d^n` together with paired permutation invariance, without signal-only
    invariance being asserted.

    References: Renner (2005) §6.5; CKR (2009) main.tex:268–:401 (\emph{Main Result}: Theorem
    `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328); Tomamichel (2016)
    §6.2.4. -/
def IsSignalPermInvariant {d n dimR : ℕ} [NeZero d] [NeZero dimR]
    (Ψ : DensityOp (d ^ n * dimR)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    let U := Math.RepresentationTheory.permutationRepresentation d n σ
    Op.tensor U (1 : Op dimR) * Ψ.toOp * (Op.tensor U (1 : Op dimR))† = Ψ.toOp

/-- Reindex a DensityOp via an equivalence on indices. This is the mathematically
    correct way to change the encoding of a tensor product space: it applies
    the permutation to both row and column indices, equivalent to unitary
    conjugation by a permutation matrix. -/
noncomputable def densityOp_reindex {m n : ℕ}
    (e : Fin m ≃ Fin n) (ψ : DensityOp m) : DensityOp n :=
  ⟨⟨⟨Matrix.reindex e e ψ.toOp, by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
      have hH := ψ.toPosSemidefOp.toHermitianOp.isHermitian
      have h := congr_fun₂ hH (e.symm i) (e.symm j)
      rwa [Matrix.conjTranspose_apply] at h⟩,
    by
      intro x
      have hpsd := ψ.toPosSemidefOp.pos_semidef (fun k => x (e k))
      simp only [quadraticForm, Matrix.reindex_apply, Matrix.submatrix_apply,
                  Matrix.mulVec, dotProduct, Pi.star_apply] at hpsd ⊢
      have hsum : (∑ x_1 : Fin n, star (x x_1) *
            ∑ x_2 : Fin n, ψ.toOp (e.symm x_1) (e.symm x_2) * x x_2) =
          (∑ x_1, star (x (e x_1)) * ∑ x_2, ψ.toOp x_1 x_2 * x (e x_2)) := by
        rw [Fintype.sum_equiv e.symm _
            (fun a : Fin m =>
              star (x (e a)) * ∑ x_2, ψ.toOp a x_2 * x (e x_2))]
        intro a
        simp only [Equiv.apply_symm_apply]
        congr 1
        rw [Fintype.sum_equiv e.symm _
            (fun b : Fin m => ψ.toOp (e.symm a) b * x (e b))]
        intro b; simp [Equiv.apply_symm_apply]
      rw [hsum]; exact hpsd⟩,
   by
      have htrace : (Matrix.reindex e e ψ.toOp).trace = ψ.toOp.trace := by
        simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
        exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
      rw [htrace]
      exact ψ.trace_one⟩

/-- The "paired" symmetric projector on ℂ^{d^n} ⊗ ℂ^{d^n}.

    P_paired = (1/n!) Σ_σ (U_σ ⊗ U_σ) where U_σ = permutationRepresentation d n σ.
    This projects onto the subspace invariant under the paired permutation action
    (Bose-symmetric sector of the bipartite system). The paired symmetric subspace
    has the same dimension as Sym^n(ℂ^{d²}), since the representations are
    isomorphic via the interleaving map. -/
noncomputable def symmetricProjectorPaired (d n : ℕ) [NeZero d] [NeZero n] :
    Op (d ^ n * d ^ n) :=
  (1 / (Nat.factorial n : ℂ)) •
    ∑ σ : Equiv.Perm (Fin n),
      Op.tensor (Math.RepresentationTheory.permutationRepresentation d n σ)
                (Math.RepresentationTheory.permutationRepresentation d n σ)

end InfoTheory.DeFinetti
end
