import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.InfoTheory.DeFinetti.MaxEntangled
import QCryptLean.Quantum.Metrics.PurificationFreedom
import QCryptLean.InfoTheory.DeFinetti.PureState.SchurLemma.Main
import QCryptLean.InfoTheory.DistanceBounds.TraceNormContraction
import QCryptLean.InfoTheory.VonNeumannEntropy.Continuity
import QCryptLean.Quantum.Metrics.RectangularPolar
import QCryptLean.Math.SpectralTheory.PSDDecomposition
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Symmetric Purification and de Finetti Reference States

Square-root/vectorization purifications, symmetric purifications for CKMR Lemma II.5,
and normalized de Finetti reference states.
Given a permutation-invariant state ρ on (ℂᵈ)^⊗n, constructs a purification Ψ
on (ℂᵈ)^⊗n ⊗ (ℂᵈ)^⊗n that is paired-permutation-invariant and pure.
The same construction also gives an unrestricted pure purification of any density
operator on `(ℂᵈ)^⊗n`.

## Main definitions
- `deFinettiState`: normalized symmetric projector `P_sym / Tr(P_sym)` on `(ℂᵈ)^⊗n`
- `sqrtOp`: Matrix square root of a density operator
- `maxEntangledOp`: Maximally entangled state |Φ⟩⟨Φ|

## Main statements
- `deFinettiState_one`: for `n = 1`, the de Finetti state is `(1/d) • I`
- `deFinettiState_eq_haar_integral`: `deFinettiState d n` is the Haar integral
  of pure tensor powers
- `symmetric_purification`: Existence of a paired-perm-invariant purification with
  symmetric subspace membership and partial trace recovery
- `symmetric_purification_with_pure`: As above, additionally proving purity
- `symmetric_purification_isPure`: The constructed purification is pure (idempotent)
- `maxEntangledOp_sandwich`: Key identity `Ω * (M ⊗ 𝟙) * Ω = Tr(M) • Ω`
- `densityOp_purification_exists`: arbitrary finite-dimensional density operators
  have a pure square-root/vectorization purification
- `purificationDensityOp_in_paired_symmetric_subspace`: permutation-invariant
  inputs have square-root/vectorization purifications with paired symmetric support
- `purificationDensityOp_continuous`: continuity of `ρ ↦ purificationDensityOp ρ`
- `maxEntangledOp_tensor_one_ricochet`, `maxEntangledOp_mul_tensor_one_ricochet`:
  operator-level ricochet identities `Ω·(A ⊗ 1) = Ω·(1 ⊗ Aᵀ)` (and left action)
- `purificationOp_partialTraceA`: the first-factor marginal of the square-root
  purification is `ρᵀ`

## Helper lemmas
- `permRep_star_entry`, `permRep_conjTranspose_eq_transpose`,
  `permRep_row_orthogonality`: Properties of the permutation representation
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator MatrixOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-!
## Helper lemmas for symmetric purification (CKMR Lemma II.5)

For a permutation-invariant state `ρ` on `(ℂᵈ)^⊗n`, the symmetric purification is
the pure state `Ψ_ρ = (√ρ ⊗ 𝟙)|Ω⟩⟨Ω|(√ρ ⊗ 𝟙)†` on
`(ℂᵈ ⊗ ℂᵈ)^⊗n ≅ (ℂ^{d²})^⊗n`. It is permutation-invariant, lies in the symmetric
subspace, and has partial trace `ρ`.
-/

-- Tensoring a matrix with a fixed identity on the right is continuous.
private lemma tensor_one_continuous {n k : ℕ} :
    Continuous (fun A : Op n => A ⊗ (1 : Op k)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun A : Op n =>
    A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      (1 : Op k) (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
  exact (continuous_apply_apply _ _).mul continuous_const

/-- The positive semidefinite square root of a density operator.
    For ρ PSD with eigendecomposition ρ = Σᵢ λᵢ|eᵢ⟩⟨eᵢ|, this is √ρ = Σᵢ √λᵢ|eᵢ⟩⟨eᵢ|.
    Satisfies sqrtOp ρ * sqrtOp ρ = ρ.toOp (proven in sqrtOp_sq). -/
noncomputable def sqrtOp {m : ℕ} (ρ : DensityOp m) : Op m :=
  letI : PartialOrder (Op m) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op m) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op m) := Matrix.instNonnegSpectrumClass
  CFC.sqrt ρ.toOp

/-- √ρ squared recovers ρ: (√ρ)(√ρ) = ρ -/
lemma sqrtOp_sq {m : ℕ} (ρ : DensityOp m) :
    sqrtOp ρ * sqrtOp ρ = ρ.toOp := by
  unfold sqrtOp
  letI : PartialOrder (Op m) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op m) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op m) := Matrix.instNonnegSpectrumClass
  exact CFC.sqrt_mul_sqrt_self ρ.toOp ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).nonneg)

section sqrtContinuity
-- `CStarAlgebra (Op m)` needed locally for CFC continuity of the matrix
-- square root.  Declared as `local instance` so it is NOT exported to
-- downstream importers via the `.olean` file, preventing the L2Operator
-- `NormedRing` from leaking into downstream typeclass synthesis.
-- The parent instances (`NormedRing`, `NormedAlgebra ℂ`, `CStarRing`) come
-- from the file-level `open scoped Matrix.Norms.L2Operator MatrixOrder`.
@[implicit_reducible] private noncomputable def instCStarAlgebraOp_def
    (m : ℕ) [DecidableEq (Fin m)] :
    CStarAlgebra (Op m) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

attribute [local instance] instCStarAlgebraOp_def

-- Matrix square root is continuous on the cone of PSD operators,
-- using CFC continuity (Mathlib.Analysis.SpecialFunctions...Rpow.Isometric).
private lemma sqrtOp_continuous {m : ℕ} [NeZero m] :
    Continuous (fun ρ : DensityOp m => sqrtOp ρ) := by
  haveI : DecidableEq (Fin m) := inferInstance
  have hsq : ∀ ρ : DensityOp m, sqrtOp ρ = CFC.sqrt ρ.toOp := fun ρ => by
    unfold sqrtOp; rfl
  simp_rw [hsq]
  apply CFC.continuousOn_sqrt.comp_continuous continuous_induced_dom
  intro ρ; exact (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).nonneg

end sqrtContinuity

/-- √ρ is Hermitian (since ρ is PSD, its square root is also PSD hence Hermitian) -/
lemma sqrtOp_isHermitian {m : ℕ} (ρ : DensityOp m) :
    (sqrtOp ρ).IsHermitian := by
  unfold sqrtOp
  letI : PartialOrder (Op m) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op m) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op m) := Matrix.instNonnegSpectrumClass
  exact ((CFC.sqrt_nonneg (a := ρ.toOp)).posSemidef).isHermitian

/-- √ρ† = √ρ (consequence of Hermiticity) -/
private lemma sqrtOp_conjTranspose {m : ℕ} (ρ : DensityOp m) :
    (sqrtOp ρ)† = sqrtOp ρ := by
  exact sqrtOp_isHermitian ρ

/-- The purification operator before packaging as DensityOp.
    Given ρ on (ℂᵈ)^⊗n, this constructs the operator
    (√ρ ⊗ 𝟙_{d^n}) · |Ψ⟩⟨Ψ| · (√ρ ⊗ 𝟙_{d^n})†
    on ℂ^{d^n} ⊗ ℂ^{d^n} ≅ ℂ^{(d·d)^n}, where |Ψ⟩⟨Ψ| is the
    maximally entangled state on ℂ^{d^n} ⊗ ℂ^{d^n}. -/
noncomputable def purificationOp {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) : Op (d ^ n * d ^ n) :=
  let sqrtρ := sqrtOp ρ
  let sqrtρ_tensor_id : Op (d ^ n * d ^ n) := sqrtρ ⊗ (1 : Op (d ^ n))
  let Ψ := maxEntangledOp (d ^ n)
  sqrtρ_tensor_id * Ψ * sqrtρ_tensor_id†

/-- The purification operator is Hermitian. -/
private lemma purificationOp_isHermitian {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) :
    (purificationOp ρ).IsHermitian := by
  unfold IsHermitian
  simp only [purificationOp]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [maxEntangledOp_isHermitian, Matrix.mul_assoc]

/-- The purification operator is positive semidefinite. -/
private lemma purificationOp_posSemidef {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) :
    ∀ x : Fin (d ^ n * d ^ n) → ℂ,
      0 ≤ (quadraticForm (purificationOp ρ) x).re := by
  intro x
  simp only [purificationOp]
  let A : Op (d ^ n * d ^ n) := sqrtOp ρ ⊗ (1 : Op (d ^ n))
  let Ψ := maxEntangledOp (d ^ n)
  -- Reduce to x†(AΨA†)x = (A†x)†Ψ(A†x) ≥ 0
  have key : quadraticForm (A * Ψ * A†) x = quadraticForm Ψ (A†.mulVec x) := by
    unfold quadraticForm
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    congr 1
    rw [Matrix.star_mulVec, conjTranspose_conjTranspose]
  rw [key]
  exact posSemidef_re_quadraticForm_nonneg (maxEntangledOp_posSemidef (d ^ n)) _

/-- The square-root purification factor has Gram matrix `ρ ⊗ 𝟙`. -/
lemma sqrtOp_tensor_one_conjTranspose_mul_self {m k : ℕ} (ρ : DensityOp m) :
    (sqrtOp ρ ⊗ (1 : Op k))† * (sqrtOp ρ ⊗ (1 : Op k)) =
      ρ.toOp ⊗ (1 : Op k) := by
  rw [Op.tensor_conjTranspose, Op.tensor_mul, conjTranspose_one, Matrix.one_mul,
    sqrtOp_conjTranspose, sqrtOp_sq]

/-- `Tr[(√ρ ⊗ 𝟙) Ψ (√ρ ⊗ 𝟙)†] = 1`. -/
private lemma purificationOp_trace_one {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) :
    (purificationOp ρ).trace = 1 := by
  simp only [purificationOp]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [sqrtOp_tensor_one_conjTranspose_mul_self, trace_maxEntangled_mul_tensor_one]
  exact ρ.trace_one

/-- Purification of an arbitrary density operator via the `(√ρ ⊗ 𝟙)|Ω⟩`
    construction, packaged as a `DensityOp` on the system and an equal-size
    reference register. -/
noncomputable def purificationDensityOp {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) : DensityOp (d ^ n * d ^ n) :=
  ⟨⟨⟨purificationOp ρ,
     purificationOp_isHermitian ρ⟩,
     purificationOp_posSemidef ρ⟩,
   purificationOp_trace_one ρ⟩

/-- CFC commutant preservation: if `U * ρ = ρ * U` then `U * √ρ = √ρ * U`. -/
lemma sqrtOp_commutes_of_commutes {m : ℕ} (ρ : DensityOp m) (U : Op m)
    (hcomm : U * ρ.toOp = ρ.toOp * U) :
    U * sqrtOp ρ = sqrtOp ρ * U := by
  letI : PartialOrder (Op m) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op m) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op m) := Matrix.instNonnegSpectrumClass
  unfold sqrtOp
  change U * CFC.sqrt ρ.toOp = CFC.sqrt ρ.toOp * U
  simp only [CFC.sqrt]
  have hc : Commute ρ.toOp U := hcomm.symm
  exact (Commute.cfcₙ_nnreal hc NNReal.sqrt).symm.eq

/-- The square root of a permutation-invariant density operator commutes with
    every tensor-factor permutation representation. -/
private lemma sqrtOp_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    ∀ σ : Equiv.Perm (Fin n),
      let U := Math.RepresentationTheory.permutationRepresentation d n σ
      U * sqrtOp ρ = sqrtOp ρ * U := by
  intro σ
  exact sqrtOp_commutes_of_commutes ρ _
    (((isPermutationInvariant_iff_commutes ρ).mp hinv) σ)

/-- Permutation representation entries are real: `star (U i j) = U i j`. -/
lemma permRep_star_entry {d n : ℕ} [NeZero d] (σ : Equiv.Perm (Fin n))
    (i j : Fin (d ^ n)) :
    star (Math.RepresentationTheory.permutationRepresentation d n σ i j) =
      Math.RepresentationTheory.permutationRepresentation d n σ i j := by
  simp only [Math.RepresentationTheory.permutationRepresentation, Matrix.of_apply]
  split_ifs <;> simp

/-- Conjugate transpose equals transpose for the permutation representation. -/
lemma permRep_conjTranspose_eq_transpose {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    (Math.RepresentationTheory.permutationRepresentation d n σ)† =
      (Math.RepresentationTheory.permutationRepresentation d n σ)ᵀ := by
  ext i j; simp [conjTranspose_apply, transpose_apply, permRep_star_entry]

/-- Row orthogonality for the permutation representation:
    `∑ k, U a k * U b k = if a = b then 1 else 0`. -/
lemma permRep_row_orthogonality {d n : ℕ} [NeZero d] (σ : Equiv.Perm (Fin n))
    (a b : Fin (d ^ n)) :
    ∑ k, Math.RepresentationTheory.permutationRepresentation d n σ a k *
      Math.RepresentationTheory.permutationRepresentation d n σ b k =
    if a = b then 1 else 0 := by
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  have hUU : U * U† = 1 :=
    (Math.RepresentationTheory.permutationRepresentation_unitary d n σ).2
  have hU_conj : U† = Uᵀ := permRep_conjTranspose_eq_transpose σ
  have := congr_fun₂ (hU_conj ▸ hUU) a b
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply] using this

/-- Left multiplication invariance: `(U_σ ⊗ U_σ) * |Ω⟩⟨Ω| = |Ω⟩⟨Ω|`. -/
lemma maxEntangledOp_left_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (σ : Equiv.Perm (Fin n)) :
    let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
    (Op.tensor U U) * maxEntangledOp (d ^ n) = maxEntangledOp (d ^ n) := by
  simp only
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  have horth : ∀ (a b : Fin (d ^ n)),
      ∑ k : Fin (d ^ n), U a k * U b k = if a = b then 1 else 0 :=
    permRep_row_orthogonality σ
  ext i j
  simp only [Matrix.mul_apply, Op.tensor, reindex_apply, submatrix_apply,
             kroneckerMap_apply, maxEntangledOp, Matrix.of_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
      (fun p => U (finProdFinEquiv.symm i).1 p.1 *
        U (finProdFinEquiv.symm i).2 p.2 *
        if p.1 = p.2 ∧ (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2
        then 1 else 0)
      (by intro a; simp)]
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext x; arg 2; ext x₁
    rw [show U (finProdFinEquiv.symm i).1 x * U (finProdFinEquiv.symm i).2 x₁ *
      (if x = x₁ ∧ (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2 then 1 else 0) =
      (if (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2 then
        (if x = x₁ then U (finProdFinEquiv.symm i).1 x * U (finProdFinEquiv.symm i).2 x₁
         else 0)
       else 0) from by
         split_ifs with h1 h2 h3 <;> simp_all [mul_one, mul_zero]]
  by_cases hj : (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2
  · simp only [hj, ite_true]
    simp_rw [Finset.sum_ite_eq Finset.univ, Finset.mem_univ, ite_true]
    rw [horth]
    simp
  · simp only [hj, ite_false, Finset.sum_const_zero]
    simp

/-- The maximally entangled state is invariant under simultaneous permutation:
    `(U_σ ⊗ U_σ) * Ψ * (U_σ ⊗ U_σ)† = Ψ`. -/
lemma maxEntangledOp_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (σ : Equiv.Perm (Fin n)) :
    let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
    (Op.tensor U U) * maxEntangledOp (d ^ n) * (Op.tensor U U)† =
      maxEntangledOp (d ^ n) := by
  simp only
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  have hleft : Op.tensor U U * maxEntangledOp (d ^ n) = maxEntangledOp (d ^ n) :=
    maxEntangledOp_left_perm_invariant σ
  have hright : maxEntangledOp (d ^ n) * (Op.tensor U U)† = maxEntangledOp (d ^ n) := by
    have h := congrArg Matrix.conjTranspose hleft
    rw [conjTranspose_mul, maxEntangledOp_isHermitian] at h
    exact h
  calc
    Op.tensor U U * maxEntangledOp (d ^ n) * (Op.tensor U U)†
      = maxEntangledOp (d ^ n) * (Op.tensor U U)† := by rw [hleft]
    _ = maxEntangledOp (d ^ n) := hright

/-- `(U_σ ⊗ U_σ) * purificationOp ρ * (U_σ ⊗ U_σ)† = purificationOp ρ`. -/
lemma purificationOp_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ)
    (σ : Equiv.Perm (Fin n)) :
    let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
    (Op.tensor U U) * purificationOp ρ * (Op.tensor U U)† = purificationOp ρ := by
  simp only
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  set S := sqrtOp ρ
  simp only [purificationOp]
  have hcomm : U * S = S * U := sqrtOp_perm_invariant ρ hinv σ
  have h1 : Op.tensor U U * Op.tensor S (1 : Op (d ^ n)) =
      Op.tensor (U * S) (U * 1) := by
    rw [Op.tensor_mul]
  rw [mul_one] at h1
  have h2 : Op.tensor (U * S) U = Op.tensor S (1 : Op (d ^ n)) * Op.tensor U U := by
    rw [hcomm]
    symm
    rw [Op.tensor_mul, one_mul]
  have h3 : Op.tensor U U * Op.tensor S (1 : Op (d ^ n)) =
      Op.tensor S (1 : Op (d ^ n)) * Op.tensor U U := by
    rw [h1, h2]
  have h3ct : (Op.tensor S (1 : Op (d ^ n)))† * (Op.tensor U U)† =
      (Op.tensor U U)† * (Op.tensor S (1 : Op (d ^ n)))† := by
    rw [← conjTranspose_mul, ← conjTranspose_mul, h3]
  calc Op.tensor U U * (Op.tensor S 1 * maxEntangledOp (d ^ n) * (Op.tensor S 1)†) *
      (Op.tensor U U)†
    _ = Op.tensor U U * Op.tensor S 1 * maxEntangledOp (d ^ n) *
        ((Op.tensor S 1)† * (Op.tensor U U)†) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc]
    _ = Op.tensor S 1 * Op.tensor U U * maxEntangledOp (d ^ n) *
        ((Op.tensor U U)† * (Op.tensor S 1)†) := by
        rw [h3, h3ct]
    _ = Op.tensor S 1 * (Op.tensor U U * maxEntangledOp (d ^ n) * (Op.tensor U U)†) *
        (Op.tensor S 1)† := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc]
    _ = Op.tensor S 1 * maxEntangledOp (d ^ n) * (Op.tensor S 1)† := by
        rw [maxEntangledOp_perm_invariant σ]

/-- The purification construction yields a paired-permutation-invariant state. -/
private lemma purification_is_paired_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    IsPairedPermInvariant (purificationDensityOp ρ) := by
  intro σ
  exact purificationOp_perm_invariant ρ hinv σ

/-- `(U_σ ⊗ U_σ) * purificationOp ρ = purificationOp ρ`. -/
private lemma purificationOp_left_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ)
    (σ : Equiv.Perm (Fin n)) :
    let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
    (Op.tensor U U) * purificationOp ρ = purificationOp ρ := by
  simp only
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  set S := sqrtOp ρ
  simp only [purificationOp]
  have hcomm : U * S = S * U := sqrtOp_perm_invariant ρ hinv σ
  have hleft : Op.tensor U U * maxEntangledOp (d ^ n) = maxEntangledOp (d ^ n) :=
    maxEntangledOp_left_perm_invariant σ
  have h3 : Op.tensor U U * Op.tensor S (1 : Op (d ^ n)) =
      Op.tensor S (1 : Op (d ^ n)) * Op.tensor U U := by
    rw [Op.tensor_mul, Op.tensor_mul, hcomm, mul_one, one_mul]
  calc Op.tensor U U * (Op.tensor S 1 * maxEntangledOp (d ^ n) * (Op.tensor S 1)†)
    _ = Op.tensor U U * Op.tensor S 1 * maxEntangledOp (d ^ n) * (Op.tensor S 1)† := by
        rw [Matrix.mul_assoc (Op.tensor U U), Matrix.mul_assoc (Op.tensor U U)]
    _ = Op.tensor S 1 * Op.tensor U U * maxEntangledOp (d ^ n) * (Op.tensor S 1)† := by
        rw [h3]
    _ = Op.tensor S 1 * (Op.tensor U U * maxEntangledOp (d ^ n)) * (Op.tensor S 1)† := by
        rw [Matrix.mul_assoc (Op.tensor S 1)]
    _ = Op.tensor S 1 * maxEntangledOp (d ^ n) * (Op.tensor S 1)† := by
        rw [hleft]

/-- The paired symmetric projector fixes any operator fixed on the left by all paired
    permutation representations. -/
lemma symmetricProjectorPaired_mul_eq_of_perm_left_invariant {d n : ℕ}
    [NeZero d] [NeZero n] (A : Op (d ^ n * d ^ n))
    (hA : ∀ σ : Equiv.Perm (Fin n),
      let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
      Op.tensor U U * A = A) :
    symmetricProjectorPaired d n * A = A := by
  unfold symmetricProjectorPaired
  rw [smul_mul_assoc, Finset.sum_mul]
  conv_lhs =>
    arg 2; arg 2; ext σ
    rw [hA σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),
    one_smul]

/-- Any operator fixed on the right by all paired permutation representations is
    fixed on the right by the paired symmetric projector. -/
lemma mul_symmetricProjectorPaired_eq_of_perm_right_invariant {d n : ℕ}
    [NeZero d] [NeZero n] (A : Op (d ^ n * d ^ n))
    (hA : ∀ σ : Equiv.Perm (Fin n),
      let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
      A * Op.tensor U U = A) :
    A * symmetricProjectorPaired d n = A := by
  unfold symmetricProjectorPaired
  rw [Matrix.mul_smul, Finset.mul_sum]
  conv_lhs =>
    arg 2; arg 2; ext σ
    rw [hA σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),
    one_smul]

/-- The purification lies in the paired symmetric subspace:
    `P_paired * Ψ * P_paired = Ψ`. -/
private lemma purification_in_paired_symmetric_subspace {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    symmetricProjectorPaired d n * (purificationDensityOp ρ).toOp *
      symmetricProjectorPaired d n = (purificationDensityOp ρ).toOp := by
  change symmetricProjectorPaired d n * purificationOp ρ *
    symmetricProjectorPaired d n = purificationOp ρ
  set Ψ := purificationOp ρ
  have hPΨ : symmetricProjectorPaired d n * Ψ = Ψ := by
    apply symmetricProjectorPaired_mul_eq_of_perm_left_invariant
    intro σ
    simpa only [Ψ] using purificationOp_left_perm_invariant ρ hinv σ
  have hΨP : Ψ * symmetricProjectorPaired d n = Ψ := by
    have hΨherm : Ψ† = Ψ := purificationOp_isHermitian ρ
    apply mul_symmetricProjectorPaired_eq_of_perm_right_invariant
    intro σ
    have hleft_inv := purificationOp_left_perm_invariant ρ hinv σ⁻¹
    have h := congr_arg Matrix.conjTranspose hleft_inv
    rw [conjTranspose_mul, hΨherm, Op.tensor_conjTranspose] at h
    simp_rw [Math.RepresentationTheory.permutationRepresentation_inv,
             conjTranspose_conjTranspose] at h
    exact h
  rw [hPΨ, hΨP]

/-- The square-root/vectorization purification of a permutation-invariant state
lies in the paired symmetric subspace. -/
lemma purificationDensityOp_in_paired_symmetric_subspace {d n : ℕ}
    [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    symmetricProjectorPaired d n * (purificationDensityOp ρ).toOp *
      symmetricProjectorPaired d n = (purificationDensityOp ρ).toOp := by
  exact purification_in_paired_symmetric_subspace (d := d) (n := n) ρ hinv

private lemma partialTraceB_purificationOp {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (ρ : DensityOp (d ^ n)) :
    partialTraceB (purificationOp ρ) = ρ.toOp := by
  simp only [purificationOp]
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [partialTraceB_sandwich_tensor_one]
  rw [maxEntangledOp_partialTraceB]
  rw [Matrix.mul_one, sqrtOp_conjTranspose, sqrtOp_sq]

/-- The partial trace of the purification recovers ρ. -/
private lemma purification_partial_trace {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (_hinv : IsPermutationInvariant ρ) :
    partialTraceB (purificationDensityOp ρ).toOp = ρ.toOp := by
  exact partialTraceB_purificationOp ρ

/-- The unrestricted purification has marginal `ρ` on the first subsystem. -/
lemma purificationDensityOp_partialTraceB {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) :
    (purificationDensityOp ρ).partialTraceB = ρ := by
  apply DensityOp.ext
  change partialTraceB (purificationOp ρ) = ρ.toOp
  exact partialTraceB_purificationOp ρ

/-- The unrestricted purification is pure. -/
lemma purificationDensityOp_isPure {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) :
    (purificationDensityOp ρ).IsPure := by
  change purificationOp ρ * purificationOp ρ = purificationOp ρ
  simp only [purificationOp]
  set A : Op (d ^ n * d ^ n) := sqrtOp ρ ⊗ (1 : Op (d ^ n))
  set Ω := maxEntangledOp (d ^ n)
  have lhs_eq : (A * Ω * A†) * (A * Ω * A†) = A * (Ω * (A† * A) * Ω) * A† := by
    simp only [Matrix.mul_assoc]
  rw [lhs_eq]
  have adjA_mul_A : A† * A = ρ.toOp ⊗ (1 : Op (d ^ n)) := by
    simpa only [A] using sqrtOp_tensor_one_conjTranspose_mul_self ρ
  rw [adjA_mul_A, maxEntangledOp_sandwich, ρ.trace_one, one_smul]

/-- Every density operator on `(ℂᵈ)^⊗n` has a pure purification with an
    equal-size reference register. -/
lemma densityOp_purification_exists {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) :
    ∃ (Ψ : DensityOp (d ^ n * d ^ n)),
      Ψ.IsPure ∧ Ψ.partialTraceB = ρ := by
  exact ⟨purificationDensityOp ρ,
    purificationDensityOp_isPure ρ,
    purificationDensityOp_partialTraceB ρ⟩

/-- The square-root/vectorization purification `(√ρ ⊗ 𝟙)|Ω⟩` is continuous in
`ρ`. -/
lemma purificationDensityOp_continuous {d n : ℕ} [NeZero d] [NeZero n] :
    Continuous (purificationDensityOp (d := d) (n := n)) := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  rw [continuous_induced_rng]
  change Continuous (fun ρ : DensityOp (d ^ n) => purificationOp ρ)
  simp only [purificationOp]
  have h_T : Continuous (fun ρ : DensityOp (d ^ n) => sqrtOp ρ ⊗ (1 : Op (d ^ n))) :=
    tensor_one_continuous.comp sqrtOp_continuous
  exact ((continuous_mul_const _).comp h_T).mul (continuous_star.comp h_T)

/-- The operator of the canonical purification of a tensor power depends continuously on
its single-copy density operator. -/
lemma continuous_purificationDensityOp_tensorPowGen_toOp {d n : ℕ}
    [NeZero d] [NeZero n] :
    Continuous (fun σ : DensityOp d => (purificationDensityOp (σ.tensorPowGen n)).toOp) :=
  DensityOp.continuous_toOp.comp
    (purificationDensityOp_continuous.comp tensorPowGen_continuous)

/-- CKMR Lemma II.5: Symmetric purification of permutation-invariant states.

    Any permutation-invariant ρ on (ℂᵈ)^⊗n has a purification
    Ψ_ρ on ℂ^{d^n} ⊗ ℂ^{d^n} that is:
    (1) Paired-permutation-invariant: (U_σ ⊗ U_σ) * Ψ * (U_σ ⊗ U_σ)† = Ψ
    (2) In the paired symmetric subspace: P_paired * Ψ * P_paired = Ψ
    (3) Partial trace recovery: Tr_B(Ψ) = ρ

    The construction uses the concatenated encoding (d^n * d^n) rather than
    the interleaved encoding ((d*d)^n), with the paired symmetric projector
    P_paired = (1/n!) Σ_σ (U_σ ⊗ U_σ) replacing the standard projector. -/
lemma symmetric_purification {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    ∃ (Ψ : DensityOp (d ^ n * d ^ n)),
      IsPairedPermInvariant Ψ ∧
      symmetricProjectorPaired d n * Ψ.toOp * symmetricProjectorPaired d n = Ψ.toOp ∧
      partialTraceB Ψ.toOp = ρ.toOp := by
  exact ⟨purificationDensityOp ρ,
    purification_is_paired_perm_invariant ρ hinv,
    purification_in_paired_symmetric_subspace ρ hinv,
    purification_partial_trace ρ hinv⟩

/-- The square-root/vectorization symmetric purification is a pure state
    (idempotent: `Ψ² = Ψ`). -/
lemma symmetric_purification_isPure {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) :
    (purificationDensityOp ρ).IsPure := by
  exact purificationDensityOp_isPure ρ

/-- `symmetric_purification` extended with purity: the purification is pure,
    paired-permutation-invariant, lies in the symmetric subspace, and recovers ρ. -/
lemma symmetric_purification_with_pure {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    ∃ (Ψ : DensityOp (d ^ n * d ^ n)),
      Ψ.IsPure ∧
      IsPairedPermInvariant Ψ ∧
      symmetricProjectorPaired d n * Ψ.toOp * symmetricProjectorPaired d n = Ψ.toOp ∧
      partialTraceB Ψ.toOp = ρ.toOp := by
  exact ⟨purificationDensityOp ρ,
    symmetric_purification_isPure ρ,
    purification_is_paired_perm_invariant ρ hinv,
    purification_in_paired_symmetric_subspace ρ hinv,
    purification_partial_trace ρ hinv⟩

/-!
## De Finetti Reference States

Normalized symmetric-projector states used as the canonical reference states in
de Finetti and CKR-style postselection arguments.
-/

/-- The trace of the symmetric projector is self-adjoint (real):
    `star(trace P_sym) = trace P_sym`. -/
lemma symmetricProjector_trace_selfAdjoint (d n : ℕ) [NeZero d] [NeZero n] :
    starRingEnd ℂ (Matrix.trace (symmetricProjector d n)) =
      Matrix.trace (symmetricProjector d n) := by
  have hP := Quantum.Symmetry.symmetricProjector_isHermitian d n
  change star (Matrix.trace (symmetricProjector d n)) = _
  rw [← Matrix.trace_conjTranspose]
  exact congrArg Matrix.trace hP

/-- The trace of the symmetric projector has positive real part:
    `Tr(P_sym).re = C(n+d-1, d-1) > 0`. -/
lemma symmetricProjector_trace_re_pos (d n : ℕ) [NeZero d] [NeZero n] :
    0 < ((symmetricProjector d n).trace).re := by
  rw [symmetricSubspace_dim]
  exact Nat.cast_pos.mpr (Nat.choose_pos (by omega))

/-- The trace of the symmetric projector is nonzero. -/
lemma symmetricProjector_trace_ne_zero (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix.trace (symmetricProjector d n) ≠ 0 := by
  intro h
  have := symmetricProjector_trace_re_pos d n
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- The symmetric projector is positive semidefinite (Mathlib sense). -/
lemma symmetricProjector_posSemidef (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjector d n).PosSemidef := by
  have ⟨hidp, hherm⟩ := symmetricProjector_is_projector d n
  rw [show symmetricProjector d n = (symmetricProjector d n)ᴴ * symmetricProjector d n
    from by rw [hherm, hidp]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Scaling a PSD matrix by a scalar with nonnegative real part and zero imaginary part
    preserves the nonnegative real-part quadratic form. -/
lemma quadraticForm_re_nonneg_of_nonnegReal_smul {m : ℕ} (c : ℂ) (A : Op m)
    (x : Fin m → ℂ) (hA : A.PosSemidef) (hc_re : 0 ≤ c.re) (hc_im : c.im = 0) :
    0 ≤ (quadraticForm (c • A) x).re := by
  rw [Quantum.Operators.quadraticForm_smul, Complex.mul_re, hc_im, zero_mul, sub_zero]
  exact mul_nonneg hc_re (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

private lemma symmetricProjector_normalized_isHermitian (d n : ℕ)
    [NeZero d] [NeZero n] :
    IsHermitian ((1 / (symmetricProjector d n).trace) • symmetricProjector d n) := by
  exact (IsSelfAdjoint.smul
    (IsSelfAdjoint.div (.one ℂ) (symmetricProjector_trace_selfAdjoint d n))
    (Quantum.Symmetry.symmetricProjector_isHermitian d n).isSelfAdjoint).isHermitian

private lemma symmetricProjector_normalized_posSemidef (d n : ℕ)
    [NeZero d] [NeZero n] :
    ∀ x : Fin (d ^ n) → ℂ,
      0 ≤
        (quadraticForm
          ((1 / (symmetricProjector d n).trace) • symmetricProjector d n) x).re := by
  intro x
  apply InfoTheory.DeFinetti.quadraticForm_re_nonneg_of_nonnegReal_smul _ _ _
      (symmetricProjector_posSemidef d n)
  · rw [one_div, Complex.inv_re]
    exact div_nonneg (symmetricProjector_trace_re_pos d n).le (Complex.normSq_nonneg _)
  · rw [one_div, Complex.inv_im,
      Complex.conj_eq_iff_im.mp (symmetricProjector_trace_selfAdjoint d n)]
    ring

private lemma symmetricProjector_normalized_trace_one (d n : ℕ)
    [NeZero d] [NeZero n] :
    Matrix.trace ((1 / (symmetricProjector d n).trace) • symmetricProjector d n) = 1 := by
  rw [Matrix.trace_smul, smul_eq_mul, one_div]
  exact inv_mul_cancel₀ (symmetricProjector_trace_ne_zero d n)

/-- **De Finetti state** on `(ℂ^d)^⊗n`: the Haar integral of pure-state tensor powers
    `∫ |ψ⟩⟨ψ|^⊗n dHaar(ψ)` over the unit sphere of ℂ^d.

    Equivalently, this is the normalized symmetric projector `P_sym / Tr(P_sym)`,
    i.e. the maximally mixed state on `Sym^n(ℂ^d)`.

    **Not equal in general to CKR's τ_{H^n}** (CKR 2009 eq. (1)), which is the
    Hilbert-Schmidt integral `∫ σ^⊗n dμ_HS(σ)` over *density operators* on ℂ^d.
    The two integrals differ for n ≥ 2: e.g. at n = 2, d = 2 the Haar-pure state
    is I/6 + swap/6 while the HS-density state is I/5 + swap/10.
    For CKR's state use `Quantum.Channels.ckrDeFinettiState`. -/
noncomputable def deFinettiState (d n : ℕ) [NeZero d] [NeZero n] : DensityOp (d ^ n) where
  toOp :=
    let P := Quantum.Symmetry.symmetricProjector d n
    (1 / P.trace) • P
  isHermitian := symmetricProjector_normalized_isHermitian d n
  pos_semidef := symmetricProjector_normalized_posSemidef d n
  trace_one := symmetricProjector_normalized_trace_one d n

/-- The symmetric de Finetti state equals the Haar integral of pure tensor powers. -/
theorem deFinettiState_eq_haar_integral (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    deFinettiState d n = integralTensorPower n (deFinetti_haarMeasure d) := by
  apply DensityOp.ext
  rw [InfoTheory.DeFinetti.PureState.integralTensorPower_deFinetti_haar_eq_coherent_integral
      (d := d) (n := n)]
  rw [InfoTheory.DeFinetti.PureState.coherent_integral_eq_inv_dim_smul_symProj_schur (d := d) (n :=
      n)]
  simp only [deFinettiState]
  rw [symmetricProjector_trace, one_div]
  change
    (((↑((n + d - 1).choose (d - 1)) : ℂ)⁻¹) • symmetricProjector d n) =
      ((((↑((n + d - 1).choose (d - 1)) : ℝ)⁻¹ : ℝ) : ℂ) • symmetricProjector d n)
  congr 1
  symm
  exact Complex.ofReal_inv ((Nat.choose (n + d - 1) (d - 1) : ℝ))

/-- For `n = 1`, the symmetric projector on `(ℂ^d)^⊗1` is the identity. -/
lemma symmetricProjector_one_eq_one (d : ℕ) [NeZero d] :
    symmetricProjector d 1 = (1 : Op (d ^ 1)) := by
  unfold Quantum.Symmetry.symmetricProjector Math.RepresentationTheory.symmetricProjectorRep
  rw [Fintype.sum_unique, Equiv.Perm.default_eq]
  simp [Nat.factorial, Math.RepresentationTheory.permutationRepresentation_one]

/-- For `n = 1`, the de Finetti state on `ℂ^d` is the maximally mixed state `(1 / d) • I`. -/
lemma deFinettiState_one (d : ℕ) [NeZero d] :
    (deFinettiState d 1).toOp = (1 / ↑d : ℂ) • (1 : Op (d ^ 1)) := by
  simp only [deFinettiState, symmetricProjector_one_eq_one,
    Matrix.trace_one, Fintype.card_fin]
  push_cast
  ring_nf

/-- Operator-level maximally-entangled ricochet (left action): acting on the
maximally entangled operator by `A ⊗ 1` equals acting by `1 ⊗ Aᵀ`. -/
lemma maxEntangledOp_tensor_one_ricochet {m : ℕ} (A : Op m) :
    Op.tensor A (1 : Op m) * maxEntangledOp m =
      Op.tensor (1 : Op m) A.transpose * maxEntangledOp m := by
  rw [maxEntangledOp_eq_ketbra, op_mul_ketbra, op_mul_ketbra,
    Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet]

/-- Operator-level maximally-entangled ricochet (right action): right-multiplying
the maximally entangled operator by `A ⊗ 1` equals right-multiplying by `1 ⊗ Aᵀ`. -/
lemma maxEntangledOp_mul_tensor_one_ricochet {m : ℕ} (A : Op m) :
    maxEntangledOp m * Op.tensor A (1 : Op m) =
      maxEntangledOp m * Op.tensor (1 : Op m) A.transpose := by
  have h := congrArg Matrix.conjTranspose
    (maxEntangledOp_tensor_one_ricochet (m := m) Aᴴ)
  simp only [Matrix.conjTranspose_mul, Op.tensor_conjTranspose, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose] at h
  rw [(maxEntangledOp_isHermitian m).eq,
    show (Aᴴ.transpose)ᴴ = A.transpose by
      ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]] at h
  exact h

/-- The square-root/vectorization purification's untouched **first-factor**
marginal is the matrix transpose of the purified state.  (For a real-symmetric
state this is the state itself, i.e. the purification is swap-symmetric.) -/
lemma purificationOp_partialTraceA {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) :
    partialTraceA (purificationOp ρ) = (ρ.toOp)ᵀ := by
  have hHerm : (sqrtOp ρ)ᴴ = sqrtOp ρ := sqrtOp_isHermitian ρ
  simp only [purificationOp]
  rw [Op.tensor_conjTranspose, conjTranspose_one, hHerm]
  rw [mul_assoc, maxEntangledOp_mul_tensor_one_ricochet, ← mul_assoc,
    maxEntangledOp_tensor_one_ricochet,
    Quantum.TensorProducts.partialTraceA_one_tensor_sandwich,
    maxEntangledOp_partialTraceA, mul_one,
    ← Matrix.transpose_mul, sqrtOp_sq]

/-- **Purification-expectation bridge (general, unconditional in `M`, `P`).** -/
theorem purificationDensityOp_tensor_sandwich_trace_bridge {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (rho : DensityOp (d ^ n)) (M P : Op (d ^ n)) :
    ((M ⊗ (1 : Op (d ^ n))) * (((1 : Op (d ^ n)) ⊗ P) * (purificationDensityOp rho).toOp *
        ((1 : Op (d ^ n)) ⊗ P))).trace
      = (sqrtOp rho * M * sqrtOp rho * (P * P).transpose).trace := by
  rw [show (purificationDensityOp rho).toOp = purificationOp rho from rfl]
  simp only [purificationOp]
  rw [Op.tensor_conjTranspose, conjTranspose_one, sqrtOp_conjTranspose]
  simp only [← mul_assoc, Op.tensor_mul, mul_one, one_mul]
  rw [mul_assoc, Matrix.trace_mul_comm]
  simp only [← mul_assoc, Op.tensor_mul, mul_one, one_mul]
  rw [Matrix.trace_mul_comm, trace_maxEntangled_mul_tensor]

/-- **Projector specialization** (`P * P = P`). -/
theorem purificationDensityOp_tensor_sandwich_trace_bridge_proj {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (rho : DensityOp (d ^ n)) (M P : Op (d ^ n)) (hP : P * P = P) :
    ((M ⊗ (1 : Op (d ^ n))) * (((1 : Op (d ^ n)) ⊗ P) * (purificationDensityOp rho).toOp *
        ((1 : Op (d ^ n)) ⊗ P))).trace
      = (sqrtOp rho * M * sqrtOp rho * P.transpose).trace := by
  rw [purificationDensityOp_tensor_sandwich_trace_bridge, hP]

/-- A density operator has positive rank: its eigenvalues are nonnegative and sum to its
trace `= 1 ≠ 0`, so at least one is nonzero, hence `rank = #{nonzero eigenvalues} ≥ 1`. -/
lemma densityOp_rank_pos {m : ℕ} [NeZero m] (ρ : DensityOp m) :
    0 < Matrix.rank ρ.toOp := by
  classical
  have hH : ρ.toOp.IsHermitian := ρ.isHermitian
  have hPSD : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- the eigenvalues sum to the trace `= 1`
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h_eq : (1 : ℂ) = ∑ k, (hH.eigenvalues k : ℂ) := by
      have h := hH.trace_eq_sum_eigenvalues; rw [ρ.trace_one] at h; exact h
    have h_re : (∑ k, (hH.eigenvalues k : ℂ)).re = ∑ k, hH.eigenvalues k := by
      simp only [Complex.re_sum, Complex.ofReal_re]
    calc ∑ i, hH.eigenvalues i = (∑ k, (hH.eigenvalues k : ℂ)).re := h_re.symm
      _ = (1 : ℂ).re := by rw [← h_eq]
      _ = 1 := rfl
  -- so some eigenvalue is nonzero
  have hex : ∃ i, hH.eigenvalues i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero (fun i _ => hcon i)] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨i₀, hi₀⟩ := hex
  rw [hH.rank_eq_card_non_zero_eigs]
  rw [Fintype.card_pos_iff]
  exact ⟨⟨i₀, hi₀⟩⟩

/-- **Generic rank-dimension purification (Schmidt/Watrous §2.2).**

Any density operator `ρ` of rank `r := Matrix.rank ρ.toOp` admits a pure purification on a
reference register of dimension exactly `r`.  Concretely, a rank-`r` PSD matrix factors as
`ρ.toOp = B * Bᴴ` with `B : Matrix (Fin m) (Fin r) ℂ` (the scaled-eigenvector column matrix
from `Math.SpectralTheory.psd_eq_sum_rank_vecMulVec`); vectorizing `B` through
`finProdFinEquiv` gives a unit ket on `m * r` whose `|ψ⟩⟨ψ|` has `B`-register marginal
`B * Bᴴ = ρ.toOp`.

This purifies onto the register of dimension `= rank`, in contrast to
`purificationDensityOp`/`densityOp_purification_exists` above, which purify onto the
**full** `m`-register. -/
lemma densityOp_purification_exists_at_rank {m : ℕ} [NeZero m]
    (ρ : DensityOp m) [NeZero (Matrix.rank ρ.toOp)] :
    ∃ ψ : DensityOp (m * Matrix.rank ρ.toOp),
      ψ.IsPure ∧
        Quantum.TensorProducts.partialTraceB ψ.toOp = ρ.toOp := by
  classical
  set r := Matrix.rank ρ.toOp with hr_def
  -- rank-`r` PSD factorization `ρ.toOp = ∑ k, vecMulVec (v k) (star (v k))`
  obtain ⟨v, hv⟩ :=
    Math.SpectralTheory.psd_eq_sum_rank_vecMulVec
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)
  -- assemble the columns into `B : m × r`
  set B : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => v k i with hB_def
  -- `B * Bᴴ = ρ.toOp`
  have hBBh : B * B.conjTranspose = ρ.toOp := by
    rw [hv]
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hB_def, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
  -- vectorize `B` into a unit ket on `m * r`
  set ψket := Quantum.Metrics.RectangularPolar.ketOfVecMatrix B with hψ_def
  have hnorm : (ψket.dag * ψket : ℂ) = 1 := by
    rw [Quantum.Metrics.RectangularPolar.dag_mul_eq_trace_vecMatrix_mul,
      Quantum.Metrics.RectangularPolar.ketVecMatrix_ketOfVecMatrix, Matrix.trace_mul_comm, hBBh,
      ρ.trace_one]
  refine ⟨DensityOp.fromPure ψket hnorm, DensityOp.fromPure_isPure ψket hnorm, ?_⟩
  -- the marginal of the pure purifier is `B * Bᴴ = ρ.toOp`
  have htoOp : (DensityOp.fromPure ψket hnorm).toOp = ψket * ψket.dag := rfl
  rw [htoOp, hψ_def, Quantum.Metrics.RectangularPolar.partialTraceB_ketOfVecMatrix, hBBh]

end InfoTheory.DeFinetti
