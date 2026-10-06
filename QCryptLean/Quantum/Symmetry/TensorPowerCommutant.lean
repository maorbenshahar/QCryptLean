import QCryptLean.Quantum.Symmetry.TensorPowerPolarization
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The matrix bicommutant half of Schur–Weyl (tensor-power commutant)

The pure-`R`-side finite-dimensional double-commutant identity

  `Com({A^{⊗n} : A ∈ Op dR}) = span_ℂ{P_R(π) : π ∈ Sₙ}`

as an equality of `Submodule ℂ (Op (dR^n))`. This is Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
Lemma 10's Schur–Weyl
ingredient (App. A L1516–1592, following CKR arXiv:0809.3019 Lemma 3.1), proved by the direct
finite-dimensional double commutant construction: group averaging entirely inside the
`Op`/`Matrix` world.

## Main statements

- `Quantum.Symmetry.commutant` : the commutant of a set of operators, as a `Submodule`.
- `Quantum.Symmetry.permSpan` : `𝒫 := span{P_R(π) : π ∈ Sₙ}`.
- `Quantum.Symmetry.permSpan_bicommutant` : the crux double-commutant `𝒫'' = 𝒫`.
- `Quantum.Symmetry.commutant_matrixTensorPow_eq_permSpan` : the commutant identity,
  `Com({A^{⊗n}}) = 𝒫`, dR-generic (including the linearly-dependent `dR < n` regime),
  `dA`-free, `1⊗`-free, no `dA ≤ dR` hypothesis.
- `Quantum.Symmetry.repCommutant`, `repCommutantFinrank` : the commutant of a unitary
  representation `W : G → UnitaryOp d` and its `ℂ`-dimension, which determines
  the exponent in Nahar et al. Corollaries 3.2/3.3.

## Conventions

For `dR < n` the `P_R(π)` are linearly **dependent**; every statement here is phrased
via `Submodule.span`/membership, never `Basis`/`LinearIndependent`/a dimension count.
The amplification convention is `ampl M := M ⊗ 1` (`kroneckerMap (·*·) M 1`),
`amplVec a (i,k) = a i k`, `blockOf Y k l i j = Y (i,k) (j,l)`; the `1⊗M` swap
breaks `[ampl ρπ, Π] = 0`. Internal amplification objects live on the product index type
`Fin N × Fin N` (Mathlib `kroneckerMap`), never `Fin (N^2)`/`finProdFinEquiv`.
-/

open Matrix Math.RepresentationTheory Quantum.Operators Quantum.TensorProducts
open scoped Matrix BigOperators

noncomputable section

namespace Quantum.Symmetry

/-! ## the commutant of a set, and `permSpan` -/

/-- **The commutant of a set of operators**, as a `Submodule ℂ (Op N)` (mirrors
`repCommutant`/`permCommutant`). -/
def commutant (N : ℕ) (S : Set (Op N)) : Submodule ℂ (Op N) where
  carrier := {M | ∀ Y ∈ S, Y * M = M * Y}
  add_mem' := by
    intro a b ha hb Y hY
    rw [mul_add, add_mul, ha Y hY, hb Y hY]
  zero_mem' := by
    intro Y _
    rw [mul_zero, zero_mul]
  smul_mem' := by
    intro c M hM Y hY
    rw [mul_smul_comm, smul_mul_assoc, hM Y hY]

/-- `𝒫 := span{P_R(π) : π ∈ Sₙ}`, the span of the permutation representation. -/
def permSpan (dR n : ℕ) [NeZero dR] : Submodule ℂ (Op (dR ^ n)) :=
  Submodule.span ℂ (Set.range fun π : Equiv.Perm (Fin n) => permutationRepresentation dR n π)

/-! ## The symmetry invariant that determines the reduced exponent `x` -/

/-- The **commutant** of a family of unitaries `W : G → UnitaryOp d`: the `ℂ`-subspace of operators
    on `ℂᵈ` commuting with every `W g`.

    This is the object that *determines* the reduced de Finetti exponent of Nahar et al. Corollary
    2.2: for a
    unitary representation `W` of a compact group with irreducible multiplicities `{mᵢ}`, Schur's
    lemma identifies the commutant with `⊕ᵢ M_{mᵢ}(ℂ)`, so `dim_ℂ (commutant) = Σᵢ mᵢ²`. -/
def repCommutant {d : ℕ} {G : Type*} (W : G → UnitaryOp d) : Submodule ℂ (Op d) where
  carrier := {M | ∀ g : G, M * (W g).toOp = (W g).toOp * M}
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [add_mul, mul_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp only [zero_mul, mul_zero]
  smul_mem' := by
    intro c M hM g
    simp only [Set.mem_ofPred_eq] at hM ⊢
    rw [smul_mul_assoc, mul_smul_comm, hM g]

/-- The **commutant dimension** `dim_ℂ (repCommutant W)`, a natural number determined entirely by
    the symmetry `W`.

    For a product group `G = G_A × G_B` acting on the round register `AB` by
    `W_{(g_A,g_B)} = W^A_{g_A} ⊗ W^B_{g_B}`, whose factor representations have `k_A` (`k_B`)
    irreducibles of multiplicities `{mᵢᴬ}` (`{mⱼᴮ}`), the irreducibles of `W` are the
    `k_A · k_B` products with multiplicities `mᵢᴬ mⱼᴮ`, so Schur's lemma (Nahar et al. Remark 2)
    gives

      `repCommutantFinrank W = Σ_{i,j} (mᵢᴬ mⱼᴮ)² = Σ_{i,j} (mᵢᴬ)²(mⱼᴮ)²`
      `                     = symReducedExponentProduct mA mB`.

    Requiring this identity is exactly the statement that
    `mA, mB` *are* the irreducible multiplicities of `W`: it pins the reduced exponent `x` to the
    representation-theoretic invariant `dim_ℂ (repCommutant W)`, forbidding a fictitious `x`. -/
def repCommutantFinrank {d : ℕ} {G : Type*} (W : G → UnitaryOp d) : ℕ :=
  Module.finrank ℂ (repCommutant W)

/-- The hypothesis that `repCommutant W` is, as a `ℂ`-vector space, (linearly) isomorphic to the
    block-diagonal matrix algebra `⊕ᵢ M_{mult i}(ℂ)` — the Schur's-lemma normal form for a
    representation `W` whose irreducible multiplicities are `{mult i}` (each isotypic block's
    commutant is a full `mult i × mult i` matrix algebra, Schur's lemma). -/
def IsSchurBlockDiagonalCommutant {d : ℕ} {G : Type*} (W : G → UnitaryOp d)
    {kIrr : ℕ} (mult : Fin kIrr → ℕ) : Prop :=
  Nonempty (repCommutant W ≃ₗ[ℂ] ((i : Fin kIrr) → Matrix (Fin (mult i)) (Fin (mult i)) ℂ))

/-- A commutant presented as a product of full matrix spaces has dimension
`∑ i, (mult i) ^ 2`. -/
theorem repCommutant_finrank_eq_sum_mult_sq
    {d : ℕ} {G : Type*} (W : G → UnitaryOp d)
    {kIrr : ℕ} (mult : Fin kIrr → ℕ)
    (hW : IsSchurBlockDiagonalCommutant W mult) :
    repCommutantFinrank W = ∑ i, (mult i) ^ 2 := by
  obtain ⟨e⟩ := hW
  unfold repCommutantFinrank
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype ℂ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
  ring

/-- **SL-CommSpan:** the commutant of a set equals the commutant of its span. -/
theorem commutant_span (N : ℕ) (S : Set (Op N)) :
    commutant N S = commutant N (↑(Submodule.span ℂ S) : Set (Op N)) := by
  apply le_antisymm
  · intro M hM Y hY
    -- `hY : Y ∈ span ℂ S`; induct.
    induction hY using Submodule.span_induction with
    | mem y hy => exact hM y hy
    | zero => rw [zero_mul, mul_zero]
    | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
    | smul c y _ hy => rw [smul_mul_assoc, mul_smul_comm, hy]
  · intro M hM Y hY
    exact hM Y (Submodule.subset_span hY)

/-- **the easy inclusion `𝒫 ⊆ 𝒫''`.** -/
theorem permSpan_le_bicommutant (dR n : ℕ) [NeZero dR] :
    permSpan dR n ≤ commutant (dR ^ n)
      (↑(Quantum.Symmetry.permCommutant dR n) : Set (Op (dR ^ n))) := by
  rw [permSpan, Submodule.span_le]
  rintro _ ⟨π, rfl⟩ Y hY
  exact (hY π).symm

/-! ## the internal amplification machinery (product-indexed, `Fin N × Fin N`)

These objects are all internal to the proof of `permSpan_bicommutant`; they never appear
in the statement of the final theorems `permSpan_bicommutant`/
`commutant_matrixTensorPow_eq_permSpan`. -/

section Amplification

variable (N : ℕ)

/-- `ampl M := M ⊗ 1` on the product index type `Fin N × Fin N` (Mathlib `kroneckerMap`,
NOT `Op.tensor`/`finProdFinEquiv`). The convention is pinned this way because the
`1 ⊗ M` swap breaks the averaged-projection commutation. -/
def ampl (M : Op N) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.kroneckerMap (· * ·) M (1 : Op N)

/-- The (unnormalized) maximally entangled vector `Ω = Σᵢ |i⟩⊗|i⟩`. -/
def maxEntVec : Fin N × Fin N → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The `(k,l)` block of an amplified operator. -/
def blockOf (Y : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (k l : Fin N) : Op N :=
  fun i j => Y (i, k) (j, l)

@[simp] lemma ampl_apply (M : Op N) (i k j l : Fin N) :
    ampl N M (i, k) (j, l) = M i j * (if k = l then (1 : ℂ) else 0) := by
  simp [ampl, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- `ampl` is multiplicative: `(M ⊗ 1)(M' ⊗ 1) = (MM') ⊗ 1`. -/
lemma ampl_mul (M M' : Op N) : ampl N (M * M') = ampl N M * ampl N M' := by
  rw [ampl, ampl, ampl, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-- `ampl` is unital: `1 ⊗ 1 = 1`. -/
lemma ampl_one : ampl N (1 : Op N) = 1 := by
  rw [ampl, Matrix.one_kronecker_one]

/-- `ampl` is `*`-preserving: `(M ⊗ 1)ᴴ = Mᴴ ⊗ 1`. -/
lemma ampl_conjTranspose (M : Op N) : (ampl N M)ᴴ = ampl N Mᴴ := by
  rw [ampl, ampl, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- **entry formula, left factor.** `(M ⊗ 1) · Y`, evaluated at `((i,k),(j,l))`, is the
`(k,l)`-block of `Y` left-multiplied by `M`. The `Fin N × Fin N`-indexed matrix product
collapses the inner `q`-sum via the Kronecker delta `[k=q]` (`Finset.sum_ite_eq'`). -/
lemma ampl_mul_apply_eq_mul_blockOf (M : Op N)
    (Y : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (i k j l : Fin N) :
    (ampl N M * Y) (i, k) (j, l) = (M * blockOf N Y k l) i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hstep : ∀ p : Fin N, (∑ q : Fin N, ampl N M (i, k) (p, q) * Y (p, q) (j, l))
      = M i p * (blockOf N Y k l) p j := by
    intro p
    have : ∀ q : Fin N, ampl N M (i, k) (p, q) * Y (p, q) (j, l)
        = if k = q then M i p * Y (p, q) (j, l) else 0 := by
      intro q
      rw [ampl_apply]
      split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_ite_eq Finset.univ k (fun q => M i p * Y (p, q) (j, l))]
    simp [blockOf]
  simp_rw [hstep]
  rfl

/-- **entry formula, right factor.** `Y · (M ⊗ 1)`, evaluated at `((i,k),(j,l))`, is the
`(k,l)`-block of `Y` right-multiplied by `M`. -/
lemma mul_ampl_apply_eq_blockOf_mul (M : Op N)
    (Y : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (i k j l : Fin N) :
    (Y * ampl N M) (i, k) (j, l) = (blockOf N Y k l * M) i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hstep : ∀ p : Fin N, (∑ q : Fin N, Y (i, k) (p, q) * ampl N M (p, q) (j, l))
      = (blockOf N Y k l) i p * M p j := by
    intro p
    have : ∀ q : Fin N, Y (i, k) (p, q) * ampl N M (p, q) (j, l)
        = if q = l then Y (i, k) (p, q) * M p j else 0 := by
      intro q
      rw [ampl_apply]
      split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_ite_eq' Finset.univ l (fun q => Y (i, k) (p, q) * M p j)]
    simp [blockOf]
  simp_rw [hstep]
  rfl

/-- **the block-commutant transfer lemma.** If `Y` (on the amplified space) commutes
with every `ampl N ρπ`, and `T` lies in the bicommutant of the permutation representation,
then `ampl N T` commutes with `Y`. The double-commutant hypothesis on `T` is used only via
`step 1`: every block of `Y` lies in `permCommutant dR n`. -/
lemma amplT_commute_of_bicommutant (dR n : ℕ) [NeZero dR]
    (T : Op (dR ^ n)) (hT : T ∈ commutant (dR ^ n)
      (↑(Quantum.Symmetry.permCommutant dR n) : Set (Op (dR ^ n))))
    (Y : Matrix (Fin (dR ^ n) × Fin (dR ^ n)) (Fin (dR ^ n) × Fin (dR ^ n)) ℂ)
    (hY : ∀ π : Equiv.Perm (Fin n),
      ampl (dR ^ n) (permutationRepresentation dR n π) * Y
        = Y * ampl (dR ^ n) (permutationRepresentation dR n π)) :
    ampl (dR ^ n) T * Y = Y * ampl (dR ^ n) T := by
  -- Step 1: each block of `Y` lies in `permCommutant dR n`.
  have hblock : ∀ k l : Fin (dR ^ n), blockOf (dR ^ n) Y k l ∈
      Quantum.Symmetry.permCommutant dR n := by
    intro k l π
    ext i j
    have hπ := congrFun (congrFun (hY π) (i, k)) (j, l)
    rwa [ampl_mul_apply_eq_mul_blockOf, mul_ampl_apply_eq_blockOf_mul] at hπ
  -- Step 2: transfer via `hT`.
  ext ⟨i, k⟩ ⟨j, l⟩
  have h2 := hT (blockOf (dR ^ n) Y k l) (hblock k l)
  have hleft : (ampl (dR ^ n) T * Y) (i, k) (j, l) = (T * blockOf (dR ^ n) Y k l) i j :=
    ampl_mul_apply_eq_mul_blockOf (dR ^ n) T Y i k j l
  have hright : (Y * ampl (dR ^ n) T) (i, k) (j, l) = (blockOf (dR ^ n) Y k l * T) i j :=
    mul_ampl_apply_eq_blockOf_mul (dR ^ n) T Y i k j l
  rw [hleft, hright, h2]

/-! ### the maximally entangled vector: `ampl` acts by `𝒫`-multiplication -/

/-- **`amplVec`, bundled as a linear map** (must be bundled
for `Submodule.map_span` in `permSpan_bicommutant`). `amplVecL N a` is the "flatten" of `a`:
`amplVecL N a (i,k)
= a i k`, definitionally the entry-formula of `(ampl N a).mulVec (maxEntVec N)`
(`amplVecL_eq_ampl_mulVec_maxEntVec` below). -/
def amplVecL (N : ℕ) : Op N →ₗ[ℂ] (Fin N × Fin N → ℂ) where
  toFun a p := a p.1 p.2
  map_add' a b := by ext p; simp [Matrix.add_apply]
  map_smul' c a := by ext p; simp [Matrix.smul_apply]

/-- `amplVec` — unbundled convenience form. -/
abbrev amplVec (N : ℕ) (a : Op N) : Fin N × Fin N → ℂ := amplVecL N a

@[simp] lemma amplVec_apply (N : ℕ) (a : Op N) (i k : Fin N) : amplVec N a (i, k) = a i k := rfl

/-- `amplVec` really is the flatten of `ampl N a` against the maximally entangled vector. -/
lemma amplVecL_eq_ampl_mulVec_maxEntVec (N : ℕ) (a : Op N) :
    amplVec N a = (ampl N a).mulVec (maxEntVec N) := by
  ext ⟨i, k⟩
  rw [amplVec_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hentry : ∀ j l : Fin N, ampl N a (i, k) (j, l) * maxEntVec N (j, l)
      = if k = l then (a i j * (if j = l then (1 : ℂ) else 0)) else 0 := by
    intro j l
    rw [ampl_apply]
    simp only [maxEntVec]
    split_ifs <;> ring
  simp_rw [hentry]
  have hinner : ∀ j : Fin N,
      (∑ l : Fin N, if k = l then (a i j * (if j = l then (1 : ℂ) else 0)) else 0)
        = a i j * (if j = k then (1 : ℂ) else 0) := by
    intro j
    rw [Finset.sum_ite_eq Finset.univ k (fun l => a i j * (if j = l then (1 : ℂ) else 0))]
    simp
  simp_rw [hinner]
  have houter : ∀ j : Fin N, a i j * (if j = k then (1 : ℂ) else 0)
      = if j = k then a i j else 0 := by
    intro j; split_ifs <;> ring
  simp_rw [houter]
  rw [Finset.sum_ite_eq' Finset.univ k (fun j => a i j)]
  simp

/-- **`amplVec` is injective** (immediate from `amplVec_apply` + `Matrix.ext`). -/
lemma amplVec_injective (N : ℕ) : Function.Injective (amplVec N) := by
  intro a b hab
  ext i j
  have := congrFun hab (i, j)
  rwa [amplVec_apply, amplVec_apply] at this

/-- **`Ω = amplVec 1`.** -/
lemma amplVec_one (N : ℕ) : amplVec N (1 : Op N) = maxEntVec N := by
  ext ⟨i, k⟩
  rw [amplVec_apply, Matrix.one_apply]
  simp [maxEntVec]

/-- **`ampl M · Ω_a = Ω_{Ma}`.** The key `ampl`-`amplVec` intertwining identity. -/
lemma ampl_mulVec_amplVec (N : ℕ) (M a : Op N) :
    (ampl N M).mulVec (amplVec N a) = amplVec N (M * a) := by
  ext ⟨i, k⟩
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, amplVec_apply, Matrix.mul_apply]
  have hstep : ∀ j : Fin N, (∑ l : Fin N, ampl N M (i, k) (j, l) * amplVec N a (j, l))
      = M i j * a j k := by
    intro j
    have : ∀ l : Fin N, ampl N M (i, k) (j, l) * amplVec N a (j, l)
        = if k = l then M i j * a j l else 0 := by
      intro l
      rw [ampl_apply, amplVec_apply]
      split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_ite_eq Finset.univ k (fun l => M i j * a j l)]
    simp
  simp_rw [hstep]

/-- The orbit subspace `W_vec := span{amplVec (ρπ) : π ∈ Sₙ} = (𝒫 ⊗ 1) · Ω`. -/
def Wvec (dR n : ℕ) [NeZero dR] : Submodule ℂ (Fin (dR ^ n) × Fin (dR ^ n) → ℂ) :=
  Submodule.span ℂ
    (Set.range fun π : Equiv.Perm (Fin n) => amplVec (dR ^ n) (permutationRepresentation dR n π))

/-- **`W_vec` is `𝒫`-invariant.** -/
lemma Wvec_invariant (dR n : ℕ) [NeZero dR] (τ : Equiv.Perm (Fin n))
    (v : Fin (dR ^ n) × Fin (dR ^ n) → ℂ) (hv : v ∈ Wvec dR n) :
    (ampl (dR ^ n) (permutationRepresentation dR n τ)).mulVec v ∈ Wvec dR n := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨π, rfl⟩ := hw
    rw [ampl_mulVec_amplVec, permutationRepresentation_mul]
    exact Submodule.subset_span ⟨τ * π, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

/-! ### a projection matrix onto a subspace (Mathlib glue) -/

/-- **`projMat N W`**: the matrix of the projection onto `W` along a (`Classical.choice`d,
harmless) complement. -/
noncomputable def projMat (N : ℕ) (W : Submodule ℂ (Fin N × Fin N → ℂ)) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  LinearMap.toMatrix' (Submodule.projection W _ W.exists_isCompl.choose_spec)

/-- `projMat N W` sends every vector into `W`. -/
lemma projMat_apply_mem (N : ℕ) (W : Submodule ℂ (Fin N × Fin N → ℂ))
    (v : Fin N × Fin N → ℂ) : (projMat N W).mulVec v ∈ W := by
  rw [projMat, LinearMap.toMatrix'_mulVec]
  exact Submodule.projection_apply_mem (W.exists_isCompl.choose_spec) v

/-- `projMat N W` fixes every vector already in `W`. -/
lemma projMat_apply_eq_self (N : ℕ) (W : Submodule ℂ (Fin N × Fin N → ℂ))
    (v : Fin N × Fin N → ℂ) (hv : v ∈ W) : (projMat N W).mulVec v = v := by
  rw [projMat, LinearMap.toMatrix'_mulVec]
  exact (Submodule.projection_eq_self_iff (W.exists_isCompl.choose_spec) v).mpr hv

/-! ### the group-averaged projection lies in the amplified commutant -/

/-- `ampl` composed with `permutationRepresentation` is multiplicative. -/
private lemma amplPermRep_mul (dR n : ℕ) [NeZero dR] (τ π : Equiv.Perm (Fin n)) :
    ampl (dR ^ n) (permutationRepresentation dR n τ) *
        ampl (dR ^ n) (permutationRepresentation dR n π)
      = ampl (dR ^ n) (permutationRepresentation dR n (τ * π)) := by
  rw [← ampl_mul, permutationRepresentation_mul]

/-- `ampl` composed with `permutationRepresentation` is `*`-preserving: `ᴴ` corresponds to
group inversion. -/
private lemma amplPermRep_conjTranspose (dR n : ℕ) [NeZero dR] (π : Equiv.Perm (Fin n)) :
    (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ
      = ampl (dR ^ n) (permutationRepresentation dR n π⁻¹) := by
  rw [ampl_conjTranspose, ← permutationRepresentation_inv]

/-- The shifted adjoint identity driving the averaging reindex in `amplProj_commute`:
`g(x)ᴴ = g(τx)ᴴ · g(τ)` where `g π := ampl (dR^n) (ρπ)`. -/
private lemma amplPermRep_conjTranspose_shift (dR n : ℕ) [NeZero dR] (τ x : Equiv.Perm (Fin n)) :
    (ampl (dR ^ n) (permutationRepresentation dR n x))ᴴ
      = (ampl (dR ^ n) (permutationRepresentation dR n (τ * x)))ᴴ
          * ampl (dR ^ n) (permutationRepresentation dR n τ) := by
  rw [amplPermRep_conjTranspose, amplPermRep_conjTranspose, amplPermRep_mul]
  congr 2
  group

/-- **The averaged conjugation of any seed `Q` by `ampl ∘ ρ`
commutes with every `ampl ρτ`.** This holds for any seed `Q`, not just
`projMat (Wvec ..)`; the reindex `π ↦ τπ` is `Q`-independent. -/
lemma amplProj_commute (dR n : ℕ) [NeZero dR]
    (Q : Matrix (Fin (dR ^ n) × Fin (dR ^ n)) (Fin (dR ^ n) × Fin (dR ^ n)) ℂ)
    (τ : Equiv.Perm (Fin n)) :
    ampl (dR ^ n) (permutationRepresentation dR n τ) *
        ((1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n),
          ampl (dR ^ n) (permutationRepresentation dR n π) * Q *
            (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ)
      = ((1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n),
            ampl (dR ^ n) (permutationRepresentation dR n π) * Q *
              (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ)
          * ampl (dR ^ n) (permutationRepresentation dR n τ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  have hstep : ∀ π : Equiv.Perm (Fin n),
      ampl (dR ^ n) (permutationRepresentation dR n τ) *
          (ampl (dR ^ n) (permutationRepresentation dR n π) * Q *
            (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ)
        = ampl (dR ^ n) (permutationRepresentation dR n (τ * π)) * Q *
            (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ := by
    intro π
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, amplPermRep_mul]
  simp_rw [hstep]
  refine Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ)
    (fun π => ampl (dR ^ n) (permutationRepresentation dR n (τ * π)) * Q *
                (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ)
    (fun π => ampl (dR ^ n) (permutationRepresentation dR n π) * Q *
                (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ *
                ampl (dR ^ n) (permutationRepresentation dR n τ))
    (fun π => ?_)
  rw [amplPermRep_conjTranspose_shift dR n τ π, ← Matrix.mul_assoc]

/-- **`amplProj dR n`: the group-averaged projection onto `W_vec`.** -/
noncomputable def amplProj (dR n : ℕ) [NeZero dR] :
    Matrix (Fin (dR ^ n) × Fin (dR ^ n)) (Fin (dR ^ n) × Fin (dR ^ n)) ℂ :=
  (1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n),
    ampl (dR ^ n) (permutationRepresentation dR n π) * projMat (dR ^ n) (Wvec dR n) *
      (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ

/-- `amplProj` commutes with every `ampl ρτ` (specialization of `amplProj_commute` at
`Q := projMat (Wvec dR n)`). -/
lemma amplProj_commutes (dR n : ℕ) [NeZero dR] (τ : Equiv.Perm (Fin n)) :
    ampl (dR ^ n) (permutationRepresentation dR n τ) * amplProj dR n
      = amplProj dR n * ampl (dR ^ n) (permutationRepresentation dR n τ) :=
  amplProj_commute dR n (projMat (dR ^ n) (Wvec dR n)) τ

/-- Each individual summand of `amplProj`'s averaged sum fixes every `v ∈ W_vec`. -/
lemma amplProj_term_apply_eq_self (dR n : ℕ) [NeZero dR]
    (v : Fin (dR ^ n) × Fin (dR ^ n) → ℂ) (hv : v ∈ Wvec dR n) (π : Equiv.Perm (Fin n)) :
    (ampl (dR ^ n) (permutationRepresentation dR n π) * projMat (dR ^ n) (Wvec dR n) *
        (ampl (dR ^ n) (permutationRepresentation dR n π))ᴴ).mulVec v = v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, amplPermRep_conjTranspose]
  have hmem : (ampl (dR ^ n) (permutationRepresentation dR n π⁻¹)).mulVec v ∈ Wvec dR n :=
    Wvec_invariant dR n π⁻¹ v hv
  rw [projMat_apply_eq_self _ _ _ hmem, Matrix.mulVec_mulVec, amplPermRep_mul,
    mul_inv_cancel, permutationRepresentation_one, ampl_one, Matrix.one_mulVec]

/-- **`amplProj_fix`: `amplProj` fixes `W_vec`.** -/
lemma amplProj_fix (dR n : ℕ) [NeZero dR]
    (v : Fin (dR ^ n) × Fin (dR ^ n) → ℂ) (hv : v ∈ Wvec dR n) :
    (amplProj dR n).mulVec v = v := by
  rw [amplProj, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp_rw [amplProj_term_apply_eq_self dR n v hv]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    show (1 / (Nat.factorial n : ℂ)) * (Nat.factorial n : ℂ) = 1 from by field_simp]
  exact one_smul ℂ v

/-- **`amplProj_range`: `amplProj` maps into `W_vec`.** -/
lemma amplProj_range (dR n : ℕ) [NeZero dR] (v : Fin (dR ^ n) × Fin (dR ^ n) → ℂ) :
    (amplProj dR n).mulVec v ∈ Wvec dR n := by
  rw [amplProj, Matrix.smul_mulVec, Matrix.sum_mulVec]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun π _ => ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact Wvec_invariant dR n π _ (projMat_apply_mem _ _ _)

end Amplification

/-! ## the crux: `𝒫'' = 𝒫` -/

/-- **`permSpan_bicommutant`: the double-commutant identity `𝒫'' = 𝒫`.**

`⊇` is `permSpan_le_bicommutant`. `⊆`: for `T` in the bicommutant, `ampl T` commutes with
the group-averaged projector `amplProj dR n` onto `W_vec` (`amplProj_commutes`); since
`amplProj` fixes `Ω = amplVec 1 ∈ W_vec` (`amplProj_fix`), pushing `Ω` through the commuting
pair shows `amplVec T = amplProj.mulVec (amplVec T) ∈ W_vec` (`amplProj_range`); and
`W_vec = amplVecL '' 𝒫` (`Submodule.map_span`), so injectivity of `amplVec` recovers
`T ∈ 𝒫`. -/
theorem permSpan_bicommutant (dR n : ℕ) [NeZero dR] [NeZero n] :
    commutant (dR ^ n) (↑(Quantum.Symmetry.permCommutant dR n) : Set (Op (dR ^ n)))
      = permSpan dR n := by
  apply le_antisymm
  · intro T hT
    have hcomm : ampl (dR ^ n) T * amplProj dR n = amplProj dR n * ampl (dR ^ n) T :=
      amplT_commute_of_bicommutant dR n T hT (amplProj dR n) (amplProj_commutes dR n)
    have hΩmem : maxEntVec (dR ^ n) ∈ Wvec dR n := by
      rw [← amplVec_one, ← permutationRepresentation_one dR n]
      exact Submodule.subset_span ⟨1, rfl⟩
    have hfix : (amplProj dR n).mulVec (maxEntVec (dR ^ n)) = maxEntVec (dR ^ n) :=
      amplProj_fix dR n (maxEntVec (dR ^ n)) hΩmem
    have hkey : amplVec (dR ^ n) T = (amplProj dR n).mulVec (amplVec (dR ^ n) T) := by
      calc amplVec (dR ^ n) T
          = (ampl (dR ^ n) T).mulVec (amplVec (dR ^ n) (1 : Op (dR ^ n))) := by
            rw [ampl_mulVec_amplVec, mul_one]
        _ = (ampl (dR ^ n) T).mulVec (maxEntVec (dR ^ n)) := by rw [amplVec_one]
        _ = (ampl (dR ^ n) T).mulVec ((amplProj dR n).mulVec (maxEntVec (dR ^ n))) := by
            rw [hfix]
        _ = (ampl (dR ^ n) T * amplProj dR n).mulVec (maxEntVec (dR ^ n)) := by
            rw [Matrix.mulVec_mulVec]
        _ = (amplProj dR n * ampl (dR ^ n) T).mulVec (maxEntVec (dR ^ n)) := by rw [hcomm]
        _ = (amplProj dR n).mulVec ((ampl (dR ^ n) T).mulVec (maxEntVec (dR ^ n))) := by
            rw [Matrix.mulVec_mulVec]
        _ = (amplProj dR n).mulVec
              ((ampl (dR ^ n) T).mulVec (amplVec (dR ^ n) (1 : Op (dR ^ n)))) := by
            rw [amplVec_one]
        _ = (amplProj dR n).mulVec (amplVec (dR ^ n) T) := by rw [ampl_mulVec_amplVec, mul_one]
    have hmem : amplVec (dR ^ n) T ∈ Wvec dR n := by
      rw [hkey]; exact amplProj_range dR n (amplVec (dR ^ n) T)
    have hWvec_eq : Wvec dR n = Submodule.map (amplVecL (dR ^ n)) (permSpan dR n) := by
      rw [Wvec, permSpan, Submodule.map_span]
      congr 1
      ext w
      constructor
      · rintro ⟨π, rfl⟩
        exact ⟨permutationRepresentation dR n π, ⟨π, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨π, rfl⟩, rfl⟩
        exact ⟨π, rfl⟩
    rw [hWvec_eq] at hmem
    obtain ⟨a, ha, hae⟩ := hmem
    have haT : a = T := amplVec_injective (dR ^ n) hae
    rwa [haT] at ha
  · exact permSpan_le_bicommutant dR n

/-! ## the commutant identity: `Com({A^{⊗n}}) = span{P_R(π)}` -/

/-- **The tensor-power commutant identity.** `Com({A^{⊗n} : A ∈ Op dR}) = span_ℂ{P_R(π) : π ∈ Sₙ}`,
`dA`-free, `1⊗`-free, no `dA ≤ dR` hypothesis, valid for all `dR, n ≥ 1` including the
linearly-dependent `dR < n` regime.

`commutant (range A^{⊗n}) = commutant ↑(span (range A^{⊗n}))` (`commutant_span`)
`= commutant ↑(permCommutant dR n)` (SL-Pol interface `span_tensorPow_eq_permCommutant`)
`= permSpan dR n` (`permSpan_bicommutant`). -/
theorem commutant_matrixTensorPow_eq_permSpan (dR n : ℕ) [NeZero dR] [NeZero n] :
    commutant (dR ^ n) (Set.range fun A : Op dR => Op.tensorPow A n) = permSpan dR n := by
  rw [commutant_span, Quantum.Symmetry.span_tensorPow_eq_permCommutant, permSpan_bicommutant]

end Quantum.Symmetry
