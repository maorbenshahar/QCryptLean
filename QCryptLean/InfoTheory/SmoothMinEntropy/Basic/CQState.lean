import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.Quantum.Metrics.BlockDiagonalTensorMaxMixed
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.Quantum.Metrics.FidelityPartialTraceMonotone
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Classical-Quantum States — joint embeddings, purified distance, uniform outputs

A classical-quantum (CQ) state on a classical register X and quantum system A
is a state of the form ρ_{XA} = Σ_x |x⟩⟨x| ⊗ ρ_A(x).

Representation: an explicit function X → SubDensityOp A whose sub-operator
weights sum to ≤ 1 (the normalized case has equality).

This file follows Tomamichel 2016, §2.4.4.

## Main definitions
- `CQState`: classical-quantum state as explicit function family with weight bound
- `CQState.classicalMarginal`: classical marginal distribution
- `CQState.partialTransposeQ`: partial transpose on the quantum register
- `CQState.partialTraceB`: blockwise partial trace over a right tensor factor
- `CQState.quantumMarginal`: quantum marginal (partial trace over X)
- `uniformCQState`: uniform classical distribution tensored with quantum state

## Main statements
- `CQState.classicalMarginal_sum_le_one`: classical weights sum to ≤ 1
- `CQState.classicalMarginal_le_one`: each classical marginal weight is ≤ 1
- `CQState.partialTraceB_stateMap_toOp_eq_of_partialTraceB_eq`: equality of
  CQ partial traces gives blockwise operator equality
- `CQState.partialTraceB_eq_of_stateMap_partialTraceB_eq`: blockwise partial-trace
  equality determines the CQ marginal
- `CQState.purifiedDistance_eq_of_fidelityGen_toJointDensity_eq`: equal joint
  generalized fidelities give equal CQ purified distances
- `CQState.fidelityGen_left_isometry_embed_eq`, `CQState.purifiedDistance_left_isometry_embed_eq`:
  blockwise conjugation by a common left isometry preserves generalized fidelity and purified
  distance
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Classical-Quantum States

A CQ state on classical system X and quantum system A has the form
  ρ_{XA} = Σ_{x ∈ X} p(x) |x⟩⟨x| ⊗ ρ_A(x)

We represent this as a function `stateMap : X → SubDensityOp A` where the
trace of `stateMap x` equals the probability weight p(x) of outcome x.
The normalization condition is Σ_x tr(stateMap x) ≤ 1.
-/

/-- A classical-quantum state on classical register X and quantum system A.

    Tomamichel 2016, §2.4.4:
      ρ_{XA} = Σ_{x ∈ X} |x⟩⟨x|_X ⊗ ρ_A(x), with Σ_x tr(ρ_A(x)) ≤ 1.

    The weight of outcome x is tr(stateMap x); normalization requires these
    weights to sum to at most 1. The function stateMap is an explicit field —
    no Classical.choose is used to extract the decomposition. -/
structure CQState (X : Type*) [Fintype X] (n : ℕ) where
  /-- The quantum state conditioned on each classical outcome -/
  stateMap : X → SubDensityOp n
  /-- Total weight (sum of traces) is at most 1 -/
  weight_le_one : ∑ x : X, (stateMap x).trace ≤ 1

/-- The all-zero CQ state, admitted among subnormalized states in Tomamichel 2016, §2.4.4. -/
def zeroCQ {X : Type*} [Fintype X] {n : ℕ} : CQState X n where
  stateMap _ := 0
  weight_le_one := by
    have h0 : (0 : SubDensityOp n).trace = 0 := by
      change ((0 : SubDensityOp n).toOp).trace.re = 0
      rw [show (0 : SubDensityOp n).toOp = 0 from rfl]; simp
    simp [h0]

/-- Classical marginal: the probability weight of each outcome x. -/
def CQState.classicalMarginal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : X → ℝ :=
  fun x => (ρ.stateMap x).trace

/-- Classical weights are nonneg. -/
lemma CQState.classicalMarginal_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) : 0 ≤ ρ.classicalMarginal x :=
  (ρ.stateMap x).trace_nonneg

/-- Classical weights sum to at most 1. -/
lemma CQState.classicalMarginal_sum_le_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) :
    ∑ x : X, ρ.classicalMarginal x ≤ 1 :=
  ρ.weight_le_one

/-- Every classical marginal weight of a CQ state is at most one. -/
lemma CQState.classicalMarginal_le_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) :
    ρ.classicalMarginal x ≤ 1 := by
  exact le_trans
    (Finset.single_le_sum (fun y _ => ρ.classicalMarginal_nonneg y) (Finset.mem_univ x))
    ρ.classicalMarginal_sum_le_one

/-!
## Partial transpose

Tomamichel's conditional max-entropy duality uses partial transpose on the
quantum register of a CQ state.
-/

/-- The partial transpose of a CQ state `ρ_{CA}` on the quantum register A.

For `ρ_{CA}` a CQ state with blocks `ρ_c : SubDensityOp n`, the partial
transpose on A is the CQ state with blocks `(ρ_c)ᵀ`.

This operation appears in the definition of conditional max-entropy:
`H_max(C|A)_ρ = -H_min(C|Ā)_{ρ̄}` where `ρ̄ = CQState.partialTransposeQ ρ`.

Tomamichel (2016), Definition 6.4 (eq. 6.13). -/
def CQState.partialTransposeQ {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : CQState X n where
  stateMap x := (ρ.stateMap x).transpose
  weight_le_one := by
    simp_rw [SubDensityOp.trace_transpose]
    exact ρ.weight_le_one

/-- Blockwise partial trace over the right tensor factor of the quantum register. -/
def CQState.partialTraceB {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρ : CQState X (dE * dR)) : CQState X dE where
  stateMap x := (ρ.stateMap x).partialTraceB
  weight_le_one := by
    simpa using ρ.weight_le_one

@[simp]
lemma CQState.partialTraceB_stateMap_toOp {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρ : CQState X (dE * dR)) (x : X) :
    (ρ.partialTraceB.stateMap x).toOp =
      Quantum.TensorProducts.partialTraceB (ρ.stateMap x).toOp :=
  rfl

@[simp]
lemma CQState.partialTraceB_stateMap_trace {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρ : CQState X (dE * dR)) (x : X) :
    (ρ.partialTraceB.stateMap x).trace = (ρ.stateMap x).trace := by
  exact SubDensityOp.trace_partialTraceB (ρ.stateMap x)

@[simp]
lemma CQState.partialTraceB_weight {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρ : CQState X (dE * dR)) :
    ∑ x : X, (ρ.partialTraceB.stateMap x).trace =
      ∑ x : X, (ρ.stateMap x).trace := by
  simp

/-- A family of extensions of the blocks of a CQ state has total weight at most one. -/
lemma CQState.sum_trace_le_one_of_partialTraceB_stateMap_eq
    {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρERMap : X → SubDensityOp (dE * dR)) (ρE : CQState X dE)
    (hpartial : ∀ x : X, (ρERMap x).partialTraceB = ρE.stateMap x) :
    ∑ x : X, (ρERMap x).trace ≤ 1 := by
  simpa only [← hpartial, SubDensityOp.trace_partialTraceB] using ρE.weight_le_one

/-- A CQ state is the blockwise partial trace of an extension when all block
operators agree after partial trace. -/
theorem CQState.partialTraceB_eq_of_stateMap_toOp
    {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      Quantum.TensorProducts.partialTraceB (ρER.stateMap x).toOp =
        (ρE.stateMap x).toOp) :
    ρER.partialTraceB = ρE := by
  cases ρE with
  | mk ρEMap ρEWeight =>
    dsimp [CQState.partialTraceB] at hblocks ⊢
    have hmap : (fun x : X => (ρER.stateMap x).partialTraceB) = ρEMap := by
      funext x
      apply SubDensityOp.ext
      exact hblocks x
    subst ρEMap
    congr

/-- Equality of CQ partial traces gives equality of the block marginal
operators. -/
lemma CQState.partialTraceB_stateMap_toOp_eq_of_partialTraceB_eq
    {X : Type*} [Fintype X] {dE dR : ℕ}
    {ρER : CQState X (dE * dR)} {ρE : CQState X dE}
    (hpartial : ρER.partialTraceB = ρE) (x : X) :
    Quantum.TensorProducts.partialTraceB (ρER.stateMap x).toOp =
      (ρE.stateMap x).toOp := by
  have hblock :
      ((ρER.partialTraceB).stateMap x).toOp =
        (ρE.stateMap x).toOp :=
    congrArg (fun ρ : CQState X dE => (ρ.stateMap x).toOp) hpartial
  simpa [CQState.partialTraceB_stateMap_toOp] using hblock

/-- A CQ state whose blocks have prescribed partial traces has that CQ marginal. -/
lemma CQState.partialTraceB_eq_of_stateMap_partialTraceB_eq
    {X : Type*} [Fintype X] {dE dR : ℕ}
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X, (ρER.stateMap x).partialTraceB = ρE.stateMap x) :
    ρER.partialTraceB = ρE := by
  apply CQState.partialTraceB_eq_of_stateMap_toOp ρER ρE
  intro x
  exact congrArg (fun ρ : SubDensityOp dE => ρ.toOp) (hblocks x)

/-- Quantum marginal operator: sum of quantum states. -/
def CQState.quantumMarginalOp {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : Op n :=
  ∑ x : X, (ρ.stateMap x).toOp

/-- The quantum marginal is Hermitian. -/
lemma CQState.quantumMarginalOp_isHermitian {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : (ρ.quantumMarginalOp).IsHermitian := by
  unfold CQState.quantumMarginalOp Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact (ρ.stateMap x).isHermitian

/-- The quantum marginal is positive semidefinite. -/
lemma CQState.quantumMarginalOp_pos_semidef {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm ρ.quantumMarginalOp v).re := by
  intro v
  unfold CQState.quantumMarginalOp quadraticForm
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro x _
  exact (ρ.stateMap x).pos_semidef v

/-- The quantum marginal has trace at most 1. -/
lemma CQState.quantumMarginalOp_trace_le_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : (ρ.quantumMarginalOp).trace.re ≤ 1 := by
  unfold CQState.quantumMarginalOp
  rw [Matrix.trace_sum, Complex.re_sum]
  exact ρ.weight_le_one

/-- The quantum marginal of a CQ state is a sub-normalized operator. -/
def CQState.quantumMarginal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : SubDensityOp n where
  toOp := ρ.quantumMarginalOp
  isHermitian := ρ.quantumMarginalOp_isHermitian
  pos_semidef := ρ.quantumMarginalOp_pos_semidef
  trace_le_one := ρ.quantumMarginalOp_trace_le_one

/-!
## Joint Density Operator

The block-diagonal embedding of a CQ state as a density operator on the joint
classical-quantum system. The classical register X contributes one block per
outcome x, each block equal to stateMap x.

Internal tensor layout: quantum-first (ℂ^n ⊗ ℂ^X, index Fin n × X), NOT the standard
ℂ^X ⊗ ℂ^n convention. The layout is self-consistent: every purified-distance
comparison in this file applies the same reindexing to both sides.
-/

/-- The block-diagonal joint operator of a CQ state, as a raw matrix on
    Fin n × X (before reindexing to a SubDensityOp).

    Tomamichel 2016, §2.4.4: the (a, x) – (b, x') entry equals
    (stateMap x).toOp a b when x = x', and 0 otherwise.

    Uses Mathlib's `Matrix.blockDiagonal`, which maps X → Matrix (Fin n) (Fin n) ℂ
    to Matrix (Fin n × X) (Fin n × X) ℂ. -/
noncomputable def CQState.toJointOp {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : Matrix (Fin n × X) (Fin n × X) ℂ :=
  Matrix.blockDiagonal (fun x => (ρ.stateMap x).toOp)

/-- The joint operator is Hermitian. -/
lemma CQState.toJointOp_isHermitian {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : ρ.toJointOp.IsHermitian := by
  unfold CQState.toJointOp Matrix.IsHermitian
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext x
  exact (ρ.stateMap x).isHermitian

/-- The joint operator is positive semidefinite. -/
lemma CQState.toJointOp_posSemidef {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : ρ.toJointOp.PosSemidef := by
  unfold CQState.toJointOp
  apply Matrix.posSemidef_blockDiagonal
  intro x
  exact Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp

/-- The joint operator has trace at most 1. -/
lemma CQState.toJointOp_trace_le_one {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : ρ.toJointOp.trace.re ≤ 1 := by
  unfold CQState.toJointOp
  rw [Matrix.trace_blockDiagonal]
  simp only [Complex.re_sum]
  exact ρ.weight_le_one

/-- The real part of the joint-operator trace equals the sum of per-outcome
    sub-density traces. -/
lemma CQState.toJointOp_trace_re_eq_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    ρ.toJointOp.trace.re = ∑ x : X, (ρ.stateMap x).trace := by
  unfold CQState.toJointOp
  rw [Matrix.trace_blockDiagonal]
  simp only [Complex.re_sum]
  rfl

/-- **Blockwise quantum reindex of a CQ state along `e : Fin n ≃ Fin m`.**

Reindex the quantum register of every classical block by the same equivalence `e`.  The classical
register is untouched.  This is `CQState.reindexQ` with the source and target descriptions of the
conditioning register allowed to differ syntactically (they necessarily have the same
cardinality). -/
def CQState.reindexQHetero {X : Type*} [Fintype X] {n m : ℕ}
    (e : Fin n ≃ Fin m) (ρ : CQState X n) : CQState X m where
  stateMap x := SubDensityOp.reindexHetero e (ρ.stateMap x)
  weight_le_one := by
    simp only [SubDensityOp.reindexHetero_trace]
    exact ρ.weight_le_one

@[simp] lemma CQState.reindexQHetero_stateMap {X : Type*} [Fintype X] {n m : ℕ}
    (e : Fin n ≃ Fin m) (ρ : CQState X n) (x : X) :
    (CQState.reindexQHetero e ρ).stateMap x = SubDensityOp.reindexHetero e (ρ.stateMap x) :=
  rfl

/-- Reindexing the quantum register commutes with taking the quantum marginal. -/
@[simp] lemma CQState.reindexQHetero_quantumMarginal {X : Type*} [Fintype X] {n m : ℕ}
    (e : Fin n ≃ Fin m) (ρ : CQState X n) :
    (CQState.reindexQHetero e ρ).quantumMarginal =
      SubDensityOp.reindexHetero e ρ.quantumMarginal := by
  apply SubDensityOp.ext
  change (∑ x, Matrix.reindex e e (ρ.stateMap x).toOp) =
    Matrix.reindex e e (∑ x, (ρ.stateMap x).toOp)
  exact (map_sum (Matrix.reindexLinearEquiv ℂ ℂ e e) _ _).symm

/-- Equivalence used to reindex the joint operator from Fin n × X to
    Fin (n * Fintype.card X). Relies on Fintype.equivFin X for the X component.

    Index layout: the quantum index comes first (Fin n), then the classical index (X
    identified with Fin (Fintype.card X)). This is a quantum-first tensor layout —
    ℂ^n ⊗ ℂ^X — NOT the standard classical-first ℂ^X ⊗ ℂ^n convention. This choice
    is self-consistent throughout this file: both sides of every purified-distance
    comparison use the same layout, so internal comparisons are valid. -/
noncomputable def cqJointEquiv (X : Type*) [Fintype X] (n : ℕ) :
    Fin n × X ≃ Fin (n * Fintype.card X) :=
  (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans finProdFinEquiv

/-- The joint density operator of a CQ state, as a SubDensityOp of dimension
    n * Fintype.card X.

    Block-diagonal operator on ℂ^n ⊗ ℂ^X (quantum-first tensor layout), with
    block x equal to stateMap(x). The index order is (quantum, classical) — i.e.,
    Fin n × X reindexed to Fin (n * Fintype.card X) via cqJointEquiv. This is
    NOT the standard Σ_x |x⟩⟨x|_X ⊗ ρ_A(x) on ℂ^X ⊗ ℂ^n; however, since the
    same reindexing is applied to both ρ and σ whenever purifiedDistance is computed,
    the distance values are correct. -/
noncomputable def CQState.toJointDensity {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) : SubDensityOp (n * Fintype.card X) where
  toOp := Matrix.reindex (cqJointEquiv X n) (cqJointEquiv X n) ρ.toJointOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_reindex]
    congr 1
    exact ρ.toJointOp_isHermitian
  pos_semidef := by
    have hpsd := ρ.toJointOp_posSemidef.reindex (cqJointEquiv X n)
    intro v
    have hc := hpsd.dotProduct_mulVec_nonneg v
    exact (Complex.nonneg_iff.mp hc).1
  trace_le_one := by
    rw [Matrix.trace_reindex_self]
    exact ρ.toJointOp_trace_le_one

/-- The joint-density matrix does not depend on which decidable equality
instance is used for the classical register. -/
lemma CQState.toJointDensity_toOp_decEq_irrel {X : Type*} [Fintype X] {n : ℕ}
    (d₁ d₂ : DecidableEq X) (ρ : CQState X n) :
    (@CQState.toJointDensity X _ d₁ n ρ).toOp =
      (@CQState.toJointDensity X _ d₂ n ρ).toOp := by
  have h : d₁ = d₂ := Subsingleton.elim d₁ d₂
  cases h
  rfl

/-- Public restatement of the joint-density operator as a `reindex` of a
    `blockDiagonal`, with the equivalence written out inline so that downstream
    callers can match it syntactically against
    `Quantum.Metrics.traceNorm_blockDiagonal`. -/
lemma CQState.toJointDensity_toOp_eq_reindex_blockDiagonal
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    ρ.toJointDensity.toOp =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal (fun x => (ρ.stateMap x).toOp)) :=
  rfl

/-- The joint-density embedding is injective on `stateMap`: equality of the joint
    `SubDensityOp`s forces equality of the per-outcome sub-density operators. -/
lemma CQState.toJointDensity_injective {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    {ρ ρ' : CQState X n} (h : ρ.toJointDensity = ρ'.toJointDensity) :
    ρ.stateMap = ρ'.stateMap := by
  funext x
  apply SubDensityOp.ext
  have h1 : ρ.toJointDensity.toOp = ρ'.toJointDensity.toOp := by rw [h]
  change Matrix.reindex (cqJointEquiv X n) (cqJointEquiv X n) ρ.toJointOp =
      Matrix.reindex (cqJointEquiv X n) (cqJointEquiv X n) ρ'.toJointOp at h1
  have h2 : ρ.toJointOp = ρ'.toJointOp := (Matrix.reindex _ _).injective h1
  have h3 : (fun y => (ρ.stateMap y).toOp) = (fun y => (ρ'.stateMap y).toOp) :=
    Matrix.blockDiagonal_injective h2
  exact congr_fun h3 x

/-- The trace of the joint density operator equals the sum of per-outcome traces. -/
lemma CQState.toJointDensity_trace_eq_sum {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    ρ.toJointDensity.trace = ∑ x : X, (ρ.stateMap x).trace := by
  change (Matrix.reindex (cqJointEquiv X n) (cqJointEquiv X n) ρ.toJointOp).trace.re
      = ∑ x : X, (ρ.stateMap x).trace
  rw [Matrix.trace_reindex_self]
  exact ρ.toJointOp_trace_re_eq_sum

/-- Purified distance between two CQ states, measured on their joint density operators.

    Tomamichel 2016, Def 6.4 (applied to CQ states):
      P(ρ_{XA}, σ_{XA}) := P(toJointDensity ρ, toJointDensity σ)

    This is the correct distance for Def 6.5 smoothing (over the full CQ state,
    not just the quantum marginal). Requires X nonempty and n > 0 so that the
    joint dimension n * Fintype.card X is nonzero. -/
noncomputable def CQState.purifiedDistance {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ σ : CQState X n) : ℝ :=
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  InfoTheory.SmoothMinEntropy.purifiedDistance ρ.toJointDensity σ.toJointDensity

/-- Equal generalized fidelities of joint densities give equal CQ purified distances. -/
lemma CQState.purifiedDistance_eq_of_fidelityGen_toJointDensity_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * Fintype.card X)] [NeZero (m * Fintype.card X)]
    (ρ σ : CQState X n) (τ υ : CQState X m)
    (hfid : fidelityGen ρ.toJointDensity σ.toJointDensity =
      fidelityGen τ.toJointDensity υ.toJointDensity) :
    CQState.purifiedDistance ρ σ = CQState.purifiedDistance τ υ := by
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  rw [hfid]

/-!
## Metric Axioms for CQState.purifiedDistance

These follow from the metric axioms for `purifiedDistance` on `SubDensityOp`
(Tomamichel 2016, §3.4), applied to the joint density operators of CQ states.
-/

/-- Purified distance between a CQ state and itself is zero. -/
theorem CQState.purifiedDistance_self_zero {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ : CQState X n) :
    CQState.purifiedDistance ρ ρ = 0 := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  exact InfoTheory.SmoothMinEntropy.purifiedDistance_self_zero ρ.toJointDensity

/-- The zero CQ state has zero joint density (Tomamichel 2016, §2.4.4). -/
@[simp] lemma zeroCQ_toJointDensity {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} :
    (zeroCQ (X := X) (n := n)).toJointDensity = 0 := by
  apply SubDensityOp.ext
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  change Matrix.reindex _ _ (Matrix.blockDiagonal (fun _ : X => (0 : Op n))) = 0
  ext i j
  simp [Matrix.reindex_apply, Matrix.blockDiagonal]

/-- The distance to zero is the square root of the weight, extending the smoothing-ball
boundary in Tomamichel 2016, Definition 6.4. -/
lemma CQState.purifiedDistance_zeroCQ {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {n : ℕ} [NeZero n] (ρ : CQState X n) :
    CQState.purifiedDistance ρ zeroCQ = Real.sqrt (∑ x, (ρ.stateMap x).trace) := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  rw [zeroCQ_toJointDensity]
  unfold InfoTheory.SmoothMinEntropy.purifiedDistance fidelityGen
  rw [Quantum.Metrics.fidelity_eq_zero_of_right_toOp_eq_zero _ _ rfl]
  have htrace : (0 : SubDensityOp (n * Fintype.card X)).trace = 0 := by
    change (0 : Op (n * Fintype.card X)).trace.re = 0
    simp
  rw [htrace, sub_zero, mul_one, zero_add]
  have hs : 0 ≤ 1 - ρ.toJointDensity.trace :=
    sub_nonneg.mpr ρ.toJointDensity.trace_le_one
  rw [Real.sq_sqrt hs]
  simp only [sub_sub_cancel, CQState.toJointDensity_trace_eq_sum]

/-- Purified distance between CQ states is symmetric. -/
theorem CQState.purifiedDistance_symm {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ σ : CQState X n) :
    CQState.purifiedDistance ρ σ = CQState.purifiedDistance σ ρ := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  exact InfoTheory.SmoothMinEntropy.purifiedDistance_symm ρ.toJointDensity σ.toJointDensity

/-- Triangle inequality for purified distance on CQ states. -/
theorem CQState.purifiedDistance_triangle {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ σ τ : CQState X n) :
    CQState.purifiedDistance ρ τ ≤
    CQState.purifiedDistance ρ σ + CQState.purifiedDistance σ τ := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  exact InfoTheory.SmoothMinEntropy.purifiedDistance_triangle
    ρ.toJointDensity σ.toJointDensity τ.toJointDensity

/-- The PSD-operator structure on the joint density of a CQ state agrees with
the block-diagonal PSD operator built from the per-outcome PSD blocks. -/
lemma CQState.toJointDensity_toPosSemidefOp_eq_cqBlock
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) :
    ρ.toJointDensity.toPosSemidefOp =
      Quantum.Metrics.cqBlockPosSemidefOp
        (fun x => (ρ.stateMap x).toPosSemidefOp) := by
  ext i j
  simp [Quantum.Metrics.cqBlockPosSemidefOp,
    CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]

/-- The real trace of a sub-density operator is preserved by rectangular
isometric conjugation. -/
lemma SubDensityOp.trace_eq_of_toOp_eq_isometry_conj
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : K.conjTranspose * K =
      (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : SubDensityOp dSrc) (ρ_embed : SubDensityOp dTgt)
    (hρ_embed : ρ_embed.toOp = K * ρ.toOp * K.conjTranspose) :
    ρ_embed.trace = ρ.trace := by
  unfold SubDensityOp.trace
  rw [hρ_embed]
  apply congrArg Complex.re
  calc
    (K * ρ.toOp * K.conjTranspose).trace
        = ((K * ρ.toOp) * K.conjTranspose).trace := by
            simp only [Matrix.mul_assoc]
    _ = (K.conjTranspose * (K * ρ.toOp)).trace := by
            rw [Matrix.trace_mul_comm]
    _ = ((K.conjTranspose * K) * ρ.toOp).trace := by
            rw [← Matrix.mul_assoc]
    _ = ((1 : Matrix (Fin dSrc) (Fin dSrc) ℂ) * ρ.toOp).trace := by
            rw [hK_iso]
    _ = ρ.toOp.trace := by rw [Matrix.one_mul]

/-- Generalized fidelity of CQ joint densities is preserved when both CQ states
are embedded blockwise by the same rectangular left-isometry. -/
theorem CQState.fidelityGen_left_isometry_embed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    [NeZero (dSrc * Fintype.card X)] [NeZero (dTgt * Fintype.card X)]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : K.conjTranspose * K =
      (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ σ : CQState X dSrc)
    (ρ_embed σ_embed : CQState X dTgt)
    (hρ_embed : ∀ x : X,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * K.conjTranspose)
    (hσ_embed : ∀ x : X,
      (σ_embed.stateMap x).toOp =
        K * (σ.stateMap x).toOp * K.conjTranspose) :
    fidelityGen ρ_embed.toJointDensity σ_embed.toJointDensity =
      fidelityGen ρ.toJointDensity σ.toJointDensity := by
  have hρjoint := ρ.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hσjoint := σ.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hρejoint := ρ_embed.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hσejoint := σ_embed.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hF :
      Quantum.Metrics.fidelity
          ρ_embed.toJointDensity.toPosSemidefOp
          σ_embed.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.fidelity
          ρ.toJointDensity.toPosSemidefOp
          σ.toJointDensity.toPosSemidefOp := by
    rw [hρjoint, hσjoint, hρejoint, hσejoint,
      Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum,
      Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      ← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]
    exact Quantum.Metrics.fidelity_isometry_conj_of_toOp_eq
      K (ρ.stateMap x).toPosSemidefOp (σ.stateMap x).toPosSemidefOp
      (ρ_embed.stateMap x).toPosSemidefOp (σ_embed.stateMap x).toPosSemidefOp
      hK_iso (by simpa using hρ_embed x) (by simpa using hσ_embed x)
  have hρtrace :
      ρ_embed.toJointDensity.trace = ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      CQState.toJointDensity_trace_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact SubDensityOp.trace_eq_of_toOp_eq_isometry_conj
      K hK_iso (ρ.stateMap x) (ρ_embed.stateMap x) (hρ_embed x)
  have hσtrace :
      σ_embed.toJointDensity.trace = σ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      CQState.toJointDensity_trace_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact SubDensityOp.trace_eq_of_toOp_eq_isometry_conj
      K hK_iso (σ.stateMap x) (σ_embed.stateMap x) (hσ_embed x)
  simp [fidelityGen, hF, hρtrace, hσtrace]

/-- **Blockwise conjugation by the same rectangular left-isometry preserves CQ purified
distance**, because it preserves the generalized fidelity of the joint densities
(`CQState.fidelityGen_left_isometry_embed_eq`). -/
theorem CQState.purifiedDistance_left_isometry_embed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : K.conjTranspose * K =
      (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ σ : CQState X dSrc)
    (ρ_embed σ_embed : CQState X dTgt)
    (hρ_embed : ∀ x : X,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * K.conjTranspose)
    (hσ_embed : ∀ x : X,
      (σ_embed.stateMap x).toOp =
        K * (σ.stateMap x).toOp * K.conjTranspose) :
    CQState.purifiedDistance ρ_embed σ_embed = CQState.purifiedDistance ρ σ := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (dSrc * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dSrc) (NeZero.ne _)⟩
  haveI : NeZero (dTgt * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dTgt) (NeZero.ne _)⟩
  exact CQState.purifiedDistance_eq_of_fidelityGen_toJointDensity_eq _ _ _ _
    (CQState.fidelityGen_left_isometry_embed_eq K hK_iso ρ σ ρ_embed σ_embed hρ_embed hσ_embed)

/-- Blockwise conjugation by the same rectangular left-isometry contracts CQ
purified distance. -/
theorem CQState.purifiedDistance_left_isometry_embed_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : K.conjTranspose * K =
      (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ σ : CQState X dSrc)
    (ρ_embed σ_embed : CQState X dTgt)
    (hρ_embed : ∀ x : X,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * K.conjTranspose)
    (hσ_embed : ∀ x : X,
      (σ_embed.stateMap x).toOp =
        K * (σ.stateMap x).toOp * K.conjTranspose) :
    CQState.purifiedDistance ρ_embed σ_embed ≤
      CQState.purifiedDistance ρ σ :=
  (CQState.purifiedDistance_left_isometry_embed_eq K hK_iso ρ σ ρ_embed σ_embed hρ_embed
    hσ_embed).le

/-- Generalized fidelity of CQ joint densities is monotone under blockwise
partial trace over a right tensor factor.

This is the CQ-specialized fidelity monotonicity input for the purified-distance
contraction below.  Mathematically it follows from Uhlmann monotonicity under
the CPTP partial-trace map, applied blockwise to the CQ joint density. -/
theorem CQState.fidelityGen_le_fidelityGen_partialTraceB
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    [NeZero ((dE * dR) * Fintype.card X)] [NeZero (dE * Fintype.card X)]
    (ρ σ : CQState X (dE * dR)) :
    fidelityGen ρ.toJointDensity σ.toJointDensity ≤
      fidelityGen ρ.partialTraceB.toJointDensity σ.partialTraceB.toJointDensity := by
  haveI : NeZero (dE * dR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  let A : X → PosSemidefOp (dE * dR) := fun x => (ρ.stateMap x).toPosSemidefOp
  let B : X → PosSemidefOp (dE * dR) := fun x => (σ.stateMap x).toPosSemidefOp
  let Atr : X → PosSemidefOp dE := fun x => (ρ.partialTraceB.stateMap x).toPosSemidefOp
  let Btr : X → PosSemidefOp dE := fun x => (σ.partialTraceB.stateMap x).toPosSemidefOp
  have hρjoint := ρ.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hσjoint := σ.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hρptr := ρ.partialTraceB.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hσptr := σ.partialTraceB.toJointDensity_toPosSemidefOp_eq_cqBlock
  have hF :
      Quantum.Metrics.fidelity
          ρ.toJointDensity.toPosSemidefOp
          σ.toJointDensity.toPosSemidefOp ≤
        Quantum.Metrics.fidelity
          ρ.partialTraceB.toJointDensity.toPosSemidefOp
          σ.partialTraceB.toJointDensity.toPosSemidefOp := by
    rw [hρjoint, hσjoint, hρptr, hσptr,
      Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum,
      Quantum.Metrics.traceNorm_sqrtProduct_cqBlock_eq_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct,
      ← Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct]
    simpa [A, B, Atr, Btr, CQState.partialTraceB] using
      Quantum.Metrics.fidelity_le_fidelity_partialTraceB (A x) (B x)
  have hρtrace :
      ρ.toJointDensity.trace = ρ.partialTraceB.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    simp
  have hσtrace :
      σ.toJointDensity.trace = σ.partialTraceB.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    simp
  unfold fidelityGen
  have hcorr :
      Real.sqrt ((1 - ρ.toJointDensity.trace) * (1 - σ.toJointDensity.trace)) =
        Real.sqrt ((1 - ρ.partialTraceB.toJointDensity.trace) *
          (1 - σ.partialTraceB.toJointDensity.trace)) := by
    rw [hρtrace, hσtrace]
  exact add_le_add hF (le_of_eq hcorr)

/-- Blockwise partial trace over a right tensor factor contracts CQ purified distance.

This is the CQ-state specialization of monotonicity of purified distance under
the CPTP map `partialTraceB`.  It is the metric input needed to lift the
unsmoothed extension data-processing inequality to smoothed min-entropy. -/
theorem CQState.purifiedDistance_partialTraceB_contract
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρ σ : CQState X (dE * dR)) :
    CQState.purifiedDistance ρ.partialTraceB σ.partialTraceB ≤
      CQState.purifiedDistance ρ σ := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero ((dE * dR) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR))
      (NeZero.ne _)⟩
  haveI : NeZero (dE * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne _)⟩
  apply purifiedDistance_le_of_fidelityGen_ge
  exact CQState.fidelityGen_le_fidelityGen_partialTraceB ρ σ

/-- Reindexing a block-diagonal matrix commutes with pointwise block subtraction. -/
lemma reindex_blockDiagonal_sub
    {X ι : Type*} [DecidableEq X] {n : ℕ}
    (e : Fin n × X ≃ ι) (A B : X → Op n) :
    Matrix.reindex e e (Matrix.blockDiagonal A) -
        Matrix.reindex e e (Matrix.blockDiagonal B) =
      Matrix.reindex e e (Matrix.blockDiagonal fun x : X => A x - B x) := by
  change (Matrix.blockDiagonal A).submatrix e.symm e.symm -
      (Matrix.blockDiagonal B).submatrix e.symm e.symm =
    (Matrix.blockDiagonal (A - B)).submatrix e.symm e.symm
  rw [Matrix.blockDiagonal_sub]
  rfl

/-- Reindexing a block-diagonal matrix commutes with scalar multiplication of all blocks. -/
lemma reindex_blockDiagonal_smul
    {X ι : Type*} [DecidableEq X] {n : ℕ}
    (e : Fin n × X ≃ ι) (c : ℂ) (A : X → Op n) :
    Matrix.reindex e e (Matrix.blockDiagonal (fun x : X => c • A x)) =
      c • Matrix.reindex e e (Matrix.blockDiagonal A) := by
  change (Matrix.blockDiagonal (c • A)).submatrix e.symm e.symm =
      c • (Matrix.blockDiagonal A).submatrix e.symm e.symm
  rw [Matrix.blockDiagonal_smul]
  rfl

/-- Lift a pointwise PSD order on block families to their reindexed
block-diagonal joint operators. -/
lemma opLe_reindex_blockDiagonal_of_forall
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (A B : X → Op n)
    (hA : ∀ x : X, (A x).IsHermitian)
    (hB : ∀ x : X, (B x).IsHermitian)
    (h : ∀ x : X, opLe (A x) (B x)) :
    let e : Fin n × X ≃ Fin (n * Fintype.card X) :=
      (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans
        finProdFinEquiv
    opLe
      (Matrix.reindex e e (Matrix.blockDiagonal A))
      (Matrix.reindex e e (Matrix.blockDiagonal B)) := by
  intro e
  apply opLe_of_posSemidef_sub
  have hdiff_blocks : ∀ x : X, (B x - A x).PosSemidef := fun x =>
    opLe.posSemidef_sub (hA x) (hB x) (h x)
  have hdiff_bd :
      (Matrix.blockDiagonal (fun x : X => B x - A x)).PosSemidef :=
    Matrix.posSemidef_blockDiagonal hdiff_blocks
  rw [reindex_blockDiagonal_sub e B A]
  exact (Matrix.posSemidef_submatrix_equiv e.symm).mpr hdiff_bd

/-- If every CQ block of `ρ` is dominated by the corresponding block of `σ`,
then the joint block-diagonal density of `ρ` is dominated by that of `σ`. -/
lemma CQState.toJointDensity_opLe_of_forall
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ σ : CQState X n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : X,
      opLe (ρ.stateMap x).toOp ((c : ℂ) • (σ.stateMap x).toOp)) :
    opLe ρ.toJointDensity.toOp ((c : ℂ) • σ.toJointDensity.toOp) := by
  let e : Fin n × X ≃ Fin (n * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans
      finProdFinEquiv
  have hbd :
      opLe
        (Matrix.reindex e e
          (Matrix.blockDiagonal (fun x : X => (ρ.stateMap x).toOp)))
        (Matrix.reindex e e
          (Matrix.blockDiagonal
            (fun x : X => (c : ℂ) • (σ.stateMap x).toOp))) := by
    apply opLe_reindex_blockDiagonal_of_forall
    · intro x
      exact (ρ.stateMap x).isHermitian
    · intro x
      exact SubDensityOp.toOp_smul_isHermitian (σ.stateMap x) hc
    · exact h
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
    CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rw [← reindex_blockDiagonal_smul e (c : ℂ) (fun x : X => (σ.stateMap x).toOp)]
  exact hbd

/-- CQ wrapper for the substate trace-deficit purified-distance bound, stated at
the joint-density order level. -/
theorem CQState.purifiedDistance_le_sqrt_two_mul_epsilon_of_toJointDensity_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ τ : CQState X n)
    (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hτ_le_ρ : opLe τ.toJointDensity.toOp ρ.toJointDensity.toOp)
    (htrace_deficit : 1 - (∑ x : X, (τ.stateMap x).trace) ≤ ε) :
    CQState.purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hρ_joint_trace : ρ.toJointDensity.trace = 1 := by
    rw [CQState.toJointDensity_trace_eq_sum]
    exact hρ_norm
  apply
    SubDensityOp.purifiedDistance_le_sqrt_two_mul_epsilon_of_opLe
      ρ.toJointDensity τ.toJointDensity hρ_joint_trace hε_nonneg hτ_le_ρ
  rw [CQState.toJointDensity_trace_eq_sum]
  exact htrace_deficit

/-- Blockwise form of the trace-deficit purified-distance bound for CQ states. -/
theorem CQState.purifiedDistance_le_sqrt_two_mul_epsilon_of_forall_stateMap_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ τ : CQState X n)
    (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hτ_le_ρ : ∀ x : X, opLe (τ.stateMap x).toOp (ρ.stateMap x).toOp)
    (htrace_deficit : 1 - (∑ x : X, (τ.stateMap x).trace) ≤ ε) :
    CQState.purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  refine
    CQState.purifiedDistance_le_sqrt_two_mul_epsilon_of_toJointDensity_opLe
      ρ τ hρ_norm hε_nonneg ?_ htrace_deficit
  simpa using
    CQState.toJointDensity_opLe_of_forall τ ρ (c := 1) (by norm_num)
      (fun x => by simpa using hτ_le_ρ x)

/-- CQ wrapper for the sub-normalized trace-gap purified-distance bound, stated at
the joint-density order level. -/
theorem CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_toJointDensity_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ τ : CQState X n)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hτ_le_ρ : opLe τ.toJointDensity.toOp ρ.toJointDensity.toOp)
    (htrace_gap :
      (∑ x : X, (ρ.stateMap x).trace) -
          (∑ x : X, (τ.stateMap x).trace) ≤ ε) :
    CQState.purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  apply
    SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_opLe
      ρ.toJointDensity τ.toJointDensity hε_nonneg hτ_le_ρ
  rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
  exact htrace_gap

/-- Blockwise form of the sub-normalized trace-gap purified-distance bound for
CQ states. -/
theorem CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ τ : CQState X n)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε)
    (hτ_le_ρ : ∀ x : X, opLe (τ.stateMap x).toOp (ρ.stateMap x).toOp)
    (htrace_gap :
      (∑ x : X, (ρ.stateMap x).trace) -
          (∑ x : X, (τ.stateMap x).trace) ≤ ε) :
    CQState.purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  refine
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_toJointDensity_opLe
      ρ τ hε_nonneg ?_ htrace_gap
  simpa using
    CQState.toJointDensity_opLe_of_forall τ ρ (c := 1) (by norm_num)
      (fun x => by simpa using hτ_le_ρ x)

/-- A normalized CQ state has classical weights summing to exactly 1. -/
structure NormalizedCQState (X : Type*) [Fintype X] (n : ℕ) extends CQState X n where
  /-- Total weight equals 1 -/
  weight_eq_one : ∑ x : X, (stateMap x).trace = 1

/-- A normalized CQ state is a CQ state. -/
instance {X : Type*} [Fintype X] {n : ℕ} :
    Coe (NormalizedCQState X n) (CQState X n) :=
  ⟨NormalizedCQState.toCQState⟩

/-!
## Uniform Classical State

The uniform distribution on a classical register, to be used in the LHL output state.
-/

/-- The uniform probability weight `1 / |X|` on a finite nonempty register. -/
private def uniformWeight (X : Type*) [Fintype X] [Nonempty X] : ℝ :=
  1 / (Fintype.card X : ℝ)

private lemma uniformWeight_pos (X : Type*) [Fintype X] [Nonempty X] :
    0 < uniformWeight X := by
  unfold uniformWeight
  positivity

private lemma uniformWeight_le_one (X : Type*) [Fintype X] [Nonempty X] :
    uniformWeight X ≤ 1 := by
  unfold uniformWeight
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero

/-- The uniform classical-quantum state: uniform distribution over X, with the
    same quantum state ρ for all outcomes. -/
def uniformCQState {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : SubDensityOp n) : CQState X n where
  stateMap := fun _ =>
    ρ.smul (uniformWeight X)
      (le_of_lt (uniformWeight_pos X))
      (uniformWeight_le_one X)
  weight_le_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        SubDensityOp.smul_trace ρ (uniformWeight X) _ _]
    calc (Fintype.card X : ℝ) * (uniformWeight X * ρ.trace)
        = ρ.trace := by unfold uniformWeight; field_simp
      _ ≤ 1 := ρ.trace_le_one

/-- The joint trace of the uniform CQ state equals the trace of the underlying
    sub-density operator: `Σ_x (1/|X|) ρ = ρ` at the level of traces. -/
lemma uniformCQState_toJointDensity_trace
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ}
    (ρ : SubDensityOp n) :
    (uniformCQState (X := X) ρ : CQState X n).toJointDensity.trace = ρ.trace := by
  rw [CQState.toJointDensity_trace_eq_sum]
  change ∑ _ : X, (ρ.smul (uniformWeight X)
      (le_of_lt (uniformWeight_pos X)) (uniformWeight_le_one X)).trace = ρ.trace
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      SubDensityOp.smul_trace ρ (uniformWeight X) _ _]
  unfold uniformWeight
  field_simp

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
