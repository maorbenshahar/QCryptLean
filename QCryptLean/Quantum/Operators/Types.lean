import QCryptLean.Math.SpectralTheory.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.PosDef

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-!
# Quantum Operator Types — Op, HermitianOp, PosSemidefOp, DensityOp, UnitaryOp, Ket, Bra

Core type hierarchy for quantum mechanics on finite-dimensional Hilbert spaces.
Operators are represented as complex matrices `Matrix (Fin n) (Fin n) ℂ`, with
successive refinements encoding Hermiticity, positive semidefiniteness, and unit trace.
Normalized kets/bras and inner-product operations are in `BraKet/Basic.lean`;
rank-one projector identities are in `BraKet/Projector.lean`.

## Main definitions
- `Op n`: alias for `Matrix (Fin n) (Fin n) ℂ`, the space of linear operators
- `HermitianOp n`: Hermitian operator (`A† = A`), with `AddCommGroup`
  and `Module ℝ` instances
- `PosSemidefOp n`: positive semidefinite operator, with `AddCommMonoid`
  and `Module NNReal` instances
- `DensityOp n`: density operator (PSD with `Tr = 1`), with convex combinations and purity
- `UnitaryOp n`: unitary operator (`U†U = UU† = I`), with group-like operations
- `phaseUnitary`: multiply a unitary by a unit complex scalar
- `Ket n` / `Bra n`: ket and bra vectors with basic algebraic instances

## Main statements
- `posSemidef_re_quadraticForm_nonneg`: Mathlib PSD matrices have nonnegative
  QI quadratic forms
- `posSemidefOp_implies_mathlib`: connects `PosSemidefOp` to Mathlib's `Matrix.PosSemidef`
- `neZero_of_densityOp`: a density operator can only exist in nonzero dimension
- `DensityOp.purity_bounds`: `1/n ≤ Tr(ρ²) ≤ 1` for density operators
- `pos_semidef_off_diag_bound`: `|Aᵢⱼ|² ≤ Aᵢᵢ · Aⱼⱼ` for PSD matrices
- `UnitaryOp.preserves_inner`: unitary operators preserve inner products
- `trace_unitary_conj`: unitary conjugation preserves matrix trace
-/

-- ============================================================================
-- Section 1: Basic Operator Type
-- ============================================================================

/-- The space of linear operators on an n-dimensional Hilbert space -/
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Dagger notation for conjugate transpose of operators -/
postfix:max "†" => Matrix.conjTranspose

-- ============================================================================
-- Section 2: Hermitian Operators (Observables)
-- ============================================================================

/-- A Hermitian operator satisfies A† = A -/
structure HermitianOp (n : ℕ) where
  toOp : Op n
  isHermitian : toOp.IsHermitian

@[ext]
theorem HermitianOp.ext {n : ℕ} {A B : HermitianOp n} (h : A.toOp = B.toOp) : A = B := by
  cases A; cases B; congr

instance {n : ℕ} : Coe (HermitianOp n) (Op n) where
  coe := HermitianOp.toOp

/-- Hermitian operators form a real vector space -/
instance {n : ℕ} : Zero (HermitianOp n) where
  zero := ⟨0, by simp [IsHermitian]⟩

instance {n : ℕ} : Add (HermitianOp n) where
  add A B := ⟨A.toOp + B.toOp, by
    unfold IsHermitian
    rw [conjTranspose_add, A.isHermitian, B.isHermitian]⟩

instance {n : ℕ} : Neg (HermitianOp n) where
  neg A := ⟨-A.toOp, by
  unfold IsHermitian
  rw [conjTranspose_neg, A.isHermitian]
  ⟩

instance {n : ℕ} : Sub (HermitianOp n) where
  sub A B := ⟨A.toOp - B.toOp, by
  unfold IsHermitian
  rw [conjTranspose_sub,A.isHermitian,B.isHermitian]
  ⟩

instance {n : ℕ} : SMul ℝ (HermitianOp n) where
  smul r A := ⟨(r : ℂ) • A.toOp, by
  unfold IsHermitian
  rw [conjTranspose_smul,A.isHermitian]
  simp
  ⟩

instance {n : ℕ} : AddCommGroup (HermitianOp n) where
  add_assoc := by intros; ext; apply add_assoc
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  neg_add_cancel := by intros; ext; apply neg_add_cancel
  add_comm := by intros; ext; apply add_comm
  nsmul := nsmulRec
  zsmul := zsmulRec

instance {n : ℕ} : Module ℝ (HermitianOp n) where
  one_smul := by
    intros b; ext i j
    change (1 : ℂ) • b.toOp i j = b.toOp i j
    exact @one_smul ℂ ℂ _ _ (b.toOp i j)
  mul_smul := by
    intros x y b; ext i j
    change ((x * y : ℝ) : ℂ) • b.toOp i j = ((x : ℝ) : ℂ) • ((y : ℝ) : ℂ) • b.toOp i j
    rw [← SemigroupAction.mul_smul]
    congr 1
    exact Complex.ofReal_mul x y
  smul_zero := by
    intros a; ext i j
    change ((a : ℝ) : ℂ) • (0 : ℂ) = 0
    exact smul_zero ((a : ℝ) : ℂ)
  smul_add := by
    intros a b c; ext i j
    change ((a : ℝ) : ℂ) • (b.toOp i j + c.toOp i j) =
      ((a : ℝ) : ℂ) • b.toOp i j + ((a : ℝ) : ℂ) • c.toOp i j
    exact smul_add ((a : ℝ) : ℂ) (b.toOp i j) (c.toOp i j)
  add_smul := by
    intros r s x; ext i j
    change (((r + s) : ℝ) : ℂ) • x.toOp i j =
      ((r : ℝ) : ℂ) • x.toOp i j + ((s : ℝ) : ℂ) • x.toOp i j
    rw [Complex.ofReal_add, add_smul]
  zero_smul := by
    intros x; ext i j
    change ((0 : ℝ) : ℂ) • x.toOp i j = 0
    exact zero_smul ℂ (x.toOp i j)

/-- The identity is Hermitian -/
def HermitianOp.one (n : ℕ) : HermitianOp n :=
  ⟨1, by simp [IsHermitian]⟩

/-- Eigenvalues of Hermitian operators are real.
Note: Mathlib's `IsHermitian.eigenvalues` already returns `ℝ`, so this is trivially true. -/
theorem HermitianOp.eigenvalues_real {n : ℕ} [NeZero n] (A : HermitianOp n) :
    ∀ i : Fin n, (A.isHermitian.eigenvalues i : ℂ).im = 0 := by
  intro i; simp only [Complex.ofReal_im]

-- ============================================================================
-- Section 3: Positive Semidefinite Operators
-- ============================================================================

/-- Quadratic form ⟨x|A|x⟩ -/
def quadraticForm {n : ℕ} (A : Op n) (x : Fin n → ℂ) : ℂ :=
  dotProduct (star x) (A.mulVec x)

/-- Real part of the QI quadratic form of a Mathlib PSD operator is nonnegative. -/
lemma posSemidef_re_quadraticForm_nonneg {n : ℕ} {M : Op n}
    (hM : M.PosSemidef) (v : Fin n → ℂ) :
    0 ≤ (quadraticForm M v).re :=
  (Complex.nonneg_iff.mp
    (by simpa [quadraticForm] using hM.dotProduct_mulVec_nonneg v)).1

/-- A positive semidefinite operator is Hermitian with non-negative quadratic form -/
structure PosSemidefOp (n : ℕ) extends HermitianOp n where
  pos_semidef : ∀ x : Fin n → ℂ, 0 ≤ (quadraticForm toOp x).re

@[ext]
theorem PosSemidefOp.ext {n : ℕ} {A B : PosSemidefOp n} (h : A.toOp = B.toOp) : A = B := by
  cases A; cases B
  simp only [mk.injEq]
  exact HermitianOp.ext h

instance {n : ℕ} : Coe (PosSemidefOp n) (HermitianOp n) where
  coe := PosSemidefOp.toHermitianOp

instance {n : ℕ} : Coe (PosSemidefOp n) (Op n) where
  coe A := A.toOp

/-- Positive semidefinite operators form a convex cone -/
instance {n : ℕ} : Zero (PosSemidefOp n) where
  zero := ⟨0, by
    intro x
    change 0 ≤ (quadraticForm (0 : Op n) x).re
    unfold quadraticForm
    simp [zero_mulVec, dotProduct_zero]⟩

instance {n : ℕ} : Add (PosSemidefOp n) where
  add A B := ⟨A.toHermitianOp + B.toHermitianOp, by
    intro x
    change 0 ≤ (quadraticForm (A.toHermitianOp.toOp + B.toHermitianOp.toOp) x).re
    unfold quadraticForm
    rw [add_mulVec, dotProduct_add, Complex.add_re]
    apply add_nonneg
    · exact A.pos_semidef x
    · exact B.pos_semidef x⟩

instance {n : ℕ} : SMul NNReal (PosSemidefOp n) where
  smul r A := ⟨(r : ℝ) • A.toHermitianOp, by
    intro x
    change 0 ≤ (quadraticForm ((r : ℝ) • A.toHermitianOp.toOp) x).re
    unfold quadraticForm
    rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
    rw [smul_eq_mul]
    apply mul_nonneg
    · exact NNReal.coe_nonneg r
    · exact A.pos_semidef x⟩

instance {n : ℕ} : AddCommMonoid (PosSemidefOp n) where
  add_assoc := by
    intros a b c
    ext i j
    apply add_assoc
  zero_add := by
    intros a
    ext i j
    apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
  nsmul := nsmulRec

instance {n : ℕ} : Module NNReal (PosSemidefOp n) where
  one_smul := by
    intros x
    ext i j
    -- After ext, goal is: (1 • x).toOp i j = x.toOp i j
    -- Scalar multiplication converts NNReal → ℝ then applies to HermitianOp
    change ((1 : ℝ) • x.toHermitianOp).toOp i j = x.toOp i j
    rw [one_smul]
  mul_smul := by
    intros x y b; ext i j
    change (((x * y : NNReal) : ℝ) : ℂ) • b.toHermitianOp.toOp i j =
      ((x : ℝ) : ℂ) • ((y : ℝ) : ℂ) • b.toHermitianOp.toOp i j
    rw [← SemigroupAction.mul_smul]
    congr 1
    simp only [NNReal.coe_mul]
    exact Complex.ofReal_mul (x : ℝ) (y : ℝ)
  smul_zero := by
    intros a; ext i j
    change ((a : ℝ) : ℂ) • (0 : ℂ) = 0
    exact smul_zero ((a : ℝ) : ℂ)
  smul_add := by
    intros a b c; ext i j
    change ((a : ℝ) : ℂ) • (b.toHermitianOp.toOp i j + c.toHermitianOp.toOp i j) =
      ((a : ℝ) : ℂ) • b.toHermitianOp.toOp i j + ((a : ℝ) : ℂ) • c.toHermitianOp.toOp i j
    exact smul_add ((a : ℝ) : ℂ) (b.toHermitianOp.toOp i j) (c.toHermitianOp.toOp i j)
  add_smul := by
    intros r s x; ext i j
    change (((r + s : NNReal) : ℝ) : ℂ) • x.toHermitianOp.toOp i j =
      ((r : ℝ) : ℂ) • x.toHermitianOp.toOp i j + ((s : ℝ) : ℂ) • x.toHermitianOp.toOp i j
    rw [show ((r + s : NNReal) : ℝ) = (r : ℝ) + (s : ℝ) from NNReal.coe_add r s]
    rw [Complex.ofReal_add, add_smul]
  zero_smul := by
    intros x; ext i j
    change ((0 : ℝ) : ℂ) • x.toHermitianOp.toOp i j = 0
    exact zero_smul ℂ (x.toHermitianOp.toOp i j)

/-- The identity is positive semidefinite -/
def PosSemidefOp.one (n : ℕ) : PosSemidefOp n :=
  ⟨HermitianOp.one n, by
    intro x
    unfold quadraticForm HermitianOp.one
    simp only [one_mulVec]
    -- Goal: 0 ≤ (dotProduct (star x) x).re
    -- dotProduct (star x) x = ∑ i, conj(x i) * x i = ∑ i, |x i|²
    unfold dotProduct
    simp only [Pi.star_apply]
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    -- Goal: 0 ≤ (star (x i) * x i).re
    -- star (x i) * x i = |x i|² which is real and non-negative
    have h : (star (x i) * x i).re = (x i).re ^ 2 + (x i).im ^ 2 := by
      simp only [star, Complex.mul_re]
      ring
    rw [h]
    apply add_nonneg <;> apply sq_nonneg⟩

-- Note: For eigenvalues of PSD operators being non-negative, use:
--   (posSemidefOp_implies_mathlib A).eigenvalues_nonneg i

-- ============================================================================
-- Section 4: Density Operators (Quantum States)
-- ============================================================================

/-- A density operator is positive semidefinite with trace 1 -/
structure DensityOp (n : ℕ) extends PosSemidefOp n where
  trace_one : toOp.trace = 1

instance {n : ℕ} : Coe (DensityOp n) (PosSemidefOp n) where
  coe := DensityOp.toPosSemidefOp

instance {n : ℕ} : Coe (DensityOp n) (HermitianOp n) where
  coe ρ := ρ.toHermitianOp

instance {n : ℕ} : Coe (DensityOp n) (Op n) where
  coe ρ := ρ.toOp

/-- DensityOp extensionality -/
@[ext]
theorem DensityOp.ext {n : ℕ} {ρ σ : DensityOp n} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ; cases σ
  simp only [DensityOp.mk.injEq]
  apply PosSemidefOp.ext
  exact h

/-- A density operator can only live on a nonzero finite-dimensional space. -/
lemma neZero_of_densityOp {N : ℕ} (ρ : DensityOp N) : NeZero N := by
  refine ⟨fun hN => ?_⟩
  subst hN
  have hzero : ρ.toOp = 0 := Subsingleton.elim _ _
  have htrace_zero : ρ.toOp.trace = 0 := by
    simp [hzero]
  have htrace_one := ρ.trace_one
  rw [htrace_zero] at htrace_one
  norm_num at htrace_one

/-- For density operators, the quadratic form is non-negative. -/
lemma density_quadraticForm_nonneg {n : ℕ} (ρ : DensityOp n) (v : Fin n → ℂ) :
    0 ≤ (star v ⬝ᵥ (ρ.toOp.mulVec v)).re :=
  ρ.toPosSemidefOp.pos_semidef v

/-- Convex combination of density operators is a density operator -/
def DensityOp.convexComb {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (ρ σ : DensityOp n) : DensityOp n :=
  ⟨⟨⟨p • ρ.toOp + (1 - p) • σ.toOp, by
    -- Hermiticity: (p•ρ + (1-p)•σ)† = p•ρ† + (1-p)•σ† = p•ρ + (1-p)•σ
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul]
    rw [ρ.toPosSemidefOp.toHermitianOp.isHermitian, σ.toPosSemidefOp.toHermitianOp.isHermitian]
    simp only [star, id_eq]⟩, by
    -- Positive semidefinite: ⟨x|(p•ρ + (1-p)•σ)|x⟩ = p⟨x|ρ|x⟩ + (1-p)⟨x|σ|x⟩ ≥ 0
    intro x
    have h_ρ := ρ.toPosSemidefOp.pos_semidef x
    have h_σ := σ.toPosSemidefOp.pos_semidef x
    unfold quadraticForm
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec]
    simp only [dotProduct_add, dotProduct_smul]
    simp only [Complex.add_re, Complex.smul_re]
    -- Both terms non-negative: p•⟨x|ρ|x⟩ ≥ 0 and (1-p)•⟨x|σ|x⟩ ≥ 0, so sum ≥ 0
    apply add_nonneg
    · exact mul_nonneg hp.1 h_ρ
    · exact mul_nonneg (by linarith : 0 ≤ 1 - p) h_σ⟩, by
    -- Trace: Tr(p•ρ + (1-p)•σ) = p•Tr(ρ) + (1-p)•Tr(σ) = p•1 + (1-p)•1 = 1
    simp only [Matrix.trace_add, Matrix.trace_smul]
    rw [ρ.trace_one, σ.trace_one]
    simp⟩

/-- A density operator is pure iff ρ² = ρ -/
def DensityOp.IsPure {n : ℕ} (ρ : DensityOp n) : Prop :=
  ρ.toOp * ρ.toOp = ρ.toOp

/-- The maximally mixed state I/n -/
def DensityOp.maxMixed (n : ℕ) [NeZero n] : DensityOp n :=
  ⟨⟨⟨(1 / n : ℂ) • (1 : Op n), by
    -- Hermiticity: I† = I, so (1/n•I)† = 1/n•I† = 1/n•I
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    norm_cast
    simp⟩, by
    -- Positive semidefinite: ⟨x|(1/n)I|x⟩ = (1/n)⟨x|x⟩ = (1/n)‖x‖² ≥ 0
    intro x
    unfold quadraticForm
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [dotProduct_smul]
    have h_re : ((1 / ↑n : ℂ) • (star x ⬝ᵥ x)).re = (1 / ↑n : ℝ) * (star x ⬝ᵥ x).re := by
      simp
    rw [h_re]
    apply mul_nonneg
    · exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    · -- The real part of ∑ i, star (x i) * (x i) is ∑ i, ‖x i‖² ≥ 0
      simp only [dotProduct, Pi.star_def]
      rw [Complex.re_sum]
      apply Finset.sum_nonneg
      intro i _
      -- (conj z * z).re = |z|^2 ≥ 0
      change 0 ≤ ((starRingEnd ℂ) (x i) * x i).re
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring_nf
      positivity⟩, by
    -- Trace: Tr((1/n)I) = (1/n)Tr(I) = (1/n)•n = 1
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin]
    norm_num⟩

-- ============================================================================
-- Dimension Casting
-- ============================================================================

/-- Cast an operator between equal dimensions -/
def Op.castDim {n m : ℕ} (h : n = m) (A : Op n) : Op m :=
  h ▸ A

/-- Entrywise form of a raw type cast between equal operator dimensions. -/
lemma Op.cast_congrArg_apply {n m : ℕ} (h : n = m) (A : Op n) (i j : Fin m) :
    (cast (congrArg Op h) A) i j =
      A (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h
  rfl

/-- Entrywise form of `Op.castDim`. -/
lemma Op.castDim_apply {n m : ℕ} (h : n = m) (A : Op n) (i j : Fin m) :
    Op.castDim h A i j = A (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

/-- Cast a density operator between equal dimensions -/
def DensityOp.castDim {n m : ℕ} (h : n = m) (ρ : DensityOp n) : DensityOp m :=
  h ▸ ρ

/-- Proof irrelevance for DensityOp.castDim: the result depends only on the
    equality, not on which proof of the equality is used. -/
lemma DensityOp.castDim_proof_irrel {n m : ℕ} (h1 h2 : n = m) (ρ : DensityOp n) :
    DensityOp.castDim h1 ρ = DensityOp.castDim h2 ρ := by
  cases h1; rfl

/-- `DensityOp.castDim` commutes with `.toOp`: the underlying operator is transported along the
dimension equality. -/
lemma densityOp_castDim_toOp {n m : ℕ} (h : n = m) (ρ : DensityOp n) :
    (DensityOp.castDim h ρ).toOp = Op.castDim h ρ.toOp := by
  subst h; rfl

/-- Accessing a `castDim`-ed density operator at index `(i, j)` equals accessing the original
    at `⟨i.val, _⟩, ⟨j.val, _⟩`. Resolves the `eq_rec` cast on dimension. -/
lemma DensityOp.castDim_toOp_apply {n m : ℕ} (h : n = m) (ρ : DensityOp n)
    (i : Fin m) (j : Fin m) :
    (DensityOp.castDim h ρ).toOp i j = ρ.toOp ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := by
  subst h; simp [DensityOp.castDim, Fin.eta]

-- ============================================================================
-- Purity Helper Lemmas
-- ============================================================================

/-- For a Hermitian matrix: A j i = conj (A i j) -/
lemma hermitian_conj {n : ℕ} (A : Op n) (hA : A.IsHermitian) (i j : Fin n) :
    A j i = conj (A i j) := by
  have h := congr_fun₂ hA j i
  simp only [conjTranspose_apply, star] at h
  exact h.symm

/-- For Hermitian A: Tr(A²) = ∑ᵢⱼ |Aᵢⱼ|² -/
lemma trace_sq_hermitian_eq_normSq_sum {n : ℕ} (A : Op n) (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  congr 1; ext i; congr 1; ext j
  rw [hermitian_conj A hA i j, mul_comm, ← Complex.normSq_eq_conj_mul_self]

/-- The real part of Tr(A²) for Hermitian A equals sum of |Aᵢⱼ|² -/
lemma trace_sq_hermitian_re {n : ℕ} (A : Op n) (hA : A.IsHermitian) :
    ((A * A).trace).re = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [trace_sq_hermitian_eq_normSq_sum A hA, Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _; rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _; exact Complex.ofReal_re _

/-- Diagonal elements of Hermitian matrices are real -/
lemma hermitian_diag_real {n : ℕ} (A : Op n) (hA : A.IsHermitian) (i : Fin n) :
    (A i i).im = 0 := by
  have h := hermitian_conj A hA i i
  rw [Complex.ext_iff] at h
  simp only [Complex.conj_re, Complex.conj_im] at h
  linarith [h.2]

/-- Trace equals sum of diagonal real parts for Hermitian matrices -/
lemma hermitian_trace_eq_sum_diag_re {n : ℕ} (A : Op n) (_hA : A.IsHermitian) :
    A.trace.re = ∑ i : Fin n, (A i i).re := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]

/-- For Hermitian matrices, normSq of diagonal = re² -/
lemma hermitian_diag_normSq {n : ℕ} (A : Op n) (hA : A.IsHermitian) (i : Fin n) :
    Complex.normSq (A i i) = (A i i).re ^ 2 := by
  have him := hermitian_diag_real A hA i
  unfold Complex.normSq
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, him, mul_zero, add_zero]
  ring

/-- The trace of a Hermitian operator is self-adjoint. -/
lemma isSelfAdjoint_trace_of_isHermitian {m : ℕ} {A : Op m} (hA : A.IsHermitian) :
    IsSelfAdjoint A.trace := by
  rw [IsSelfAdjoint, ← Matrix.trace_conjTranspose A, hA]

/-- Scalar multiplication by a nonnegative real scalar preserves PSD. -/
lemma posSemidef_smul_of_nonneg_re {d : ℕ} (c : ℂ) (A : Op d)
    (hA : A.PosSemidef) (hc_re : 0 ≤ c.re) (hc_im : c.im = 0) :
    (c • A).PosSemidef := by
  -- `Complex.nonneg_iff` packs the re/im hypotheses into `0 ≤ c`.
  exact hA.smul (Complex.nonneg_iff.mpr ⟨hc_re, hc_im.symm⟩)

-- ============================================================================
-- Connecting to Mathlib's PosSemidef for off-diagonal bound
-- ============================================================================

/-- Quadratic form of Hermitian matrix is real (equals its own conjugate) -/
lemma quadraticForm_hermitian_conj_eq_self {n : ℕ} (A : Op n) (hA : A.IsHermitian)
    (x : Fin n → ℂ) : conj (quadraticForm A x) = quadraticForm A x := by
  unfold quadraticForm
  simp only [dotProduct, mulVec, Pi.star_apply]
  have herm : ∀ i j, conj (A i j) = A j i := fun i j => by
    have := congr_fun₂ hA j i
    simp only [conjTranspose_apply, star] at this
    exact this
  have star_eq_conj : ∀ (z : ℂ), star z = conj z := fun _ => rfl
  simp only [map_sum, map_mul, star_eq_conj, Complex.conj_conj, herm]
  conv_lhs => arg 2; ext i; rw [Finset.mul_sum]
  conv_rhs => arg 2; ext i; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  ring

/-- Connect our PosSemidefOp to Mathlib's Matrix.PosSemidef -/
lemma posSemidefOp_implies_mathlib {n : ℕ} (A : PosSemidefOp n) :
    Matrix.PosSemidef A.toOp := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨A.toHermitianOp.isHermitian, fun x => ?_⟩
  have h := A.pos_semidef x
  have hA := A.toHermitianOp.isHermitian
  have heq : star x ⬝ᵥ (A.toOp *ᵥ x) = quadraticForm A.toOp x := rfl
  have h_real := quadraticForm_hermitian_conj_eq_self A.toOp hA x
  have h_im : (quadraticForm A.toOp x).im = 0 := by
    rw [Complex.ext_iff] at h_real
    simp only [Complex.conj_re, Complex.conj_im] at h_real
    linarith [h_real.2]
  rw [heq, Complex.nonneg_iff]
  exact ⟨h, h_im.symm⟩

/-- Helper for 2-element index function -/
private def twoElems (i j : α) : Fin 2 → α := ![i, j]

/-- The 2×2 submatrix indexed by {i, j} -/
private def submatrix_2x2 {n : ℕ} (A : Op n) (i j : Fin n) : Op 2 :=
  A.submatrix (twoElems i j) (twoElems i j)

/-- For Hermitian: M 1 0 = conj(M 0 1) -/
lemma hermitian_2x2_offdiag (M : Op 2) (hM : M.IsHermitian) :
    M 1 0 = conj (M 0 1) := by
  have h := congr_fun₂ hM 1 0
  simp only [conjTranspose_apply, star] at h
  exact h.symm

/-- Diagonal entries of 2×2 Hermitian are real -/
lemma hermitian_2x2_diag_real (M : Op 2) (hM : M.IsHermitian) :
    (M 0 0).im = 0 ∧ (M 1 1).im = 0 := by
  constructor
  · have h := congr_fun₂ hM 0 0
    simp only [conjTranspose_apply, star] at h
    rw [Complex.ext_iff] at h
    linarith [h.2]
  · have h := congr_fun₂ hM 1 1
    simp only [conjTranspose_apply, star] at h
    rw [Complex.ext_iff] at h
    linarith [h.2]

/-- Product sum factorization: ∑ᵢⱼ f(i)*f(j) = (∑ᵢ f(i))² -/
lemma sum_prod_eq_sq_sum {n : ℕ} (f : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, f i * f j = (∑ i : Fin n, f i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

/-- Diagonal entries of PSD matrices have non-negative real part -/
lemma psd_diag_re_nonneg {n : ℕ} (M : Op n)
    (hM : M.PosSemidef) (i : Fin n) :
    0 ≤ (M i i).re := by
  have h := hM.re_dotProduct_nonneg (Pi.single i 1)
  have h1 : star (Pi.single i 1 : Fin n → ℂ) ⬝ᵥ M *ᵥ Pi.single i 1 = M i i := by
    simp only [dotProduct, Pi.star_apply, mulVec, Pi.single_apply, mul_boole]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, star_one, one_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    · intro j _ hj; simp [hj]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [h1] at h
  exact h

/-- The 2×2 submatrix of a PSD matrix is PSD -/
private lemma submatrix_2x2_posSemidef {n : ℕ} (A : PosSemidefOp n) (i j : Fin n) :
    Matrix.PosSemidef (submatrix_2x2 A.toOp i j) :=
  (posSemidefOp_implies_mathlib A).submatrix (twoElems i j)

/-- Determinant real part formula for 2×2 Hermitian -/
lemma det_hermitian_2x2_re (M : Op 2) (hM : M.IsHermitian) :
    M.det.re = (M 0 0).re * (M 1 1).re - Complex.normSq (M 0 1) := by
  rw [Matrix.det_fin_two, hermitian_2x2_offdiag M hM]
  have h := hermitian_2x2_diag_real M hM
  simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, h.1, h.2,
    mul_zero, sub_zero, mul_neg, sub_neg_eq_add, Complex.normSq_apply]

/-- Key PSD property: |Aᵢⱼ|² ≤ Aᵢᵢ.re * Aⱼⱼ.re -/
lemma pos_semidef_off_diag_bound {n : ℕ} (A : PosSemidefOp n) (i j : Fin n) :
    Complex.normSq (A.toOp i j) ≤ (A.toOp i i).re * (A.toOp j j).re := by
  by_cases hij : i = j
  · subst hij; rw [hermitian_diag_normSq A.toOp A.toHermitianOp.isHermitian i, sq]
  · -- Off-diagonal case: use 2×2 principal minor PSD property
    let M := submatrix_2x2 A.toOp i j
    have hM_psd := submatrix_2x2_posSemidef A i j
    -- det(M) ≥ 0 in ComplexOrder
    have h_det_nonneg : 0 ≤ M.det := hM_psd.det_nonneg
    -- 0 ≤ det means 0 ≤ det.re
    have h_det_re_nonneg : 0 ≤ M.det.re := by
      rw [Complex.nonneg_iff] at h_det_nonneg
      exact h_det_nonneg.1
    -- det.re = (M 0 0).re * (M 1 1).re - |M 0 1|²
    have h_det_re := det_hermitian_2x2_re M hM_psd.isHermitian
    -- Submatrix entries equal original: M 0 0 = A i i, M 0 1 = A i j, M 1 1 = A j j
    have h00 : (M 0 0).re = (A.toOp i i).re := rfl
    have h01 : Complex.normSq (M 0 1) = Complex.normSq (A.toOp i j) := rfl
    have h11 : (M 1 1).re = (A.toOp j j).re := rfl
    rw [h00, h01, h11] at h_det_re
    rw [h_det_re] at h_det_re_nonneg
    linarith

-- ============================================================================
-- Purity Definition and Bounds
-- ============================================================================

/-- Purity Tr(ρ²) -/
def DensityOp.purity {n : ℕ} (ρ : DensityOp n) : ℝ :=
  ((ρ.toOp * ρ.toOp).trace).re

theorem DensityOp.purity_bounds {n : ℕ} [NeZero n] (ρ : DensityOp n) :
    1 / n ≤ ρ.purity ∧ ρ.purity ≤ 1 := by
  constructor
  · -- Lower bound: Tr(ρ²) ≥ 1/n using Cauchy-Schwarz
    unfold purity
    rw [trace_sq_hermitian_re ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian]
    -- Diagonal terms ≤ full sum
    have h_diag_le : ∑ i : Fin n, (ρ.toOp i i).re ^ 2 ≤
                     ∑ i, ∑ j, Complex.normSq (ρ.toOp i j) := by
      apply Finset.sum_le_sum; intro i _
      rw [← hermitian_diag_normSq ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian i]
      apply @Finset.single_le_sum (Fin n) ℝ _ _ (fun j => Complex.normSq (ρ.toOp i j)) Finset.univ
      · intro j _; exact Complex.normSq_nonneg _
      · exact Finset.mem_univ i
    -- Trace equals 1
    have h_tr_re : ∑ i : Fin n, (ρ.toOp i i).re = 1 := by
      rw [← hermitian_trace_eq_sum_diag_re ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian]
      rw [ρ.trace_one]; simp
    -- Cauchy-Schwarz: (∑ aᵢ)² ≤ n * ∑ aᵢ²
    have h_cs : (∑ i : Fin n, (1 : ℝ) * (ρ.toOp i i).re) ^ 2 ≤
                (∑ i : Fin n, (1 : ℝ) ^ 2) * (∑ i : Fin n, (ρ.toOp i i).re ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => 1) (fun i => (ρ.toOp i i).re)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at h_cs
    rw [h_tr_re] at h_cs; simp only [one_pow] at h_cs
    -- Conclude 1/n ≤ Tr(ρ²)
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    have h1 : 1 / (n : ℝ) ≤ ∑ i : Fin n, (ρ.toOp i i).re ^ 2 := by
      calc 1 / n ≤ (n * ∑ i : Fin n, (ρ.toOp i i).re ^ 2) / n := by
             apply div_le_div_of_nonneg_right h_cs (le_of_lt hn)
        _ = ∑ i : Fin n, (ρ.toOp i i).re ^ 2 := by field_simp
    linarith
  · -- Upper bound: Tr(ρ²) ≤ 1 using |ρᵢⱼ|² ≤ ρᵢᵢ*ρⱼⱼ
    unfold purity
    rw [trace_sq_hermitian_re ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian]
    have h_tr_re : ∑ i : Fin n, (ρ.toOp i i).re = 1 := by
      rw [← hermitian_trace_eq_sum_diag_re ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian]
      rw [ρ.trace_one]; simp
    have h_bound : ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (ρ.toOp i j) ≤
                   ∑ i : Fin n, ∑ j : Fin n, (ρ.toOp i i).re * (ρ.toOp j j).re := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact pos_semidef_off_diag_bound ρ.toPosSemidefOp i j
    have h_eq : ∑ i : Fin n, ∑ j : Fin n, (ρ.toOp i i).re * (ρ.toOp j j).re = 1 := by
      rw [sum_prod_eq_sq_sum, h_tr_re]; norm_num
    linarith

-- ============================================================================
-- Section 5: Unitary Operators (Quantum Gates)
-- ============================================================================

/-- A unitary operator satisfies U†U = UU† = I -/
structure UnitaryOp (n : ℕ) where
  toOp : Op n
  unitary_left : toOp.conjTranspose * toOp = 1
  unitary_right : toOp * toOp.conjTranspose = 1

instance {n : ℕ} : Coe (UnitaryOp n) (Op n) where
  coe := UnitaryOp.toOp

/-- The identity is unitary -/
def UnitaryOp.one (n : ℕ) : UnitaryOp n :=
  ⟨1, by simp, by simp⟩

/-- Product of unitaries is unitary -/
def UnitaryOp.mul {n : ℕ} (U V : UnitaryOp n) : UnitaryOp n :=
  ⟨U.toOp * V.toOp, by
    -- Need: (U * V)† * (U * V) = 1
    rw [conjTranspose_mul]
    -- Goal: V† * U† * (U * V) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U.toOp.conjTranspose]
    rw [U.unitary_left, Matrix.one_mul]
    exact V.unitary_left,
   by
    -- Need: (U * V) * (U * V)† = 1
    rw [conjTranspose_mul]
    -- Goal: (U * V) * (V† * U†) = 1
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U.toOp]
    rw [V.unitary_right, Matrix.mul_one]
    exact U.unitary_right⟩

instance {n : ℕ} : Mul (UnitaryOp n) where
  mul := UnitaryOp.mul

/-- Adjoint of a unitary is unitary (and is its inverse) -/
def UnitaryOp.adj {n : ℕ} (U : UnitaryOp n) : UnitaryOp n :=
  ⟨U.toOp.conjTranspose, by
    rw [conjTranspose_conjTranspose]
    exact U.unitary_right,
   by
    rw [conjTranspose_conjTranspose]
    exact U.unitary_left⟩

postfix:max "†" => UnitaryOp.adj

/-- The un-conjugated transpose of a unitary operator is again unitary. -/
def UnitaryOp.transpose {d : ℕ} (W : UnitaryOp d) : UnitaryOp d :=
  ⟨W.toOp.transpose,
    by
      rw [show W.toOp.transpose.conjTranspose = W.toOp.conjTranspose.transpose from rfl,
          ← Matrix.transpose_mul, W.unitary_right, Matrix.transpose_one],
    by
      rw [show W.toOp.transpose.conjTranspose = W.toOp.conjTranspose.transpose from rfl,
          ← Matrix.transpose_mul, W.unitary_left, Matrix.transpose_one]⟩

@[ext]
theorem UnitaryOp.ext {n : ℕ} {U V : UnitaryOp n} (h : U.toOp = V.toOp) : U = V := by
  cases U; cases V
  simp only [mk.injEq]
  exact h

theorem UnitaryOp.adj_mul_self {n : ℕ} (U : UnitaryOp n) : U† * U = UnitaryOp.one n := by
  apply UnitaryOp.ext
  change U.toOp.conjTranspose * U.toOp = 1
  exact U.unitary_left

theorem UnitaryOp.mul_adj_self {n : ℕ} (U : UnitaryOp n) : U * U† = UnitaryOp.one n := by
  apply UnitaryOp.ext
  change U.toOp * U.toOp.conjTranspose = 1
  exact U.unitary_right

/-- A unit-modulus scalar satisfies `star α * α = 1`. -/
lemma star_mul_self_eq_one_of_norm_eq_one (α : ℂ) (hα : ‖α‖ = 1) :
    star α * α = 1 := by
  have hnormSq : Complex.normSq α = 1 := by
    rw [Complex.normSq_eq_norm_sq, hα]
    norm_num
  have hcomplex : ((Complex.normSq α : ℝ) : ℂ) = (1 : ℂ) := by
    norm_num [hnormSq]
  rw [Complex.normSq_eq_conj_mul_self] at hcomplex
  exact hcomplex

/-- Multiplying a unitary by a unit complex phase is unitary. -/
def phaseUnitary {d : ℕ} (α : ℂ) (hα : ‖α‖ = 1) (U : UnitaryOp d) :
    UnitaryOp d :=
  ⟨α • U.toOp, by
    have hstar : star α * α = 1 := star_mul_self_eq_one_of_norm_eq_one α hα
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hstar, one_smul, U.unitary_left],
  by
    have hstar : α * star α = 1 := by
      rw [mul_comm, star_mul_self_eq_one_of_norm_eq_one α hα]
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hstar, one_smul, U.unitary_right]⟩

/-- Unitary preserves inner products -/
theorem UnitaryOp.preserves_inner {n : ℕ} (U : UnitaryOp n) (x y : Fin n → ℂ) :
    dotProduct (star (U.toOp.mulVec x)) (U.toOp.mulVec y) = dotProduct (star x) y := by
  -- ⟨Ux|Uy⟩ = ⟨x|U†U|y⟩ = ⟨x|y⟩
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, U.unitary_left, vecMul_one]

/-- Unitary conjugation preserves Hermiticity -/
def UnitaryOp.conj {n : ℕ} (U : UnitaryOp n) (A : HermitianOp n) : HermitianOp n :=
  ⟨U.toOp * A.toOp * U.toOp.conjTranspose, by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, A.isHermitian]
    rw [Matrix.mul_assoc]⟩

/-- Matrix trace is invariant under conjugation by a matrix `W` with `W† * W = 1`. -/
lemma trace_unitary_conj_of_conjTranspose_mul_self {m : ℕ} (W U : Op m)
    (hW : W† * W = 1) :
    (W * U * W†).trace = U.trace := by
  calc
    (W * U * W†).trace =
        (W† * W * U).trace := by
          rw [Matrix.trace_mul_cycle]
    _ = U.trace := by
          rw [hW, Matrix.one_mul]

/-- Unitary conjugation preserves the matrix trace. -/
lemma trace_unitary_conj {m : ℕ} (W : UnitaryOp m) (U : Op m) :
    (W.toOp * U * W.toOp†).trace = U.trace :=
  trace_unitary_conj_of_conjTranspose_mul_self W.toOp U W.unitary_left

/-- If conjugation by a unitary sends a nonzero-trace operator to a scalar
multiple of itself, then the scalar is `1`, so the unitary commutes with it. -/
lemma unitary_commutes_of_projective_conj_of_trace_ne_zero
    {m : ℕ} (W : UnitaryOp m) (U : Op m)
    (hU_trace : U.trace ≠ 0)
    (hproj : ∃ α : ℂ, W.toOp * U * W.toOp† = α • U) :
    W.toOp * U = U * W.toOp := by
  obtain ⟨α, hα⟩ := hproj
  have hα_eq_one : α = 1 := by
    have htrace_eq : U.trace = α * U.trace := by
      calc
        U.trace = (W.toOp * U * W.toOp†).trace := (trace_unitary_conj W U).symm
        _ = (α • U).trace := by rw [hα]
        _ = α * U.trace := by rw [Matrix.trace_smul]; rfl
    have hfactor : (α - 1) * U.trace = 0 := by
      rw [sub_mul, one_mul, ← htrace_eq, sub_self]
    have hα_sub : α - 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hU_trace
    exact sub_eq_zero.mp hα_sub
  have hconj : W.toOp * U * W.toOp† = U := by
    rw [hα, hα_eq_one, one_smul]
  calc
    W.toOp * U = W.toOp * U * 1 := by
      rw [Matrix.mul_one]
    _ = W.toOp * U * (W.toOp† * W.toOp) := by
      rw [W.unitary_left]
    _ = (W.toOp * U * W.toOp†) * W.toOp := by
      simp only [Matrix.mul_assoc]
    _ = U * W.toOp := by
      rw [hconj]

/-- A unitary conjugation fixes every operator that commutes with the unitary. -/
lemma unitary_conj_eq_of_mul_comm {m : ℕ} (W : UnitaryOp m) (A : Op m)
    (hcomm : W.toOp * A = A * W.toOp) :
    W.toOp * A * W.toOp† = A := by
  calc
    W.toOp * A * W.toOp† = (A * W.toOp) * W.toOp† := by
      rw [hcomm]
    _ = A * (W.toOp * W.toOp†) := by
      rw [Matrix.mul_assoc]
    _ = A := by
      rw [W.unitary_right, Matrix.mul_one]

/-- Unitary evolution of density operator -/
def UnitaryOp.evolve {n : ℕ} (U : UnitaryOp n) (ρ : DensityOp n) : DensityOp n :=
  ⟨⟨⟨U.toOp * ρ.toOp * U.toOp.conjTranspose, by
    -- Hermiticity: same as UnitaryOp.conj
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [ρ.toPosSemidefOp.toHermitianOp.isHermitian]
    rw [Matrix.mul_assoc]⟩, by
    -- Positive semidefinite: ⟨x|UρU†|x⟩ = ⟨U†x|ρ|U†x⟩ ≥ 0
    intro x
    unfold quadraticForm
    -- Decompose (U * ρ * U†).mulVec x = U.mulVec (ρ.mulVec (U†.mulVec x))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    -- Let y = U†x
    set y := U.toOp.conjTranspose.mulVec x with hy_def
    -- Show U.mulVec y = x using UU† = I
    have hx : U.toOp.mulVec y = x := by
      rw [hy_def, Matrix.mulVec_mulVec, U.unitary_right, Matrix.one_mulVec]
    -- Transform using preserves_inner: ⟨Ux|Uy⟩ = ⟨x|y⟩
    have h2 : dotProduct (star x) (U.toOp.mulVec (ρ.toOp.mulVec y)) =
              dotProduct (star y) (ρ.toOp.mulVec y) := by
      rw [← hx]
      exact U.preserves_inner y (ρ.toOp.mulVec y)
    rw [h2]
    exact ρ.toPosSemidefOp.pos_semidef y⟩, by
    -- Trace: Tr(UρU†) = Tr(U†Uρ) = Tr(ρ) = 1
    rw [Matrix.trace_mul_cycle, U.unitary_left, Matrix.one_mul]
    exact ρ.trace_one⟩

-- ============================================================================
-- Section 6: Ket and Bra Types
-- ============================================================================

/-- A ket |ψ⟩ is an element of the Hilbert space -/
structure Ket (n : ℕ) where
  vec : Fin n → ℂ

/-- A bra ⟨ψ| is an element of the dual space -/
structure Bra (n : ℕ) where
  vec : Fin n → ℂ

/-- Addition of kets (vector space structure) -/
instance {n : ℕ} : Add (Ket n) where
  add ψ φ := ⟨ψ.vec + φ.vec⟩

/-- Scalar multiplication of kets (vector space structure) -/
instance {n : ℕ} : SMul ℂ (Ket n) where
  smul c ψ := ⟨c • ψ.vec⟩

/-- Scalar multiplication of bras (vector space structure) -/
instance {n : ℕ} : SMul ℂ (Bra n) where
  smul c φ := ⟨c • φ.vec⟩

/-- Addition of bras (vector space structure) -/
instance {n : ℕ} : Add (Bra n) where
  add ψ φ := ⟨ψ.vec + φ.vec⟩

/-- Negation of bras -/
instance {n : ℕ} : Neg (Bra n) where
  neg φ := ⟨-φ.vec⟩

/-- Subtraction of bras -/
instance {n : ℕ} : Sub (Bra n) where
  sub ψ φ := ⟨ψ.vec - φ.vec⟩

/-- Zero ket -/
instance {n : ℕ} : Zero (Ket n) where
  zero := ⟨0⟩

/-- Zero bra -/
instance {n : ℕ} : Zero (Bra n) where
  zero := ⟨0⟩

/-- Negation of kets -/
instance {n : ℕ} : Neg (Ket n) where
  neg ψ := ⟨-ψ.vec⟩

/-- Subtraction of kets -/
instance {n : ℕ} : Sub (Ket n) where
  sub ψ φ := ⟨ψ.vec - φ.vec⟩

/-- Extensionality for kets: two kets are equal if their components are equal -/
@[ext]
theorem Ket.ext {n : ℕ} {ψ φ : Ket n} (h : ∀ i, ψ.vec i = φ.vec i) : ψ = φ := by
  cases ψ; cases φ; congr; funext i; exact h i

/-- Extensionality for bras: two bras are equal if their components are equal -/
@[ext]
theorem Bra.ext {n : ℕ} {φ ψ : Bra n} (h : ∀ i, φ.vec i = ψ.vec i) : φ = ψ := by
  cases φ; cases ψ; congr; funext i; exact h i

-- ============================================================================
-- Ket Algebra Lemmas (Essential for algebraic proofs)
-- ============================================================================

/-- One times a ket: 1 • |ψ⟩ = |ψ⟩ -/
@[simp]
theorem Ket.one_smul {n : ℕ} (ψ : Ket n) : (1 : ℂ) • ψ = ψ := by
  ext i
  change (1 : ℂ) * ψ.vec i = ψ.vec i
  exact one_mul _

/-- Zero times a ket: 0 • |ψ⟩ = 0 -/
@[simp]
theorem Ket.zero_smul {n : ℕ} (ψ : Ket n) : (0 : ℂ) • ψ = 0 := by
  ext i
  change (0 : ℂ) * ψ.vec i = (0 : Ket n).vec i
  simp only [zero_mul]
  rfl

/-- Ket plus zero: |ψ⟩ + 0 = |ψ⟩ -/
@[simp]
theorem Ket.add_zero' {n : ℕ} (ψ : Ket n) : ψ + 0 = ψ := by
  ext i
  change ψ.vec i + 0 = ψ.vec i
  exact _root_.add_zero (ψ.vec i)

/-- Zero plus ket: 0 + |ψ⟩ = |ψ⟩ -/
@[simp]
theorem Ket.zero_add' {n : ℕ} (ψ : Ket n) : 0 + ψ = ψ := by
  ext i
  change 0 + ψ.vec i = ψ.vec i
  exact _root_.zero_add (ψ.vec i)

/-- Scalar distributes over ket addition: c • (|ψ⟩ + |φ⟩) = c • |ψ⟩ + c • |φ⟩ -/
theorem Ket.smul_add {n : ℕ} (c : ℂ) (ψ φ : Ket n) : c • (ψ + φ) = c • ψ + c • φ := by
  ext i
  change c * (ψ.vec i + φ.vec i) = c * ψ.vec i + c * φ.vec i
  ring

/-- Scalars multiply: (c * d) • |ψ⟩ = c • (d • |ψ⟩) -/
theorem Ket.mul_smul {n : ℕ} (c d : ℂ) (ψ : Ket n) : (c * d) • ψ = c • (d • ψ) := by
  ext i
  change (c * d) * ψ.vec i = c * (d * ψ.vec i)
  ring

/-- Scalars add: (c + d) • |ψ⟩ = c • |ψ⟩ + d • |ψ⟩ -/
theorem Ket.add_smul {n : ℕ} (c d : ℂ) (ψ : Ket n) : (c + d) • ψ = c • ψ + d • ψ := by
  ext i
  change (c + d) * ψ.vec i = c * ψ.vec i + d * ψ.vec i
  ring

/-- Zero ket has zero components -/
@[simp] lemma Ket.zero_vec {n : ℕ} (j : Fin n) : (0 : Ket n).vec j = 0 := rfl

/-- Scalar times zero ket is zero -/
@[simp] lemma Ket.smul_zero {n : ℕ} (c : ℂ) : c • (0 : Ket n) = 0 := by
  ext i
  change c * (0 : Ket n).vec i = (0 : Ket n).vec i
  simp only [Ket.zero_vec, mul_zero]

/-- Scalar multiplication is associative: c • (d • ψ) = (c * d) • ψ -/
@[simp] lemma Ket.smul_smul {n : ℕ} (c d : ℂ) (ψ : Ket n) :
    c • (d • ψ) = (c * d) • ψ := by
  ext i
  change c * (d * ψ.vec i) = (c * d) * ψ.vec i
  ring

/-- Cast a ket between equal dimensions -/
def Ket.cast {n m : ℕ} (h : n = m) (ψ : Ket n) : Ket m :=
  h ▸ ψ

end  -- noncomputable section

end Quantum.Operators

open scoped BigOperators ComplexConjugate

/-- (conj z * z).im = 0 (product with conjugate is real) -/
lemma Complex.im_conj_mul_self (z : ℂ) : (starRingEnd ℂ z * z).im = 0 := by
  simp [mul_comm]
