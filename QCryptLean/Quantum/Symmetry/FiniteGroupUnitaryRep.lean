import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.CastDim
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Unitary representations of finite groups and their paired twirls

A unitary representation of a finite group is a multiplicative family of unitary
operators. The paired twirl — the uniform average of `π₁(g) ⊗ conj(π₂(g))` — is
the orthogonal projection onto the invariant vectors of the paired action; it is
the basic representation-theoretic object behind the group-symmetric de Finetti
reduction of Nahar–Tupkary–Zhao–Lütkenhaus–Tan, arXiv:2403.11851, Lemma
`lem:groupPurification`.
-/

open Matrix Quantum.Operators Quantum.TensorProducts
open scoped BigOperators

noncomputable section

namespace Quantum.Symmetry

/-! ### Unitary representations and the paired twirl projector -/

/-- A unitary representation, given by a multiplicative family of unitary operators. -/
def IsUnitaryRep {G : Type*} [Group G] {d : ℕ} (π : G → Op d) : Prop :=
  (∀ g h : G, π (g * h) = π g * π h) ∧ ∀ g : G, (π g)ᴴ * π g = 1

/-- The scalar-commutant form of irreducibility: every operator in the commutant is scalar. -/
def IsIrreducibleRep {G : Type*} [Group G] {d : ℕ} (π : G → Op d) : Prop :=
  ∀ T : Op d, (∀ g : G, π g * T = T * π g) → ∃ c : ℂ, T = c • (1 : Op d)

/-- Unitary equivalence of representations, with an explicit equality of their dimensions. -/
def IsIrreduciblyEquivalentGen {G : Type*} [Group G] {d d' : ℕ} (π₁ : G → Op d)
    (π₂ : G → Op d') : Prop :=
  ∃ (h : d = d') (W : Op d), (Wᴴ * W = 1 ∧ W * Wᴴ = 1) ∧
    ∀ g : G, π₁ g = W * Op.castDim h.symm (π₂ g) * Wᴴ

/-- Unitary equivalence of two representations on the same space. -/
def IsIrreduciblyEquivalent {G : Type*} [Group G] {d : ℕ} (π₁ π₂ : G → Op d) : Prop :=
  ∃ W : Op d, (Wᴴ * W = 1 ∧ W * Wᴴ = 1) ∧ ∀ g : G, π₁ g = W * π₂ g * Wᴴ

/-- Entrywise complex conjugation of an operator. -/
def entryConj {d : ℕ} (M : Op d) : Op d :=
  Matrix.of fun i j => star (M i j)

/-- The uniform average of `π₁(g) ⊗ conj(π₂(g))`. For unitary representations
this is the orthogonal projection onto the invariant vectors of the paired action. -/
def groupTwirlProjectorPair {G : Type*} [Group G] [Fintype G] {d d' : ℕ} (π₁ : G → Op d)
    (π₂ : G → Op d') : Op (d * d') :=
  ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))

/-- The paired twirl of a representation with itself. Its range corresponds to
the commutant of the representation under vectorization. -/
def groupTwirlProjector {G : Type*} [Group G] [Fintype G] {d : ℕ} (π : G → Op d) :
    Op (d * d) :=
  groupTwirlProjectorPair π π

/-! ### Helper lemmas: `entryConj` and unitary representations -/

/-- `entryConj` preserves multiplication: entrywise conjugation is applied to each entry of a
matrix product, and conjugation on ℂ is a ring homomorphism (`star_sum`, `star_mul'`). -/
lemma entryConj_mul {d : ℕ} (A B : Op d) :
    entryConj (A * B) = entryConj A * entryConj B := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.mul_apply, star_sum, star_mul']

/-- `entryConj` commutes with the conjugate transpose: the two conjugations commute
(entrywise conjugation vs. conjugate-transposition). -/
lemma entryConj_conjTranspose {d : ℕ} (A : Op d) :
    (entryConj A)ᴴ = entryConj Aᴴ := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.conjTranspose_apply, star_star]

/-- `entryConj` fixes the identity matrix. -/
lemma entryConj_one {d : ℕ} : entryConj (1 : Op d) = 1 := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Matrix.one_apply]
  split <;> simp

/-- Entrywise conjugation distributes over the Kronecker product: `conj(A ⊗ B) = conj(A) ⊗
conj(B)` (entries: `star (A i j * B k l) = star (A i j) * star (B k l)`, `star_mul'`). -/
lemma entryConj_opTensor {n m : ℕ} (A : Op n) (B : Op m) :
    entryConj (Op.tensor A B) = Op.tensor (entryConj A) (entryConj B) := by
  ext i j
  simp only [entryConj, Matrix.of_apply, Op_tensor_apply_finProd, star_mul']

/-- Transposing the entrywise conjugate gives the conjugate transpose:
    `(conj M)ᵀ = Mᴴ` (both have entries `conj(M j i)`). -/
lemma entryConj_transpose {d : ℕ} (M : Op d) : (entryConj M).transpose = Mᴴ := by
  ext i j
  simp [entryConj, Matrix.conjTranspose_apply]

/-- A unitary representation sends the group identity to the identity operator: `π 1` is
idempotent (`π (1 · 1) = π 1 · π 1`) and unitary, and a unitary idempotent is `1`. -/
lemma IsUnitaryRep.one {G : Type*} [Group G] {d : ℕ} {π : G → Op d} (hπ : IsUnitaryRep π) :
    π 1 = 1 := by
  have h1 : π 1 * π 1 = π 1 := by rw [← hπ.1 1 1, one_mul]
  have h2 : (π 1)ᴴ * (π 1 * π 1) = 1 := by rw [h1, hπ.2 1]
  have h3 : (π 1)ᴴ * (π 1 * π 1) = π 1 := by rw [← Matrix.mul_assoc, hπ.2 1, one_mul]
  exact h3.symm.trans h2

/-- In a unitary representation, `π g⁻¹ = (π g)ᴴ`: `π g⁻¹` is the two-sided inverse of `π g`
(since `π g · π g⁻¹ = π 1 = 1`), and `(π g)ᴴ` is a left inverse by unitarity. -/
lemma IsUnitaryRep.inv {G : Type*} [Group G] {d : ℕ} {π : G → Op d} (hπ : IsUnitaryRep π)
    (g : G) : π g⁻¹ = (π g)ᴴ := by
  have h1 : (π g)ᴴ * (π g * π g⁻¹) = (π g)ᴴ := by
    rw [← hπ.1 g g⁻¹, mul_inv_cancel, IsUnitaryRep.one hπ, mul_one]
  rw [← Matrix.mul_assoc, hπ.2 g, one_mul] at h1
  exact h1

/-- The paired twirl of two unitary representations is the orthogonal
projection onto the invariant subspace of their paired action. -/
theorem groupTwirlProjectorPair_isOrthogonalProjection {G : Type*} [Group G] [Fintype G]
    {d d' : ℕ} (π₁ : G → Op d) (π₂ : G → Op d') (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂) :
    (groupTwirlProjectorPair π₁ π₂)ᴴ = groupTwirlProjectorPair π₁ π₂ ∧
      groupTwirlProjectorPair π₁ π₂ * groupTwirlProjectorPair π₁ π₂ =
        groupTwirlProjectorPair π₁ π₂ := by
  have hc0 : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Product and adjoint of the twirl summands
  have key_mul : ∀ g h : G, Op.tensor (π₁ g) (entryConj (π₂ g)) *
      Op.tensor (π₁ h) (entryConj (π₂ h)) =
      Op.tensor (π₁ (g * h)) (entryConj (π₂ (g * h))) := by
    intro g h
    rw [Op.tensor_mul, ← hπ₁.1 g h, ← entryConj_mul, ← hπ₂.1 g h]
  have key_inv : ∀ g : G, (Op.tensor (π₁ g) (entryConj (π₂ g)))ᴴ =
      Op.tensor (π₁ g⁻¹) (entryConj (π₂ g⁻¹)) := by
    intro g
    rw [Op.tensor_conjTranspose, entryConj_conjTranspose, IsUnitaryRep.inv hπ₁ g,
      IsUnitaryRep.inv hπ₂ g]
  -- Left-multiplication invariance of the sum (reindex `g ↦ h · g`)
  have key_sum : ∀ h : G, ∑ g : G, (Op.tensor (π₁ h) (entryConj (π₂ h)) *
      Op.tensor (π₁ g) (entryConj (π₂ g))) =
      ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)) := fun h =>
    Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => key_mul h g
  have hSadj : (∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)))ᴴ
      = ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)) := by
    rw [Matrix.conjTranspose_sum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => key_inv g
  -- Right-multiplication invariance of the sum (reindex `g ↦ g · h`)
  have key_sumR : ∀ h : G, ∑ g : G, Op.tensor (π₁ (g * h)) (entryConj (π₂ (g * h)))
      = ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)) := fun h =>
    Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl
  -- The sum squares to `|G| • Σ` (each factor appears `|G|` times)
  have hSS : (∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))) *
      (∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)))
      = ((Fintype.card G : ℕ) : ℂ) • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, key_mul, key_sumR, Finset.sum_const,
      Nat.cast_smul_eq_nsmul ℂ, Finset.card_univ]
  constructor
  · -- Πᴴ = Π: conjugation fixes the positive scalar and reverses the sum to itself
    change (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)))ᴴ
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))
    rw [conjTranspose_smul, hSadj, star_inv₀, star_natCast]
  · -- Π · Π = Π: average the invariance `T h · S = S` over `h`
    change (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))) *
      (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g)))
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))
    rw [smul_mul_assoc, mul_smul_comm, hSS,
      smul_smul (((Fintype.card G : ℕ) : ℂ)⁻¹) (((Fintype.card G : ℕ) : ℂ)⁻¹)
        (((Fintype.card G : ℕ) : ℂ) • ∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))),
      smul_smul (((Fintype.card G : ℕ) : ℂ)⁻¹ * ((Fintype.card G : ℕ) : ℂ)⁻¹)
        ((Fintype.card G : ℕ) : ℂ) (∑ g : G, Op.tensor (π₁ g) (entryConj (π₂ g))),
      mul_assoc, inv_mul_cancel₀ hc0, mul_one]

/-! ### Product representations -/

/-- The tensor-product representation of `G_A × G_B` on Alice and Bob. -/
def prodRep {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB : ℕ} (πA : G_A → Op dA)
    (πB : G_B → Op dB) : G_A × G_B → Op (dA * dB) :=
  fun g => Op.tensor (πA g.1) (πB g.2)

/-- The tensor product of unitary representations is a unitary representation
of the product group. -/
theorem prodRep_isUnitaryRep {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB : ℕ}
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA) (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    IsUnitaryRep (prodRep πA πB) := by
  constructor
  · -- Multiplicativity: (g_A·h_A, g_B·h_B) ↦ (πA g_A · πA h_A) ⊗ (πB g_B · πB h_B)
    intro g h
    change Op.tensor (πA (g.1 * h.1)) (πB (g.2 * h.2)) =
      Op.tensor (πA g.1) (πB g.2) * Op.tensor (πA h.1) (πB h.2)
    rw [hπA.1 g.1 h.1, hπB.1 g.2 h.2, Op.tensor_mul]
  · -- Unitarity: (U ⊗ V)† (U ⊗ V) = (U†U) ⊗ (V†V) = 1
    intro g
    change (Op.tensor (πA g.1) (πB g.2))ᴴ * Op.tensor (πA g.1) (πB g.2) = 1
    rw [Op.tensor_conjTranspose, Op.tensor_mul, hπA.2 g.1, hπB.2 g.2, Op.tensor_one]

/-! ### Traces of the paired twirl projectors -/

/-- **The trace of the pair twirl projector** is the average of the summand traces
(`Matrix.trace_smul`, `Matrix.trace_sum`): `Tr Π₁₂ = (1/|G|) Σ_g Tr(π₁ g) · Tr(conj(π₂ g))`. -/
lemma groupTwirlProjectorPair_trace {G : Type*} [Group G] [Fintype G] {d d' : ℕ}
    (π₁ : G → Op d) (π₂ : G → Op d') :
    (groupTwirlProjectorPair π₁ π₂).trace =
      ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, (π₁ g).trace * (entryConj (π₂ g)).trace := by
  rw [groupTwirlProjectorPair, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  -- `rw` cannot rewrite under the `Finset.sum` binder; `simp only` can (`Op.trace_tensor`).
  simp only [Op.trace_tensor]

/-- **The pair twirl's trace is unchanged when the first representation is unitarily
conjugated**: if `π₁ g = W π₂ g Wᴴ` for all `g` (i.e. `IsIrreduciblyEquivalent π₁ π₂`), then
`Tr Π_{π₁,π₂} = Tr Π_{π₂,π₂}`. Both traces equal the same character-type sum
(`groupTwirlProjectorPair_trace`); the summand traces agree because the trace is cyclic,
`Tr(W A Wᴴ) = Tr(A Wᴴ W) = Tr A` (`Matrix.trace_mul_cycle`, `Wᴴ W = 1`). -/
theorem groupTwirlProjectorPair_trace_equiv {G : Type*} [Group G] [Fintype G] {d : ℕ}
    {π₁ π₂ : G → Op d} (h : IsIrreduciblyEquivalent π₁ π₂) :
    (groupTwirlProjectorPair π₁ π₂).trace = (groupTwirlProjectorPair π₂ π₂).trace := by
  obtain ⟨W, hW, hintw⟩ := h
  -- Cyclic trace: `Tr(W A Wᴴ) = Tr A` for unitary `W`
  have hcycle : ∀ A : Op d, (W * A * Wᴴ).trace = A.trace := by
    intro A
    rw [Matrix.trace_mul_cycle, hW.1, one_mul]
  -- Summand-wise agreement after substituting the intertwining relation
  have hsum : ∀ g : G, (π₁ g).trace * (entryConj (π₂ g)).trace
      = (π₂ g).trace * (entryConj (π₂ g)).trace := by
    intro g
    rw [hintw g, hcycle]
  rw [groupTwirlProjectorPair_trace π₁ π₂, groupTwirlProjectorPair_trace π₂ π₂]
  simp only [hsum]

/-- `entryConj` preserves the trace: `Tr(conj A) = conj(Tr A)` (the trace is a finite sum and
conjugation is additive, `star_sum`). -/
lemma entryConj_trace {d : ℕ} (A : Op d) :
    (entryConj A).trace = star A.trace := by
  simp only [entryConj, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, star_sum]

/-- The trace of a unitary representation's twirl is the average of
`χ(g)χ(g⁻¹)`, where `χ` is its character. -/
lemma groupTwirlProjector_trace_inv {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (π : G → Op d) (hπ : IsUnitaryRep π) :
    (groupTwirlProjector π).trace =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, (π g).trace * (π g⁻¹).trace := by
  rw [groupTwirlProjector, groupTwirlProjectorPair_trace]
  simp only [hπ.inv, Matrix.trace_conjTranspose, entryConj_trace]

/-- The trace of the twirl projector of a unitary representation on `ℂ^d ≠ 0` is nonzero:
`Tr Π_π = (1/|G|) Σ_g |Tr(π g)|² ≥ |Tr(π 1)|²/|G| = d²/|G| > 0` (the `g = 1` summand is `d²`
because `π 1 = 1`). Used to derive `NeZero x` for the de Finetti prefactor `g_{n,x}` of the
group-symmetric corollary. -/
lemma groupTwirlProjector_trace_ne_zero {G : Type*} [Group G] [Fintype G] {d : ℕ} [NeZero d]
    (π : G → Op d) (hπ : IsUnitaryRep π) : (groupTwirlProjector π).trace ≠ 0 := by
  -- each summand is `|Tr(π g)|²`, a nonnegative real number as a complex
  have hterm : ∀ g : G, (π g).trace * (entryConj (π g)).trace
      = ((Complex.normSq (π g).trace : ℝ) : ℂ) := fun g => by
    rw [entryConj_trace, Complex.star_def, Complex.mul_conj]
  -- the sum of squared moduli is a positive real (the `g = 1` summand is `d²`)
  have hRpos : 0 < ∑ g : G, Complex.normSq (π g).trace := by
    refine Finset.sum_pos' (fun g _ => Complex.normSq_nonneg _) ⟨1, Finset.mem_univ _, ?_⟩
    rw [IsUnitaryRep.one hπ, Matrix.trace_one, Fintype.card_fin]
    exact Complex.normSq_pos.mpr (Nat.cast_ne_zero.mpr (NeZero.ne d))
  -- fold the real sum into a single `ofReal`, then the trace is a nonzero multiple of it
  have hsum : ∑ g : G, (π g).trace * (entryConj (π g)).trace
      = ((∑ g : G, Complex.normSq (π g).trace : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun g _ => hterm g
  have hcard : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [groupTwirlProjector, groupTwirlProjectorPair_trace, hsum]
  exact mul_ne_zero (inv_ne_zero hcard)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hRpos))

/-! ### The trivial representation -/

/-- The constant-identity family is a unitary representation of any group (the trivial
representation; used for the `Unit` instances of the group-symmetric theorems). -/
lemma isUnitaryRep_const_one {G : Type*} [Group G] {d : ℕ} :
    IsUnitaryRep (fun _ : G => (1 : Op d)) := by
  constructor
  · intro _ _; simp
  · intro _; simp

/-- The product representation of two trivial representations is the identity operator. -/
lemma prodRep_const_one {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB : ℕ}
    (g : G_A × G_B) :
    prodRep (fun _ : G_A => (1 : Op dA)) (fun _ : G_B => (1 : Op dB)) g = 1 := by
  simp [prodRep]

/-- **The twirl projector of the trivial representation on `Unit`** is the identity operator,
so its trace is `d²` — the `k = 1` instance of the multiplicity identity `hxA` with the
single irreducible of dimension `d` (multiplicity `d`). -/
lemma groupTwirlProjector_unit_const_one_trace {d : ℕ} :
    (groupTwirlProjector (fun _ : Unit => (1 : Op d))).trace = (d : ℂ) ^ 2 := by
  have hsum : ∑ _g : Unit, Op.tensor (1 : Op d) (entryConj (1 : Op d)) = 1 := by
    simp [entryConj_one, Op.tensor_one]
  simp only [groupTwirlProjector, groupTwirlProjectorPair]
  rw [show (((Fintype.card Unit : ℕ) : ℂ)⁻¹) = 1 from by simp, hsum, one_smul,
    Matrix.trace_one]
  rw [Fintype.card_fin, pow_two, ← Nat.cast_mul]

/-! ### Entrywise Schur orthogonality -/

/-- **Entrywise Schur orthogonality** (matrix-coefficient form — the core of the paper's proof of
Lemma `\label{lem:projection}`, main.tex:1200–:1213): for an irreducible unitary representation
`π` of a finite group `G` on `ℂ^d ≠ 0` and indices `j i k l`,

`(1/|G|) Σ_g π(g)_{k j} · conj(π(g)_{l i}) = (if j = i then 1/d else 0) · (if k = l then 1 else 0)`.

*Proof* (commutant form of Schur's lemma): the twirled matrix unit
`T := (1/|G|) Σ_g π(g) · E_{ji} · π(g)ᴴ` (with `E_{ji} = Matrix.single j i 1`) satisfies the
invariance `π(h) · T · π(h)ᴴ = T` for every `h` (reindex `g ↦ h·g` in the sum via
`Equiv.sum_comp (Equiv.mulLeft h)`), hence `π(h) · T = T · π(h)` (multiply by `π h` on the right,
using unitarity); `IsIrreducibleRep` gives `T = c • 1`; tracing (`Matrix.trace_mul_cycle`,
`(π g)ᴴ · π g = 1`) gives `c · d = Tr E_{ji} = δ_{ji} · |G|`, i.e. `c/|G| = δ_{ji}/d`; reading off
the `(k, l)` entry of `T` (`Matrix.sum_apply`, `Matrix.single_apply`) is the displayed identity. -/
theorem schurOrthogonal_entry {G : Type*} [Group G] [Fintype G] {d : ℕ} [NeZero d]
    (π : G → Op d) (hπ : IsUnitaryRep π) (hirr : IsIrreducibleRep π) (j i k l : Fin d) :
    ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, π g k j * star (π g l i)
      = (if j = i then (1 / (d : ℂ)) else 0) * (if k = l then (1 : ℂ) else 0) := by
  have hc0 : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  -- The twirled matrix unit `E_{ji}` and its group average `S`
  set E : Op d := Matrix.single j i (1 : ℂ) with hE
  set S : Op d := ∑ g : G, π g * E * (π g)ᴴ with hS
  -- Invariance `π h · S · (π h)ᴴ = S`: each summand is conjugated into the summand at `h · g`
  have hterm : ∀ h g : G, π h * (π g * E * (π g)ᴴ) * (π h)ᴴ
      = π (h * g) * E * (π (h * g))ᴴ := by
    intro h g
    -- Unfold `π (h · g)`, use that `ᴴ` reverses products, then reassociate
    rw [hπ.1 h g, Matrix.conjTranspose_mul]
    simp only [← mul_assoc]
  have hinv : ∀ h : G, π h * S * (π h)ᴴ = S := by
    intro h
    rw [hS, Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hterm h g]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun y => π y * E * (π y)ᴴ)
  -- Hence `S` commutes with every `π h` (multiply the invariance by `π h` on the right)
  have hcomm : ∀ h : G, π h * S = S * π h := by
    intro h
    have h1 : (π h * S * (π h)ᴴ) * π h = S * π h := by rw [hinv h]
    rw [mul_assoc, hπ.2 h, mul_one] at h1
    exact h1
  -- Schur: `S` is a scalar operator
  obtain ⟨c, hc⟩ := hirr S hcomm
  -- The scalar is `δ_{ji} · |G| / d`: trace `S` two ways
  have htrE : E.trace = (if j = i then (1 : ℂ) else 0) := by
    simp only [hE, Matrix.trace, Matrix.diag_apply, Matrix.single_apply]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [if_neg hij]
      exact Finset.sum_eq_zero fun a _ => by
        have hna : ¬ (j = a ∧ i = a) := fun h => hij (h.1.trans h.2.symm)
        simp [hna]
  have htrS : S.trace = (if j = i then ((Fintype.card G : ℕ) : ℂ) else 0) := by
    rw [hS, Matrix.trace_sum]
    -- Each summand has trace `Tr E` (cyclic trace + unitarity)
    have h1 : ∀ g : G, (π g * E * (π g)ᴴ).trace = E.trace := fun g =>
      by rw [Matrix.trace_mul_cycle, hπ.2 g, one_mul]
    by_cases hij : j = i
    · rw [if_pos hij, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => h1 g, htrE,
        if_pos hij, Finset.sum_const, Finset.card_univ, nsmul_eq_mul', one_mul]
    · rw [if_neg hij, Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => h1 g, htrE,
        if_neg hij]
      exact Finset.sum_const_zero
  have hcval : c * (d : ℂ) = (if j = i then ((Fintype.card G : ℕ) : ℂ) else 0) := by
    rw [← htrS, hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  -- So `c / |G| = δ_{ji} / d`
  have hscale : ((Fintype.card G : ℕ) : ℂ)⁻¹ * c = if j = i then (1 / (d : ℂ)) else 0 := by
    by_cases hij : j = i
    · rw [if_pos hij]
      -- hcval : c · d = |G|; goal: |G|⁻¹ · c = 1/d
      have hc2 : c = ((Fintype.card G : ℕ) : ℂ) / (d : ℂ) := by
        rw [eq_div_iff hd0]
        rw [if_pos hij] at hcval
        exact hcval
      rw [hc2, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, one_div]
    · have hc0' : c = 0 := by
        rw [if_neg hij] at hcval
        exact (mul_eq_zero.1 hcval).resolve_right hd0
      rw [if_neg hij, hc0', mul_zero]
  -- Read off the `(k, l)` entry of `S = c • 1`
  have hentry : ∀ g : G, (π g * E * (π g)ᴴ) k l = π g k j * star (π g l i) := by
    intro g
    rw [hE, Matrix.mul_apply]
    -- Only the `x = i` summand survives: `(π g · E_{ji}) k x = 0` unless `x = i`
    rw [Finset.sum_eq_single i]
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply, mul_one]
    · intro x _ hx
      simp [hx]
    · intro hc
      exact (hc (Finset.mem_univ i)).elim
  have hsum : S k l = ∑ g : G, π g k j * star (π g l i) := by
    rw [hS, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun g _ => hentry g
  by_cases hkl : k = l
  · rw [← hsum, hc, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_pos hkl,
      mul_one, mul_one, hscale]
  · rw [← hsum, hc, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hkl,
      mul_zero, mul_zero, mul_zero]

/-- **Trace of the self-twirl of an irreducible representation** — the `π₁ = π₂` case of the
trace part of Nahar et al. Lemma `\label{lem:projection}` (main.tex:1200–:1213): for an
irreducible unitary representation `π` of a finite group `G` on `ℂ^d ≠ 0`,
`Tr Π_{π,π} = 1`.

*Proof* (matrix-coefficient Schur orthogonality, concrete form): for matrix units
`E_{ji}`, the twirl `T := (1/|G|) Σ_g π(g) E_{ji} π(g)ᴴ` commutes with every `π(h)` (reindex
`g ↦ hg`), so `IsIrreducibleRep` gives `T = c • 1` with `c = Tr T / d` (trace both sides,
using `NeZero d`); reading off entries,
`(1/|G|) Σ_g π(g)_{kj} conj(π(g)_{li}) = (δ_{ij}/d) δ_{kl}`; summing over `k = l, i = j` turns
`Tr Π_{π,π} = (1/|G|) Σ_g (π g).trace * conj((π g).trace)` (via `groupTwirlProjectorPair_trace`
and an `entryConj`-trace lemma) into `1`. -/
theorem groupTwirlProjectorPair_trace_self_irreducible {G : Type*} [Group G] [Fintype G]
    {d : ℕ} [NeZero d] (π : G → Op d) (hπ : IsUnitaryRep π) (hirr : IsIrreducibleRep π) :
    (groupTwirlProjectorPair π π).trace = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  -- Trace of a matrix as the sum of its diagonal entries
  have hexp : ∀ A : Op d, A.trace = ∑ i, A i i := fun A => by
    simp only [Matrix.trace, Matrix.diag_apply]
  -- Each summand trace is the double sum of the products of diagonal entries
  have hterm : ∀ g : G, (π g).trace * (entryConj (π g)).trace
      = ∑ j : Fin d, ∑ l : Fin d, π g j j * star (π g l l) := by
    intro g
    rw [hexp, entryConj_trace, hexp, star_sum]
    simp only [Finset.sum_mul_sum]
  -- Entry-wise Schur orthogonality on the diagonal, specialised to `(j, i, k, l) = (j, l, j, l)`
  have key : ∀ j l : Fin d, ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G,
      π g j j * star (π g l l) = if j = l then (1 / (d : ℂ)) else 0 := by
    intro j l
    rw [schurOrthogonal_entry π hπ hirr j l j l]
    by_cases hjeql : j = l
    · rw [if_pos hjeql, if_pos hjeql, mul_one]
    · rw [if_neg hjeql, if_neg hjeql, mul_zero]
  -- Move the group sum inward (below the two index sums)
  have hreorder : ∑ g : G, ∑ j : Fin d, ∑ l : Fin d, π g j j * star (π g l l)
      = ∑ j : Fin d, ∑ l : Fin d, ∑ g : G, π g j j * star (π g l l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _j _ => Finset.sum_comm
  -- Push the prefactor `1/|G|` next to the group sum
  have hpush : ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ j : Fin d, ∑ l : Fin d, ∑ g : G,
      π g j j * star (π g l l)
      = ∑ j : Fin d, ∑ l : Fin d, ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G,
        π g j j * star (π g l l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _j _ => by rw [Finset.mul_sum]
  -- Each index `j` contributes `1/d` exactly once (at `l = j`), so the total is `d · 1/d = 1`
  have hinner : ∀ j : Fin d, ∑ l : Fin d, (if j = l then (1 / (d : ℂ)) else 0) = 1 / (d : ℂ) := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro l _ hl
      rw [if_neg (Ne.symm hl)]
    · intro hc
      exact absurd (Finset.mem_univ j) hc
  have hsum2 : ∑ j : Fin d, ∑ l : Fin d, (if j = l then (1 / (d : ℂ)) else 0) = 1 := by
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hinner j,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul',
      one_div, inv_mul_cancel₀ hd0]
  rw [groupTwirlProjectorPair_trace π π]
  simp only [hterm, hreorder, hpush, key, hsum2]

/-! ### Intertwiners and Schur's lemma -/

/-- Averaging a rectangular operator over two unitary representations gives an
intertwiner between those representations. -/
lemma groupTwirlPairSandwich_intertwines {G : Type*} [Group G] [Fintype G] {d d' : ℕ}
    (π₁ : G → Op d) (π₂ : G → Op d') (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂)
    (X : Matrix (Fin d) (Fin d') ℂ) (h : G) :
    π₁ h * ∑ g : G, π₁ g * X * (π₂ g)ᴴ = (∑ g : G, π₁ g * X * (π₂ g)ᴴ) * π₂ h := by
  -- Conjugation by `(π₁ h, π₂ h)` maps the summand at `g` to the summand at `h · g`
  have hterm : ∀ g : G, π₁ h * (π₁ g * X * (π₂ g)ᴴ) * (π₂ h)ᴴ
      = π₁ (h * g) * X * (π₂ (h * g))ᴴ := by
    intro g
    rw [hπ₁.1 h g, hπ₂.1 h g, Matrix.conjTranspose_mul]
    -- rectangular matrices have no `Mul` instance, so use `Matrix.mul_assoc`, not `mul_assoc`
    simp only [Matrix.mul_assoc]
  have hconj : π₁ h * (∑ g : G, π₁ g * X * (π₂ g)ᴴ) * (π₂ h)ᴴ
      = ∑ g : G, π₁ g * X * (π₂ g)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hterm g]
    exact Equiv.sum_comp (Equiv.mulLeft h) fun y => π₁ y * X * (π₂ y)ᴴ
  -- Multiply the invariance by `π₂ h` on the right (unitarity) to get the intertwining relation
  have h1 : (π₁ h * (∑ g : G, π₁ g * X * (π₂ g)ᴴ) * (π₂ h)ᴴ) * π₂ h
      = (∑ g : G, π₁ g * X * (π₂ g)ᴴ) * π₂ h := by
    rw [hconj]
  rw [Matrix.mul_assoc, hπ₂.2 h, Matrix.mul_one] at h1
  exact h1

/-- A nonzero intertwiner between irreducible unitary representations gives a
unitary equivalence. Schur's lemma makes both Gram matrices scalar; a nonzero
entry identifies the scalars, and their traces identify the dimensions. -/
theorem IsIrreduciblyEquivalentGen_of_intertwiner_ne_zero {G : Type*} [Group G]
    {d d' : ℕ} (π₁ : G → Op d) (π₂ : G → Op d') (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂)
    (hirr₁ : IsIrreducibleRep π₁) (hirr₂ : IsIrreducibleRep π₂)
    (Λ : Matrix (Fin d) (Fin d') ℂ) (hΛ0 : Λ ≠ 0)
    (hintw : ∀ h : G, π₁ h * Λ = Λ * π₂ h) :
    IsIrreduciblyEquivalentGen π₁ π₂ := by
  -- A nonzero entry `(k, l)` of `Λ` (both dimensions are then positive)
  obtain ⟨k, l, hkl⟩ : ∃ k : Fin d, ∃ l : Fin d', Λ k l ≠ 0 := by
    by_contra h
    push Not at h
    exact hΛ0 (Matrix.ext fun i j => h i j)
  -- The adjoint intertwines back: `π₂ h · Λᴴ = Λᴴ · π₁ h`
  have hadj : ∀ h : G, π₂ h * Λᴴ = Λᴴ * π₁ h := by
    intro h
    have h1 : (π₁ h⁻¹ * Λ)ᴴ = (Λ * π₂ h⁻¹)ᴴ := by rw [hintw (h⁻¹)]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← hπ₁.inv (h⁻¹),
      ← hπ₂.inv (h⁻¹), inv_inv h] at h1
    exact h1.symm
  -- `ΛᴴΛ` commutes with every `π₂ h`, so Schur gives `ΛᴴΛ = c • 1_{d'}`
  have hcomm₂ : ∀ h : G, π₂ h * (Λᴴ * Λ) = (Λᴴ * Λ) * π₂ h := by
    intro h
    calc π₂ h * (Λᴴ * Λ) = (π₂ h * Λᴴ) * Λ := (Matrix.mul_assoc (π₂ h) Λᴴ Λ).symm
      _ = Λᴴ * π₁ h * Λ := by rw [hadj h]
      _ = Λᴴ * (π₁ h * Λ) := Matrix.mul_assoc Λᴴ (π₁ h) Λ
      _ = Λᴴ * (Λ * π₂ h) := by rw [hintw h]
      _ = (Λᴴ * Λ) * π₂ h := (Matrix.mul_assoc Λᴴ Λ (π₂ h)).symm
  obtain ⟨c, hc⟩ := hirr₂ (Λᴴ * Λ) hcomm₂
  -- `ΛΛᴴ` commutes with every `π₁ h`, so Schur gives `ΛΛᴴ = c' • 1_d`
  have hcomm₁ : ∀ h : G, π₁ h * (Λ * Λᴴ) = (Λ * Λᴴ) * π₁ h := by
    intro h
    calc π₁ h * (Λ * Λᴴ) = (π₁ h * Λ) * Λᴴ := (Matrix.mul_assoc (π₁ h) Λ Λᴴ).symm
      _ = (Λ * π₂ h) * Λᴴ := by rw [hintw h]
      _ = Λ * (π₂ h * Λᴴ) := Matrix.mul_assoc Λ (π₂ h) Λᴴ
      _ = Λ * (Λᴴ * π₁ h) := by rw [hadj h]
      _ = (Λ * Λᴴ) * π₁ h := (Matrix.mul_assoc Λ Λᴴ (π₁ h)).symm
  obtain ⟨c', hc'⟩ := hirr₁ (Λ * Λᴴ) hcomm₁
  -- The diagonal of `ΛᴴΛ` is real nonnegative: `(ΛᴴΛ) i i = Σ_k ‖Λ k i‖²`
  have hdiag : ∀ i : Fin d', (Λᴴ * Λ) i i = ((∑ k : Fin d, ‖Λ k i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' (Λ k i)
  have hcii : ∀ i : Fin d', (Λᴴ * Λ) i i = c := by
    intro i
    rw [hc, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_pos rfl, mul_one]
  -- `c` is the real number `s := Σ_k ‖Λ k l‖² > 0` (the `l`-th column contains the entry `Λ k l`)
  obtain ⟨s, hs_ge, hsc⟩ : ∃ s : ℝ, 0 ≤ s ∧ c = (s : ℂ) :=
    ⟨∑ k : Fin d, ‖Λ k l‖ ^ 2, Finset.sum_nonneg fun k _ => sq_nonneg (‖Λ k l‖),
      (hcii l).symm.trans (hdiag l)⟩
  have hsne : s ≠ 0 := by
    intro h
    refine hkl ?_
    have h1 := hdiag l
    rw [hcii l, hsc, h] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (‖Λ k l‖ : ℝ))).1 ((Complex.ofReal_eq_zero).1 h1.symm)
      k (Finset.mem_univ k)
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 h2)
  have hcne : c ≠ 0 := by rw [hsc]; exact_mod_cast hsne
  -- The scaling `t := (sqrt s)⁻¹` satisfies `t · t · c = 1`
  set t : ℂ := (((Real.sqrt s : ℝ) : ℂ)⁻¹) with ht
  have htc : t * t * c = 1 := by
    rw [ht, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hs_ge, hsc,
      inv_mul_cancel₀ (by exact_mod_cast hsne)]
  -- `c' = c`: evaluate the associativity `(Λ Λᴴ) Λ = Λ (Λᴴ Λ)` at the nonzero entry `(k, l)`
  have hc'eq : c' = c := by
    have hassoc : (Λ * Λᴴ) * Λ = Λ * (Λᴴ * Λ) := Matrix.mul_assoc Λ Λᴴ Λ
    rw [hc', Matrix.smul_mul, Matrix.one_mul, hc, Matrix.mul_smul, Matrix.mul_one] at hassoc
    have hentry : c' * Λ k l = c * Λ k l := by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d') ℂ => M k l) hassoc
      exact h
    exact mul_right_cancel₀ hkl hentry
  -- The dimensions agree: the traces give `c · d = c' · d'` (cyclicity of the trace)
  have hdd : d = d' := by
    have htrc : ∀ {n : ℕ} (x : ℂ), (x • (1 : Op n)).trace = x * (n : ℂ) := fun x => by
      rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
    have e1 : (c : ℂ) * (d : ℂ) = (Λ * Λᴴ).trace := by
      rw [hc', htrc c', hc'eq]
    have e2 : (Λ * Λᴴ).trace = (Λᴴ * Λ).trace := Matrix.trace_mul_comm Λ Λᴴ
    have e3 : (Λᴴ * Λ).trace = c * (d' : ℂ) := by
      rw [hc, htrc c]
    exact Nat.cast_injective (mul_left_cancel₀ hcne (by rw [e1, e2, e3]))
  subst hdd
  -- `W := t · Λ` is the unitary intertwiner
  have hct : (t • Λ)ᴴ = t • Λᴴ := by
    -- `star` on `ℂ` unfolds to `conj` before `Complex.conj_ofReal` can fire
    rw [Matrix.conjTranspose_smul, ht, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  refine ⟨rfl, t • Λ, ⟨?_, ?_⟩, fun g => ?_⟩
  · -- `Wᴴ W = t² · ΛᴴΛ = t² c • 1 = 1`
    rw [hct, smul_mul_assoc, mul_smul_comm, smul_smul, hc, smul_smul,
      htc, one_smul]
  · -- `W Wᴴ = t² · ΛΛᴴ = t² c' • 1 = 1` (using `c' = c`)
    rw [hct, smul_mul_assoc, mul_smul_comm, smul_smul, hc', smul_smul,
      hc'eq, htc, one_smul]
  · -- `W π₂ g Wᴴ = t² · Λ π₂ g Λᴴ = t² · c' π₁ g = π₁ g` (the cast is the identity)
    have hscale : ∀ X : Op d, (t • Λ) * X * (t • Λᴴ) = (t * t) • (Λ * X * Λᴴ) := fun X => by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hstep : Λ * π₂ g * Λᴴ = c' • π₁ g := by
      rw [← hintw g, mul_assoc, hc', mul_smul_comm, mul_one]
    rw [Op.castDim_eq, hct, hscale, hstep, smul_smul, hc'eq, htc, one_smul]

/-- The paired twirl of inequivalent irreducible unitary representations has zero
trace: each of its matrix entries comes from a vanishing averaged intertwiner. -/
theorem groupTwirlProjectorPair_trace_zero_of_not_equiv {G : Type*} [Group G] [Fintype G]
    {d d' : ℕ} (π₁ : G → Op d) (π₂ : G → Op d') (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂)
    (hirr₁ : IsIrreducibleRep π₁) (hirr₂ : IsIrreducibleRep π₂)
    (hne : ¬ IsIrreduciblyEquivalentGen π₁ π₂) :
    (groupTwirlProjectorPair π₁ π₂).trace = 0 := by
  -- Every rectangular intertwiner `π₁ → π₂` vanishes: a nonzero one would give `π₁ ≅ π₂` (Schur)
  have hint0 : ∀ Λ : Matrix (Fin d) (Fin d') ℂ, (∀ h : G, π₁ h * Λ = Λ * π₂ h) → Λ = 0 := by
    intro Λ hΛ
    by_contra hΛ0
    exact hne
      (IsIrreduciblyEquivalentGen_of_intertwiner_ne_zero π₁ π₂ hπ₁ hπ₂ hirr₁ hirr₂ Λ hΛ0 hΛ)
  have hP0 : groupTwirlProjectorPair π₁ π₂ = 0 := by
    ext i j
    simp only [groupTwirlProjectorPair, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Matrix.zero_apply]
    -- Read the entry off the averaged rectangular sandwich with the matrix unit `E_{b b'}`
    set a := (finProdFinEquiv.symm i).1 with ha
    set a' := (finProdFinEquiv.symm i).2 with ha'
    set b := (finProdFinEquiv.symm j).1 with hb
    set b' := (finProdFinEquiv.symm j).2 with hb'
    set E : Matrix (Fin d) (Fin d') ℂ := Matrix.single b b' (1 : ℂ) with hE
    set T : Matrix (Fin d) (Fin d') ℂ :=
      ((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, π₁ g * E * (π₂ g)ᴴ with hT
    -- `T` is an averaged rectangular sandwich, hence an intertwiner, hence zero
    have hTintw : ∀ h : G, π₁ h * T = T * π₂ h := by
      intro h
      calc π₁ h * T = ((Fintype.card G : ℕ) : ℂ)⁻¹ • (π₁ h * ∑ g : G, π₁ g * E * (π₂ g)ᴴ) := by
            rw [hT, Matrix.mul_smul]
        _ = ((Fintype.card G : ℕ) : ℂ)⁻¹ • ((∑ g : G, π₁ g * E * (π₂ g)ᴴ) * π₂ h) := by
            rw [groupTwirlPairSandwich_intertwines π₁ π₂ hπ₁ hπ₂ E h]
        _ = (((Fintype.card G : ℕ) : ℂ)⁻¹ • ∑ g : G, π₁ g * E * (π₂ g)ᴴ) * π₂ h :=
            (Matrix.smul_mul _ _ _).symm
        _ = T * π₂ h := rfl
    have hT0 : T = 0 := hint0 T hTintw
    -- Entry of the rectangular sandwich: only the `q = b'` summand survives
    have hentry : ∀ g : G, (π₁ g * E * (π₂ g)ᴴ) a a' = π₁ g a b * star (π₂ g a' b') := by
      intro g
      rw [hE, Matrix.mul_apply]
      rw [Finset.sum_eq_single b']
      · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply, mul_one]
      · intro x _ hx
        simp [hx]
      · intro hc
        exact (hc (Finset.mem_univ b')).elim
    have hTval : ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, π₁ g a b * star (π₂ g a' b') = T a a' := by
      rw [hT, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
        Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hentry g]
    -- The `(i, j)` entry of `Π` is exactly `T a a' = 0`
    have hten : ∀ g : G, (Op.tensor (π₁ g) (entryConj (π₂ g))) i j
        = π₁ g a b * star (π₂ g a' b') := fun g => by
      simp only [Op_tensor_apply_finProd, entryConj, Matrix.of_apply, ← ha, ← ha', ← hb, ← hb']
    simp only [hten]
    rw [hTval, hT0, Matrix.zero_apply]
  -- The trace of the zero operator is zero
  rw [hP0, Matrix.trace_zero]

/-! ### Twirl projections and isotypic multiplicities -/

/-- The self-paired group twirl is an orthogonal projection. -/
theorem groupTwirlProjector_isOrthogonalProjection {G : Type*} [Group G] [Fintype G] {d : ℕ}
    [NeZero d] (π : G → Op d) (hπ : IsUnitaryRep π) :
    (groupTwirlProjector π)ᴴ = groupTwirlProjector π ∧
      groupTwirlProjector π * groupTwirlProjector π = groupTwirlProjector π :=
  groupTwirlProjectorPair_isOrthogonalProjection π π hπ hπ

/-- An isotypic decomposition in a unitary basis: each block is an irreducible
representation tensored with the identity on its multiplicity space, and distinct
blocks carry inequivalent irreducible representations. -/
def IsIsotypicDecomposition {G : Type*} [Group G] {d k : ℕ} (π : G → Op d)
    (δ mult : Fin k → ℕ) (πi : (i : Fin k) → G → Op (δ i)) : Prop :=
  ∃ (W : Op d) (he : Fin d ≃ Σ i : Fin k, Fin (δ i * mult i)),
    (Wᴴ * W = 1 ∧ W * Wᴴ = 1) ∧
    (∀ i : Fin k, IsUnitaryRep (πi i) ∧ IsIrreducibleRep (πi i)) ∧
    (∀ i i' : Fin k, i ≠ i' → ¬ IsIrreduciblyEquivalentGen (πi i) (πi i')) ∧
    ∀ g : G, Matrix.reindex he he (W * π g * Wᴴ) =
      Matrix.blockDiagonal' (fun i => Op.tensor (πi i g) (1 : Op (mult i)))

open Classical in
/-- Schur orthogonality for the paired twirl: its trace is one for equivalent
irreducible representations and zero otherwise. -/
theorem groupTwirlProjection_irreducible {G : Type*} [Group G] [Fintype G] {d : ℕ} [NeZero d]
    (π₁ π₂ : G → Op d) (hπ₁ : IsUnitaryRep π₁) (hπ₂ : IsUnitaryRep π₂)
    (hirr₁ : IsIrreducibleRep π₁) (hirr₂ : IsIrreducibleRep π₂) :
    (groupTwirlProjectorPair π₁ π₂)ᴴ = groupTwirlProjectorPair π₁ π₂ ∧
      groupTwirlProjectorPair π₁ π₂ * groupTwirlProjectorPair π₁ π₂ =
        groupTwirlProjectorPair π₁ π₂ ∧
      (groupTwirlProjectorPair π₁ π₂).trace =
        if IsIrreduciblyEquivalent π₁ π₂ then (1 : ℂ) else 0 := by
  -- The projection conjuncts are the pair-twirl averaging lemma
  have hproj := groupTwirlProjectorPair_isOrthogonalProjection π₁ π₂ hπ₁ hπ₂
  refine ⟨hproj.1, hproj.2, ?_⟩
  by_cases he : IsIrreduciblyEquivalent π₁ π₂
  · -- Equivalent case: the trace reduces to the self-twirl of the irreducible `π₂`
    rw [if_pos he, groupTwirlProjectorPair_trace_equiv he,
      groupTwirlProjectorPair_trace_self_irreducible π₂ hπ₂ hirr₂]
  · -- Non-equivalent case: the twirl projection has trace zero (Schur)
    rw [if_neg he]
    apply groupTwirlProjectorPair_trace_zero_of_not_equiv π₁ π₂ hπ₁ hπ₂ hirr₁ hirr₂
    rintro ⟨h, W, hW, hconj⟩
    exact he ⟨W, hW, by simpa only [Op.castDim_eq] using hconj⟩

/-- The trace of the paired twirl is the sum of the squared irreducible
multiplicities. Positive irreducible dimensions exclude empty blocks with
nonzero recorded multiplicity. -/
theorem groupTwirlProjector_trace_isotypic {G : Type*} [Group G] [Fintype G] {d k : ℕ} [NeZero d]
    (π : G → Op d) (hπ : IsUnitaryRep π) (δ mult : Fin k → ℕ)
    (πi : (i : Fin k) → G → Op (δ i)) (hpos : ∀ i, 0 < δ i)
    (hiso : IsIsotypicDecomposition π δ mult πi) :
    (groupTwirlProjector π).trace = ∑ i : Fin k, (((mult i : ℕ) : ℂ) ^ 2) := by
  obtain ⟨W, he, hW, hπi, hne, hdiag⟩ := hiso
  -- The character of `π` from the isotypic decomposition: `χ(g) = Σ_i m_i χ_i(g)`
  have h2 : ∀ g : G, (π g).trace = ∑ i : Fin k, (((mult i : ℕ) : ℂ) * (πi i g).trace) := by
    intro g
    -- Cyclic trace under the unitary change of basis, then reindex into the block basis
    have hcyc : (π g).trace = (W * π g * Wᴴ).trace := by
      rw [Matrix.trace_mul_cycle, hW.1, one_mul]
    rw [hcyc, ← Matrix.trace_reindex_self he, hdiag g, Matrix.trace_blockDiagonal']
    simp only [Op.trace_tensor, Matrix.trace_one, Fintype.card_fin]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hInv : ∀ (i : Fin k) (g : G), (πi i g⁻¹).trace = star ((πi i g).trace) := by
    intro i g
    rw [(hπi i).1.inv, Matrix.trace_conjTranspose]
  -- The pair-twirl trace is `1` on the diagonal (self-irreducible) and `0` off it (Schur)
  have hcase : ∀ i i' : Fin k, (groupTwirlProjectorPair (πi i) (πi i')).trace
      = if i = i' then (1 : ℂ) else 0 := by
    intro i i'
    by_cases h : i = i'
    · subst h
      rw [if_pos rfl]
      haveI : NeZero (δ i) := ⟨Nat.ne_of_gt (hpos i)⟩
      exact groupTwirlProjectorPair_trace_self_irreducible (πi i) (hπi i).1 (hπi i).2
    · rw [if_neg h]
      exact groupTwirlProjectorPair_trace_zero_of_not_equiv (πi i) (πi i') (hπi i).1
        (hπi i').1 (hπi i).2 (hπi i').2 (hne i i' h)
  -- Pushing `m_i · m_{i'}` next to the character inner product
  have key : ∀ i i' : Fin k, ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G,
      (((mult i : ℕ) : ℂ) * (πi i g).trace) *
        (((mult i' : ℕ) : ℂ) * star ((πi i' g).trace))
      = ((mult i : ℕ) : ℂ) * ((mult i' : ℕ) : ℂ) *
        (groupTwirlProjectorPair (πi i) (πi i')).trace := by
    intro i i'
    rw [groupTwirlProjectorPair_trace (πi i) (πi i')]
    simp only [entryConj_trace, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  calc (groupTwirlProjector π).trace
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ * ∑ g : G, (π g).trace * (π g⁻¹).trace :=
        groupTwirlProjector_trace_inv π hπ
    _ = ∑ i : Fin k, ∑ i' : Fin k, (((mult i : ℕ) : ℂ) * ((mult i' : ℕ) : ℂ) *
          (groupTwirlProjectorPair (πi i) (πi i')).trace) := by
        -- Substitute the characters, expand the product of sums, reorder the group sum inward
        simp only [h2, hInv, Finset.sum_mul_sum]
        -- Reorder: move the group sum inward, first past the outer `Fin k` sum, then past the
        -- `j` sum. Each step after a `Finset.sum_congr` peel so that `rw`'s matches never need
        -- to capture a bound variable (only the peeled locals).
        rw [Finset.sum_comm (s := (Finset.univ : Finset G))
          (t := (Finset.univ : Finset (Fin k))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm (s := (Finset.univ : Finset G))
          (t := (Finset.univ : Finset (Fin k))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact key y j
    _ = ∑ i : Fin k, (((mult i : ℕ) : ℂ) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        -- Only the summand `i' = i` survives: the pair-twirl trace is `δ_{i i'}`
        rw [Finset.sum_eq_single i]
        · rw [hcase i i, if_pos rfl, mul_one, pow_two]
        · intro i' _ hi'
          rw [hcase i i', if_neg (Ne.symm hi'), mul_zero]
        · intro hc
          exact absurd (Finset.mem_univ i) hc

end Quantum.Symmetry
