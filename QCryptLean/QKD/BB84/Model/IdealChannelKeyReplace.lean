import QCryptLean.Quantum.TensorProducts.PartialTrace
import QCryptLean.QKD.BB84.Model.BB84ClassicalProgram
import QCryptLean.QKD.BB84.Model.RealChannelEntrywise
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacement
import QCryptLean.LOCC.Local
import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.Quantum.Channels.CPTP.DiamondNormReindex

/-!
# The key-replacement law of the ideal channel

The ideal channel, at a general parameter-estimation test-set size `m`, is exactly the
protocol-independent `keyReplace` functor applied to the real channel. This module has two
halves: generic `keyReplace`/Kraus calculus (needs nothing BB84-specific), then that calculus
applied to the BB84 channel pair.

## What is actually true, and why

The ideal channel applies key replacement to the final, symmetrized, announced register.

1. **The bare half.** The ideal privacy-amplification/abort map is `keyReplace` applied
   to the real map, with Eve carried along by `mapTensorId`. The proof is index
   bookkeeping over the two Kraus families:
   * on the **accept** flag the real pass Kraus writes `(kA, kB, 0, st, evTag, syn, pe)` and each
     `freshKeyKraus ℓ D k a b` reads the key pair out and writes `(k, k)` back at amplitude
     `(√(2^ℓ))⁻¹`, giving weight `2⁻ˡ` per fresh key (`keyReplace_sum_pass`,
     `keyReplace_kraus_pass_of`);
   * on the **abort** flag `abortProjOp` fixes the term and every `freshKeyKraus` annihilates it —
     the fail Kraus is literally the same `def` in the two maps (`keyReplace_sum_fail`,
     `keyReplace_kraus_fail_of`).
2. **The commutation half.** `keyReplace_castDim_tensor`: `keyReplace ℓ (D · E)` applied to
   `A ⊗ B` is `(keyReplace ℓ D A) ⊗ B`. Every `keyReplace` Kraus operator is
   `(key part) ⊗ (flag ⊗ 1_D)`, and a register appended on the right of the transcript — for us
   the `n!` permutation announcement — reassociates past the flag untouched (`tensor4_castDim`).

## Main results

- `retainedSiftedPEAnnounceIdealKeyAndAbortChannel_eq_keyReplace`: the general-`m` ideal
  privacy-amplification/abort map is `keyReplace` applied to the general-`m` real map, with
  Eve carried along by `mapTensorId`. Unconditional: `keyReplace` reads the accept flag and the two
  key slots and nothing else, so it never meets the parameter-estimation block whose size `m` fixes.
- `bb84SymIdealChannel_eq_keyReplace_real`: the same statement after the `1/n!` announcement
  mixture, by linearity plus the commutation half `keyReplace_castDim_tensor`: `keyReplace` never
  sees a register appended on the right of the transcript, and the `n!` permutation announcement is
  exactly such a register at every `m`.

## Also here

`mapTensorId_krausMapFintype`, `mapTensorId_sum`, `mapTensorId_one`, `kronId` and its algebra, and
the matrix-unit column lemmas — generic statements about Kraus maps, `mapTensorId` and
`Matrix.single` at arbitrary registers, used by the key-replacement law above.

## What this does NOT claim

It does **not** claim the ideal channel is LOCC, and the ideal must not be: `keyReplace` writes one
fresh uniform key into *both* parties' registers at once, which is a specification of what a secure
key is, not a procedure either party could run.

References: Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024,
arXiv:2403.11851, `main.tex:909` and `:913` (the protocol at a general test-set size `m`,
`\nkey = n - m`).
-/
open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Quantum.Channels Quantum.Metrics
    Matrix
open Math.RepresentationTheory InfoTheory.Postselection QKD.BB84.Engine
open LOCC
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model

/-! ## The two output registers -/

/-- The transcript enlarges on the right: `keyedFlagOutDim ℓ (D · E) = keyedFlagOutDim ℓ D · E`. -/
theorem outDim_mul_right (ℓ D E : ℕ) :
    QKD.keyedFlagOutDim ℓ (D * E) = QKD.keyedFlagOutDim ℓ D * E := by
  simp only [QKD.keyedFlagOutDim]; ring

/-! ## Generic: `mapTensorId` of a finite Kraus map -/

/-- `mapTensorId` is additive in the *map* slot. -/
theorem mapTensorId_sum_map {N M E : ℕ} [NeZero N] [NeZero M] [NeZero E] {κ : Type*} [Fintype κ]
    (Φ : κ → (Op N →ₗ[ℂ] Op M)) (W : Op (N * E)) :
    mapTensorId (k := E) (∑ o, Φ o) W = ∑ o, mapTensorId (k := E) (Φ o) W := by
  ext p q
  simp only [mapTensorId_apply_eq_apply_block, LinearMap.sum_apply, Matrix.sum_apply]

/-- Tensoring a single matrix conjugation with the identity is conjugation by `G ⊗ 1`. -/
theorem mapTensorId_matrixConjLinear {N E : ℕ} [NeZero N] [NeZero E] (G : Op N) (W : Op (N * E)) :
    mapTensorId (k := E) (matrixConjLinear G) W =
      Op.tensor G (1 : Op E) * W * (Op.tensor G (1 : Op E))ᴴ := by
  ext p q
  rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one,
    tensor_sandwich_apply_eq_block G Gᴴ W p q, mapTensorId_apply_eq_apply_block]
  simp only [matrixConjLinear_apply, finProdFinEquiv_symm_apply]

/-- Tensoring a finite Kraus map with the identity is the Kraus map of the `· ⊗ 1` family. -/
theorem mapTensorId_krausMapFintype {N E : ℕ} [NeZero N] [NeZero E] {κ : Type*} [Fintype κ]
    (G : κ → Op N) (W : Op (N * E)) :
    mapTensorId (k := E) (krausMapFintype G) W =
      ∑ o, Op.tensor (G o) (1 : Op E) * W * (Op.tensor (G o) (1 : Op E))ᴴ := by
  have h : (krausMapFintype G : Op N →ₗ[ℂ] Op N) = ∑ o, matrixConjLinear (G o) := by
    refine LinearMap.ext fun A => ?_
    simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
      matrixConjLinear_apply]
  rw [h, mapTensorId_sum_map]
  exact Finset.sum_congr rfl fun o _ => mapTensorId_matrixConjLinear (G o) W

/-! ## Generic: `A ⊗ 1` for a rectangular `A` -/

/-- `A ⊗ 1_E` for a rectangular `A`, in `finProdFinEquiv` coordinates. This is the shape every
retained-Eve Kraus operator has. -/
def kronId (E : ℕ) {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin (p * E)) (Fin (q * E)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin E) (Fin E) ℂ))

theorem kronId_eq_opTensor (E : ℕ) {p : ℕ} (A : Op p) :
    kronId E A = Op.tensor A (1 : Op E) := rfl

theorem kronId_mul (E : ℕ) {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin q) (Fin r) ℂ) :
    kronId E A * kronId E B = kronId E (A * B) := by
  simp only [kronId, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem kronId_conjTranspose (E : ℕ) {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    (kronId E A)ᴴ = kronId E Aᴴ := by
  simp only [kronId, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem kronId_zero (E : ℕ) {p q : ℕ} : kronId E (0 : Matrix (Fin p) (Fin q) ℂ) = 0 := by
  simp only [kronId, Matrix.zero_kronecker, Matrix.reindex_apply, Matrix.submatrix_zero]
  rfl

theorem kronId_smul (E : ℕ) {p q : ℕ} (c : ℂ) (A : Matrix (Fin p) (Fin q) ℂ) :
    kronId E (c • A) = c • kronId E A := by
  ext i j
  simp only [kronId, Matrix.smul_kronecker, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.smul_apply]

/-! ## Generic: right multiplication by a matrix unit reads off a column -/

theorem mul_single_eq_single {D M : ℕ} (A : Op D) (P P' : Fin D) (w : Fin M) (μ : ℂ)
    (h : ∀ i, A i P = if P' = i then μ else 0) :
    A * Matrix.single P w (1 : ℂ) = Matrix.single P' w μ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ P), h i]
  by_cases hj : w = j <;> by_cases hi : P' = i <;> simp [hj, hi]

/-! ## Generic: columns of a tensor product -/

theorem opTensor_col {p q : ℕ} (A : Op p) (B : Op q) (x x' : Fin p) (y y' : Fin q) (μ ν : ℂ)
    (hA : ∀ i, A i x = if x' = i then μ else 0)
    (hB : ∀ i, B i y = if y' = i then ν else 0) (i : Fin (p * q)) :
    Op.tensor A B i (finProdFinEquiv (x, y)) =
      if finProdFinEquiv (x', y') = i then μ * ν else 0 := by
  obtain ⟨⟨i1, i2⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply, hA, hB]
  by_cases h1 : x' = i1 <;> by_cases h2 : y' = i2 <;>
    simp [h1, h2, Prod.ext_iff]

theorem one_col {q : ℕ} (y : Fin q) (i : Fin q) :
    (1 : Op q) i y = if y = i then (1 : ℂ) else 0 := by
  rw [Matrix.one_apply]
  by_cases h : y = i <;> simp [h, eq_comm]

theorem single_col {p : ℕ} (x' a c : Fin p) (i : Fin p) :
    Matrix.single x' a (1 : ℂ) i c = if x' = i then (if a = c then (1 : ℂ) else 0) else 0 := by
  rw [Matrix.single_apply]
  by_cases h1 : x' = i <;> by_cases h2 : a = c <;> simp [h1, h2]

theorem smul_col {p : ℕ} (c : ℂ) (A : Op p) (x x' : Fin p) (μ : ℂ)
    (h : ∀ i, A i x = if x' = i then μ else 0) (i : Fin p) :
    (c • A) i x = if x' = i then c * μ else 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, h i]
  by_cases hh : x' = i <;> simp [hh]

/-! ## The three `keyReplace` Kraus operators against a transcript matrix unit

Each of `abortProjOp`, `acceptProjOp` and `freshKeyKraus` has, in the column indexed by a transcript
index `(keys, flag, rest)`, at most one nonzero entry. These three lemmas read that column off. -/

theorem abortFlagOp_col {D : ℕ} (f : Fin 2) (r : Fin D) (i : Fin (2 * D)) :
    abortFlagOp D i (finProdFinEquiv (f, r)) =
      if finProdFinEquiv ((1 : Fin 2), r) = i then
        (if (1 : Fin 2) = f then (1 : ℂ) else 0) * 1 else 0 :=
  opTensor_col _ _ f (1 : Fin 2) r r _ 1 (single_col (1 : Fin 2) 1 f) (one_col r) i

theorem acceptFlagOp_col {D : ℕ} (f : Fin 2) (r : Fin D) (i : Fin (2 * D)) :
    acceptFlagOp D i (finProdFinEquiv (f, r)) =
      if finProdFinEquiv ((0 : Fin 2), r) = i then
        (if (0 : Fin 2) = f then (1 : ℂ) else 0) * 1 else 0 :=
  opTensor_col _ _ f (0 : Fin 2) r r _ 1 (single_col (0 : Fin 2) 0 f) (one_col r) i

/-- `abortProjOp` keeps a transcript matrix unit exactly on the abort flag. -/
theorem abortProjOp_mul_single {ℓ D M : ℕ} (kp : Fin (2 ^ ℓ * 2 ^ ℓ)) (f : Fin 2) (r : Fin D)
    (w : Fin M) :
    abortProjOp ℓ D * Matrix.single (finProdFinEquiv (kp, finProdFinEquiv (f, r))) w (1 : ℂ) =
      Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w
        (if (1 : Fin 2) = f then (1 : ℂ) else 0) := by
  refine mul_single_eq_single _ _ _ _ _ fun i => ?_
  rw [abortProjOp]
  refine (opTensor_col (1 : Op (2 ^ ℓ * 2 ^ ℓ)) (abortFlagOp D) kp kp
    (finProdFinEquiv (f, r)) (finProdFinEquiv ((1 : Fin 2), r)) 1 _
    (one_col kp) (abortFlagOp_col f r) i).trans ?_
  by_cases h : finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r)) = i <;> simp [h]

/-- **The fresh-key Kraus operator against a pass transcript.** It reads the two key slots out and
writes the same fresh `k` into both, keeping the flag and every announcement untouched; it vanishes
unless the read-out pair matches, and on the abort flag. -/
theorem freshKeyKraus_mul_single {ℓ D M : ℕ} (k a b kA kB : Fin (2 ^ ℓ)) (f : Fin 2) (r : Fin D)
    (w : Fin M) :
    freshKeyKraus ℓ D k a b *
        Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv (f, r))) w
          (1 : ℂ) =
      Matrix.single (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r))) w
        ((((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℝ) : ℂ) *
          ((if a = kA then (1 : ℂ) else 0) * (if b = kB then (1 : ℂ) else 0) *
            ((if (0 : Fin 2) = f then (1 : ℂ) else 0) * 1))) := by
  refine mul_single_eq_single _ _ _ _ _ fun i => ?_
  rw [freshKeyKraus]
  refine smul_col _ _ _ (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r)))
    _ (fun i' => ?_) i
  exact opTensor_col _ (acceptFlagOp D) (finProdFinEquiv (kA, kB)) (finProdFinEquiv (k, k))
    (finProdFinEquiv (f, r)) (finProdFinEquiv ((0 : Fin 2), r)) _ _
    (opTensor_col _ _ kA k kB k _ _ (single_col k a kA) (single_col k b kB))
    (acceptFlagOp_col f r) i'

/-! ## Pushing `keyReplace ⊗ 1` through a `A ⊗ 1` Kraus sandwich -/

/-- `mapTensorIdLinear` applied, as its underlying `mapTensorId`. -/
theorem mapTensorIdLinear_apply {a b e : ℕ} [NeZero a] [NeZero b] [NeZero e]
    (Φ : Op a →ₗ[ℂ] Op b) (M : Op (a * e)) :
    mapTensorIdLinear (k := e) Φ M = mapTensorId Φ M := rfl

theorem single_eq_smul {p q : ℕ} (i : Fin p) (j : Fin q) (μ : ℂ) :
    Matrix.single i j μ = μ • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem kronId_conj_smul {E p q : ℕ} (μ : ℂ) (A : Matrix (Fin p) (Fin q) ℂ) (M : Op (q * E)) :
    kronId E (μ • A) * M * (kronId E (μ • A))ᴴ =
      (μ * (starRingEnd ℂ) μ) • (kronId E A * M * (kronId E A)ᴴ) := by
  rw [kronId_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rfl

theorem mapTensorId_keyReplace_kronId_conj {ℓ D E N : ℕ} [NeZero D] [NeZero E]
    (A : Matrix (Fin (QKD.keyedFlagOutDim ℓ D)) (Fin N) ℂ) (M : Op (N * E)) :
    mapTensorId (k := E) (keyReplace ℓ D) (kronId E A * M * (kronId E A)ᴴ) =
      ∑ o, kronId E (keyReplaceKraus ℓ D o * A) * M *
        (kronId E (keyReplaceKraus ℓ D o * A))ᴴ := by
  rw [keyReplace_eq_krausMapFintype, mapTensorId_krausMapFintype]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← kronId_eq_opTensor, ← kronId_mul, Matrix.conjTranspose_mul, kronId_conjTranspose]
  simp only [Matrix.mul_assoc]

/-! ## The two branch computations -/

/-- **The abort branch is fixed.** On a transcript matrix unit carrying the abort flag, the whole
`keyReplace` Kraus family collapses to the identity: the abort projector keeps it and every
fresh-key operator kills it. -/
theorem keyReplace_sum_fail (ℓ D E N : ℕ) [NeZero D] [NeZero E]
    (kp : Fin (2 ^ ℓ * 2 ^ ℓ)) (r : Fin D) (w : Fin N) (M : Op (N * E)) :
    ∑ o, kronId E (keyReplaceKraus ℓ D o *
          Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ)) * M *
        (kronId E (keyReplaceKraus ℓ D o *
          Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ)))ᴴ =
      kronId E (Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ)) *
        M *
        (kronId E
          (Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ)))ᴴ := by
  rw [Fintype.sum_option]
  have hnone : keyReplaceKraus ℓ D none *
      Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ) =
      Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ) := by
    rw [keyReplaceKraus_none, abortProjOp_mul_single]
    simp
  have hsome : ∀ p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
      keyReplaceKraus ℓ D (some p) *
        Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ) = 0 := by
    rintro ⟨k, a, b⟩
    obtain ⟨⟨kA, kB⟩, hkp⟩ := finProdFinEquiv.surjective kp
    rw [keyReplaceKraus_some, ← hkp, freshKeyKraus_mul_single]
    simp
  simp only [hnone, hsome, kronId_zero, Matrix.zero_mul, Finset.sum_const_zero, add_zero]

/-- **The accept branch is key-replaced.** On a transcript matrix unit carrying the accept flag and
a key pair `(kA, kB)`, the `keyReplace` Kraus family produces exactly the uniform mixture of the
`(k, k)` transcripts, at weight `2⁻ˡ`, with every announcement untouched. -/
theorem keyReplace_sum_pass (ℓ D E N : ℕ) [NeZero D] [NeZero E]
    (kA kB : Fin (2 ^ ℓ)) (r : Fin D) (w : Fin N) (M : Op (N * E)) :
    ∑ o, kronId E (keyReplaceKraus ℓ D o *
          Matrix.single
              (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r)))
            w (1 : ℂ)) * M *
        (kronId E (keyReplaceKraus ℓ D o *
          Matrix.single
              (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r)))
            w (1 : ℂ)))ᴴ =
      (((2 : ℂ) ^ ℓ)⁻¹) • ∑ k : Fin (2 ^ ℓ),
        kronId E (Matrix.single
            (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ))
                *
          M *
          (kronId E (Matrix.single
            (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r))) w
              (1 : ℂ)))ᴴ := by
  classical
  rw [Fintype.sum_option]
  have hnone : keyReplaceKraus ℓ D none *
      Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r)))
        w (1 : ℂ) = 0 := by
    rw [keyReplaceKraus_none, abortProjOp_mul_single]
    simp
  rw [hnone, kronId_zero, Matrix.zero_mul, Matrix.zero_mul, zero_add]
  have hc : (((Real.sqrt ((2 : ℝ) ^ ℓ) : ℝ) : ℂ))⁻¹ * (((Real.sqrt ((2 : ℝ) ^ ℓ) : ℝ) : ℂ))⁻¹ =
      ((2 : ℂ) ^ ℓ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hterm : ∀ p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
      kronId E (keyReplaceKraus ℓ D (some p) *
          Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
            finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)) * M *
        (kronId E (keyReplaceKraus ℓ D (some p) *
          Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
            finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)))ᴴ =
      (if p.2.1 = kA ∧ p.2.2 = kB then (((2 : ℂ) ^ ℓ)⁻¹) else 0) •
          (kronId E (Matrix.single (finProdFinEquiv (finProdFinEquiv (p.1, p.1),
              finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)) * M *
            (kronId E (Matrix.single (finProdFinEquiv (finProdFinEquiv (p.1, p.1),
              finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)))ᴴ) := by
    rintro ⟨k, a, b⟩
    rw [keyReplaceKraus_some, freshKeyKraus_mul_single, single_eq_smul, kronId_conj_smul]
    by_cases ha : a = kA <;> by_cases hb : b = kB <;> simp [ha, hb, hc]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hterm p, Fintype.sum_prod_type,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [ite_and, ite_smul, zero_smul]
  simp

/-! ## The two branches, at the level of a whole gated Kraus family -/

/-- **The abort branch of a Kraus family is untouched by key replacement.** Every member is
`A ⊗ 1` for an `A` that is either zero or a transcript matrix unit carrying the abort flag. -/
theorem keyReplace_kraus_fail_of {ℓ D E N : ℕ} [NeZero D] [NeZero E] {κ : Type*} [Fintype κ]
    (G : κ → Matrix (Fin (QKD.keyedFlagOutDim ℓ D * E)) (Fin (N * E)) ℂ)
    (hG : ∀ x, ∃ A : Matrix (Fin (QKD.keyedFlagOutDim ℓ D)) (Fin N) ℂ,
        G x = kronId E A ∧
        (A = 0 ∨ ∃ (kp : Fin (2 ^ ℓ * 2 ^ ℓ)) (r : Fin D) (w : Fin N),
          A = Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w (1 : ℂ)))
    (M : Op (N * E)) :
    mapTensorId (k := E) (keyReplace ℓ D) (krausMapFintype G M) = krausMapFintype G M := by
  classical
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  change mapTensorIdLinear (k := E) (keyReplace ℓ D) (∑ x, G x * M * (G x)ᴴ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨A, hGA, hA⟩ := hG x
  rw [hGA, mapTensorIdLinear_apply, mapTensorId_keyReplace_kronId_conj]
  rcases hA with rfl | ⟨kp, r, w, rfl⟩
  · simp [kronId_zero]
  · exact keyReplace_sum_fail ℓ D E N kp r w M

/-- **The accept branch of a Kraus family is key-replaced.** Every member is `A ⊗ 1` for an `A`
that is either zero or a transcript matrix unit carrying the accept flag and a key pair; the
output is the uniform `(k, k)` family at weight `2⁻ˡ`, with every announcement untouched. -/
theorem keyReplace_kraus_pass_of {ℓ D E N : ℕ} [NeZero D] [NeZero E] {κ : Type*} [Fintype κ]
    (G : κ → Matrix (Fin (QKD.keyedFlagOutDim ℓ D * E)) (Fin (N * E)) ℂ)
    (Hf : Fin (2 ^ ℓ) × κ → Matrix (Fin (QKD.keyedFlagOutDim ℓ D * E)) (Fin (N * E)) ℂ)
    (hGH : ∀ x, (G x = 0 ∧ ∀ k, Hf (k, x) = 0) ∨
        ∃ (kA kB : Fin (2 ^ ℓ)) (r : Fin D) (w : Fin N),
          G x = kronId E (Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
              finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)) ∧
          ∀ k, Hf (k, x) = kronId E (Matrix.single (finProdFinEquiv (finProdFinEquiv (k, k),
              finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)))
    (M : Op (N * E)) :
    mapTensorId (k := E) (keyReplace ℓ D) (krausMapFintype G M) =
      ((2 : ℂ) ^ ℓ)⁻¹ • krausMapFintype Hf M := by
  classical
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  change mapTensorIdLinear (k := E) (keyReplace ℓ D) (∑ x, G x * M * (G x)ᴴ) = _
  rw [map_sum, Fintype.sum_prod_type,
    Finset.sum_comm (s := (Finset.univ : Finset (Fin (2 ^ ℓ)))) (t := (Finset.univ : Finset κ)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases hGH x with ⟨hG0, hH0⟩ | ⟨kA, kB, r, w, hGx, hHx⟩
  · simp [hG0, hH0]
  · rw [hGx, mapTensorIdLinear_apply, mapTensorId_keyReplace_kronId_conj]
    simp only [hHx]
    exact keyReplace_sum_pass ℓ D E N kA kB r w M

/-! ## The bare half of the ideal bridge -/

/-- The relabelling between the real map's `(seed pair, outcome)` index and the ideal map's
`(outcome, fresh key, seed pair)` index, with the fresh key pulled out in front. -/
def idealPassIndexEquiv (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    Fin (2 ^ ℓ) × (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) ≃
      ((Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun q := (q.2.1, (q.2.2, q.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The commutation half: key replacement ignores a register appended on the right -/

/-- Reassociating a trailing spectator register past a middle block: four-factor tensor
reassociation, `(Xp ⊗ (f ⊗ Yq)) ⊗ Zq = Xp ⊗ (f ⊗ (Yq ⊗ Zq))`, modulo the index cast.

At the call sites in this module the middle factor `f` is the accept/abort flag on `Op 2` and the
content is "the flag and the two key slots sit strictly to the LEFT of everything the announcement
appends". The *statement*, though, never reads the flag: it is pure reassociation, so `f` is left
at an arbitrary dimension `q` and the flag instance is recovered by instantiation. -/
theorem tensor4_castDim {p q D E : ℕ} (Xp : Op p) (f : Op q) (Yq : Op D) (Zq : Op E)
    (h : p * (q * D) * E = p * (q * (D * E))) :
    Op.castDim h (Op.tensor (Op.tensor Xp (Op.tensor f Yq)) Zq) =
      Op.tensor Xp (Op.tensor f (Op.tensor Yq Zq)) := by
  have hcast : ∀ (x : Fin p) (a : Fin q) (d : Fin D) (e : Fin E),
      Fin.cast h.symm (finProdFinEquiv (x, finProdFinEquiv (a, finProdFinEquiv (d, e)))) =
        finProdFinEquiv (finProdFinEquiv (x, finProdFinEquiv (a, d)), e) := by
    intro x a d e
    refine Fin.ext ?_
    simp only [Fin.val_cast, finProdFinEquiv_apply_val]
    ring
  ext i j
  obtain ⟨⟨x, u⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨a, v⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨d, e⟩, rfl⟩ := finProdFinEquiv.surjective v
  obtain ⟨⟨x', u'⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨a', v'⟩, rfl⟩ := finProdFinEquiv.surjective u'
  obtain ⟨⟨d', e'⟩, rfl⟩ := finProdFinEquiv.surjective v'
  rw [Op.castDim_apply, hcast, hcast]
  simp only [Op_tensor_apply_finProd, Equiv.symm_apply_apply]
  ring

/-- The identity-tailed specialization of `tensor4_castDim`: a spectator register appended to a
block that ends in identities is absorbed into a single identity. Same dimension-genericity — the
middle factor `f` is the flag only at the call sites, never in the statement. -/
theorem tensor_flag_castDim {p q D E : ℕ} (Xp : Op p) (f : Op q)
    (h : p * (q * D) * E = p * (q * (D * E))) :
    Op.castDim h (Op.tensor (Op.tensor Xp (Op.tensor f (1 : Op D))) (1 : Op E)) =
      Op.tensor Xp (Op.tensor f (1 : Op (D * E))) := by
  rw [tensor4_castDim Xp f (1 : Op D) (1 : Op E) h, Op.tensor_one]

/-- Every `keyReplace` Kraus operator on the enlarged transcript `D · E` is the corresponding
operator on `D` with the spectator register `E` carried along. -/
theorem keyReplaceKraus_castDim (ℓ D E : ℕ)
    (o : Option (Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ))) :
    keyReplaceKraus ℓ (D * E) o =
      Op.castDim (outDim_mul_right ℓ D E).symm
        (Op.tensor (keyReplaceKraus ℓ D o) (1 : Op E)) := by
  cases o with
  | none =>
      simp only [keyReplaceKraus_none, abortProjOp, abortFlagOp]
      exact (tensor_flag_castDim _ _ _).symm
  | some p =>
      simp only [keyReplaceKraus_some, freshKeyKraus, acceptFlagOp, Op.tensor_smul_left,
        Op.castDim_smul]
      exact congrArg _ (tensor_flag_castDim _ _ _).symm

/-- **The commutation half.** `keyReplace` never sees a register appended on the right of the
transcript — in particular not the `n!` permutation announcement. -/
theorem keyReplace_castDim_tensor (ℓ D E : ℕ)
    (A : Op (QKD.keyedFlagOutDim ℓ D)) (B : Op E) :
    keyReplace ℓ (D * E) (Op.castDim (outDim_mul_right ℓ D E).symm (Op.tensor A B)) =
      Op.castDim (outDim_mul_right ℓ D E).symm (Op.tensor (keyReplace ℓ D A) B) := by
  rw [keyReplace_eq_krausMapFintype, keyReplace_eq_krausMapFintype]
  change (∑ o, keyReplaceKraus ℓ (D * E) o *
      Op.castDim (outDim_mul_right ℓ D E).symm (Op.tensor A B) *
      (keyReplaceKraus ℓ (D * E) o)ᴴ) =
    Op.castDim (outDim_mul_right ℓ D E).symm (Op.tensor (∑ o, keyReplaceKraus ℓ D o * A *
      (keyReplaceKraus ℓ D o)ᴴ) B)
  rw [Op.tensor_finsetSum_left, Op.castDim_sum_univ]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [keyReplaceKraus_castDim, Op.castDim_conjTranspose, Op.castDim_mul, Op.castDim_mul,
    Op.tensor_conjTranspose, Matrix.conjTranspose_one, Op.tensor_mul, Op.tensor_mul,
    Matrix.one_mul, Matrix.mul_one]

/-! ## `mapTensorId` at the unit ancilla -/

theorem finProdFinEquiv_one_fst {b : ℕ} (p : Fin (b * 1)) :
    (finProdFinEquiv.symm p).1 = Fin.cast (Nat.mul_one b) p := by
  refine Fin.ext ?_
  rw [finProdFinEquiv_symm_apply]
  simp [Fin.coe_divNat]

theorem finProdFinEquiv_one_apply {a : ℕ} (i : Fin a) (s : Fin 1) :
    (finProdFinEquiv (i, s) : Fin (a * 1)) = Fin.cast (Nat.mul_one a).symm i := by
  refine Fin.ext ?_
  simp [finProdFinEquiv_apply_val]

theorem mapTensorId_sum {N M E : ℕ} [NeZero N] [NeZero M] [NeZero E] {κ : Type*} [Fintype κ]
    (Φ : Op N →ₗ[ℂ] Op M) (f : κ → Op (N * E)) :
    mapTensorId (k := E) Φ (∑ x, f x) = ∑ x, mapTensorId (k := E) Φ (f x) := by
  change mapTensorIdLinear (k := E) Φ (∑ x, f x) = _
  rw [map_sum]
  rfl

/-- At the unit ancilla, `mapTensorId` is the map itself, conjugated by the `· * 1` register
    cast. -/
theorem mapTensorId_one {a b : ℕ} [NeZero a] [NeZero b] (Φ : Op a →ₗ[ℂ] Op b) (W : Op (a * 1)) :
    mapTensorId (k := 1) Φ W =
      Op.castDim (Nat.mul_one b).symm (Φ (Op.castDim (Nat.mul_one a) W)) := by
  ext p q
  rw [mapTensorId_apply_eq_apply_block, Op.castDim_apply]
  have hblock : (Matrix.of fun i j => W (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))) = Op.castDim (Nat.mul_one a) W := by
    ext i j
    rw [Op.castDim_apply]
    simp only [Matrix.of_apply]
    rw [finProdFinEquiv_one_apply, finProdFinEquiv_one_apply]
  rw [hblock, finProdFinEquiv_one_fst, finProdFinEquiv_one_fst]

/-! ## The bare half of the general-`m` ideal bridge

The one place the general-`m` PE block appears is inside the transcript index, and neither
`keyReplace` nor any of the three Kraus-column lemmas it is built from ever reads it: the block sits
strictly to the right of the accept flag and the two key slots. That is why this module needs no
count hypothesis, and why the branch computations are reused rather than mirrored. -/

/-- **The bare half, at a general `m`.** The general-`m` ideal PA/abort map is exactly
`keyReplace` — the protocol-independent key-replacement functor — applied to the general-`m`
real PA/abort map, with Eve carried along untouched, carrying no hypothesis. -/
theorem retainedSiftedPEAnnounceIdealKeyAndAbortChannel_eq_keyReplace
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (M : Op (4 ^ n * eveDim)) :
    bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q M =
      mapTensorId (k := eveDim)
        (keyReplace ℓ (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))
        (bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel
          xSel leakEC ec δ Q M) := by
  classical
  have hfailG : ∀ x : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
      ∃ A : Matrix (Fin (QKD.keyedFlagOutDim ℓ
          (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))) (Fin (4 ^ n)) ℂ,
        bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
              x = kronId eveDim A ∧
          (A = 0 ∨ ∃ (kp : Fin (2 ^ ℓ * 2 ^ ℓ))
              (r : Fin (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))
              (w : Fin (4 ^ n)),
            A = Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) w
              (1 : ℂ)) := by
    rintro ⟨st, ω⟩
    by_cases hg : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
    · exact ⟨0, by simp [bb84.retainedSiftedPEAnnounceFailBranchKraus, hg, kronId_zero],
        Or.inl rfl⟩
    · refine ⟨Matrix.single (bb84.peFailOutIndex n m ℓ ℓEV peSel leakEC st
          (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
          (ec.syndrome (aliceKeyString peSel ω))
          (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2)) (finFunctionFinEquiv ω)
          (1 : ℂ), ?_, Or.inr ⟨_, _, _, rfl⟩⟩
      simp [bb84.retainedSiftedPEAnnounceFailBranchKraus, hg, kronId]
  have hpassG : ∀ x : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
      (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            x = 0 ∧
          ∀ k : Fin (2 ^ ℓ),
            bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec
              δ Q (idealPassIndexEquiv n ℓ ℓEV peSel (k, x)) = 0) ∨
        ∃ (kA kB : Fin (2 ^ ℓ))
          (r : Fin (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))
          (w : Fin (4 ^ n)),
          bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec
              δ Q x =
              kronId eveDim (Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
                finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)) ∧
            ∀ k : Fin (2 ^ ℓ),
              bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC
                  ec δ Q (idealPassIndexEquiv n ℓ ℓEV peSel (k, x)) =
                kronId eveDim (Matrix.single (finProdFinEquiv (finProdFinEquiv (k, k),
                  finProdFinEquiv ((0 : Fin 2), r))) w (1 : ℂ)) := by
    rintro ⟨st, ω⟩
    by_cases hg : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
    · refine Or.inr
        ⟨(aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω),
        (aliceKeyHashFamily n ℓ peSel).hash st.1
          (ec.decode (bobKeyString peSel ω)
            (ec.syndrome (aliceKeyString peSel ω))),
        finProdFinEquiv
          (finProdFinEquiv
            (finProdFinEquiv (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) st,
              verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω)),
              ec.syndrome (aliceKeyString peSel ω)),
            finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2),
        finFunctionFinEquiv ω, ?_, fun k => ?_⟩
      · simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, hg, kronId,
          bb84.pePassOutIndex]
      · simp [bb84.retainedSiftedPEAnnounceIdealPassKraus, idealPassIndexEquiv, hg, kronId,
          bb84.pePassOutIndex]
    · exact Or.inl ⟨by simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, hg],
        fun k => by simp [bb84.retainedSiftedPEAnnounceIdealPassKraus, idealPassIndexEquiv,
          hg]⟩
  have hfail := keyReplace_kraus_fail_of
    (ℓ := ℓ) (D := bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC) (E := eveDim)
    (N := 4 ^ n)
    (bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
    hfailG M
  have hpass := keyReplace_kraus_pass_of
    (ℓ := ℓ) (D := bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC) (E := eveDim)
    (N := 4 ^ n)
    (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
    (fun p => bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC
      ec δ Q (idealPassIndexEquiv n ℓ ℓEV peSel p))
    hpassG M
  rw [Quantum.Channels.krausMapFintype_equiv (idealPassIndexEquiv n ℓ ℓEV peSel)
    (bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
    M] at hpass
  rw [bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel,
    bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [mapTensorId_add_basic, mapTensorId_smul_basic, mapTensorId_smul_basic, hpass, hfail,
    smul_smul]
  congr 2
  rw [one_div, one_div, mul_inv]
  ring

/-! ## The general-`m` symmetrized ideal channel is key replacement of the real one

The commutation half is `keyReplace_castDim_tensor`, which reads no split point and is imported
unchanged: `keyReplace` never sees a register appended on the right of the transcript, and the `n!`
permutation announcement is exactly such a register at every `m`. -/

/-- **The general-`m` symmetrized ideal channel is key replacement applied to the general-`m`
symmetrized real channel.** Unconditional. -/
theorem bb84SymIdealChannel_eq_keyReplace_real (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (ρ : Op (4 ^ n)) :
    bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ =
      mapTensorId (k := 1)
        (keyReplace ℓ (bb84SymPEAnnounceTranscriptInnerDim n m ℓ ℓEV peSel leakEC))
        (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ) := by
  have hcomm : ∀ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π).comp
          (keyReplace ℓ (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC)) =
        (keyReplace ℓ (bb84SymPEAnnounceTranscriptInnerDim n m ℓ ℓEV peSel leakEC)).comp
          (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π) := by
    intro π
    refine LinearMap.ext fun A => ?_
    simp only [LinearMap.comp_apply, bb84SiftedPEAnnounceLinear, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (keyReplace_castDim_tensor ℓ
      (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC) n.factorial A
      (permAnnounceProjector n π)).symm
  simp only [bb84SymIdealChannel, bb84SymRealChannel, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, bb84SiftedPEAnnounceEveVisibleProtocol]
  rw [mapTensorId_smul_basic, mapTensorId_sum]
  refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
  simp only [bb84SiftedPEAnnounceLinearEveVisible, mapTensorIdLinear_apply]
  rw [retainedSiftedPEAnnounceIdealKeyAndAbortChannel_eq_keyReplace,
    mapTensorId_comp, mapTensorId_comp, hcomm]

end QKD.BB84.Model

end
