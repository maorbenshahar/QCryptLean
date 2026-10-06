import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Self-Adjoint Dilation for Trace-Norm Contractivity

Block maps, dilation identities and general CPTP contraction.  The general CPTP
trace-norm contractivity `traceNorm (Φ A) ≤ traceNorm A` is reduced
to the already-proven Hermitian case via the **self-adjoint dilation trick**:

For any n×n matrix A, the (n+n)×(n+n) block matrix
  H_A = [0, A; A†, 0]
is Hermitian. The "block CPTP" map id₂ ⊗ Φ that applies Φ independently to each
n×n block is CPTP, and satisfies (id₂ ⊗ Φ)(H_A) = H_{Φ(A)}. Moreover,
traceNorm(H_A) = 2 · traceNorm(A).

Combining with `traceNorm_cptp_contractive_hermitian`:
  2·‖Φ(A)‖₁ = ‖H_{Φ(A)}‖₁ = ‖(id₂⊗Φ)(H_A)‖₁ ≤ ‖H_A‖₁ = 2·‖A‖₁

## Main definitions
- `selfAdjointDilation`: H_A = [0, A; A†, 0] as Op (n + n)
- `blockMap`: (id₂ ⊗ Φ)(X) — applies Φ independently to each n×n block of X

## Main statements
- `selfAdjointDilation_isHermitian`: H_A is Hermitian
- `traceNorm_selfAdjointDilation`: ‖H_A‖₁ = 2·‖A‖₁ (proven via charpoly factorization)
- `blockMap_isCPTP`: id₂ ⊗ Φ is CPTP when Φ is (via Kraus decomposition)
- `blockMap_selfAdjointDilation`: (id₂⊗Φ)(H_A) = H_{Φ(A)} (proven, uses Φ(A†) = Φ(A)†)
- `Quantum.Metrics.blockMap_selfAdjointDilation_of_preserves_conj`: Hermitian-preserving variant of
the block-map dilation identity
- `traceNorm_cptp_contractive_general`: ‖Φ(A)‖₁ ≤ ‖A‖₁ for any CPTP Φ, any A
- `traceNorm_sub_le`: ‖X - Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁
- `traceNorm_add_le`: ‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁
- `traceNorm_neg`: ‖-A‖₁ = ‖A‖₁
- `traceNorm_conjTranspose`: ‖Aᴴ‖₁ = ‖A‖₁
- `traceNorm_star`: ‖star A‖₁ = ‖A‖₁ (star-notation wrapper)

## References
- Watrous (2018) "The Theory of Quantum Information", Theorem 3.33
- Ruskai (1994) "Beyond strong subadditivity"
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Self-Adjoint Dilation

For an n×n matrix A, the self-adjoint dilation is the (n+n)×(n+n) Hermitian matrix
  H_A = [0, A; A†, 0]

We define this as `Op (n + n)` by reindexing the `Fin n ⊕ Fin n`-indexed
block matrix via `finSumFinEquiv`.
-/

/-- The self-adjoint dilation of A: the block matrix [0, A; A†, 0] as `Op (n + n)`.

    This is Hermitian for any A, and satisfies traceNorm(H_A) = 2·traceNorm(A).
    Used to reduce general CPTP contractivity to the Hermitian case. -/
def selfAdjointDilation {n : ℕ} (A : Op n) : Op (n + n) :=
  (Matrix.fromBlocks 0 A A.conjTranspose 0).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- The self-adjoint dilation is Hermitian.

    H_A = [0, A; A†, 0] satisfies H_A† = [0†, (A†)†; A†, 0†] = [0, A; A†, 0] = H_A. -/
lemma selfAdjointDilation_isHermitian {n : ℕ} (A : Op n) :
    (selfAdjointDilation A).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  exact Matrix.IsHermitian.fromBlocks isHermitian_zero
    (by rfl) isHermitian_zero

/-- The self-adjoint dilation distributes over subtraction:
    H_{A-B} = H_A - H_B, i.e. [0, A-B; (A-B)†, 0] = [0,A;A†,0] - [0,B;B†,0]. -/
lemma selfAdjointDilation_sub {n : ℕ} (A B : Op n) :
    selfAdjointDilation (A - B) = selfAdjointDilation A - selfAdjointDilation B := by
  ext i j
  simp only [selfAdjointDilation, Matrix.submatrix_apply, Matrix.sub_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks]

/-- The self-adjoint dilation distributes over addition:
    H_{A+B} = H_A + H_B. -/
lemma selfAdjointDilation_add {n : ℕ} (A B : Op n) :
    selfAdjointDilation (A + B) = selfAdjointDilation A + selfAdjointDilation B := by
  ext i j
  simp only [selfAdjointDilation, Matrix.submatrix_apply, Matrix.add_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks]

/-!
## Block Map

The block map `id₂ ⊗ Φ` applies a map Φ independently to each n×n block
of a (n+n)×(n+n) matrix. When the input is a 2×2 block matrix
[A₁₁, A₁₂; A₂₁, A₂₂], the output is [Φ(A₁₁), Φ(A₁₂); Φ(A₂₁), Φ(A₂₂)].
-/

/-- Extract the (i,j) block of a (n+n)×(n+n) matrix, where i,j ∈ {0,1}.

    Block (i,j) is the n×n submatrix at rows [i·n, (i+1)·n) and columns [j·n, (j+1)·n). -/
def extractBlock {n : ℕ} (X : Op (n + n)) (bi bj : Fin 2) : Op n :=
  Matrix.of fun i j =>
    X (finSumFinEquiv (if bi = 0 then Sum.inl i else Sum.inr i))
      (finSumFinEquiv (if bj = 0 then Sum.inl j else Sum.inr j))

/-- The block map `id₂ ⊗ Φ`: applies Φ independently to each n×n block of
    a (n+n)×(n+n) matrix.

    For X with 2×2 block decomposition [A₁₁, A₁₂; A₂₁, A₂₂]:
      blockMap Φ X = [Φ(A₁₁), Φ(A₁₂); Φ(A₂₁), Φ(A₂₂)] -/
def blockMap {n m : ℕ} (Φ : Op n → Op m) (X : Op (n + n)) : Op (m + m) :=
  (Matrix.fromBlocks
    (Φ (extractBlock X 0 0))
    (Φ (extractBlock X 0 1))
    (Φ (extractBlock X 1 0))
    (Φ (extractBlock X 1 1))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-!
## Key Lemmas (helper lemmas for the dilation argument)
-/

/-- H_A† · H_A = H_A² = reindex of block diagonal [A·A†, 0; 0, A†·A]. -/
private lemma conjTranspose_mul_self_dilation {n : ℕ} (A : Op n) :
    (selfAdjointDilation A).conjTranspose * selfAdjointDilation A =
      (Matrix.fromBlocks (A * A.conjTranspose) 0 0 (A.conjTranspose * A)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  -- H_A† = H_A (Hermitian), so H_A† * H_A = H_A * H_A
  have hH := selfAdjointDilation_isHermitian A
  rw [hH.eq]
  -- H_A * H_A via submatrix_mul_equiv
  simp only [selfAdjointDilation]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  -- fromBlocks multiplication: [0,A;A†,0] * [0,A;A†,0] = [A·A†,0;0,A†·A]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Charpoly of H_A†·H_A factors as charpoly(A†·A)². -/
private lemma charpoly_conjTranspose_mul_self_dilation {n : ℕ} (A : Op n) :
    ((selfAdjointDilation A).conjTranspose * selfAdjointDilation A).charpoly =
      (A.conjTranspose * A).charpoly * (A.conjTranspose * A).charpoly := by
  rw [conjTranspose_mul_self_dilation]
  -- submatrix with equiv preserves charpoly (= reindex)
  rw [show (Matrix.fromBlocks (A * A.conjTranspose) 0 0 (A.conjTranspose * A)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (A * A.conjTranspose) 0 0 (A.conjTranspose * A))
    from rfl]
  rw [Matrix.charpoly_reindex]
  -- Block diagonal charpoly = product of charpolys
  rw [Matrix.charpoly_fromBlocks_zero₂₁]
  -- charpoly(A·A†) = charpoly(A†·A) by charpoly_mul_comm
  rw [Matrix.charpoly_mul_comm A A.conjTranspose]

/-- Eigenvalue multiset of H_A†·H_A equals doubled eigenvalue multiset of A†·A.

    Since charpoly(H_A†·H_A) = charpoly(A†·A)², the roots (= eigenvalues for
    Hermitian matrices) of the larger matrix are the roots of the smaller, doubled. -/
private lemma eigenvalues_dilation_eq_doubled {n : ℕ} [NeZero n] (A : Op n)
    (hHH : ((selfAdjointDilation A).conjTranspose * selfAdjointDilation A).IsHermitian)
    (hAA : (A.conjTranspose * A).IsHermitian) :
    Multiset.map hHH.eigenvalues Finset.univ.val =
      Multiset.map hAA.eigenvalues Finset.univ.val +
      Multiset.map hAA.eigenvalues Finset.univ.val := by
  have h_roots_HH := hHH.roots_charpoly_eq_eigenvalues
  have h_roots_AA := hAA.roots_charpoly_eq_eigenvalues
  have h_cp := charpoly_conjTranspose_mul_self_dilation A
  have h_cp_ne : (A.conjTranspose * A).charpoly * (A.conjTranspose * A).charpoly ≠ 0 :=
    mul_ne_zero (A.conjTranspose * A).charpoly_monic.ne_zero
      (A.conjTranspose * A).charpoly_monic.ne_zero
  have h_roots_prod : ((A.conjTranspose * A).charpoly * (A.conjTranspose * A).charpoly).roots =
      (A.conjTranspose * A).charpoly.roots + (A.conjTranspose * A).charpoly.roots :=
    Polynomial.roots_mul h_cp_ne
  have h_complex_eq :
      Multiset.map (RCLike.ofReal (K := ℂ) ∘ hHH.eigenvalues) Finset.univ.val =
        Multiset.map (RCLike.ofReal (K := ℂ) ∘ hAA.eigenvalues) Finset.univ.val +
        Multiset.map (RCLike.ofReal (K := ℂ) ∘ hAA.eigenvalues) Finset.univ.val := by
    rw [← h_roots_HH, h_cp, h_roots_prod, h_roots_AA]
  apply Multiset.map_injective Complex.ofReal_injective
  simp only [Multiset.map_add, Multiset.map_map]
  exact h_complex_eq

/-- **Trace norm of the self-adjoint dilation**: ‖H_A‖₁ = 2·‖A‖₁.

    The eigenvalues of H_A = [0,A;A†,0] are ±σᵢ(A) where σᵢ are the singular
    values of A. So ‖H_A‖₁ = Σᵢ(σᵢ + σᵢ) = 2·Σᵢ σᵢ = 2·‖A‖₁.

    Proof: H_A†·H_A = block_diag(A·A†, A†·A), so charpoly(H_A†·H_A) = charpoly(A†·A)².
    The eigenvalue multiset doubles, giving
    ∑ √(eigenvalues of H_A†·H_A) = 2·∑ √(eigenvalues of A†·A). -/
lemma traceNorm_selfAdjointDilation {n : ℕ} [NeZero n] (A : Op n) :
    traceNorm (selfAdjointDilation A) = 2 * traceNorm A := by
  -- Unfold traceNorm and name Hermiticity proofs
  simp only [traceNorm]
  set hHH : ((selfAdjointDilation A).conjTranspose * selfAdjointDilation A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  set hAA : (A.conjTranspose * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  -- Get the eigenvalue multiset doubling
  have h_ms := eigenvalues_dilation_eq_doubled A hHH hAA
  -- Convert goal to multiset form, prove using h_ms
  rw [show (∑ i, Real.sqrt (hHH.eigenvalues i)) =
      Multiset.sum (Multiset.map (Real.sqrt ∘ hHH.eigenvalues) Finset.univ.val)
    from (Finset.sum_map_val ..).symm]
  rw [show (∑ i, Real.sqrt (hAA.eigenvalues i)) =
      Multiset.sum (Multiset.map (Real.sqrt ∘ hAA.eigenvalues) Finset.univ.val)
    from (Finset.sum_map_val ..).symm]
  -- Map sqrt over the eigenvalue multiset equality and sum
  have h_sqrt := congr_arg (fun s => (Multiset.map Real.sqrt s).sum) h_ms
  simp only [Multiset.map_map, Multiset.map_add, Multiset.sum_add] at h_sqrt
  rw [h_sqrt]
  ring

private lemma extractBlock_add {n : ℕ} (X Y : Op (n + n)) (bi bj : Fin 2) :
    extractBlock (X + Y) bi bj = extractBlock X bi bj + extractBlock Y bi bj := by
  ext i j; simp [extractBlock, Matrix.of_apply, Matrix.add_apply]

private lemma extractBlock_smul {n : ℕ} (c : ℂ) (X : Op (n + n)) (bi bj : Fin 2) :
    extractBlock (c • X) bi bj = c • extractBlock X bi bj := by
  ext i j; simp [extractBlock, Matrix.of_apply, Matrix.smul_apply]

private lemma blockMap_add {n m : ℕ} (Φ : Op n → Op m) (hlin : IsLinearMap ℂ Φ)
    (X Y : Op (n + n)) :
    blockMap Φ (X + Y) = blockMap Φ X + blockMap Φ Y := by
  simp only [blockMap, extractBlock_add, hlin.1]
  rw [show (Matrix.fromBlocks
      (Φ (extractBlock X 0 0) + Φ (extractBlock Y 0 0))
      (Φ (extractBlock X 0 1) + Φ (extractBlock Y 0 1))
      (Φ (extractBlock X 1 0) + Φ (extractBlock Y 1 0))
      (Φ (extractBlock X 1 1) + Φ (extractBlock Y 1 1))) =
    Matrix.fromBlocks (Φ (extractBlock X 0 0)) (Φ (extractBlock X 0 1))
      (Φ (extractBlock X 1 0)) (Φ (extractBlock X 1 1)) +
    Matrix.fromBlocks (Φ (extractBlock Y 0 0)) (Φ (extractBlock Y 0 1))
      (Φ (extractBlock Y 1 0)) (Φ (extractBlock Y 1 1))
    from (Matrix.fromBlocks_add _ _ _ _ _ _ _ _).symm]
  simp [Matrix.submatrix_add]

private lemma blockMap_smul {n m : ℕ} (Φ : Op n → Op m) (hlin : IsLinearMap ℂ Φ)
    (c : ℂ) (X : Op (n + n)) :
    blockMap Φ (c • X) = c • blockMap Φ X := by
  simp only [blockMap, extractBlock_smul, hlin.2]
  rw [show (Matrix.fromBlocks
      (c • Φ (extractBlock X 0 0)) (c • Φ (extractBlock X 0 1))
      (c • Φ (extractBlock X 1 0)) (c • Φ (extractBlock X 1 1))) =
    c • Matrix.fromBlocks (Φ (extractBlock X 0 0)) (Φ (extractBlock X 0 1))
      (Φ (extractBlock X 1 0)) (Φ (extractBlock X 1 1))
    from (Matrix.fromBlocks_smul _ _ _ _ _).symm]
  simp [Matrix.submatrix_smul]

private lemma trace_submatrix_equiv {n m : ℕ} (M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ) :
    (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)

private lemma trace_fromBlocks {n : ℕ} (A B C D : Op n) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp only [Matrix.trace, Matrix.diag]
  rw [show (∑ i : Fin n ⊕ Fin n, (Matrix.fromBlocks A B C D) i i) =
    (∑ i : Fin n, (Matrix.fromBlocks A B C D) (Sum.inl i) (Sum.inl i)) +
    (∑ i : Fin n, (Matrix.fromBlocks A B C D) (Sum.inr i) (Sum.inr i)) from
    Fintype.sum_sum_type _]
  simp [Matrix.fromBlocks]

/-- Block-diagonal matrix: places K in both diagonal blocks of a (p+p)×(q+q) matrix. -/
private def blockDiag {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin (p + p)) (Fin (q + q)) ℂ :=
  (Matrix.fromBlocks K 0 0 K).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Block diagonal times block matrix = block matrix with K applied to each block row. -/
private lemma fromBlocks_blockDiag_mul {p q s : ℕ}
    (K : Matrix (Fin p) (Fin q) ℂ) (A B C D : Matrix (Fin q) (Fin s) ℂ) :
    Matrix.fromBlocks K 0 0 K * Matrix.fromBlocks A B C D =
      Matrix.fromBlocks (K * A) (K * B) (K * C) (K * D) := by
  rw [Matrix.fromBlocks_multiply]; simp

/-- Block matrix times block diagonal = block matrix with K applied to each block column. -/
private lemma fromBlocks_mul_blockDiag {p q s : ℕ}
    (A B C D : Matrix (Fin p) (Fin q) ℂ) (K : Matrix (Fin q) (Fin s) ℂ) :
    Matrix.fromBlocks A B C D * Matrix.fromBlocks K 0 0 K =
      Matrix.fromBlocks (A * K) (B * K) (C * K) (D * K) := by
  rw [Matrix.fromBlocks_multiply]; simp

/-- Any Op (n+n) matrix decomposes into blocks via extractBlock. -/
private lemma matrix_eq_fromBlocks_extractBlock {n : ℕ}
    (X : Op (n + n)) :
    X = (Matrix.fromBlocks
      (extractBlock X 0 0) (extractBlock X 0 1)
      (extractBlock X 1 0) (extractBlock X 1 1)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext a b
  simp only [Matrix.submatrix_apply, extractBlock]
  -- Replace a and b with finSumFinEquiv applied to their block decomposition
  conv_lhs =>
    rw [show a = finSumFinEquiv (finSumFinEquiv.symm a) from
      (finSumFinEquiv.apply_symm_apply a).symm]
    rw [show b = finSumFinEquiv (finSumFinEquiv.symm b) from
      (finSumFinEquiv.apply_symm_apply b).symm]
  rcases finSumFinEquiv.symm a with a' | a' <;>
  rcases finSumFinEquiv.symm b with b' | b' <;>
  simp [Matrix.fromBlocks, finSumFinEquiv]

private lemma blockMap_eq_kraus_sum {n m : ℕ} (Φ : Op n → Op m)
    {r : ℕ} (K : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (hK : ∀ A, Φ A = ∑ k, K k * A * (K k)†)
    (X : Op (n + n)) :
    blockMap Φ X =
      ∑ k, blockDiag (K k) * X * (blockDiag (K k))† := by
  -- Both sides are (n+n)×(n+n) matrices; prove entry-wise
  -- LHS via blockMap + Kraus, RHS via blockDiag multiplication
  -- Rewrite Φ using Kraus decomposition in blockMap
  simp only [blockMap]
  simp_rw [hK]
  -- Work on the RHS: unfold blockDiag and use block decomposition of X
  conv_rhs => rw [matrix_eq_fromBlocks_extractBlock X]
  simp only [blockDiag]
  simp_rw [Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.submatrix_mul_equiv]
  -- Apply block multiplication laws inside the sum
  simp_rw [fromBlocks_blockDiag_mul, fromBlocks_mul_blockDiag]
  -- Prove entry-wise equality
  ext a b
  -- Unfold submatrix and fromBlocks on both sides
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks]
  -- RHS: distribute sum and unfold submatrix
  -- (∑ x, M x) a b = ∑ x, M x a b
  have h_dist : ∀ (f : Fin r → Op (m + m)) (i j : Fin (m + m)),
      (∑ k, f k) i j = ∑ k, f k i j :=
    fun f i j => by
      rw [show (∑ k, f k) i = ∑ k, (f k) i from
        Finset.sum_apply i Finset.univ f]
      exact Finset.sum_apply j Finset.univ _
  rw [h_dist]
  simp only [Matrix.submatrix_apply]
  -- Case split on blocks
  rcases finSumFinEquiv.symm a with a' | a' <;>
  rcases finSumFinEquiv.symm b with b' | b' <;> (
    simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    -- Remaining: (∑ f) a' b' = ∑ f a' b' (Finset.sum_apply)
    rw [Matrix.sum_apply])

/-- Kraus decomposition from CP and linearity alone (no trace-preservation required):
    if Φ is linear and completely positive then Φ(A) = ∑_k K_k * A * K_k† for some operators K_k. -/
private lemma kraus_sum_of_cp_linear {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ_linear : IsLinearMap ℂ Φ) (hΦ_cp : IsCompletelyPositive Φ) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin m) (Fin n) ℂ),
      ∀ A, Φ A = ∑ k, K k * A * (K k)† := by
  -- Decompose PSD Choi matrix into sum of vecMulVec
  unfold IsCompletelyPositive at hΦ_cp
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hΦ_cp
  obtain ⟨r, v, hv⟩ := hΦ_cp
  -- Define Kraus operators K_k(a, i) = v_k(finProdFinEquiv(i, a))
  set K : Fin r → Matrix (Fin m) (Fin n) ℂ :=
    fun k => Matrix.of fun a i => v k (finProdFinEquiv (i, a))
  refine ⟨r, K, ?_⟩
  intro A; ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K, Matrix.of_apply]
  set E := fun i j : Fin n => Matrix.of fun r c =>
    if r = i ∧ c = j then (1:ℂ) else 0 with hE_def
  set hL := IsLinearMap.mk' Φ hΦ_linear
  have hA_decomp : A = ∑ i, ∑ j, A i j • E i j := by
    ext r c; simp only [E, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact if_neg (fun ⟨h1, _⟩ => hi h1.symm)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2.symm))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  have hΦ_entry : Φ A a b = ∑ i, ∑ j, A i j *
      ChoiMatrix n m Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
    conv_lhs => rw [hA_decomp, show Φ = hL from rfl, map_sum hL]
    simp_rw [map_sum hL, hL.map_smul, show ∀ x, (hL x : Op m) = Φ x from fun _ => rfl,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext i; congr 1; ext j
    congr 1
    simp only [E, ChoiMatrix, Matrix.of_apply, Equiv.symm_apply_apply]
  rw [hΦ_entry, hv]
  simp only [vecMulVec, Pi.star_apply]
  have h_push : ∀ i j : Fin n,
      (∑ k, Matrix.of fun x_2 y => v k x_2 * star (v k y))
        (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      ∑ k, v k (finProdFinEquiv (i, a)) * star (v k (finProdFinEquiv (j, b))) :=
    fun i j => Matrix.sum_apply _ _ Finset.univ _
  simp_rw [h_push]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have reorder : ∀ (f : Fin n → Fin n → Fin r → ℂ),
      ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ b, ∑ a, f a b k := by
    intro f
    calc ∑ a, ∑ b, ∑ k, f a b k
        = ∑ a, ∑ k, ∑ b, f a b k := by
          congr 1; ext a; exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, f a b k := Finset.sum_comm
      _ = ∑ k, ∑ b, ∑ a, f a b k := by
          congr 1; ext k; exact Finset.sum_comm
  rw [reorder]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- Complete positivity of blockMap: if Φ is CP then blockMap Φ is CP. -/
private lemma isCompletelyPositive_blockMap {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ_linear : IsLinearMap ℂ Φ) (hΦ_cp : IsCompletelyPositive Φ) :
    IsCompletelyPositive (blockMap Φ) := by
  -- Get Kraus decomposition: Φ(A) = ∑_k K_k * A * K_k† using CP + linearity only
  obtain ⟨r, K, hK⟩ := kraus_sum_of_cp_linear Φ hΦ_linear hΦ_cp
  -- Define vectors for the Choi decomposition
  let L : Fin r → Matrix (Fin (m + m)) (Fin (n + n)) ℂ := fun k => blockDiag (K k)
  let w : Fin r → Fin ((n + n) * (m + m)) → ℂ := fun k α =>
    L k (finProdFinEquiv.symm α).2 (finProdFinEquiv.symm α).1
  -- Show Choi matrix = ∑_k vecMulVec w_k (star w_k) → PSD
  unfold IsCompletelyPositive
  suffices h_eq : ChoiMatrix (n + n) (m + m) (blockMap Φ) =
      ∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k)) by
    rw [h_eq]
    exact posSemidef_sum Finset.univ (fun k _ => posSemidef_vecMulVec_self_star (w k))
  -- Same entry-wise proof as in KrausRepresentation.is_cptp, but using blockDiag Kraus operators
  have h_sum_entry : ∀ (f : Fin r → Op (m + m)) (a b : Fin (m + m)),
      (∑ k, f k) a b = ∑ k, f k a b := by
    intro f a b
    rw [show (∑ k, f k) a = ∑ k, (f k) a from Finset.sum_apply a Finset.univ f]
    exact Finset.sum_apply b Finset.univ _
  ext α β
  simp only [ChoiMatrix, Matrix.of_apply]
  -- Rewrite using blockMap = Kraus sum
  rw [blockMap_eq_kraus_sum Φ K hK]
  -- Now both sides are sums over K, match per-entry
  rw [h_sum_entry]
  -- Distribute RHS
  have h_rhs : (∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k))) α β =
      ∑ k, w k α * star (w k β) := by
    rw [show (∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k))) α =
        ∑ k, vecMulVec (w k) (star (w k)) α from Finset.sum_apply α Finset.univ _]
    rw [show (∑ k, vecMulVec (w k) (star (w k)) α) β =
        ∑ k, vecMulVec (w k) (star (w k)) α β from Finset.sum_apply β Finset.univ _]
    simp only [vecMulVec, Matrix.of_apply, Pi.star_apply]
  rw [h_rhs]
  -- Each summand: (L k * E_{ij} * (L k)†)(a,b) = L k(a,i) * star(L k(b,j))
  apply Finset.sum_congr rfl; intro k _
  simp only [L, w]
  exact mul_unitMatrix_conjTranspose_apply (blockDiag (K k)) _ _ _ _

/-- **Block map is CPTP**: If Φ is CPTP on Op n → Op m, then blockMap Φ is
    CPTP on Op (n+n) → Op (m+m).

    If Φ has Kraus representation Φ(X) = Σₖ KₖXKₖ†, then blockMap Φ has
    Kraus operators of the form [Kₖ, 0; 0, Kₖ] (= I₂ ⊗ Kₖ), giving
    (blockMap Φ)(X) = Σₖ (I₂⊗Kₖ)X(I₂⊗Kₖ)† with Σₖ(I₂⊗Kₖ)†(I₂⊗Kₖ) = I₂⊗I_n. -/
lemma blockMap_isCPTP {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) :
    IsCPTP (blockMap Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Linearity
    exact ⟨blockMap_add Φ hΦ.1, blockMap_smul Φ hΦ.1⟩
  · -- Complete positivity via Kraus decomposition
    exact isCompletelyPositive_blockMap Φ hΦ.1 hΦ.2.1
  · -- Trace preservation
    intro X
    simp only [blockMap]
    rw [trace_submatrix_equiv]
    rw [trace_fromBlocks]
    -- trace(Φ(X₀₀)) + trace(Φ(X₁₁)) = trace(X₀₀) + trace(X₁₁)
    rw [hΦ.2.2 (extractBlock X 0 0), hΦ.2.2 (extractBlock X 1 1)]
    -- trace(X₀₀) + trace(X₁₁) = trace(X)
    simp only [extractBlock, Matrix.trace, Matrix.of_apply, Matrix.diag]
    simp only [show (1 : Fin 2) ≠ 0 from by omega, ite_true, ite_false]
    rw [Fin.sum_univ_add (fun i => X i i)]
    congr 1

lemma extractBlock_dilation_eq {n : ℕ} (A : Op n) (bi bj : Fin 2) :
    extractBlock (selfAdjointDilation A) bi bj =
      Matrix.of fun i j =>
        (Matrix.fromBlocks 0 A A.conjTranspose 0)
          (if bi = 0 then Sum.inl i else Sum.inr i)
          (if bj = 0 then Sum.inl j else Sum.inr j) := by
  ext i j
  simp only [extractBlock, selfAdjointDilation, Matrix.submatrix_apply,
    Matrix.of_apply]
  congr 1 <;> exact (Equiv.symm_apply_apply finSumFinEquiv _)

lemma extractBlock_dilation_00 {n : ℕ} (A : Op n) :
    extractBlock (selfAdjointDilation A) 0 0 = 0 := by
  rw [extractBlock_dilation_eq]; ext i j
  simp [Matrix.of_apply]

lemma extractBlock_dilation_01 {n : ℕ} (A : Op n) :
    extractBlock (selfAdjointDilation A) 0 1 = A := by
  rw [extractBlock_dilation_eq]; ext i j; simp [Matrix.of_apply]

lemma extractBlock_dilation_10 {n : ℕ} (A : Op n) :
    extractBlock (selfAdjointDilation A) 1 0 = A.conjTranspose := by
  rw [extractBlock_dilation_eq]; ext i j; simp [Matrix.of_apply]

lemma extractBlock_dilation_11 {n : ℕ} (A : Op n) :
    extractBlock (selfAdjointDilation A) 1 1 = 0 := by
  rw [extractBlock_dilation_eq]; ext i j; simp [Matrix.of_apply]

/-- **Block map applied to the dilation**: (id₂ ⊗ Φ)(H_A) = H_{Φ(A)}.

    Uses Φ(A†) = Φ(A)† (from `cptp_preserves_conjTranspose`) to show the
    off-diagonal blocks match:
      Φ(A†) = Φ(A)† = (Φ(A))†

    The diagonal blocks are zero maps: Φ(0) = 0 by linearity. -/
lemma blockMap_selfAdjointDilation {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) (A : Op n) :
    blockMap Φ (selfAdjointDilation A) = selfAdjointDilation (Φ A) := by
  simp only [blockMap, extractBlock_dilation_00, extractBlock_dilation_01,
    extractBlock_dilation_10, extractBlock_dilation_11]
  -- Φ(0) = 0 by linearity
  have hΦ_zero : Φ 0 = 0 := hΦ.1.map_zero
  -- Φ(A†) = (Φ A)† by cptp_preserves_conjTranspose
  have hΦ_conj : Φ A.conjTranspose = (Φ A).conjTranspose :=
    (cptp_preserves_conjTranspose Φ hΦ A).symm
  rw [hΦ_zero, hΦ_conj]
  -- Now both sides are selfAdjointDilation (Φ A)
  rfl

/-- Block-map dilation identity for Hermitian-preserving maps.

    This is the same block computation as `blockMap_selfAdjointDilation`, but it
    only assumes that `Ψ` preserves `conjTranspose` and maps `0` to `0`. -/
lemma blockMap_selfAdjointDilation_of_preserves_conj
    {N M : ℕ}
    (Ψ : Op N → Op M)
    (hΨ_zero : Ψ 0 = 0)
    (hΨ_conj : ∀ B : Op N, Ψ B.conjTranspose = (Ψ B).conjTranspose)
    (A : Op N) :
    blockMap Ψ (selfAdjointDilation A) =
      selfAdjointDilation (Ψ A) := by
  simp only [blockMap, extractBlock_dilation_00, extractBlock_dilation_01,
    extractBlock_dilation_10, extractBlock_dilation_11]
  rw [hΨ_zero, hΨ_conj]
  rfl

/-!
## Main Reduction Theorem
-/

/-- **CPTP trace-norm contractivity (general operators)** via self-adjoint dilation.

    For any CPTP map Φ and any operator A: ‖Φ(A)‖₁ ≤ ‖A‖₁.

    Reduces to `traceNorm_cptp_contractive_hermitian` using the self-adjoint
    dilation H_A = [0,A;A†,0]:

      2·‖Φ(A)‖₁ = ‖H_{Φ(A)}‖₁              (traceNorm_selfAdjointDilation)
                = ‖(id₂⊗Φ)(H_A)‖₁           (blockMap_selfAdjointDilation)
                ≤ ‖H_A‖₁                      (Hermitian contractivity)
                = 2·‖A‖₁                      (traceNorm_selfAdjointDilation)

    Reference: Watrous (2018) Theorem 3.33, Ruskai (1994). -/
theorem traceNorm_cptp_contractive_general {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) (A : Op n) :
    traceNorm (Φ A) ≤ traceNorm A := by
  have h_contract := traceNorm_cptp_contractive_hermitian
    (blockMap Φ) (blockMap_isCPTP Φ hΦ) (selfAdjointDilation A)
    (selfAdjointDilation_isHermitian A)
  rw [blockMap_selfAdjointDilation Φ hΦ A,
    traceNorm_selfAdjointDilation A,
    traceNorm_selfAdjointDilation (Φ A)] at h_contract
  linarith

/-- **Trace norm triangle inequality** (sub version): ‖X - Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁.

    Proved via the self-adjoint dilation: H_{X-Y} = H_X - H_Y, both Hermitian.
    Then ‖H_X - H_Y‖₁ = ‖H_X + (-H_Y)‖₁ ≤ ‖H_X‖₁ + ‖-H_Y‖₁ = ‖H_X‖₁ + ‖H_Y‖₁
    and ‖H_A‖₁ = 2·‖A‖₁. -/
theorem traceNorm_sub_le {n : ℕ} [NeZero n] (X Y : Op n) :
    traceNorm (X - Y) ≤ traceNorm X + traceNorm Y := by
  have h_dil := traceNorm_selfAdjointDilation (X - Y)
  rw [selfAdjointDilation_sub, sub_eq_add_neg] at h_dil
  have hX_herm := selfAdjointDilation_isHermitian X
  have hY_herm := selfAdjointDilation_isHermitian Y
  have hNY_herm := hY_herm.neg
  have h_add_herm := hX_herm.add hNY_herm
  rw [traceNorm_hermitian_eq _ h_add_herm] at h_dil
  have h_tri := traceNormHermitian_triangle _ _ hX_herm hNY_herm
  rw [traceNormHermitian_neg _ hY_herm,
    ← traceNorm_hermitian_eq _ hX_herm,
    traceNorm_selfAdjointDilation,
    ← traceNorm_hermitian_eq _ hY_herm,
    traceNorm_selfAdjointDilation] at h_tri
  linarith

/-- The self-adjoint dilation distributes over negation:
    H_{-A} = -H_A. -/
lemma selfAdjointDilation_neg {n : ℕ} (A : Op n) :
    selfAdjointDilation (-A) = -selfAdjointDilation A := by
  ext i j
  simp only [selfAdjointDilation, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks]

/-- **Trace norm is invariant under negation**: ‖-A‖₁ = ‖A‖₁.

    Proof via self-adjoint dilation:
    2·‖-A‖₁ = ‖H_{-A}‖₁ = ‖-H_A‖₁ = ‖H_A‖₁ = 2·‖A‖₁. -/
theorem traceNorm_neg {n : ℕ} [NeZero n] (A : Op n) :
    traceNorm (-A) = traceNorm A := by
  have hH := selfAdjointDilation_isHermitian A
  have h1 := traceNorm_selfAdjointDilation (-A)
  rw [selfAdjointDilation_neg, traceNorm_hermitian_eq _ hH.neg] at h1
  rw [traceNormHermitian_neg _ hH,
    ← traceNorm_hermitian_eq _ hH,
    traceNorm_selfAdjointDilation] at h1
  linarith

/-- **Trace norm triangle inequality** (add version): ‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁. -/
theorem traceNorm_add_le {n : ℕ} [NeZero n] (A B : Op n) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  rw [show A + B = A - (-B) from (sub_neg_eq_add A B).symm]
  calc traceNorm (A - (-B)) ≤ traceNorm A + traceNorm (-B) := traceNorm_sub_le A (-B)
    _ = traceNorm A + traceNorm B := by rw [traceNorm_neg]

private lemma addNat_eq_natAdd_self {N : ℕ} (x : Fin N) :
    x.addNat N = Fin.natAdd N x := by
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

@[simp] private lemma finSumFinEquiv_symm_apply_addNat_self {N : ℕ} (x : Fin N) :
    finSumFinEquiv.symm (x.addNat N) = Sum.inr x := by
  rw [addNat_eq_natAdd_self]
  simpa using (finSumFinEquiv_symm_apply_natAdd (m := N) (x := x))

/-- Taking the conjugate transpose swaps the two `n × n` blocks
in the self-adjoint dilation. -/
private lemma selfAdjointDilation_conjTranspose_eq_submatrix_swap {n : ℕ} (A : Op n) :
    selfAdjointDilation A.conjTranspose =
      (selfAdjointDilation A).submatrix
        (((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm.trans
          (Equiv.sumComm (Fin n) (Fin n))).trans finSumFinEquiv)
        (((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm.trans
          (Equiv.sumComm (Fin n) (Fin n))).trans finSumFinEquiv) := by
  ext i j
  simp only [selfAdjointDilation, Matrix.submatrix_apply]
  rcases h_i : finSumFinEquiv.symm i with a | a <;>
    rcases h_j : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, h_i, h_j]

/-- **Trace norm of the conjugate transpose**: ‖Aᴴ‖₁ = ‖A‖₁.

    The self-adjoint dilation of `Aᴴ` is obtained from the dilation of `A`
    by swapping the two block coordinates, so the two dilations have the same
    trace norm by reindexing invariance. Since `‖H_M‖₁ = 2 · ‖M‖₁`, the same
    holds for `A` and `Aᴴ`. -/
theorem traceNorm_conjTranspose {n : ℕ} [NeZero n] (A : Op n) :
    traceNorm A.conjTranspose = traceNorm A := by
  have h_swap :
      traceNorm (selfAdjointDilation A.conjTranspose) =
        traceNorm (selfAdjointDilation A) := by
    rw [selfAdjointDilation_conjTranspose_eq_submatrix_swap]
    exact traceNorm_submatrix_equiv _ _
  linarith [traceNorm_selfAdjointDilation A.conjTranspose,
            traceNorm_selfAdjointDilation A, h_swap]

/-- Trace norm is invariant under `star` (i.e. conjugate transpose). -/
lemma traceNorm_star {k : ℕ} [NeZero k] (M : Op k) :
    traceNorm (star M) = traceNorm M := by
  rw [Matrix.star_eq_conjTranspose]; exact traceNorm_conjTranspose M

end Quantum.Metrics
