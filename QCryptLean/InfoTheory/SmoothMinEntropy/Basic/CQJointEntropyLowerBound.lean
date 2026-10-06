import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic

/-!
# CQ joint von-Neumann entropy lower bound `H(X) ≤ S(XE)`

For a normalized classical-quantum state `ρ` with classical register `X` and
quantum register dimension `n`, the joint von-Neumann entropy on `XE` is at
least the classical Shannon entropy of the classical marginal:

  `H(X) = H({p_x}) ≤ S(XE)`.

The joint density `ρ.toJointDensityOp` is block-diagonal `⊕_x ρ_x` (each block
`ρ.stateMap x` of trace `p_x = ρ.classicalMarginal x`). Its eigenvalue spectrum
is the disjoint union of the per-block spectra, so

  `S(XE) = H({λ_{x,i}})`,

and grouping the fine spectrum `{λ_{x,i}}` by the block index `x` (whose group
sums are `p_x = ∑_i λ_{x,i}`) can only decrease Shannon entropy, giving
`S(XE) ≥ H({p_x}) = H(X)`.

## Main statements

- `entropyTerm_sum_le_sum_entropyTerm`: superadditivity of `entropyTerm` over a
  finset of nonnegative values, `entropyTerm (∑ λ) ≤ ∑ entropyTerm λ`.
- `shannonEntropy_group_le`: grouping a fine nonnegative spectrum by a function
  `g` can only decrease Shannon entropy.
- `CQState.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues`: the block-diagonal
  joint eigenvalue spectrum of `ρ.toJointDensityOp`.
- `CQState.shannonEntropy_classicalMarginal_le_vonNeumannEntropy_toJointDensityOp`:
  the CQ joint-entropy lower bound `H(X) ≤ S(XE)`.

## References

- Tomamichel (2016). Quantum Information Processing with Finite Resources.
  Springer. §4.3 (CQ joint entropy decomposition).
-/

open Quantum.Operators Matrix
open Math.ClassicalEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ### Grouping inequality for Shannon entropy -/

/-- **Superadditivity of `entropyTerm`** over a finset of nonnegative values:
`entropyTerm (∑_{i ∈ s} f i) ≤ ∑_{i ∈ s} entropyTerm (f i)`.

Write `S = ∑ f i`. Each summand satisfies `0 ≤ f i ≤ S`, so `log (f i) ≤ log S`
(or `f i = 0`), hence `f i · log (f i) ≤ f i · log S`; summing gives
`∑ f i · log (f i) ≤ S · log S`, i.e. the claim after negating. -/
lemma entropyTerm_sum_le_sum_entropyTerm {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    entropyTerm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, entropyTerm (f i) := by
  set S := ∑ i ∈ s, f i with hS
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg hf
  have hle : ∀ i ∈ s, f i ≤ S :=
    fun i hi => Finset.single_le_sum hf hi
  -- `∑ f i · log (f i) ≤ S · log S`.
  have key : ∑ i ∈ s, f i * Real.log (f i) ≤ S * Real.log S := by
    have hpt : ∀ i ∈ s, f i * Real.log (f i) ≤ f i * Real.log S := by
      intro i hi
      rcases eq_or_lt_of_le (hf i hi) with hfi | hfi
      · simp [← hfi]
      · exact mul_le_mul_of_nonneg_left
          (Real.log_le_log hfi (hle i hi)) (le_of_lt hfi)
    calc ∑ i ∈ s, f i * Real.log (f i)
        ≤ ∑ i ∈ s, f i * Real.log S := Finset.sum_le_sum hpt
      _ = (∑ i ∈ s, f i) * Real.log S := by rw [Finset.sum_mul]
      _ = S * Real.log S := by rw [← hS]
  -- Negate and rewrite via `entropyTerm = -(· * log ·)`.
  rw [entropyTerm_eq_neg_mul_log]
  rw [Finset.sum_congr rfl (fun i _ => entropyTerm_eq_neg_mul_log (f i)),
      Finset.sum_neg_distrib]
  linarith

/-- **Grouping reduces Shannon entropy.** For nonnegative `f : Fin N → ℝ` and a
grouping map `g : Fin N → Fin m`, the coarse-grained distribution
`y ↦ ∑_{g i = y} f i` has Shannon entropy at most that of `f`:

  `H ({∑_{g i = y} f i}) ≤ H (f)`. -/
lemma shannonEntropy_group_le {N m : ℕ} (f : Fin N → ℝ) (g : Fin N → Fin m)
    (hf : ∀ i, 0 ≤ f i) :
    shannonEntropy (fun y : Fin m => ∑ i ∈ Finset.univ.filter (g · = y), f i) ≤
      shannonEntropy f := by
  unfold shannonEntropy
  -- Fiber the fine sum over the group index `g`.
  have hfiber :
      ∑ i : Fin N, entropyTerm (f i) =
        ∑ y : Fin m, ∑ i ∈ Finset.univ.filter (g · = y), entropyTerm (f i) :=
    (Finset.sum_fiberwise Finset.univ g _).symm
  rw [hfiber]
  apply Finset.sum_le_sum
  intro y _
  exact entropyTerm_sum_le_sum_entropyTerm _ f (fun i _ => hf i)

/-! ### Block-diagonal joint eigenvalue spectrum -/

/-- Eigenvalues of the `x`-th block `ρ.stateMap x` of a CQ state, as a function
`Fin n → ℝ`. -/
def CQState.blockEigenvalues {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) : Fin n → ℝ :=
  (ρ.stateMap x).isHermitian.eigenvalues

/-- The block eigenvalues are nonnegative (each block is PSD). -/
lemma CQState.blockEigenvalues_nonneg {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) (i : Fin n) :
    0 ≤ ρ.blockEigenvalues x i :=
  (Quantum.Operators.posSemidefOp_implies_mathlib
    (ρ.stateMap x).toPosSemidefOp).eigenvalues_nonneg i

/-- The block eigenvalues of `ρ.stateMap x` sum to its trace `p_x`. -/
lemma CQState.sum_blockEigenvalues_eq_classicalMarginal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) :
    ∑ i, ρ.blockEigenvalues x i = ρ.classicalMarginal x := by
  have h := (ρ.stateMap x).isHermitian.trace_eq_sum_eigenvalues
  have hre : (ρ.stateMap x).toOp.trace.re = ∑ i, ρ.blockEigenvalues x i := by
    rw [h]
    simp only [Complex.re_sum]
    rfl
  rw [← hre]
  rfl

/-- The block-diagonal joint eigenvalue spectrum of a normalized CQ state:
the eigenvalue indexed by `k ↦ (i, x)` is the `i`-th eigenvalue of block
`ρ.stateMap x`. -/
def CQState.jointEigenvalues {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) : Fin (n * Fintype.card X) → ℝ :=
  fun k => ρ.blockEigenvalues ((cqJointEquiv X n).symm k).2 ((cqJointEquiv X n).symm k).1

/-- **Block-diagonal joint eigenvalue spectrum.** `ρ.jointEigenvalues` is a valid
eigenvalue spectrum of `ρ.toJointDensityOp`.

The block-diagonal joint operator equals `(blockDiagonal U)ᴴ · (blockDiagonal D) ·
(blockDiagonal U)` where `U x` is the eigenvector unitary of block `ρ.stateMap x`
and `D x = diagonal (block eigenvalues)`. Block-diagonality is a ring/`*`-homomorphism
(`Matrix.blockDiagonal_mul`, `Matrix.blockDiagonal_conjTranspose`,
`Matrix.blockDiagonal_diagonal`), and the joint reindexing carries this through to a
`Fin (n * card X)`-diagonalization. -/
theorem CQState.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    IsEigenvalueSpectrum (ρ.toJointDensityOp hρ_norm) ρ.jointEigenvalues := by
  classical
  set e := cqJointEquiv X n with he
  -- eigenvector unitaries and diagonal blocks
  let U : X → Matrix (Fin n) (Fin n) ℂ :=
    fun x => ((ρ.stateMap x).isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let D : X → Matrix (Fin n) (Fin n) ℂ :=
    fun x => Matrix.diagonal (fun i => (ρ.blockEigenvalues x i : ℂ))
  -- spectral decomposition of each block: ρ_x = U_x D_x U_xᴴ
  have hblock_spec : ∀ x, (ρ.stateMap x).toOp = U x * D x * (U x)ᴴ := by
    intro x
    have hsp := (ρ.stateMap x).isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at hsp
    simpa [U, D, CQState.blockEigenvalues, Function.comp] using hsp
  have hUU : ∀ x, U x * (U x)ᴴ = 1 := by
    intro x
    exact_mod_cast (ρ.stateMap x).isHermitian.eigenvectorUnitary.2.2
  have hUU' : ∀ x, (U x)ᴴ * U x = 1 := by
    intro x
    exact_mod_cast (ρ.stateMap x).isHermitian.eigenvectorUnitary.2.1
  -- block-diagonal operator factorization
  have hblockdiag :
      Matrix.blockDiagonal (fun x => (ρ.stateMap x).toOp) =
        (Matrix.blockDiagonal U) * (Matrix.blockDiagonal D) *
          (Matrix.blockDiagonal U)ᴴ := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
        ← Matrix.blockDiagonal_mul]
    exact congrArg Matrix.blockDiagonal (funext hblock_spec)
  -- nonnegativity / sum / ≤1 of the joint spectrum
  refine ⟨?nonneg, ?sumone, ?leone, ?spec⟩
  case nonneg =>
    intro k
    exact ρ.blockEigenvalues_nonneg _ _
  case sumone =>
    -- ∑_k jointEigs k = ∑_x ∑_i blockEigs = ∑_x p_x = 1
    have h1 : ∑ k, ρ.jointEigenvalues k
        = ∑ p : Fin n × X, ρ.blockEigenvalues p.2 p.1 := by
      rw [← Equiv.sum_comp e.symm (fun p : Fin n × X => ρ.blockEigenvalues p.2 p.1)]
      rfl
    rw [h1, Fintype.sum_prod_type_right]
    have : ∀ x : X, ∑ i, ρ.blockEigenvalues x i = (ρ.stateMap x).trace :=
      fun x => ρ.sum_blockEigenvalues_eq_classicalMarginal x
    simp_rw [this]
    exact hρ_norm
  case leone =>
    intro k
    -- each eigenvalue ≤ its block trace ≤ joint trace = 1
    have hk_nonneg : ∀ j, 0 ≤ ρ.blockEigenvalues (e.symm k).2 j :=
      fun j => ρ.blockEigenvalues_nonneg _ j
    have hsingle : ρ.jointEigenvalues k ≤ ∑ j, ρ.blockEigenvalues (e.symm k).2 j :=
      Finset.single_le_sum (fun j _ => hk_nonneg j) (Finset.mem_univ _)
    have hblock_le : ∑ j, ρ.blockEigenvalues (e.symm k).2 j ≤ 1 := by
      rw [ρ.sum_blockEigenvalues_eq_classicalMarginal (e.symm k).2]
      calc (ρ.stateMap (e.symm k).2).trace
          ≤ ∑ x : X, (ρ.stateMap x).trace :=
            Finset.single_le_sum
              (fun x _ => (ρ.stateMap x).trace_nonneg) (Finset.mem_univ _)
        _ = 1 := hρ_norm
    exact le_trans hsingle hblock_le
  case spec =>
    -- V := reindex e e ((blockDiagonal U)ᴴ); then V† D' V = toJointDensityOp,
    -- where D' = diagonal (jointEigs).
    refine ⟨Matrix.reindex e e ((Matrix.blockDiagonal U)ᴴ), ?_, ?_, ?_⟩
    · -- V† * V = 1
      rw [Matrix.conjTranspose_reindex]
      simp only [Matrix.conjTranspose_conjTranspose, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv]
      rw [show Matrix.blockDiagonal U * (Matrix.blockDiagonal U)ᴴ
            = Matrix.blockDiagonal (fun x => U x * (U x)ᴴ) by
            rw [Matrix.blockDiagonal_conjTranspose, Matrix.blockDiagonal_mul]]
      simp_rw [hUU]
      rw [show (fun _ : X => (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : X → Matrix (Fin n) (Fin n) ℂ)
            from rfl, Matrix.blockDiagonal_one]
      simp
    · -- V * V† = 1
      rw [Matrix.conjTranspose_reindex]
      simp only [Matrix.conjTranspose_conjTranspose, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv]
      rw [show (Matrix.blockDiagonal U)ᴴ * Matrix.blockDiagonal U
            = Matrix.blockDiagonal (fun x => (U x)ᴴ * U x) by
            rw [Matrix.blockDiagonal_conjTranspose, Matrix.blockDiagonal_mul]]
      simp_rw [hUU']
      rw [show (fun _ : X => (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : X → Matrix (Fin n) (Fin n) ℂ)
            from rfl, Matrix.blockDiagonal_one]
      simp
    · -- toJointDensityOp.toOp = V† * diagonal jointEigs * V
      change ρ.toJointDensity.toOp = _
      rw [ρ.toJointDensity_toOp_eq_reindex_blockDiagonal]
      rw [hblockdiag]
      -- diagonal (jointEigs) = reindex e e (blockDiagonal D)
      have hdiag : Matrix.diagonal (fun k => (ρ.jointEigenvalues k : ℂ)) =
          Matrix.reindex e e (Matrix.blockDiagonal D) := by
        rw [show Matrix.blockDiagonal D
              = Matrix.diagonal (fun p : Fin n × X =>
                  (ρ.blockEigenvalues p.2 p.1 : ℂ)) from
            Matrix.blockDiagonal_diagonal _]
        rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
        rfl
      rw [hdiag, Matrix.conjTranspose_reindex]
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, he]
      rfl

/-- **CQ joint von-Neumann entropy lower bound** `H(X) ≤ S(XE)`.

For a normalized CQ state `ρ` with classical register `Fin k` and quantum register
dimension `n`, the joint von-Neumann entropy is at least the classical Shannon
entropy of the classical marginal. -/
theorem CQState.shannonEntropy_classicalMarginal_le_vonNeumannEntropy_toJointDensityOp
    {k n : ℕ} [NeZero n] [NeZero (n * Fintype.card (Fin k))]
    (ρ : CQState (Fin k) n) (hρ_norm : ∑ x : Fin k, (ρ.stateMap x).trace = 1) :
    shannonEntropy ρ.classicalMarginal ≤
      vonNeumannEntropy (ρ.toJointDensityOp hρ_norm) := by
  classical
  -- S(XE) = H(jointEigs)
  rw [vonNeumannEntropy_eq_shannonEntropy (ρ.toJointDensityOp hρ_norm)
        ρ.jointEigenvalues
        (ρ.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues hρ_norm)]
  -- Group jointEigs by the classical index; group sums recover p_x.
  set e := cqJointEquiv (Fin k) n with he
  -- the grouping map: k' ↦ classical index of e.symm k'
  set g : Fin (n * Fintype.card (Fin k)) → Fin k := fun k' => (e.symm k').2 with hg
  have hjoint_nonneg : ∀ k', 0 ≤ ρ.jointEigenvalues k' :=
    fun k' => ρ.blockEigenvalues_nonneg _ _
  -- coarse-grained distribution equals the classical marginal
  have hgroup : ∀ x : Fin k,
      ∑ k' ∈ Finset.univ.filter (g · = x), ρ.jointEigenvalues k' =
        ρ.classicalMarginal x := by
    intro x
    have hbij :
        ∑ k' ∈ Finset.univ.filter (g · = x), ρ.jointEigenvalues k' =
          ∑ i : Fin n, ρ.blockEigenvalues x i := by
      refine Finset.sum_nbij' (fun k' => (e.symm k').1)
        (fun i => e (i, x)) ?_ ?_ ?_ ?_ ?_
      · intro k' _
        exact Finset.mem_univ _
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg, Equiv.symm_apply_apply]
      · intro k' hk'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg] at hk'
        simp only [← hk', Prod.mk.eta, Equiv.apply_symm_apply]
      · intro i _
        simp only [Equiv.symm_apply_apply]
      · intro k' hk'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg] at hk'
        simp only [CQState.jointEigenvalues]
        rw [hk']
    rw [hbij, ρ.sum_blockEigenvalues_eq_classicalMarginal x]
  -- apply the grouping inequality, with classical index already in `Fin k`
  have hkey := shannonEntropy_group_le (m := k)
    ρ.jointEigenvalues g hjoint_nonneg
  calc shannonEntropy ρ.classicalMarginal
      = shannonEntropy
          (fun x : Fin k => ∑ k' ∈ Finset.univ.filter (g · = x),
            ρ.jointEigenvalues k') :=
        shannonEntropy_congr _ _ (fun x => (hgroup x).symm)
    _ ≤ shannonEntropy ρ.jointEigenvalues := hkey

end InfoTheory.SmoothMinEntropy

end
