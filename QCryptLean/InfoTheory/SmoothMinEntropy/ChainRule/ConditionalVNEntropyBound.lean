import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Conditional von Neumann entropy bound `H(AB) − H(B) ≤ log dX`

This module isolates the named lemma chain behind the conditional-entropy upper
bound used by `cqConditionalVNEntropy_le_log_alphabet` in
the symmetric-subspace AEP development.

For `σ_XB : DensityOp (dX * dB)` with marginals

* `ρA := DensityOp.partialTraceB σ_XB : DensityOp dX`  (the X/A-marginal),
* `ρB := DensityOp.partialTraceA σ_XB : DensityOp dB`  (the B-marginal),

the standard chain is `H(A|B) = H(AB) − H(B) ≤ H(A) ≤ log dim A = log dX`.
Subadditivity `H(σ_XB) ≤ H(ρA) + H(ρB)` is the non-negativity of the quantum
relative entropy `relativeEntropyReal σ_XB (ρA.tensor ρB) ≥ 0` (Klein), which
this file derives from two deep leaves and the support form of Klein's
inequality (`InfoTheory.RelativeEntropy.klein_inequality_support`).

## Layout

* `traceProductLogSigma_tensor_marginal` — DEEP LEAF (1), PROVED.
* `tensor_marginal_klein_support` — DEEP LEAF (2), PROVED.
* `vonNeumannEntropy_le_partialTrace_add` — PROVED subadditivity reduction.
* `conditionalVNEntropy_le_log_dim` — PROVED conditional-entropy bound.

All leaves are now proved; this module is `sorry`-free.
-/

open Quantum.Operators Quantum.TensorProducts
open InfoTheory.RelativeEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.VonNeumannEntropy

/-!
## Real-polynomial functional calculus helpers (for leaf (1a))

Low-level matrix lemmas: applying a real polynomial to a unitary-conjugated diagonal
operator conjugates the pointwise-`eval` diagonal, and the polynomial-weighted spectral
diagonal sum equals the *basis-free* real trace `Re Tr(ρ · p(σ))`. Composing with a
Lagrange interpolant of `Real.log` over the (finite) spectrum yields basis independence
of `traceProductLogSigma`.
-/

/-- Applying a real polynomial to `U† diag(μ) U` conjugates the pointwise-`eval`
    diagonal: `p(U† diag(μ) U) = U† diag(fun i => eval (μ i) p) U`. -/
lemma aeval_unitaryConjDiagonal {n : ℕ} (U : Op n) (μ : Fin n → ℝ)
    (hUL : U† * U = 1) (hUR : U * U† = 1) (p : Polynomial ℝ) :
    (Polynomial.aeval (U† * Matrix.diagonal (fun i => (μ i : ℂ)) * U)) p
      = U† * Matrix.diagonal (fun i => ((Polynomial.eval (μ i) p : ℝ) : ℂ)) * U := by
  induction p using Polynomial.induction_on with
  | C r =>
      rw [Polynomial.aeval_C]
      simp only [Polynomial.eval_C]
      have hdiag : algebraMap ℝ (Op n) r
          = Matrix.diagonal (fun _ : Fin n => ((r : ℝ) : ℂ)) := by
        ext i j
        rw [Matrix.algebraMap_matrix_apply]
        by_cases h : i = j <;>
          simp [h, Complex.coe_algebraMap]
      rw [← hdiag]
      rw [mul_assoc, Algebra.commutes r U, ← mul_assoc, hUL, one_mul]
  | add p q hp hq =>
      rw [map_add, hp, hq]
      have hsplit :
          Matrix.diagonal (fun i => ((Polynomial.eval (μ i) (p + q) : ℝ) : ℂ))
            = Matrix.diagonal (fun i => ((Polynomial.eval (μ i) p : ℝ) : ℂ))
              + Matrix.diagonal (fun i => ((Polynomial.eval (μ i) q : ℝ) : ℂ)) := by
        ext i j
        by_cases h : i = j
        · subst h
          simp [Matrix.add_apply, Matrix.diagonal_apply_eq, Polynomial.eval_add]
        · simp [Matrix.add_apply, Matrix.diagonal_apply_ne, h]
      rw [hsplit, mul_add, add_mul]
  | monomial k r ih =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, ih]
      have hregroup :
          (U† * Matrix.diagonal
              (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ)) * U)
              * (U† * Matrix.diagonal (fun i => (μ i : ℂ)) * U)
            = U† * (Matrix.diagonal
                (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ))
                * Matrix.diagonal (fun i => (μ i : ℂ))) * U := by
        calc (U† * Matrix.diagonal
                (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ)) *
                    U)
                * (U† * Matrix.diagonal (fun i => (μ i : ℂ)) * U)
            = U† * Matrix.diagonal
                (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ))
                * (U * U†) * Matrix.diagonal (fun i => (μ i : ℂ)) * U := by noncomm_ring
          _ = U† * (Matrix.diagonal
                (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ))
                * Matrix.diagonal (fun i => (μ i : ℂ))) * U := by rw [hUR]; noncomm_ring
      have hfun :
          (fun i => ((Polynomial.eval (μ i) (Polynomial.C r * Polynomial.X ^ k) : ℝ) : ℂ)
              * (μ i : ℂ))
            = (fun i => ((Polynomial.eval (μ i)
                  (Polynomial.C r * Polynomial.X ^ k * Polynomial.X) : ℝ) : ℂ)) := by
        funext i
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
          Polynomial.eval_X]
        push_cast
        ring
      rw [hregroup, Matrix.diagonal_mul_diagonal, hfun]

/-- The polynomial-weighted spectral diagonal sum equals the basis-free real trace
    `Re Tr(ρ · p(σ))` for `σ = U† diag(μ) U`. The right-hand side depends only on `σ`
    and `p`, not on the diagonalizing pair `(U, μ)`. -/
lemma weightedDiag_eq_traceProductAeval {n : ℕ} [NeZero n] (ρ : DensityOp n) (U : Op n)
    (μ : Fin n → ℝ) (p : Polynomial ℝ) (hUL : U† * U = 1) (hUR : U * U† = 1) :
    ∑ i, ((U * ρ.toOp * U†) i i).re * Polynomial.eval (μ i) p
      = (Matrix.trace (ρ.toOp *
          (Polynomial.aeval (U† * Matrix.diagonal (fun i => (μ i : ℂ)) * U)) p)).re := by
  rw [aeval_unitaryConjDiagonal U μ hUL hUR p]
  set N := U * ρ.toOp * U† with hN
  set D := Matrix.diagonal (fun i => ((Polynomial.eval (μ i) p : ℝ) : ℂ)) with hD
  have e1 : (ρ.toOp * (U† * D * U)).trace = (N * D).trace := by
    rw [show ρ.toOp * (U† * D * U) = (ρ.toOp * U† * D) * U by noncomm_ring]
    rw [Matrix.trace_mul_comm]
    rw [show U * (ρ.toOp * U† * D) = (U * ρ.toOp * U†) * D by noncomm_ring, ← hN]
  rw [e1]
  have e2 : (N * D).trace = ∑ i, N i i * ((Polynomial.eval (μ i) p : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD, Matrix.diagonal_apply_eq]
    · intro j _ hj
      rw [hD, Matrix.diagonal_apply_ne _ hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [e2, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-!
## Sub-decomposition of leaf (1)

Leaf (1) (`traceProductLogSigma_tensor_marginal`) is not a one-shot: the value of
`traceProductLogSigma ρ σ` is pinned to the `Classical.choose` spectral
decomposition `eigenbasisOf σ`/`eigenvaluesOf σ` of `σ`, but to evaluate it for
`σ = ρA ⊗ ρB` one must move to the *product* diagonalizing unitary `V_A ⊗ V_B`
with product eigenvalues `λ_i · μ_j`. We carve leaf (1) into:

* `traceProductLogSigma_basis_indep` — **load-bearing leaf (1a)**:
  basis-independence of `traceProductLogSigma`, the genuinely deep + reusable piece.
* `marginalProductBasis_diagonal_fold_A/_B` — **leaf (1b)**: partial-trace
  adjunction in eigenbasis (the joint diagonal folded over one factor is the
  marginal diagonal).
* `traceProductLogSigma_tensor_marginal` — **PROVED assembly (1c)**: instantiates
  (1a) at the product unitary/eigenvalues (the witness constructed exactly as in
  `vonNeumannEntropy_tensor_additive`'s `case spec`), splits `log(λ_i μ_j)` (zero
  indices killed by non-negativity + the fold), and folds each half with (1b).
-/

/-- **Load-bearing leaf (1a) — basis-independence of `traceProductLogSigma`.**

    `traceProductLogSigma ρ σ` is *defined* via the project's
    `Classical.choose` spectral data `eigenbasisOf σ`/`eigenvaluesOf σ`, but it is a
    genuine trace `Tr(ρ · log σ)` and so does not depend on *which* diagonalizing
    pair is used. Concretely: for any unitary `W` (`W† W = 1`, `W W† = 1`) and
    non-negative `ν` with `σ.toOp = W† · diag(ν) · W` (the project's
    `IsEigenvalueSpectrum` orientation, cf. `eigenvaluesOf_spec`),

    `traceProductLogSigma ρ σ = ∑ i, (W · ρ.toOp · W†)ᵢᵢ.re · Real.log (ν i)`.

    Both sides equal `(Tr(ρ.toOp · f(σ.toOp))).re` for `f = Real.log`, by the
    spectral-mapping uniqueness of `W† diag(log ν) W` (independent of the chosen
    `(W, ν)`). Taking `W = eigenbasisOf σ`, `ν = eigenvaluesOf σ` recovers the
    definition; the content is that *any* valid spectral pair gives the same value.

    This is the reusable piece; it also unblocks leaf (2) (`tensor_marginal_klein_support`). -/
theorem traceProductLogSigma_basis_indep {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) (W : Op n) (ν : Fin n → ℝ)
    (_hW_left : W† * W = 1) (_hW_right : W * W† = 1)
    (_hν_nonneg : ∀ i, 0 ≤ ν i)
    (_hspec : σ.toOp = W† * Matrix.diagonal (fun i => (ν i : ℂ)) * W) :
    traceProductLogSigma ρ σ =
      ∑ i, ((W * ρ.toOp * W†) i i).re * Real.log (ν i) := by
  classical
  -- canonical spectral decomposition of σ
  have hVspec : σ.toOp =
      (eigenbasisOf σ)† * Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * (eigenbasisOf σ) :=
    (Classical.choose_spec (eigenvaluesOf_spec σ).2.2.2).2.2
  -- Lagrange interpolant of `Real.log` over the (finite) spectrum: nodes = both spectra.
  set S : Finset ℝ :=
    Finset.image (eigenvaluesOf σ) Finset.univ ∪ Finset.image ν Finset.univ with hS
  set p : Polynomial ℝ := (Lagrange.interpolate S id) (fun x => Real.log x) with hp
  have hinj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have heval : ∀ x ∈ S, Polynomial.eval x p = Real.log x := by
    intro x hx
    have h := Lagrange.eval_interpolate_at_node (s := S) (v := (id : ℝ → ℝ))
      (fun x => Real.log x) hinj hx
    simpa [hp] using h
  have heval_evσ : ∀ i, Polynomial.eval (eigenvaluesOf σ i) p = Real.log (eigenvaluesOf σ i) := by
    intro i
    exact heval _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have heval_ν : ∀ i, Polynomial.eval (ν i) p = Real.log (ν i) := by
    intro i
    exact heval _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  -- LHS: rewrite `log` as `eval p` and fold into the basis-free trace form.
  have hLHS : traceProductLogSigma ρ σ =
      (Matrix.trace (ρ.toOp *
        (Polynomial.aeval ((eigenbasisOf σ)† *
          Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * (eigenbasisOf σ))) p)).re := by
    rw [← weightedDiag_eq_traceProductAeval ρ (eigenbasisOf σ) (eigenvaluesOf σ) p
          (eigenbasisOf_unitary_left σ) (eigenbasisOf_unitary_right σ)]
    unfold traceProductLogSigma diagonalOfRhoInSigmaBasis
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [heval_evσ i]
  -- RHS: same, in the given basis.
  have hRHS : (∑ i, ((W * ρ.toOp * W†) i i).re * Real.log (ν i)) =
      (Matrix.trace (ρ.toOp *
        (Polynomial.aeval (W† * Matrix.diagonal (fun i => (ν i : ℂ)) * W)) p)).re := by
    rw [← weightedDiag_eq_traceProductAeval ρ W ν p _hW_left _hW_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [heval_ν i]
  rw [hLHS, hRHS, ← hVspec, ← _hspec]

/-- The product diagonalizing unitary `V_A ⊗ V_B` of the marginals of `σ_XB`,
    where `V_A := eigenbasisOf (partialTraceB σ_XB)` and
    `V_B := eigenbasisOf (partialTraceA σ_XB)` diagonalize the A- and B-marginals. -/
def marginalProductBasis {dX dB : ℕ} (σ_XB : DensityOp (dX * dB)) : Op (dX * dB) :=
  Op.tensor (eigenbasisOf (DensityOp.partialTraceB σ_XB))
            (eigenbasisOf (DensityOp.partialTraceA σ_XB))

/-- The product eigenvalues `λ_i · μ_j` of `ρA ⊗ ρB` for the marginals of `σ_XB`,
    indexed through `finProdFinEquiv` (matching `vonNeumannEntropy_tensor_additive`). -/
def marginalProductEigs {dX dB : ℕ} (σ_XB : DensityOp (dX * dB)) : Fin (dX * dB) → ℝ :=
  fun k =>
    eigenvaluesOf (DensityOp.partialTraceB σ_XB) (finProdFinEquiv.symm k).1 *
      eigenvaluesOf (DensityOp.partialTraceA σ_XB) (finProdFinEquiv.symm k).2

/-- The joint diagonal of `σ_XB` in the product eigenbasis `V_A ⊗ V_B`, at the
    paired index `(i, j)`: `(V σ_XB V†)_{(i,j),(i,j)}.re`. -/
def marginalJointDiag {dX dB : ℕ} (σ_XB : DensityOp (dX * dB))
    (p : Fin dX × Fin dB) : ℝ :=
  ((marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†)
      (finProdFinEquiv p) (finProdFinEquiv p)).re

/-- The joint diagonal in the product eigenbasis is non-negative (`V σ V†` is PSD). -/
theorem marginalJointDiag_nonneg {dX dB : ℕ} (σ_XB : DensityOp (dX * dB))
    (p : Fin dX × Fin dB) : 0 ≤ marginalJointDiag σ_XB p := by
  unfold marginalJointDiag
  have hσpsd : σ_XB.toOp.PosSemidef := posSemidefOp_implies_mathlib σ_XB.toPosSemidefOp
  have hMpsd :
      (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†).PosSemidef :=
    posSemidef_conj_aux σ_XB.toOp (marginalProductBasis σ_XB) hσpsd
  exact psd_diag_re_nonneg _ hMpsd (finProdFinEquiv p)

/-- `V_A ⊗ V_B` is unitary on the left. -/
theorem marginalProductBasis_unitary_left {dX dB : ℕ} (σ_XB : DensityOp (dX * dB)) :
    (marginalProductBasis σ_XB)† * marginalProductBasis σ_XB = 1 := by
  unfold marginalProductBasis
  rw [Op.tensor_conjTranspose, Op.tensor_mul,
      eigenbasisOf_unitary_left (DensityOp.partialTraceB σ_XB),
      eigenbasisOf_unitary_left (DensityOp.partialTraceA σ_XB), Op.tensor_one]

/-- `V_A ⊗ V_B` is unitary on the right. -/
theorem marginalProductBasis_unitary_right {dX dB : ℕ} (σ_XB : DensityOp (dX * dB)) :
    marginalProductBasis σ_XB * (marginalProductBasis σ_XB)† = 1 := by
  unfold marginalProductBasis
  rw [Op.tensor_conjTranspose, Op.tensor_mul,
      eigenbasisOf_unitary_right (DensityOp.partialTraceB σ_XB),
      eigenbasisOf_unitary_right (DensityOp.partialTraceA σ_XB), Op.tensor_one]

/-- **Product spectral decomposition of the marginal reference.**

    `ρA ⊗ ρB = (V_A ⊗ V_B)† · diag(λ_i μ_j) · (V_A ⊗ V_B)`. This is the product
    spectrum witness mirrored from `vonNeumannEntropy_tensor_additive`'s `case spec`,
    specialized to the marginals' own eigenbases `V_A = eigenbasisOf ρA`,
    `V_B = eigenbasisOf ρB`. -/
theorem marginalProductBasis_spectrum {dX dB : ℕ} (σ_XB : DensityOp (dX * dB)) :
    ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB)).toOp =
      (marginalProductBasis σ_XB)† *
        Matrix.diagonal (fun k => (marginalProductEigs σ_XB k : ℂ)) *
        marginalProductBasis σ_XB := by
  have hA_decomp : (DensityOp.partialTraceB σ_XB).toOp =
      (eigenbasisOf (DensityOp.partialTraceB σ_XB))†
        * Matrix.diagonal (fun i => (eigenvaluesOf (DensityOp.partialTraceB σ_XB) i : ℂ))
        * eigenbasisOf (DensityOp.partialTraceB σ_XB) :=
    (Classical.choose_spec (eigenvaluesOf_spec (DensityOp.partialTraceB σ_XB)).2.2.2).2.2
  have hB_decomp : (DensityOp.partialTraceA σ_XB).toOp =
      (eigenbasisOf (DensityOp.partialTraceA σ_XB))†
        * Matrix.diagonal (fun j => (eigenvaluesOf (DensityOp.partialTraceA σ_XB) j : ℂ))
        * eigenbasisOf (DensityOp.partialTraceA σ_XB) :=
    (Classical.choose_spec (eigenvaluesOf_spec (DensityOp.partialTraceA σ_XB)).2.2.2).2.2
  set Dρ : Op dX :=
    Matrix.diagonal (fun i => (eigenvaluesOf (DensityOp.partialTraceB σ_XB) i : ℂ)) with hDρ
  set Dσ : Op dB :=
    Matrix.diagonal (fun j => (eigenvaluesOf (DensityOp.partialTraceA σ_XB) j : ℂ)) with hDσ
  have h_diag_eq : Op.tensor Dρ Dσ
      = Matrix.diagonal (fun k => (marginalProductEigs σ_XB k : ℂ)) := by
    rw [hDρ, hDσ, Op_tensor_diagonal]
    congr 1
    ext k
    simp only [marginalProductEigs, Complex.ofReal_mul]
  have h_tensor_op :
      ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB)).toOp
        = Op.tensor (DensityOp.partialTraceB σ_XB).toOp
                    (DensityOp.partialTraceA σ_XB).toOp := rfl
  rw [h_tensor_op, hA_decomp, hB_decomp]
  unfold marginalProductBasis
  rw [← Op.tensor_mul, ← Op.tensor_mul, ← Op.tensor_conjTranspose, h_diag_eq]

/-!
## Partial-trace conjugation helpers (for leaf (1b))
-/

/-- Partial trace over `B` is invariant under conjugation by `1 ⊗ U` when `U` is a
    left-unitary (`U† U = 1`). -/
lemma partialTraceB_one_tensor_unitary_conj {n m : ℕ}
    (U : Op m) (M : Op (n * m)) (hU : U† * U = 1) :
    partialTraceB (Op.tensor (1 : Op n) U * M * Op.tensor (1 : Op n) U†) = partialTraceB M := by
  have hUU := columns_orthonormal_of_conjTranspose_mul_eq_one U hU
  ext i j
  simp only [partialTraceB, Matrix.of_apply]
  simp_rw [one_tensor_mul_mul_one_tensor_apply, Matrix.conjTranspose_apply]
  trans ∑ a : Fin m, ∑ c : Fin m,
    (∑ K : Fin m, U K a * star (U K c)) *
      M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c))
  · rw [Finset.sum_comm]
    congr 1
    funext a
    rw [Finset.sum_comm]
    congr 1
    funext c
    rw [Finset.sum_mul]
    congr 1
    funext K
    ring
  · simp_rw [hUU, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']

/-- Partial trace over `B` of a `V_A ⊗ V_B` conjugation pulls the `A`-factor out and
    traces away the (left-unitary) `B`-factor. -/
lemma partialTraceB_tensor_conj {n m : ℕ} (A : Op n) (B : Op m) (M : Op (n * m))
    (hB : B† * B = 1) :
    partialTraceB (Op.tensor A B * M * (Op.tensor A B)†) = A * partialTraceB M * A† := by
  have hsplit1 : Op.tensor A B = Op.tensor A (1 : Op m) * Op.tensor (1 : Op n) B := by
    rw [Op.tensor_mul, mul_one, one_mul]
  have hsplit2 : (Op.tensor A B)† = Op.tensor (1 : Op n) B† * Op.tensor A† (1 : Op m) := by
    rw [Op.tensor_conjTranspose, Op.tensor_mul, one_mul, mul_one]
  rw [hsplit2, hsplit1,
    show Op.tensor A (1 : Op m) * Op.tensor (1 : Op n) B * M
          * (Op.tensor (1 : Op n) B† * Op.tensor A† (1 : Op m))
        = Op.tensor A (1 : Op m)
            * (Op.tensor (1 : Op n) B * M * Op.tensor (1 : Op n) B†)
            * Op.tensor A† (1 : Op m) by noncomm_ring,
    partialTraceB_sandwich_tensor_one A A†
      (Op.tensor (1 : Op n) B * M * Op.tensor (1 : Op n) B†),
    partialTraceB_one_tensor_unitary_conj B M hB]

/-- Partial trace over `A` of a `V_A ⊗ V_B` conjugation pulls the `B`-factor out and
    traces away the (left-unitary) `A`-factor. -/
lemma partialTraceA_tensor_conj {n m : ℕ} (A : Op n) (B : Op m) (M : Op (n * m))
    (hA : A† * A = 1) :
    partialTraceA (Op.tensor A B * M * (Op.tensor A B)†) = B * partialTraceA M * B† := by
  have hsplit1 : Op.tensor A B = Op.tensor (1 : Op n) B * Op.tensor A (1 : Op m) := by
    rw [Op.tensor_mul, one_mul, mul_one]
  have hsplit2 : (Op.tensor A B)† = Op.tensor A† (1 : Op m) * Op.tensor (1 : Op n) B† := by
    rw [Op.tensor_conjTranspose, Op.tensor_mul, mul_one, one_mul]
  rw [hsplit2, hsplit1,
    show Op.tensor (1 : Op n) B * Op.tensor A (1 : Op m) * M
          * (Op.tensor A† (1 : Op m) * Op.tensor (1 : Op n) B†)
        = Op.tensor (1 : Op n) B
            * (Op.tensor A (1 : Op m) * M * Op.tensor A† (1 : Op m))
            * Op.tensor (1 : Op n) B† by noncomm_ring,
    partialTraceA_one_tensor_sandwich B B†
      (Op.tensor A (1 : Op m) * M * Op.tensor A† (1 : Op m)),
    partialTraceA_tensor_one_unitary_conj A M hA]

/-- **Leaf (1b) — diagonal folding over the `B` factor.**

    Summing the joint diagonal in the product eigenbasis over the `B`-index recovers
    the `A`-marginal diagonal in its own eigenbasis:
    `∑ⱼ (V σ V†)_{(i,j),(i,j)}.re = (V_A ρA V_A†)_{i,i}.re`. This is the partial-trace
    adjunction in eigenbasis, building on `quadraticForm_partialTraceB_eq_sum` and the
    `finProdFinEquiv` tensor-index regrouping. -/
theorem marginalProductBasis_diagonal_fold_A {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) (i : Fin dX) :
    ∑ j : Fin dB, marginalJointDiag σ_XB (i, j)
      = diagonalOfRhoInSigmaBasis (DensityOp.partialTraceB σ_XB)
          (DensityOp.partialTraceB σ_XB) i := by
  have hρA : (DensityOp.partialTraceB σ_XB).toOp = partialTraceB σ_XB.toOp := rfl
  have hconj : partialTraceB
        (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†)
      = eigenbasisOf (DensityOp.partialTraceB σ_XB)
          * partialTraceB σ_XB.toOp
          * (eigenbasisOf (DensityOp.partialTraceB σ_XB))† := by
    unfold marginalProductBasis
    exact partialTraceB_tensor_conj _ _ _
      (eigenbasisOf_unitary_left (DensityOp.partialTraceA σ_XB))
  unfold marginalJointDiag diagonalOfRhoInSigmaBasis
  rw [← Complex.re_sum]
  congr 1
  rw [show (∑ j : Fin dB,
        (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†)
          (finProdFinEquiv (i, j)) (finProdFinEquiv (i, j)))
      = partialTraceB
          (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†) i i from rfl,
    hconj, hρA]

/-- **Leaf (1b) — diagonal folding over the `A` factor.**

    `∑ᵢ (V σ V†)_{(i,j),(i,j)}.re = (V_B ρB V_B†)_{j,j}.re`, the partial-trace
    adjunction in eigenbasis for the other factor (via `quadraticForm_partialTraceA_eq_sum`). -/
theorem marginalProductBasis_diagonal_fold_B {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) (j : Fin dB) :
    ∑ i : Fin dX, marginalJointDiag σ_XB (i, j)
      = diagonalOfRhoInSigmaBasis (DensityOp.partialTraceA σ_XB)
          (DensityOp.partialTraceA σ_XB) j := by
  have hρB : (DensityOp.partialTraceA σ_XB).toOp = partialTraceA σ_XB.toOp := rfl
  have hconj : partialTraceA
        (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†)
      = eigenbasisOf (DensityOp.partialTraceA σ_XB)
          * partialTraceA σ_XB.toOp
          * (eigenbasisOf (DensityOp.partialTraceA σ_XB))† := by
    unfold marginalProductBasis
    exact partialTraceA_tensor_conj _ _ _
      (eigenbasisOf_unitary_left (DensityOp.partialTraceB σ_XB))
  unfold marginalJointDiag diagonalOfRhoInSigmaBasis
  rw [← Complex.re_sum]
  congr 1
  rw [show (∑ i : Fin dX,
        (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†)
          (finProdFinEquiv (i, j)) (finProdFinEquiv (i, j)))
      = partialTraceA
          (marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†) j j from rfl,
    hconj, hρB]

/-- **DEEP LEAF (1) — tensor-marginal log-trace decomposition.**

    For `σ_XB : DensityOp (dX * dB)` with marginals
    `ρA := DensityOp.partialTraceB σ_XB`, `ρB := DensityOp.partialTraceA σ_XB`,
    the log-trace of `σ_XB` against the product reference splits across the
    marginals:

    `Tr(σ_XB · log(ρA ⊗ ρB)) = Tr(ρA · log ρA) + Tr(ρB · log ρB)`,

    i.e. in the project's `traceProductLogSigma` encoding,
    `traceProductLogSigma σ_XB (ρA.tensor ρB)
      = traceProductLogSigma ρA ρA + traceProductLogSigma ρB ρB`.

    Mathematically: `log(ρA ⊗ ρB) = (log ρA) ⊗ I + I ⊗ (log ρB)` on the joint
    support, so the trace splits into `Tr(σ_XB·(log ρA ⊗ I)) + Tr(σ_XB·(I ⊗ log ρB))`,
    and the partial-trace adjunction `Tr(σ_XB·(M ⊗ I)) = Tr(ρA·M)` folds each term
    onto its marginal. The eigenvalues/eigenbasis of `ρA ⊗ ρB` come from
    `Math.SpectralTheory.eigenvalues_kronecker`; `Real.log` of a product splits,
    with the zero-eigenvalue indices controlled by the support condition
    (`tensor_marginal_klein_support`). -/
theorem traceProductLogSigma_tensor_marginal {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    traceProductLogSigma σ_XB
        ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB)) =
      traceProductLogSigma (DensityOp.partialTraceB σ_XB) (DensityOp.partialTraceB σ_XB) +
        traceProductLogSigma (DensityOp.partialTraceA σ_XB) (DensityOp.partialTraceA σ_XB) := by
  -- (1c) Assembly of leaf (1) from the load-bearing leaf (1a) and the folds (1b).
  -- Step 1: basis-independence (1a) at the product reference, product unitary and eigenvalues.
  have hLHS :
      traceProductLogSigma σ_XB
          ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB))
        = ∑ k, ((marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†) k k).re
            * Real.log (marginalProductEigs σ_XB k) :=
    traceProductLogSigma_basis_indep σ_XB
      ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB))
      (marginalProductBasis σ_XB) (marginalProductEigs σ_XB)
      (marginalProductBasis_unitary_left σ_XB) (marginalProductBasis_unitary_right σ_XB)
      (fun k => mul_nonneg ((eigenvaluesOf_spec (DensityOp.partialTraceB σ_XB)).1 _)
                           ((eigenvaluesOf_spec (DensityOp.partialTraceA σ_XB)).1 _))
      (marginalProductBasis_spectrum σ_XB)
  -- Step 2: reindex the `Fin (dX*dB)` sum to a double sum over the paired index.
  have hreindex :
      (∑ k, ((marginalProductBasis σ_XB * σ_XB.toOp * (marginalProductBasis σ_XB)†) k k).re
          * Real.log (marginalProductEigs σ_XB k))
        = ∑ p : Fin dX × Fin dB, marginalJointDiag σ_XB p
            * Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) p.1
                        * eigenvaluesOf (DensityOp.partialTraceA σ_XB) p.2) := by
    apply Fintype.sum_equiv finProdFinEquiv.symm
    intro k
    simp only [marginalJointDiag, marginalProductEigs, Equiv.apply_symm_apply]
  -- Step 3: fold each marginal half (1b) back into `traceProductLogSigma ρ ρ`.
  have hRHS_A :
      traceProductLogSigma (DensityOp.partialTraceB σ_XB) (DensityOp.partialTraceB σ_XB)
        = ∑ i, (∑ j, marginalJointDiag σ_XB (i, j))
            * Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) i) := by
    unfold traceProductLogSigma
    apply Finset.sum_congr rfl
    intro i _
    rw [← marginalProductBasis_diagonal_fold_A σ_XB i]
  have hRHS_B :
      traceProductLogSigma (DensityOp.partialTraceA σ_XB) (DensityOp.partialTraceA σ_XB)
        = ∑ j, (∑ i, marginalJointDiag σ_XB (i, j))
            * Real.log (eigenvaluesOf (DensityOp.partialTraceA σ_XB) j) := by
    unfold traceProductLogSigma
    apply Finset.sum_congr rfl
    intro j _
    rw [← marginalProductBasis_diagonal_fold_B σ_XB j]
  -- Step 4: termwise log-split, killing zero-eigenvalue indices via the folds + non-negativity.
  have hterm : ∀ (i : Fin dX) (j : Fin dB),
      marginalJointDiag σ_XB (i, j)
          * Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) i
                      * eigenvaluesOf (DensityOp.partialTraceA σ_XB) j)
        = marginalJointDiag σ_XB (i, j)
            * (Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) i)
               + Real.log (eigenvaluesOf (DensityOp.partialTraceA σ_XB) j)) := by
    intro i j
    by_cases hlam : eigenvaluesOf (DensityOp.partialTraceB σ_XB) i = 0
    · -- zero `A`-eigenvalue ⇒ the joint diagonal vanishes (fold A + non-negativity)
      have hsum : ∑ j' : Fin dB, marginalJointDiag σ_XB (i, j') = 0 := by
        rw [marginalProductBasis_diagonal_fold_A σ_XB i,
            diagonalOfRhoInSigmaBasis_self (DensityOp.partialTraceB σ_XB) i]
        exact hlam
      have hzero : marginalJointDiag σ_XB (i, j) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j' _ => marginalJointDiag_nonneg σ_XB (i, j'))).mp hsum j (Finset.mem_univ j)
      rw [hzero]; ring
    · by_cases hmu : eigenvaluesOf (DensityOp.partialTraceA σ_XB) j = 0
      · -- zero `B`-eigenvalue ⇒ the joint diagonal vanishes (fold B + non-negativity)
        have hsum : ∑ i' : Fin dX, marginalJointDiag σ_XB (i', j) = 0 := by
          rw [marginalProductBasis_diagonal_fold_B σ_XB j,
              diagonalOfRhoInSigmaBasis_self (DensityOp.partialTraceA σ_XB) j]
          exact hmu
        have hzero : marginalJointDiag σ_XB (i, j) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun i' _ => marginalJointDiag_nonneg σ_XB (i', j))).mp hsum i (Finset.mem_univ i)
        rw [hzero]; ring
      · -- both eigenvalues positive ⇒ `Real.log` splits
        have hlampos : 0 < eigenvaluesOf (DensityOp.partialTraceB σ_XB) i :=
          lt_of_le_of_ne ((eigenvaluesOf_spec (DensityOp.partialTraceB σ_XB)).1 i) (Ne.symm hlam)
        have hmupos : 0 < eigenvaluesOf (DensityOp.partialTraceA σ_XB) j :=
          lt_of_le_of_ne ((eigenvaluesOf_spec (DensityOp.partialTraceA σ_XB)).1 j) (Ne.symm hmu)
        rw [Real.log_mul hlampos.ne' hmupos.ne']
  -- Combine: LHS double sum splits and each half folds to the marginal log-trace.
  rw [hLHS, hreindex, hRHS_A, hRHS_B]
  have hsum_eq :
      (∑ p : Fin dX × Fin dB, marginalJointDiag σ_XB p
          * Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) p.1
                      * eigenvaluesOf (DensityOp.partialTraceA σ_XB) p.2))
        = ∑ p : Fin dX × Fin dB,
            (marginalJointDiag σ_XB p
                * Real.log (eigenvaluesOf (DensityOp.partialTraceB σ_XB) p.1)
              + marginalJointDiag σ_XB p
                * Real.log (eigenvaluesOf (DensityOp.partialTraceA σ_XB) p.2)) := by
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨i, j⟩ := p
    rw [hterm i j, mul_add]
  rw [hsum_eq, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]

/-- The joint diagonal in the product eigenbasis vanishes at `(i,j)` whenever a
    marginal eigenvalue vanishes (`λ_i = 0` or `μ_j = 0`): the relevant marginal fold
    is a sum of non-negatives equal to that eigenvalue. -/
lemma marginalJointDiag_eq_zero_of_eig_zero {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) (i : Fin dX) (j : Fin dB)
    (h : eigenvaluesOf (DensityOp.partialTraceB σ_XB) i = 0
        ∨ eigenvaluesOf (DensityOp.partialTraceA σ_XB) j = 0) :
    marginalJointDiag σ_XB (i, j) = 0 := by
  rcases h with hl | hr
  · have hsum : ∑ j' : Fin dB, marginalJointDiag σ_XB (i, j') = 0 := by
      rw [marginalProductBasis_diagonal_fold_A σ_XB i,
          diagonalOfRhoInSigmaBasis_self (DensityOp.partialTraceB σ_XB) i]
      exact hl
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j' _ => marginalJointDiag_nonneg σ_XB (i, j'))).mp hsum j (Finset.mem_univ j)
  · have hsum : ∑ i' : Fin dX, marginalJointDiag σ_XB (i', j) = 0 := by
      rw [marginalProductBasis_diagonal_fold_B σ_XB j,
          diagonalOfRhoInSigmaBasis_self (DensityOp.partialTraceA σ_XB) j]
      exact hr
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i' _ => marginalJointDiag_nonneg σ_XB (i', j))).mp hsum i (Finset.mem_univ i)

/-- **DEEP LEAF (2) — support condition for Klein.**

    For `σ_XB : DensityOp (dX * dB)` with marginals
    `ρA := DensityOp.partialTraceB σ_XB`, `ρB := DensityOp.partialTraceA σ_XB`,
    the joint state's diagonal in the product-reference eigenbasis vanishes wherever
    the product reference eigenvalue vanishes:

    `∀ i, eigenvaluesOf (ρA ⊗ ρB) i = 0
        → diagonalOfRhoInSigmaBasis σ_XB (ρA ⊗ ρB) i = 0`.

    True because the joint support is contained in the product of the marginal
    supports: where a product reference eigenvalue is zero, `σ_XB` carries no
    diagonal weight. This is exactly the support hypothesis consumed by
    `InfoTheory.RelativeEntropy.klein_inequality_support`. -/
theorem tensor_marginal_klein_support {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    ∀ i, eigenvaluesOf
          ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB)) i = 0 →
        diagonalOfRhoInSigmaBasis σ_XB
          ((DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB)) i = 0 := by
  classical
  set τ := (DensityOp.partialTraceB σ_XB).tensor (DensityOp.partialTraceA σ_XB) with hτ
  -- Reduce the diagonal support condition to kernel containment `ker τ ⊆ ker σ_XB`.
  rw [eigenvalue_support_iff_ker_sub σ_XB τ]
  intro v hv
  set V := marginalProductBasis σ_XB with hV
  have hVL : V† * V = 1 := marginalProductBasis_unitary_left σ_XB
  have hVR : V * V† = 1 := marginalProductBasis_unitary_right σ_XB
  set w := V.mulVec v with hw
  set N := V * σ_XB.toOp * V† with hN
  have hτspec : τ.toOp =
      V† * Matrix.diagonal (fun k => (marginalProductEigs σ_XB k : ℂ)) * V :=
    marginalProductBasis_spectrum σ_XB
  -- In the product basis, the kernel hypothesis pins `w = V v` to the joint kernel.
  have hdiagw : (Matrix.diagonal (fun k => (marginalProductEigs σ_XB k : ℂ))).mulVec w = 0 := by
    have h1 : V.mulVec (τ.toOp.mulVec v) = 0 := by rw [hv, Matrix.mulVec_zero]
    have h2 : V * τ.toOp = Matrix.diagonal (fun k => (marginalProductEigs σ_XB k : ℂ)) * V := by
      rw [hτspec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVR, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec] at h1
    exact h1
  have heigw : ∀ k, (marginalProductEigs σ_XB k : ℂ) * w k = 0 := by
    intro k
    have hk := congrFun hdiagw k
    rwa [Matrix.mulVec_diagonal, Pi.zero_apply] at hk
  -- `N = V σ_XB V†` is PSD.
  have hNpsd : N.PosSemidef :=
    posSemidef_conj_aux σ_XB.toOp V (posSemidefOp_implies_mathlib σ_XB.toPosSemidefOp)
  -- The joint operator kills `w`: every column on `supp w` has a zero diagonal.
  have hNw : N.mulVec w = 0 := by
    funext p
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hwq : w q = 0
    · rw [hwq, mul_zero]
    · -- `w q ≠ 0` forces the product eigenvalue at `q` to vanish.
      have heig0 : marginalProductEigs σ_XB q = 0 := by
        rcases mul_eq_zero.mp (heigw q) with hcast | hzero
        · exact_mod_cast hcast
        · exact absurd hzero hwq
      have hfactor :
          eigenvaluesOf (DensityOp.partialTraceB σ_XB) (finProdFinEquiv.symm q).1 = 0
            ∨ eigenvaluesOf (DensityOp.partialTraceA σ_XB) (finProdFinEquiv.symm q).2 = 0 := by
        simp only [marginalProductEigs] at heig0
        exact mul_eq_zero.mp heig0
      have hmjd : marginalJointDiag σ_XB
          ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2) = 0 :=
        marginalJointDiag_eq_zero_of_eig_zero σ_XB _ _ hfactor
      have hq : finProdFinEquiv ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2) = q := by
        rw [Prod.mk.eta]; exact finProdFinEquiv.apply_symm_apply q
      have hNqq_re : (N q q).re = 0 := by
        have heq : (N q q).re
            = marginalJointDiag σ_XB ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2) := by
          unfold marginalJointDiag
          rw [hN, hV, hq]
        rw [heq]; exact hmjd
      have hbound := pos_semidef_off_diag_bound
        (⟨⟨N, hNpsd.isHermitian⟩, fun x => hNpsd.re_dotProduct_nonneg x⟩ :
          Quantum.Operators.PosSemidefOp (dX * dB)) p q
      simp only at hbound
      have hle : Complex.normSq (N p q) ≤ 0 := le_trans hbound (by rw [hNqq_re, mul_zero])
      have hNpq : N p q = 0 :=
        Complex.normSq_eq_zero.mp (le_antisymm hle (Complex.normSq_nonneg _))
      rw [hNpq, zero_mul]
  -- Transport back: `σ_XB = V† N V`, so `σ_XB v = V† (N w) = 0`.
  have hσ : σ_XB.toOp = V† * N * V := by
    rw [hN, show V† * (V * σ_XB.toOp * V†) * V
          = (V† * V) * σ_XB.toOp * (V† * V) by noncomm_ring, hVL, Matrix.one_mul, Matrix.mul_one]
  rw [hσ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw, hNw, Matrix.mulVec_zero]

/-- **PROVED REDUCTION — subadditivity.**

    `H(σ_XB) ≤ H(ρA) + H(ρB)` where `ρA = DensityOp.partialTraceB σ_XB` and
    `ρB = DensityOp.partialTraceA σ_XB`. Derived from Klein's inequality
    (`klein_inequality_support` + leaf (2)) together with the log-trace splitting
    (leaf (1)) and `relativeEntropyReal_self`. -/
theorem vonNeumannEntropy_le_partialTrace_add {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    vonNeumannEntropy σ_XB ≤
      vonNeumannEntropy (DensityOp.partialTraceB σ_XB) +
        vonNeumannEntropy (DensityOp.partialTraceA σ_XB) := by
  set ρA := DensityOp.partialTraceB σ_XB with hρA
  set ρB := DensityOp.partialTraceA σ_XB with hρB
  -- Klein non-negativity for the product reference, via the support leaf.
  have hklein : 0 ≤ relativeEntropyReal σ_XB (ρA.tensor ρB) :=
    klein_inequality_support σ_XB (ρA.tensor ρB)
      (tensor_marginal_klein_support σ_XB)
  -- Expand the relative entropy and split the log-trace across marginals.
  rw [relativeEntropyReal_eq, traceProductLogSigma_tensor_marginal σ_XB] at hklein
  -- `traceProductLogSigma ρ ρ = - H(ρ)` from self relative entropy.
  have hA : traceProductLogSigma ρA ρA = -vonNeumannEntropy ρA := by
    have h := relativeEntropyReal_self ρA
    rw [relativeEntropyReal_eq] at h
    linarith
  have hB : traceProductLogSigma ρB ρB = -vonNeumannEntropy ρB := by
    have h := relativeEntropyReal_self ρB
    rw [relativeEntropyReal_eq] at h
    linarith
  rw [hA, hB] at hklein
  linarith

/-- **PROVED REDUCTION — conditional von Neumann entropy bound.**

    `H(σ_XB) − H(ρB) ≤ log dX`, where `ρB = DensityOp.partialTraceA σ_XB` is the
    B-marginal. This is exactly `cqConditionalVNEntropy σ_XB ≤ Real.log dX` after
    unfolding the definition. Derived from subadditivity plus the dimension bound
    `vonNeumannEntropy_le_log_dim` on the `dX`-dimensional X-marginal
    `ρA = DensityOp.partialTraceB σ_XB`. -/
theorem conditionalVNEntropy_le_log_dim {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    vonNeumannEntropy σ_XB - vonNeumannEntropy (DensityOp.partialTraceA σ_XB) ≤
      Real.log dX := by
  have hsub := vonNeumannEntropy_le_partialTrace_add σ_XB
  have hdim : vonNeumannEntropy (DensityOp.partialTraceB σ_XB) ≤ Real.log dX :=
    vonNeumannEntropy_le_log_dim (DensityOp.partialTraceB σ_XB)
  linarith

end InfoTheory.VonNeumannEntropy
