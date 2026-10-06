import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.InfoTheory.Measurement.POVM
import Mathlib.Data.Finset.Sort
import QCryptLean.Quantum.Operators.InverseSqrtSandwichIff

/-!
# Fuchs–Caves measurement achievability

This file constructs the optimal Fuchs–Caves measurement and proves that its classical
(Bhattacharyya) fidelity of the outcome distributions equals the quantum Uhlmann fidelity,
in all three cases: `σ` positive definite, `ρ` positive definite, and both singular.

The construction (Khatri–Wilde Thm 6.12 / Nielsen–Chuang §9.3.1, inverse-based route) is:
for positive-definite `σ`, set

  `A := σ^{-1/2} · √(σ^{1/2} ρ σ^{1/2}) · σ^{-1/2}`,

a Hermitian PSD operator satisfying `A σ A = ρ`.  The optimal POVM is the projective
measurement in the eigenbasis of `A`; its outcome distributions `p_i = Tr(P_i ρ)`,
`q_i = Tr(P_i σ)` satisfy `p_i = λ_i² q_i`, hence `√(p_i q_i) = λ_i q_i`, and
`∑ λ_i q_i = Tr(A σ) = Tr √(σ^{1/2} ρ σ^{1/2}) = F(ρ, σ)`.

The both-singular case is reduced to the positive-definite case by compressing both
operators to `range σ` via the support isometry `V` (columns: positive-eigenvalue
eigenvectors of `σ`).  On the support `σ` becomes positive definite, the fidelity is
unchanged (`√σ` is fixed by the support projector), and the resulting `r`-outcome POVM is
embedded back to the ambient space with one extra (support-complement) outcome that carries
zero probability against `σ`.

## Main statements

* `Matrix.PosDef.inverseSqrt_mul_sqrt` — `σ^{-1/2} · σ^{1/2} = 1`.
* `fuchsCavesOperator` — the explicit operator `A`.
* `eigenbasisPOVM` — the explicit projective POVM in the eigenbasis of a Hermitian operator.
* `fidelity_eq_classicalFidelity_measurement_of_posDef` — achievability when `σ` is PosDef.
* `fidelity_eq_classicalFidelity_measurement_of_posDef_psd` — the same with sub-normalized
  `ρ` allowed (the engine for the support-restricted both-singular case).
* `fidelity_eq_classicalFidelity_measurement_of_posDef_left` — achievability when `ρ` is
  PosDef.
* `supportIso`, `compressedSigmaDensity`, `compressedRhoPSD`, `POVM.supportEmbed` — the
  support-restriction toolkit.
* `fidelity_eq_classicalFidelity_measurement_of_bothSingular` — achievability by support
  restriction, for arbitrary `ρ` and `σ` (the case used when both are singular).
-/

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- Classical (Bhattacharyya) fidelity of two finite distributions. -/
def classicalFidelity {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i * q i)

/-!
## Rank-one eigenprojectors of a Hermitian operator

These generic spectral facts (the eigenvalue-weighted spectral expansion, and the
rank-one eigenprojectors being nonzero orthogonal Hermitian idempotents that resolve
the identity) underwrite the projective Fuchs–Caves measurement.  They are stated for a
general Hermitian `M : Matrix (Fin d) (Fin d) ℂ`.
-/

/-- Spectral expansion of a Hermitian operator as a sum of rank-one eigenprojectors:
`M = ∑ i, (λ_i : ℂ) • |u_i⟩⟨u_i|`, where `u_i = (hM.eigenvectorBasis i).ofLp`. -/
lemma isHermitian_eq_sum_smul_vecMulVec {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    M = ∑ i, ((hM.eigenvalues i : ℝ) : ℂ) •
        Matrix.vecMulVec ((hM.eigenvectorBasis i).ofLp)
          (star (hM.eigenvectorBasis i).ofLp) := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ :=
    (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU_def
  set D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  have hspec : M = U * D * star U := by
    have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  ext a b
  have hentry : M a b = (U * D * star U) a b := by rw [← hspec]
  rw [hentry, Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [show star ((hM.eigenvectorBasis i).ofLp) b
        = star ((hM.eigenvectorBasis i).ofLp b) from rfl]
  rw [hU_def, hM.eigenvectorUnitary_apply a i, hM.eigenvectorUnitary_apply b i]
  simp only [Function.comp_apply]
  change ((hM.eigenvectorBasis i).ofLp a) * ((hM.eigenvalues i : ℝ) : ℂ)
        * (star ((hM.eigenvectorBasis i).ofLp b) : ℂ)
      = ((hM.eigenvalues i : ℝ) : ℂ)
        * (((hM.eigenvectorBasis i).ofLp a)
           * (star ((hM.eigenvectorBasis i).ofLp b) : ℂ))
  ring

/-- The rank-one eigenprojector of a Hermitian `M` for eigenindex `z`:
`P_z = |u_z⟩⟨u_z|`. -/
noncomputable def eigenProjector {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) (z : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
    (star (hM.eigenvectorBasis z).ofLp)

/-- The rank-one eigenprojectors `P_z = |u_z⟩⟨u_z|` of a Hermitian `M` are nonzero
orthogonal Hermitian idempotents resolving the identity. -/
lemma eigenProjector_increments {d : ℕ} [NeZero d]
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    (∀ z, eigenProjector hM z * eigenProjector hM z = eigenProjector hM z) ∧
      (∀ z, (eigenProjector hM z)ᴴ = eigenProjector hM z) ∧
      (∀ z, eigenProjector hM z ≠ 0) ∧
      (∀ z z', z ≠ z' → eigenProjector hM z * eigenProjector hM z' = 0) ∧
      (∑ z, eigenProjector hM z) = 1 := by
  classical
  have hdot : ∀ i j : Fin d,
      star ((hM.eigenvectorBasis i).ofLp) ⬝ᵥ ((hM.eigenvectorBasis j).ofLp) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [dotProduct_comm]
    have h := orthonormal_iff_ite.mp hM.eigenvectorBasis.orthonormal i j
    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [eigenProjector, Matrix.vecMulVec_mul_vecMulVec, hdot z z]; simp
  · intro z
    rw [eigenProjector, Matrix.conjTranspose_vecMulVec]; simp
  · intro z
    have hvec : ((hM.eigenvectorBasis z).ofLp) ≠ 0 := by
      intro hzero
      exact hM.eigenvectorBasis.orthonormal.ne_zero z (by ext j; exact congr_fun hzero j)
    exact Matrix.vecMulVec_ne_zero hvec (star_ne_zero.mpr hvec)
  · intro z z' hzz'
    rw [eigenProjector, eigenProjector, Matrix.vecMulVec_mul_vecMulVec, hdot z z']
    simp [hzz']
  · set U : Matrix (Fin d) (Fin d) ℂ :=
      (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU_def
    have hUstar : Uᴴ * U = 1 := by
      simpa [hU_def, star_eq_conjTranspose] using
        UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    have hUU : U * Uᴴ = 1 :=
      (Matrix.mul_eq_one_comm_of_card_eq
        (m := Fin d) (n := Fin d) (R := ℂ) (A := Uᴴ) (B := U) (by rfl)).mp hUstar
    ext a b
    calc (∑ z, eigenProjector hM z) a b
        = ∑ z, ((hM.eigenvectorBasis z).ofLp a) *
              star ((hM.eigenvectorBasis z).ofLp b) := by
          simp [eigenProjector, Matrix.sum_apply, Matrix.vecMulVec_apply]
      _ = (U * Uᴴ) a b := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_def]
      _ = (1 : Matrix (Fin d) (Fin d) ℂ) a b := by rw [hUU]

/-- Each rank-one eigenprojector `P_z = |u_z⟩⟨u_z|` is positive semidefinite. -/
lemma eigenProjector_posSemidef {d : ℕ} [NeZero d]
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) (z : Fin d) :
    (eigenProjector hM z).PosSemidef := by
  obtain ⟨hidem, hherm, _, _, _⟩ := eigenProjector_increments hM
  have hP : eigenProjector hM z = (eigenProjector hM z)ᴴ * eigenProjector hM z := by
    rw [hherm z, hidem z]
  rw [hP]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The eigenprojector action: `M = ∑ λ_z • P_z` and both `M * P_z` and `P_z * M`
equal `λ_z • P_z`. -/
lemma eigenProjector_action {d : ℕ} [NeZero d]
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    (M = ∑ z, (hM.eigenvalues z : ℂ) • eigenProjector hM z) ∧
      ∀ z, (M * eigenProjector hM z = (hM.eigenvalues z : ℂ) • eigenProjector hM z) ∧
        (eigenProjector hM z * M = (hM.eigenvalues z : ℂ) • eigenProjector hM z) := by
  classical
  have hPherm : ∀ z, (eigenProjector hM z)ᴴ = eigenProjector hM z := by
    intro z; rw [eigenProjector, Matrix.conjTranspose_vecMulVec]; simp
  have hleft : ∀ z,
      M * eigenProjector hM z = (hM.eigenvalues z : ℂ) • eigenProjector hM z := by
    intro z
    rw [eigenProjector, Matrix.mul_vecMulVec, hM.mulVec_eigenvectorBasis]
    ext a b
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul]
    ring
  refine ⟨isHermitian_eq_sum_smul_vecMulVec hM, ?_⟩
  intro z
  refine ⟨hleft z, ?_⟩
  have h := congrArg Matrix.conjTranspose (hleft z)
  rw [Matrix.conjTranspose_mul, hM, hPherm z, Matrix.conjTranspose_smul, hPherm z] at h
  simpa [Complex.conj_ofReal] using h

/-!
## The inverse-square-root / square-root cancellation
-/

/-!
## The Fuchs–Caves operator `A = σ^{-1/2} √(σ^{1/2} ρ σ^{1/2}) σ^{-1/2}`
-/

/-- `CFC.sqrt σ` is positive semidefinite for a PosDef `σ`. -/
lemma sqrt_posSemidef {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℂ) :
    (CFC.sqrt σ).PosSemidef :=
  (CFC.sqrt_nonneg σ).posSemidef

/-- The inner PSD operator `√σ · ρ · √σ` of the fidelity quantity is positive
semidefinite. -/
lemma sqrtSandwich_posSemidef {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) :
    (CFC.sqrt σ * ρ * CFC.sqrt σ).PosSemidef := by
  have hsqrt_herm : (CFC.sqrt σ).IsHermitian := (sqrt_posSemidef σ).isHermitian
  have h := hρ.conjTranspose_mul_mul_same (CFC.sqrt σ)
  rwa [hsqrt_herm.eq] at h

/-- **The Fuchs–Caves operator** for a positive-definite reference `σ`:
`A = σ^{-1/2} · √(σ^{1/2} ρ σ^{1/2}) · σ^{-1/2}`.

Its eigenbasis defines the optimal Fuchs–Caves measurement.  It is Hermitian and PSD
(`fuchsCavesOperator_posSemidef`) and satisfies the load-bearing identity `A σ A = ρ`
(`fuchsCavesOperator_sandwich`). -/
noncomputable def fuchsCavesOperator {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) : Matrix (Fin n) (Fin n) ℂ :=
  hσ.inverseSqrt * CFC.sqrt (CFC.sqrt σ * ρ * CFC.sqrt σ) * hσ.inverseSqrt

/-- The Fuchs–Caves operator is positive semidefinite. -/
lemma fuchsCavesOperator_posSemidef {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) :
    (fuchsCavesOperator ρ hσ).PosSemidef := by
  unfold fuchsCavesOperator
  have hP_psd : (CFC.sqrt (CFC.sqrt σ * ρ * CFC.sqrt σ)).PosSemidef :=
    sqrt_posSemidef _
  have hS_herm : hσ.inverseSqrt.IsHermitian := hσ.inverseSqrt_isHermitian
  have h := hP_psd.conjTranspose_mul_mul_same hσ.inverseSqrt
  rwa [hS_herm.eq] at h

/-- The Fuchs–Caves operator is Hermitian. -/
lemma fuchsCavesOperator_isHermitian {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) :
    (fuchsCavesOperator ρ hσ).IsHermitian :=
  (fuchsCavesOperator_posSemidef ρ hσ).isHermitian

/-- **The load-bearing sandwich identity** `A σ A = ρ` for a PSD `ρ` and PosDef `σ`.

This recovers `ρ` from the Fuchs–Caves operator `A` and the reference `σ`, and is the
algebraic heart of the achievability proof. -/
lemma fuchsCavesOperator_sandwich {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    fuchsCavesOperator ρ hσ * σ * fuchsCavesOperator ρ hσ = ρ := by
  set S := hσ.inverseSqrt with hS
  set P := CFC.sqrt (CFC.sqrt σ * ρ * CFC.sqrt σ) with hP
  have hPP : P * P = CFC.sqrt σ * ρ * CFC.sqrt σ :=
    CFC.sqrt_mul_sqrt_self _ (ha := (sqrtSandwich_posSemidef hρ).nonneg)
  have hSσS : S * σ * S = 1 := hσ.inverseSqrt_sandwich_eq_one
  have hSsqrt : S * CFC.sqrt σ = 1 := hσ.inverseSqrt_mul_sqrt
  have hsqrtS : CFC.sqrt σ * S = 1 := hσ.sqrt_mul_inverseSqrt
  calc fuchsCavesOperator ρ hσ * σ * fuchsCavesOperator ρ hσ
      = (S * P * S) * σ * (S * P * S) := by rw [fuchsCavesOperator]
    _ = S * P * (S * σ * S) * P * S := by
          simp only [Matrix.mul_assoc]
    _ = S * P * 1 * P * S := by rw [hSσS]
    _ = S * (P * P) * S := by
          rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = S * (CFC.sqrt σ * ρ * CFC.sqrt σ) * S := by rw [hPP]
    _ = (S * CFC.sqrt σ) * ρ * (CFC.sqrt σ * S) := by
          simp only [Matrix.mul_assoc]
    _ = 1 * ρ * 1 := by rw [hSsqrt, hsqrtS]
    _ = ρ := by rw [Matrix.mul_one, Matrix.one_mul]

/-- The Uhlmann fidelity expressed through the `σ`-side square-root sandwich:
`F(ρ, σ) = Tr √(σ^{1/2} ρ σ^{1/2})`. -/
lemma fidelity_eq_re_trace_sqrt_sigmaSandwich {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    DensityOp.fidelity ρ σ =
      (CFC.sqrt (CFC.sqrt σ.toOp * ρ.toOp * CFC.sqrt σ.toOp)).trace.re := by
  rw [DensityOp.fidelity, fidelity_comm]
  unfold Quantum.Metrics.fidelity
  rw [sqrtPosSemidefOp]

/-!
## The projective Fuchs–Caves POVM
-/

/-- The **projective POVM in the eigenbasis of a Hermitian operator** `M`: its `n`
elements are the rank-one eigenprojectors `P_z = |u_z⟩⟨u_z|`. -/
noncomputable def eigenbasisPOVM {n : ℕ} [NeZero n]
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    InfoTheory.Measurement.POVM n n where
  elements := eigenProjector hM
  hermitian := fun z => (eigenProjector_posSemidef hM z).isHermitian
  positive := fun z x =>
    posSemidef_re_quadraticForm_nonneg (eigenProjector_posSemidef hM z) x
  complete := (eigenProjector_increments hM).2.2.2.2

/-!
## Achievability
-/

/-- **Fuchs–Caves achievability for a positive-definite reference `σ`.**

For density operators `ρ σ` with `σ` positive definite, the projective measurement in
the eigenbasis of the Fuchs–Caves operator `A = σ^{-1/2} √(σ^{1/2} ρ σ^{1/2}) σ^{-1/2}`
has classical (Bhattacharyya) fidelity of its outcome distributions equal to the quantum
Uhlmann fidelity `F(ρ, σ)`. -/
theorem fidelity_eq_classicalFidelity_measurement_of_posDef {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) (hσ : σ.toOp.PosDef) :
    ∃ (k : ℕ) (M : InfoTheory.Measurement.POVM n k),
      DensityOp.fidelity ρ σ
        = classicalFidelity (fun i => (M.elements i * ρ.toOp).trace.re)
            (fun i => (M.elements i * σ.toOp).trace.re) := by
  classical
  set A := fuchsCavesOperator ρ.toOp hσ with hA_def
  have hA_herm : A.IsHermitian := fuchsCavesOperator_isHermitian ρ.toOp hσ
  have hA_psd : A.PosSemidef := fuchsCavesOperator_posSemidef ρ.toOp hσ
  set lam := hA_herm.eigenvalues with hlam
  set P := eigenProjector hA_herm with hP
  obtain ⟨hAsum, hact⟩ := eigenProjector_action hA_herm
  refine ⟨n, eigenbasisPOVM hA_herm, ?_⟩
  -- The POVM elements are the eigenprojectors.
  have hPelt : ∀ i, (eigenbasisPOVM hA_herm).elements i = P i := fun _ => rfl
  -- `A σ A = ρ`: the load-bearing sandwich identity.
  have hρ_eq : ρ.toOp = A * σ.toOp * A := by
    rw [hA_def]
    exact (fuchsCavesOperator_sandwich
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) hσ).symm
  -- Action lemmas, packaged.
  have hActL : ∀ z, A * P z = (lam z : ℂ) • P z := fun z => (hact z).1
  have hActR : ∀ z, P z * A = (lam z : ℂ) • P z := fun z => (hact z).2
  -- Step 1: `Tr(P_z ρ) = λ_z² · Tr(P_z σ)` as a complex identity.
  have hp_eq : ∀ z, (P z * ρ.toOp).trace = (lam z : ℂ) ^ 2 * (P z * σ.toOp).trace := by
    intro z
    have hPσA : (P z * σ.toOp * A).trace = (lam z : ℂ) * (P z * σ.toOp).trace := by
      calc (P z * σ.toOp * A).trace
          = (A * (P z * σ.toOp)).trace := by
              rw [Matrix.trace_mul_comm (P z * σ.toOp) A]
        _ = ((A * P z) * σ.toOp).trace := by rw [Matrix.mul_assoc]
        _ = ((lam z : ℂ) • P z * σ.toOp).trace := by rw [hActL]
        _ = (lam z : ℂ) * (P z * σ.toOp).trace := by
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    calc (P z * ρ.toOp).trace
        = (P z * (A * σ.toOp * A)).trace := by rw [hρ_eq]
      _ = ((P z * A) * (σ.toOp * A)).trace := by simp only [Matrix.mul_assoc]
      _ = (((lam z : ℂ) • P z) * (σ.toOp * A)).trace := by rw [hActR]
      _ = (lam z : ℂ) * ((P z * σ.toOp) * A).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
      _ = (lam z : ℂ) * ((lam z : ℂ) * (P z * σ.toOp).trace) := by rw [hPσA]
      _ = (lam z : ℂ) ^ 2 * (P z * σ.toOp).trace := by ring
  -- Nonnegativity facts.
  have hσ_psd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hP_psd : ∀ z, (P z).PosSemidef := fun z => eigenProjector_posSemidef hA_herm z
  have hq_nonneg : ∀ z, 0 ≤ (P z * σ.toOp).trace.re := fun z =>
    Quantum.Operators.trace_mul_psd_nonneg (P z) σ.toOp (hP_psd z) hσ_psd
  have hlam_nonneg : ∀ z, 0 ≤ lam z := fun z => hA_psd.eigenvalues_nonneg z
  -- Step 2: `p_z = λ_z² · q_z` after taking real parts.
  have hp_re : ∀ z, (P z * ρ.toOp).trace.re = lam z ^ 2 * (P z * σ.toOp).trace.re := by
    intro z
    rw [hp_eq z, Complex.mul_re]
    have him : ((lam z : ℂ) ^ 2).im = 0 := by
      rw [show ((lam z : ℂ) ^ 2) = ((lam z ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_im]
    have hre : ((lam z : ℂ) ^ 2).re = lam z ^ 2 := by
      rw [show ((lam z : ℂ) ^ 2) = ((lam z ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [him, hre, zero_mul, sub_zero]
  -- Step 3: each Bhattacharyya term equals `λ_z · q_z`.
  have hsqrt_term : ∀ z, Real.sqrt ((P z * ρ.toOp).trace.re * (P z * σ.toOp).trace.re)
      = lam z * (P z * σ.toOp).trace.re := by
    intro z
    rw [hp_re z]
    have hsq : lam z ^ 2 * (P z * σ.toOp).trace.re * (P z * σ.toOp).trace.re
        = (lam z * (P z * σ.toOp).trace.re) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg (hlam_nonneg z) (hq_nonneg z))]
  -- Step 4: `∑ λ_z q_z = Tr(A σ).re`.
  have hsum : ∑ z, lam z * (P z * σ.toOp).trace.re = (A * σ.toOp).trace.re := by
    have hAσ : (A * σ.toOp).trace = ∑ z, (lam z : ℂ) * (P z * σ.toOp).trace := by
      conv_lhs => rw [hAsum, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [hAσ, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- Step 5: `Tr(A σ).re = F(ρ, σ)`.
  have hfid : (A * σ.toOp).trace.re = DensityOp.fidelity ρ σ := by
    rw [fidelity_eq_re_trace_sqrt_sigmaSandwich ρ σ]
    congr 1
    set Q := CFC.sqrt (CFC.sqrt σ.toOp * ρ.toOp * CFC.sqrt σ.toOp) with hQ
    have hAQ : A = hσ.inverseSqrt * Q * hσ.inverseSqrt := by
      rw [hA_def, fuchsCavesOperator, hQ]
    calc (A * σ.toOp).trace
        = (hσ.inverseSqrt * (Q * hσ.inverseSqrt * σ.toOp)).trace := by
            rw [hAQ]; congr 1; simp only [Matrix.mul_assoc]
      _ = ((Q * hσ.inverseSqrt * σ.toOp) * hσ.inverseSqrt).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (Q * (hσ.inverseSqrt * σ.toOp * hσ.inverseSqrt)).trace := by
            congr 1; simp only [Matrix.mul_assoc]
      _ = (Q * 1).trace := by rw [hσ.inverseSqrt_sandwich_eq_one]
      _ = Q.trace := by rw [Matrix.mul_one]
  -- Assemble.
  rw [classicalFidelity]
  simp only [hPelt]
  rw [← hfid, ← hsum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  exact (hsqrt_term z).symm

/-- The Uhlmann fidelity of two PSD operators expressed through the `B`-side square-root
sandwich: `F(A, B) = Tr √(√B · A · √B)`.  This is the `PosSemidefOp`-level form of
`fidelity_eq_re_trace_sqrt_sigmaSandwich`, with no normalization assumption on either
operand. -/
lemma fidelity_eq_re_trace_sqrt_sandwich {n : ℕ} [NeZero n] (A B : PosSemidefOp n) :
    Quantum.Metrics.fidelity A B =
      (CFC.sqrt (CFC.sqrt B.toOp * A.toOp * CFC.sqrt B.toOp)).trace.re := by
  rw [fidelity_comm]
  unfold Quantum.Metrics.fidelity
  rw [sqrtPosSemidefOp]

/-- **Fuchs–Caves achievability for a positive-definite reference `σ`, sub-normalized
`ρ` allowed.**

The exact analogue of `fidelity_eq_classicalFidelity_measurement_of_posDef`, but with the
test operator `ρ` only assumed positive semidefinite (not necessarily trace one).  The
construction and proof are identical: the original proof never used `Tr ρ = 1`.  This
generalization is what lets the both-singular case feed the *sub-normalized* support
compression `ρ̃ = V† ρ V` of a state `ρ` that has mass outside `range σ`. -/
theorem fidelity_eq_classicalFidelity_measurement_of_posDef_psd {n : ℕ} [NeZero n]
    (ρ : PosSemidefOp n) (σ : DensityOp n) (hσ : σ.toOp.PosDef) :
    ∃ (k : ℕ) (M : InfoTheory.Measurement.POVM n k),
      Quantum.Metrics.fidelity ρ σ.toPosSemidefOp
        = classicalFidelity (fun i => (M.elements i * ρ.toOp).trace.re)
            (fun i => (M.elements i * σ.toOp).trace.re) := by
  classical
  set A := fuchsCavesOperator ρ.toOp hσ with hA_def
  have hA_herm : A.IsHermitian := fuchsCavesOperator_isHermitian ρ.toOp hσ
  have hA_psd : A.PosSemidef := fuchsCavesOperator_posSemidef ρ.toOp hσ
  set lam := hA_herm.eigenvalues with hlam
  set P := eigenProjector hA_herm with hP
  obtain ⟨hAsum, hact⟩ := eigenProjector_action hA_herm
  refine ⟨n, eigenbasisPOVM hA_herm, ?_⟩
  have hPelt : ∀ i, (eigenbasisPOVM hA_herm).elements i = P i := fun _ => rfl
  -- `A σ A = ρ`: the load-bearing sandwich identity.
  have hρ_eq : ρ.toOp = A * σ.toOp * A := by
    rw [hA_def]
    exact (fuchsCavesOperator_sandwich
      (posSemidefOp_implies_mathlib ρ) hσ).symm
  have hActL : ∀ z, A * P z = (lam z : ℂ) • P z := fun z => (hact z).1
  have hActR : ∀ z, P z * A = (lam z : ℂ) • P z := fun z => (hact z).2
  -- Step 1: `Tr(P_z ρ) = λ_z² · Tr(P_z σ)` as a complex identity.
  have hp_eq : ∀ z, (P z * ρ.toOp).trace = (lam z : ℂ) ^ 2 * (P z * σ.toOp).trace := by
    intro z
    have hPσA : (P z * σ.toOp * A).trace = (lam z : ℂ) * (P z * σ.toOp).trace := by
      calc (P z * σ.toOp * A).trace
          = (A * (P z * σ.toOp)).trace := by
              rw [Matrix.trace_mul_comm (P z * σ.toOp) A]
        _ = ((A * P z) * σ.toOp).trace := by rw [Matrix.mul_assoc]
        _ = ((lam z : ℂ) • P z * σ.toOp).trace := by rw [hActL]
        _ = (lam z : ℂ) * (P z * σ.toOp).trace := by
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    calc (P z * ρ.toOp).trace
        = (P z * (A * σ.toOp * A)).trace := by rw [hρ_eq]
      _ = ((P z * A) * (σ.toOp * A)).trace := by simp only [Matrix.mul_assoc]
      _ = (((lam z : ℂ) • P z) * (σ.toOp * A)).trace := by rw [hActR]
      _ = (lam z : ℂ) * ((P z * σ.toOp) * A).trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
      _ = (lam z : ℂ) * ((lam z : ℂ) * (P z * σ.toOp).trace) := by rw [hPσA]
      _ = (lam z : ℂ) ^ 2 * (P z * σ.toOp).trace := by ring
  have hσ_psd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hP_psd : ∀ z, (P z).PosSemidef := fun z => eigenProjector_posSemidef hA_herm z
  have hq_nonneg : ∀ z, 0 ≤ (P z * σ.toOp).trace.re := fun z =>
    Quantum.Operators.trace_mul_psd_nonneg (P z) σ.toOp (hP_psd z) hσ_psd
  have hlam_nonneg : ∀ z, 0 ≤ lam z := fun z => hA_psd.eigenvalues_nonneg z
  have hp_re : ∀ z, (P z * ρ.toOp).trace.re = lam z ^ 2 * (P z * σ.toOp).trace.re := by
    intro z
    rw [hp_eq z, Complex.mul_re]
    have him : ((lam z : ℂ) ^ 2).im = 0 := by
      rw [show ((lam z : ℂ) ^ 2) = ((lam z ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_im]
    have hre : ((lam z : ℂ) ^ 2).re = lam z ^ 2 := by
      rw [show ((lam z : ℂ) ^ 2) = ((lam z ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [him, hre, zero_mul, sub_zero]
  have hsqrt_term : ∀ z, Real.sqrt ((P z * ρ.toOp).trace.re * (P z * σ.toOp).trace.re)
      = lam z * (P z * σ.toOp).trace.re := by
    intro z
    rw [hp_re z]
    have hsq : lam z ^ 2 * (P z * σ.toOp).trace.re * (P z * σ.toOp).trace.re
        = (lam z * (P z * σ.toOp).trace.re) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg (hlam_nonneg z) (hq_nonneg z))]
  have hsum : ∑ z, lam z * (P z * σ.toOp).trace.re = (A * σ.toOp).trace.re := by
    have hAσ : (A * σ.toOp).trace = ∑ z, (lam z : ℂ) * (P z * σ.toOp).trace := by
      conv_lhs => rw [hAsum, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [hAσ, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- `Tr(A σ).re = F(ρ, σ)`, now at the PosSemidefOp level.
  have hfid : (A * σ.toOp).trace.re = Quantum.Metrics.fidelity ρ σ.toPosSemidefOp := by
    rw [fidelity_eq_re_trace_sqrt_sandwich ρ σ.toPosSemidefOp]
    congr 1
    set Q := CFC.sqrt (CFC.sqrt σ.toOp * ρ.toOp * CFC.sqrt σ.toOp) with hQ
    have hAQ : A = hσ.inverseSqrt * Q * hσ.inverseSqrt := by
      rw [hA_def, fuchsCavesOperator, hQ]
    calc (A * σ.toOp).trace
        = (hσ.inverseSqrt * (Q * hσ.inverseSqrt * σ.toOp)).trace := by
            rw [hAQ]; congr 1; simp only [Matrix.mul_assoc]
      _ = ((Q * hσ.inverseSqrt * σ.toOp) * hσ.inverseSqrt).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (Q * (hσ.inverseSqrt * σ.toOp * hσ.inverseSqrt)).trace := by
            congr 1; simp only [Matrix.mul_assoc]
      _ = (Q * 1).trace := by rw [hσ.inverseSqrt_sandwich_eq_one]
      _ = Q.trace := by rw [Matrix.mul_one]
  -- Assemble.
  rw [classicalFidelity]
  simp only [hPelt]
  rw [← hfid, ← hsum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  exact (hsqrt_term z).symm

/-- The classical (Bhattacharyya) fidelity is symmetric in its two distributions. -/
lemma classicalFidelity_comm {α : Type*} [Fintype α] (p q : α → ℝ) :
    classicalFidelity p q = classicalFidelity q p := by
  unfold classicalFidelity
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]

/-- Symmetry of the Uhlmann fidelity for density operators: `F(ρ, σ) = F(σ, ρ)`. -/
lemma densityOp_fidelity_comm {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    DensityOp.fidelity ρ σ = DensityOp.fidelity σ ρ :=
  fidelity_comm ρ.toPosSemidefOp σ.toPosSemidefOp

/-- **Fuchs–Caves achievability for a positive-definite first argument `ρ`.**

The role-swapped companion of `fidelity_eq_classicalFidelity_measurement_of_posDef`:
when `ρ` (rather than `σ`) is positive definite, the eigenbasis measurement of the
Fuchs–Caves operator built from `(σ, ρ)` achieves the quantum fidelity. -/
theorem fidelity_eq_classicalFidelity_measurement_of_posDef_left {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) (hρ : ρ.toOp.PosDef) :
    ∃ (k : ℕ) (M : InfoTheory.Measurement.POVM n k),
      DensityOp.fidelity ρ σ
        = classicalFidelity (fun i => (M.elements i * ρ.toOp).trace.re)
            (fun i => (M.elements i * σ.toOp).trace.re) := by
  obtain ⟨k, M, hM⟩ := fidelity_eq_classicalFidelity_measurement_of_posDef σ ρ hρ
  refine ⟨k, M, ?_⟩
  rw [densityOp_fidelity_comm ρ σ, hM, classicalFidelity_comm]

/-!
## Support restriction to `range σ`

The both-singular case is handled by compressing both operators to `range σ`, where `σ`
becomes positive definite and the proved `..._of_posDef_psd` achievability applies.  The
support isometry `V : Matrix (Fin n) (Fin r) ℂ` has the positive-eigenvalue eigenvectors of
`σ.toOp` as columns (`r = ` number of strictly positive eigenvalues).  Everything is built
locally from the plain `Matrix.IsHermitian` spectral data of `σ.toOp` (the same
`eigenvectorBasis`/`eigenvalues`/`eigenvectorUnitary` machinery as `eigenProjector`),
without importing heavier general support-compression infrastructure.
-/

/-- Indices of the strictly positive eigenvalues of `σ.toOp`. -/
noncomputable def posEigIndices {n : ℕ} (σ : DensityOp n) : Finset (Fin n) :=
  let hσH := (posSemidefOp_implies_mathlib σ.toPosSemidefOp).isHermitian
  Finset.univ.filter (fun i => hσH.eigenvalues i ≠ 0)

/-- Dimension of `range σ`, counted via the strictly positive eigenvalues of `σ.toOp`. -/
noncomputable def posEigDim {n : ℕ} (σ : DensityOp n) : ℕ :=
  (posEigIndices σ).card

/-- The support of a density operator is nonempty: a trace-one operator cannot have all
eigenvalues zero, so it has at least one strictly positive eigenvalue. -/
lemma posEigDim_pos {n : ℕ} [NeZero n] (σ : DensityOp n) : 0 < posEigDim σ := by
  classical
  set hσH := (posSemidefOp_implies_mathlib σ.toPosSemidefOp).isHermitian with hσH_def
  rw [posEigDim, Finset.card_pos]
  -- Some eigenvalue is nonzero, else the trace would be `0`, not `1`.
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hall : ∀ i, hσH.eigenvalues i = 0 := by
    intro i
    by_contra hi
    have hmem : i ∈ posEigIndices σ := by
      simp only [posEigIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  have htr : (σ.toOp.trace).re = ∑ i, hσH.eigenvalues i := by
    rw [hσH.trace_eq_sum_eigenvalues, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Complex.ofReal_re _
  have hsum0 : (∑ i, hσH.eigenvalues i) = 0 := Finset.sum_eq_zero (fun i _ => hall i)
  have htr1 : (σ.toOp.trace).re = 1 := by rw [σ.trace_one]; simp
  rw [htr1, hsum0] at htr
  norm_num at htr

instance posEigDim_neZero {n : ℕ} [NeZero n] (σ : DensityOp n) : NeZero (posEigDim σ) :=
  ⟨Nat.ne_of_gt (posEigDim_pos σ)⟩

/-- The local Hermitian view of `σ.toOp`, supplying the spectral data used by the support
isometry. -/
noncomputable abbrev sigmaHerm {n : ℕ} (σ : DensityOp n) : (σ.toOp).IsHermitian :=
  (posSemidefOp_implies_mathlib σ.toPosSemidefOp).isHermitian

/-- The order embedding enumerating the positive-eigenvalue indices of `σ.toOp`. -/
noncomputable def posEigEmb {n : ℕ} (σ : DensityOp n) :
    Fin (posEigDim σ) ↪o Fin n :=
  (posEigIndices σ).orderEmbOfFin rfl

lemma posEigEmb_mem {n : ℕ} (σ : DensityOp n) (i : Fin (posEigDim σ)) :
    posEigEmb σ i ∈ posEigIndices σ :=
  Finset.orderEmbOfFin_mem _ _ i

/-- The eigenvalue selected by `posEigEmb σ i` is strictly positive. -/
lemma posEigEmb_eigenvalue_pos {n : ℕ} (σ : DensityOp n) (i : Fin (posEigDim σ)) :
    0 < (sigmaHerm σ).eigenvalues (posEigEmb σ i) := by
  have hnn : 0 ≤ (sigmaHerm σ).eigenvalues (posEigEmb σ i) :=
    (posSemidefOp_implies_mathlib σ.toPosSemidefOp).eigenvalues_nonneg _
  have hne : (sigmaHerm σ).eigenvalues (posEigEmb σ i) ≠ 0 :=
    (Finset.mem_filter.mp (posEigEmb_mem σ i)).2
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- **The support isometry of `σ`**: the `n × r` matrix whose columns are the
positive-eigenvalue eigenvectors of `σ.toOp` (`r = posEigDim σ`). -/
noncomputable def supportIso {n : ℕ} (σ : DensityOp n) :
    Matrix (Fin n) (Fin (posEigDim σ)) ℂ :=
  fun i j => (((sigmaHerm σ).eigenvectorBasis (posEigEmb σ j)).ofLp) i

/-- The support isometry has orthonormal columns: `V† V = 1`. -/
lemma supportIso_isometry {n : ℕ} (σ : DensityOp n) :
    (supportIso σ).conjTranspose * supportIso σ = 1 := by
  classical
  have hdot : ∀ a b : Fin n,
      star (((sigmaHerm σ).eigenvectorBasis a).ofLp) ⬝ᵥ
          (((sigmaHerm σ).eigenvectorBasis b).ofLp) =
        if a = b then (1 : ℂ) else 0 := by
    intro a b
    rw [dotProduct_comm]
    have h := orthonormal_iff_ite.mp (sigmaHerm σ).eigenvectorBasis.orthonormal a b
    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h
  ext i j
  rw [Matrix.mul_apply]
  have hsum :
      ∑ k, (supportIso σ).conjTranspose i k * supportIso σ k j =
        star (((sigmaHerm σ).eigenvectorBasis (posEigEmb σ i)).ofLp) ⬝ᵥ
          (((sigmaHerm σ).eigenvectorBasis (posEigEmb σ j)).ofLp) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [supportIso, Matrix.conjTranspose_apply, star]
  rw [hsum, hdot]
  by_cases hij : i = j
  · subst hij; simp
  · have hneq : posEigEmb σ i ≠ posEigEmb σ j :=
      fun h => hij ((posEigEmb σ).injective h)
    simp [hneq, hij]

/-- The eigenvector unitary of `σ.toOp`, as a plain matrix. -/
noncomputable def sigmaU {n : ℕ} (σ : DensityOp n) : Matrix (Fin n) (Fin n) ℂ :=
  (↑(sigmaHerm σ).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)

/-- The diagonal eigenvalue matrix of `σ.toOp`. -/
noncomputable def sigmaD {n : ℕ} (σ : DensityOp n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => ((sigmaHerm σ).eigenvalues i : ℂ))

lemma sigmaU_apply {n : ℕ} (σ : DensityOp n) (a i : Fin n) :
    sigmaU σ a i = (((sigmaHerm σ).eigenvectorBasis i).ofLp) a := by
  rw [sigmaU, (sigmaHerm σ).eigenvectorUnitary_apply]

lemma sigmaU_unitary_left {n : ℕ} (σ : DensityOp n) :
    (sigmaU σ).conjTranspose * sigmaU σ = 1 := by
  simpa [sigmaU, star_eq_conjTranspose] using
    UnitaryGroup.star_mul_self (sigmaHerm σ).eigenvectorUnitary

lemma sigmaU_unitary_right {n : ℕ} (σ : DensityOp n) :
    sigmaU σ * (sigmaU σ).conjTranspose = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := Fin n) (n := Fin n) (R := ℂ)
    (A := (sigmaU σ).conjTranspose) (B := sigmaU σ) (by rfl)).mp (sigmaU_unitary_left σ)

/-- Spectral decomposition: `σ.toOp = U D U†`. -/
lemma sigma_spectral {n : ℕ} (σ : DensityOp n) :
    σ.toOp = sigmaU σ * sigmaD σ * (sigmaU σ).conjTranspose := by
  have h := (sigmaHerm σ).spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  rw [sigmaU, sigmaD]
  have hDeq : (Matrix.diagonal (fun i => ((sigmaHerm σ).eigenvalues i : ℂ))) =
      Matrix.diagonal (RCLike.ofReal ∘ (sigmaHerm σ).eigenvalues) := by
    rfl
  rw [hDeq]
  exact h

/-- The column-selector matrix picking the positive-spectrum coordinates: `V = U · S`. -/
noncomputable def supportSel {n : ℕ} (σ : DensityOp n) :
    Matrix (Fin n) (Fin (posEigDim σ)) ℂ :=
  fun i j => if i = posEigEmb σ j then 1 else 0

lemma supportIso_eq_U_mul_sel {n : ℕ} (σ : DensityOp n) :
    supportIso σ = sigmaU σ * supportSel σ := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (posEigEmb σ j)]
  · simp [supportIso, supportSel, sigmaU_apply]
  · intro b _ hb
    simp [supportSel, hb]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

lemma supportSel_isometry {n : ℕ} (σ : DensityOp n) :
    (supportSel σ).conjTranspose * supportSel σ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [supportSel, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · have hneq : posEigEmb σ i ≠ posEigEmb σ j :=
      fun h => hij ((posEigEmb σ).injective h)
    rw [Matrix.one_apply_ne hij, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = posEigEmb σ i
    · subst hxi
      simp [supportSel, Matrix.conjTranspose_apply, hneq]
    · simp [supportSel, Matrix.conjTranspose_apply, hxi]

/-- Sandwiching a matrix by the selector reads off the principal submatrix indexed by the
positive-eigenvalue embedding. -/
lemma supportSel_sandwich_apply {n : ℕ} (σ : DensityOp n)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin (posEigDim σ)) :
    ((supportSel σ).conjTranspose * A * supportSel σ) i j =
      A (posEigEmb σ i) (posEigEmb σ j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (posEigEmb σ j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (posEigEmb σ i)]
    · simp [supportSel, Matrix.conjTranspose_apply]
    · intro b _ hbi
      simp [supportSel, Matrix.conjTranspose_apply, hbi]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  · intro b _ hbj
    simp [supportSel, hbj]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

/-- An index lies in the range of `posEigEmb` iff its eigenvalue is nonzero. -/
lemma mem_range_posEigEmb_iff {n : ℕ} (σ : DensityOp n) (k : Fin n) :
    (∃ x, posEigEmb σ x = k) ↔ (sigmaHerm σ).eigenvalues k ≠ 0 := by
  classical
  have hrange : Set.range (posEigEmb σ) = (posEigIndices σ : Set (Fin n)) := by
    rw [posEigEmb]
    exact Finset.range_orderEmbOfFin (posEigIndices σ) rfl
  constructor
  · rintro ⟨x, rfl⟩
    exact (Finset.mem_filter.mp (posEigEmb_mem σ x)).2
  · intro hk
    have hmem : k ∈ posEigIndices σ := by
      simp only [posEigIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
    have : k ∈ Set.range (posEigEmb σ) := by rw [hrange]; exact hmem
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩

/-- The coordinate projector `S Sᵀ` onto the positive-eigenvalue coordinates, in the
eigenbasis: it is the diagonal `1`-on-positive-indices matrix. -/
lemma sel_mul_selConjTranspose_eq_diagonal {n : ℕ} (σ : DensityOp n) :
    supportSel σ * (supportSel σ).conjTranspose =
      Matrix.diagonal (fun k => if (sigmaHerm σ).eigenvalues k ≠ 0 then (1 : ℂ) else 0) := by
  classical
  ext i k
  rw [Matrix.mul_apply]
  by_cases hik : i = k
  · subst hik
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : ∃ x, posEigEmb σ x = i
    · obtain ⟨x, rfl⟩ := hi
      rw [Finset.sum_eq_single x]
      · have hne := (mem_range_posEigEmb_iff σ (posEigEmb σ x)).mp ⟨x, rfl⟩
        simp [supportSel, Matrix.conjTranspose_apply, hne]
      · intro b _ hbx
        simp [supportSel, Matrix.conjTranspose_apply, Ne.symm hbx]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    · have hi0 : ¬ (sigmaHerm σ).eigenvalues i ≠ 0 :=
        fun hne => hi ((mem_range_posEigEmb_iff σ i).mpr hne)
      simp only [hi0, ite_false]
      apply Finset.sum_eq_zero
      intro x _
      have hix : i ≠ posEigEmb σ x := fun h => hi ⟨x, h.symm⟩
      simp [supportSel, Matrix.conjTranspose_apply, hix]
  · rw [Matrix.diagonal_apply_ne _ hik]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hix : i = posEigEmb σ x
    · have hkx : k ≠ posEigEmb σ x := fun h => hik (hix.trans h.symm)
      simp [supportSel, Matrix.conjTranspose_apply, hkx]
    · simp [supportSel, Matrix.conjTranspose_apply, hix]

/-- The coordinate projector fixes the eigenvalue diagonal: `D · (S Sᵀ) = D`. -/
lemma sigmaD_mul_coordProj {n : ℕ} (σ : DensityOp n) :
    sigmaD σ * (supportSel σ * (supportSel σ).conjTranspose) = sigmaD σ := by
  rw [sel_mul_selConjTranspose_eq_diagonal, sigmaD, Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  by_cases hk : (sigmaHerm σ).eigenvalues k ≠ 0
  · simp [hk]
  · push Not at hk
    simp [hk]

/-- The coordinate projector fixes the eigenvalue diagonal on the left: `(S Sᵀ) · D = D`. -/
lemma coordProj_mul_sigmaD {n : ℕ} (σ : DensityOp n) :
    (supportSel σ * (supportSel σ).conjTranspose) * sigmaD σ = sigmaD σ := by
  rw [sel_mul_selConjTranspose_eq_diagonal, sigmaD, Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  by_cases hk : (sigmaHerm σ).eigenvalues k ≠ 0
  · simp [hk]
  · push Not at hk
    simp [hk]

/-- The compression of `σ` to its support: `V† σ.toOp V`, the `r × r` diagonal of the
strictly positive eigenvalues. -/
noncomputable def compressedSigmaMat {n : ℕ} (σ : DensityOp n) :
    Matrix (Fin (posEigDim σ)) (Fin (posEigDim σ)) ℂ :=
  Matrix.diagonal (fun i => ((sigmaHerm σ).eigenvalues (posEigEmb σ i) : ℂ))

/-- The conjugation `U† σ U = D`. -/
lemma sigmaU_conjTranspose_mul_sigma_mul_sigmaU {n : ℕ} (σ : DensityOp n) :
    (sigmaU σ).conjTranspose * σ.toOp * sigmaU σ = sigmaD σ := by
  have hUL := sigmaU_unitary_left σ
  have hUR := sigmaU_unitary_right σ
  calc (sigmaU σ).conjTranspose * σ.toOp * sigmaU σ
      = (sigmaU σ).conjTranspose * (sigmaU σ * sigmaD σ * (sigmaU σ).conjTranspose) *
          sigmaU σ := by rw [sigma_spectral]
    _ = ((sigmaU σ).conjTranspose * sigmaU σ) * sigmaD σ *
          ((sigmaU σ).conjTranspose * sigmaU σ) := by
            simp only [Matrix.mul_assoc]
    _ = sigmaD σ := by rw [hUL, Matrix.one_mul, Matrix.mul_one]

/-- The support compression of `σ` equals the diagonal of selected positive eigenvalues:
`V† σ.toOp V = compressedSigmaMat σ`. -/
lemma supportIso_conjTranspose_mul_sigma_mul_supportIso {n : ℕ} (σ : DensityOp n) :
    (supportIso σ).conjTranspose * σ.toOp * supportIso σ = compressedSigmaMat σ := by
  rw [supportIso_eq_U_mul_sel]
  have hrw : (sigmaU σ * supportSel σ).conjTranspose * σ.toOp * (sigmaU σ * supportSel σ) =
      (supportSel σ).conjTranspose *
        ((sigmaU σ).conjTranspose * σ.toOp * sigmaU σ) * supportSel σ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hrw, sigmaU_conjTranspose_mul_sigma_mul_sigmaU]
  ext i j
  rw [supportSel_sandwich_apply]
  by_cases hij : i = j
  · subst hij
    simp [sigmaD, compressedSigmaMat]
  · have hneq : posEigEmb σ i ≠ posEigEmb σ j :=
      fun h => hij ((posEigEmb σ).injective h)
    simp [sigmaD, compressedSigmaMat, hneq, hij]

/-- `σ` is supported on `range σ`: `σ.toOp = V · (V† σ.toOp V) · V†`. -/
lemma sigma_eq_supportIso_compress {n : ℕ} (σ : DensityOp n) :
    σ.toOp = supportIso σ *
      ((supportIso σ).conjTranspose * σ.toOp * supportIso σ) * (supportIso σ).conjTranspose := by
  rw [supportIso_conjTranspose_mul_sigma_mul_supportIso, supportIso_eq_U_mul_sel]
  -- `V (V†σV) V† = U (S S† D S S†) U† = U D U† = σ`.
  have hcompr : compressedSigmaMat σ =
      (supportSel σ).conjTranspose * sigmaD σ * supportSel σ := by
    ext i j
    rw [supportSel_sandwich_apply]
    by_cases hij : i = j
    · subst hij; simp [sigmaD, compressedSigmaMat]
    · have hneq : posEigEmb σ i ≠ posEigEmb σ j :=
        fun h => hij ((posEigEmb σ).injective h)
      simp [sigmaD, compressedSigmaMat, hneq, hij]
  rw [hcompr]
  symm
  calc sigmaU σ * supportSel σ *
        ((supportSel σ).conjTranspose * sigmaD σ * supportSel σ) *
        (sigmaU σ * supportSel σ).conjTranspose
      = sigmaU σ *
          ((supportSel σ * (supportSel σ).conjTranspose) * sigmaD σ *
            (supportSel σ * (supportSel σ).conjTranspose)) *
          (sigmaU σ).conjTranspose := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = sigmaU σ * sigmaD σ * (sigmaU σ).conjTranspose := by
        rw [coordProj_mul_sigmaD, sigmaD_mul_coordProj]
    _ = σ.toOp := (sigma_spectral σ).symm

/-- The orthogonal projector onto `range σ`: `P = V V†`. -/
noncomputable def supportProj {n : ℕ} (σ : DensityOp n) : Matrix (Fin n) (Fin n) ℂ :=
  supportIso σ * (supportIso σ).conjTranspose

/-- The square root of `σ.toOp` is fixed by the support projector on the right:
`√σ · (V V†) = √σ`. -/
lemma sqrt_sigma_mul_supportProj {n : ℕ} (σ : DensityOp n) :
    CFC.sqrt σ.toOp * supportProj σ = CFC.sqrt σ.toOp := by
  -- `√σ = V (√(V†σV)) V†`, so `√σ · VV† = V √(V†σV) (V†V) V† = √σ`.
  have hσ_psd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hcompr_psd :
      ((supportIso σ).conjTranspose * σ.toOp * supportIso σ).PosSemidef := by
    have h := hσ_psd.mul_mul_conjTranspose_same (supportIso σ).conjTranspose
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hsqrt : CFC.sqrt σ.toOp =
      supportIso σ *
        CFC.sqrt ((supportIso σ).conjTranspose * σ.toOp * supportIso σ) *
        (supportIso σ).conjTranspose := by
    conv_lhs => rw [sigma_eq_supportIso_compress σ]
    exact TraceNormHoelder.cfc_sqrt_isometry_conj (supportIso σ)
      ((supportIso σ).conjTranspose * σ.toOp * supportIso σ)
      (supportIso_isometry σ) hcompr_psd
  rw [supportProj]
  conv_lhs => rw [hsqrt]
  rw [show supportIso σ *
        CFC.sqrt ((supportIso σ).conjTranspose * σ.toOp * supportIso σ) *
        (supportIso σ).conjTranspose * (supportIso σ * (supportIso σ).conjTranspose)
      = supportIso σ *
          CFC.sqrt ((supportIso σ).conjTranspose * σ.toOp * supportIso σ) *
          (((supportIso σ).conjTranspose * supportIso σ) * (supportIso σ).conjTranspose) from by
        simp only [Matrix.mul_assoc]]
  rw [supportIso_isometry σ, Matrix.one_mul]
  conv_rhs => rw [hsqrt]

/-- The support compression of `σ` is positive definite on `range σ`. -/
lemma compressedSigmaMat_posDef {n : ℕ} (σ : DensityOp n) :
    (compressedSigmaMat σ).PosDef := by
  rw [compressedSigmaMat]
  apply Matrix.PosDef.diagonal
  intro i
  have hpos : 0 < (sigmaHerm σ).eigenvalues (posEigEmb σ i) := posEigEmb_eigenvalue_pos σ i
  exact_mod_cast hpos

lemma compressedSigmaMat_isHermitian {n : ℕ} (σ : DensityOp n) :
    (compressedSigmaMat σ).IsHermitian :=
  (compressedSigmaMat_posDef σ).isHermitian

/-- The trace of the support compression of `σ` is `1`: the zero eigenvalues contribute
nothing, so summing the selected positive eigenvalues recovers `Tr σ = 1`. -/
lemma compressedSigmaMat_trace {n : ℕ} [NeZero n] (σ : DensityOp n) :
    (compressedSigmaMat σ).trace = 1 := by
  classical
  have hsumsel : ∑ i, (sigmaHerm σ).eigenvalues (posEigEmb σ i) =
      ∑ k, (sigmaHerm σ).eigenvalues k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => (sigmaHerm σ).eigenvalues k ≠ 0) (sigmaHerm σ).eigenvalues]
    have hzero : ∑ k ∈ Finset.univ.filter (fun k => ¬ (sigmaHerm σ).eigenvalues k ≠ 0),
        (sigmaHerm σ).eigenvalues k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, not_not] at hk
      exact hk.2
    rw [hzero, add_zero]
    -- reindex the positive-spectrum sum through the order embedding
    refine Finset.sum_bij
      (fun (i : Fin (posEigDim σ)) _ => posEigEmb σ i) ?_ ?_ ?_ ?_
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp (posEigEmb_mem σ i)).2
    · intro i _ j _ hij
      exact (posEigEmb σ).injective hij
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨x, hx⟩ := (mem_range_posEigEmb_iff σ k).mpr hk
      exact ⟨x, Finset.mem_univ _, hx⟩
    · intro i _; rfl
  have htr : (compressedSigmaMat σ).trace =
      ((∑ i, (sigmaHerm σ).eigenvalues (posEigEmb σ i) : ℝ) : ℂ) := by
    rw [compressedSigmaMat, Matrix.trace_diagonal]
    push_cast
    rfl
  rw [htr, hsumsel]
  rw [show (∑ k, (sigmaHerm σ).eigenvalues k : ℝ) = (σ.toOp.trace).re from ?_]
  · rw [σ.trace_one]; simp
  · rw [(sigmaHerm σ).trace_eq_sum_eigenvalues, Complex.re_sum]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).symm
    exact (Complex.ofReal_re _).symm

/-- The support compression of `σ` packaged as a density operator on `range σ`. -/
noncomputable def compressedSigmaDensity {n : ℕ} [NeZero n] (σ : DensityOp n) :
    DensityOp (posEigDim σ) where
  toPosSemidefOp :=
    { toHermitianOp := ⟨compressedSigmaMat σ, compressedSigmaMat_isHermitian σ⟩
      pos_semidef := fun x =>
        posSemidef_re_quadraticForm_nonneg (compressedSigmaMat_posDef σ).posSemidef x }
  trace_one := compressedSigmaMat_trace σ

lemma compressedSigmaDensity_toOp {n : ℕ} [NeZero n] (σ : DensityOp n) :
    (compressedSigmaDensity σ).toOp = compressedSigmaMat σ := rfl

lemma compressedSigmaDensity_posDef {n : ℕ} [NeZero n] (σ : DensityOp n) :
    (compressedSigmaDensity σ).toOp.PosDef := by
  rw [compressedSigmaDensity_toOp]; exact compressedSigmaMat_posDef σ

/-- The support compression of `ρ` to `range σ`: `V† ρ.toOp V`, only positive
semidefinite (sub-normalized, since `ρ` may have mass outside `range σ`). -/
noncomputable def compressedRhoPSD {n : ℕ} (σ ρ : DensityOp n) :
    PosSemidefOp (posEigDim σ) where
  toHermitianOp :=
    ⟨(supportIso σ).conjTranspose * ρ.toOp * supportIso σ, by
      have hρH : ρ.toOp.IsHermitian := ρ.toPosSemidefOp.toHermitianOp.isHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hρH.eq, Matrix.mul_assoc]⟩
  pos_semidef := fun x => by
    have hρ_psd : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    have h := hρ_psd.mul_mul_conjTranspose_same (supportIso σ).conjTranspose
    rw [Matrix.conjTranspose_conjTranspose] at h
    exact posSemidef_re_quadraticForm_nonneg h x

lemma compressedRhoPSD_toOp {n : ℕ} (σ ρ : DensityOp n) :
    (compressedRhoPSD σ ρ).toOp = (supportIso σ).conjTranspose * ρ.toOp * supportIso σ := rfl

/-- The support projector `P = V V†` is a Hermitian idempotent. -/
lemma supportProj_isHermitian {n : ℕ} (σ : DensityOp n) :
    (supportProj σ).IsHermitian := by
  unfold supportProj Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma supportProj_idem {n : ℕ} (σ : DensityOp n) :
    supportProj σ * supportProj σ = supportProj σ := by
  unfold supportProj
  rw [show supportIso σ * (supportIso σ).conjTranspose *
        (supportIso σ * (supportIso σ).conjTranspose)
      = supportIso σ * ((supportIso σ).conjTranspose * supportIso σ) *
        (supportIso σ).conjTranspose from by simp only [Matrix.mul_assoc]]
  rw [supportIso_isometry σ, Matrix.mul_one]

/-- The complementary projector `1 - V V†` onto the orthogonal complement of `range σ` is
positive semidefinite. -/
lemma one_sub_supportProj_posSemidef {n : ℕ} (σ : DensityOp n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ).PosSemidef := by
  have hidem : ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ) *
      ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ) =
      (1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, supportProj_idem]
    abel
  have hH : ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (supportProj_isHermitian σ).eq]
  have hform : ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ) =
      ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ).conjTranspose *
        ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ) := by
    rw [hH.eq, hidem]
  rw [hform]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The support projector fixes `σ` on the left: `(V V†) σ = σ`. -/
lemma supportProj_mul_sigma {n : ℕ} (σ : DensityOp n) :
    supportProj σ * σ.toOp = σ.toOp := by
  set Vc := (supportIso σ).conjTranspose with hVc
  have hkey : supportProj σ * σ.toOp =
      supportIso σ * Vc * (supportIso σ * (Vc * σ.toOp * supportIso σ) * Vc) := by
    unfold supportProj
    rw [← hVc]
    congr 1
    exact sigma_eq_supportIso_compress σ
  rw [hkey,
    show supportIso σ * Vc * (supportIso σ * (Vc * σ.toOp * supportIso σ) * Vc)
      = supportIso σ * (Vc * supportIso σ) * (Vc * σ.toOp * supportIso σ) * Vc from by
        simp only [Matrix.mul_assoc],
    hVc, supportIso_isometry σ, Matrix.mul_one]
  exact (sigma_eq_supportIso_compress σ).symm

/-- The complement carries zero probability against `σ`: `Tr((1 - V V†) σ) = 0`, because
`σ` is supported on `range σ` and `V V† σ = σ`. -/
lemma trace_one_sub_supportProj_mul_sigma {n : ℕ} (σ : DensityOp n) :
    (((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ) * σ.toOp).trace = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, supportProj_mul_sigma σ, sub_self, Matrix.trace_zero]

/-- **Embed a POVM on `range σ` to an ambient POVM via the support isometry.**

Given a POVM `Ñ` on the `r`-dimensional support of `σ`, its support embedding is the
ambient `(k+1)`-outcome POVM whose first `k` elements are `V Ñ_i V†` and whose extra
(`Fin.last`) outcome is the complement projector `1 - V V†`.  The complement absorbs the
mass that the embedded measurement loses off `range σ`. -/
noncomputable def POVM.supportEmbed {n : ℕ} (σ : DensityOp n) {k : ℕ}
    (N : InfoTheory.Measurement.POVM (posEigDim σ) k) :
    InfoTheory.Measurement.POVM n (k + 1) where
  elements := Fin.lastCases ((1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ)
    (fun i => supportIso σ * N.elements i * (supportIso σ).conjTranspose)
  hermitian := by
    refine Fin.lastCases ?_ ?_
    · rw [Fin.lastCases_last]; exact (one_sub_supportProj_posSemidef σ).isHermitian
    · intro i
      rw [Fin.lastCases_castSucc]
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, (N.hermitian i).eq, Matrix.mul_assoc]
  positive := by
    refine Fin.lastCases ?_ ?_
    · intro x
      rw [Fin.lastCases_last]
      exact posSemidef_re_quadraticForm_nonneg (one_sub_supportProj_posSemidef σ) x
    · intro i x
      rw [Fin.lastCases_castSucc]
      have hNi : (N.elements i).PosSemidef :=
        InfoTheory.Measurement.povm_element_is_mathlib_psd N i
      exact posSemidef_re_quadraticForm_nonneg
        (hNi.mul_mul_conjTranspose_same (supportIso σ)) x
  complete := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have hsum : ∑ i : Fin k, supportIso σ * N.elements i * (supportIso σ).conjTranspose =
        supportIso σ * (∑ i, N.elements i) * (supportIso σ).conjTranspose := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    rw [hsum, N.complete, Matrix.mul_one]
    have : supportIso σ * (supportIso σ).conjTranspose = supportProj σ := rfl
    rw [this]
    abel

/-- Trace bookkeeping: tracing an embedded POVM element against an ambient state equals
tracing the original element against the compressed state.  `Tr((V A V†) B) = Tr(A (V† B V))`. -/
lemma trace_supportEmbed_mul {n : ℕ} (σ : DensityOp n)
    (A : Matrix (Fin (posEigDim σ)) (Fin (posEigDim σ)) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ((supportIso σ * A * (supportIso σ).conjTranspose) * B).trace =
      (A * ((supportIso σ).conjTranspose * B * supportIso σ)).trace := by
  calc ((supportIso σ * A * (supportIso σ).conjTranspose) * B).trace
      = ((supportIso σ * A) * ((supportIso σ).conjTranspose * B)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (((supportIso σ).conjTranspose * B) * (supportIso σ * A)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = (A * ((supportIso σ).conjTranspose * B * supportIso σ)).trace := by
          rw [show (supportIso σ).conjTranspose * B * (supportIso σ * A)
              = ((supportIso σ).conjTranspose * B * supportIso σ) * A from by
                simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]

/-- `P ρ P` packaged as a positive semidefinite operator. -/
noncomputable def supportProjConjRho {n : ℕ} (σ ρ : DensityOp n) : PosSemidefOp n where
  toHermitianOp :=
    ⟨supportProj σ * ρ.toOp * supportProj σ, by
      have hρH : ρ.toOp.IsHermitian := ρ.toPosSemidefOp.toHermitianOp.isHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        (supportProj_isHermitian σ).eq, hρH.eq, Matrix.mul_assoc]⟩
  pos_semidef := fun x => by
    have hρ_psd : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    have h := hρ_psd.conjTranspose_mul_mul_same (supportProj σ)
    rw [(supportProj_isHermitian σ).eq] at h
    exact posSemidef_re_quadraticForm_nonneg h x

lemma supportProjConjRho_toOp {n : ℕ} (σ ρ : DensityOp n) :
    (supportProjConjRho σ ρ).toOp = supportProj σ * ρ.toOp * supportProj σ := rfl

/-- The support projector fixes `√σ` on the left: `(V V†) √σ = √σ` (transpose of
`sqrt_sigma_mul_supportProj`). -/
lemma supportProj_mul_sqrt_sigma {n : ℕ} (σ : DensityOp n) :
    supportProj σ * CFC.sqrt σ.toOp = CFC.sqrt σ.toOp := by
  have h := congrArg Matrix.conjTranspose (sqrt_sigma_mul_supportProj σ)
  rw [Matrix.conjTranspose_mul, (supportProj_isHermitian σ).eq] at h
  have hsqrtH : (CFC.sqrt σ.toOp).IsHermitian :=
    (sqrt_posSemidef σ.toOp).isHermitian
  rwa [hsqrtH.eq] at h

/-- The conjugation `(V V†) ρ (V V†) = V ρ̃ V†` with `ρ̃ = V† ρ V`. -/
lemma supportProj_sandwich_eq_supportIso_conj {n : ℕ} (σ ρ : DensityOp n) :
    supportProj σ * ρ.toOp * supportProj σ =
      supportIso σ * (compressedRhoPSD σ ρ).toOp * (supportIso σ).conjTranspose := by
  rw [compressedRhoPSD_toOp]
  unfold supportProj
  simp only [Matrix.mul_assoc]

/-- The fidelity is unchanged by sandwiching `ρ` with the support projector:
`F(ρ, σ) = F(P ρ P, σ)`, because `√σ · P = √σ`. -/
lemma fidelity_eq_fidelity_supportProj_conj {n : ℕ} [NeZero n] (σ ρ : DensityOp n)
    (PρP : PosSemidefOp n) (hPρP : PρP.toOp = supportProj σ * ρ.toOp * supportProj σ) :
    Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp =
      Quantum.Metrics.fidelity PρP σ.toPosSemidefOp := by
  rw [fidelity_eq_re_trace_sqrt_sandwich ρ.toPosSemidefOp σ.toPosSemidefOp,
    fidelity_eq_re_trace_sqrt_sandwich PρP σ.toPosSemidefOp]
  -- `√σ ρ √σ = √σ (P ρ P) √σ` since `√σ P = √σ` and `P √σ = √σ`.
  have hinner : CFC.sqrt σ.toOp * ρ.toOp * CFC.sqrt σ.toOp =
      CFC.sqrt σ.toOp * PρP.toOp * CFC.sqrt σ.toOp := by
    rw [hPρP]
    calc CFC.sqrt σ.toOp * ρ.toOp * CFC.sqrt σ.toOp
        = (CFC.sqrt σ.toOp * supportProj σ) * ρ.toOp *
            (supportProj σ * CFC.sqrt σ.toOp) := by
          rw [sqrt_sigma_mul_supportProj σ, supportProj_mul_sqrt_sigma σ]
      _ = CFC.sqrt σ.toOp * (supportProj σ * ρ.toOp * supportProj σ) * CFC.sqrt σ.toOp := by
          simp only [Matrix.mul_assoc]
  rw [hinner]

/-- **Fuchs–Caves achievability by support restriction.**

The inverse-square-root construction
(`fidelity_eq_classicalFidelity_measurement_of_posDef`) requires one of the two states
to be invertible.  The support-restricted construction below needs no invertibility and
holds for all density operators `ρ`, `σ`; it is the case used by
`fidelity_eq_classicalFidelity_measurement` when *both* `ρ` and `σ` are rank deficient
(neither is positive definite), which is what the name records.  The construction is
carried out on `range σ`: compress `ρ` and `σ` by the
support isometry `V` to `σt = V† σ V` (positive definite, `compressedSigmaDensity`) and
`ρt = V† ρ V` (positive semidefinite but generally sub-normalized, `compressedRhoPSD`).

The quantum fidelity is preserved by this compression: `√σ` is fixed by the support
projector `P = V V†`, so `F(ρ, σ) = F(P ρ P, σ) = F(ρt, σt)`
(`fidelity_eq_fidelity_supportProj_conj`, then `fidelity_isometry_conj_of_toOp_eq`).  The
compressed achievability `fidelity_eq_classicalFidelity_measurement_of_posDef_psd` (the
sub-normalized-`ρ` generalization, since `ρt` may have trace `< 1`) yields a POVM `N` on
`range σ`; embedding it back with one extra support-complement outcome
(`POVM.supportEmbed`) gives the ambient POVM.  The extra outcome carries zero probability
against `σ` (`trace_one_sub_supportProj_mul_sigma`), so the classical fidelity is unchanged.

References: Chen–Zhu, arXiv:2511.22487; Wilde, *From Classical to Quantum Shannon
Theory*, Lecture 16 (support restriction of the Fuchs–Caves measurement). -/
theorem fidelity_eq_classicalFidelity_measurement_of_bothSingular {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) :
    ∃ (k : ℕ) (M : InfoTheory.Measurement.POVM n k),
      DensityOp.fidelity ρ σ
        = classicalFidelity (fun i => (M.elements i * ρ.toOp).trace.re)
            (fun i => (M.elements i * σ.toOp).trace.re) := by
  classical
  set V := supportIso σ with hVdef
  set ρt := compressedRhoPSD σ ρ with hρtdef
  set σt := compressedSigmaDensity σ with hσtdef
  -- Achievability on the compressed support, where `σt` is positive definite.
  obtain ⟨k, N, hN⟩ :=
    fidelity_eq_classicalFidelity_measurement_of_posDef_psd ρt σt
      (compressedSigmaDensity_posDef σ)
  refine ⟨k + 1, POVM.supportEmbed σ N, ?_⟩
  -- The ambient quantum fidelity equals the compressed quantum fidelity.
  have hfid_eq : DensityOp.fidelity ρ σ = Quantum.Metrics.fidelity ρt σt := by
    rw [DensityOp.fidelity]
    rw [fidelity_eq_fidelity_supportProj_conj σ ρ (supportProjConjRho σ ρ)
      (supportProjConjRho_toOp σ ρ)]
    -- `F(PρP, σ) = F(ρt, σt)` by the support isometry.
    refine fidelity_isometry_conj_of_toOp_eq V ρt σt.toPosSemidefOp
      (supportProjConjRho σ ρ) σ.toPosSemidefOp (supportIso_isometry σ) ?_ ?_
    · rw [supportProjConjRho_toOp, supportProj_sandwich_eq_supportIso_conj σ ρ, hρtdef,
        compressedRhoPSD_toOp]
    · change σ.toOp = V * σt.toOp * (supportIso σ).conjTranspose
      rw [hσtdef, compressedSigmaDensity_toOp,
        ← supportIso_conjTranspose_mul_sigma_mul_supportIso σ]
      exact sigma_eq_supportIso_compress σ
  rw [hfid_eq, hN]
  -- The embedded classical fidelity reduces to the compressed classical fidelity.
  rw [classicalFidelity, classicalFidelity, Fin.sum_univ_castSucc]
  -- The extra (`Fin.last`) outcome contributes `0` since `Tr((1 - V V†) σ) = 0`.
  have hlastElt : (POVM.supportEmbed σ N).elements (Fin.last k) =
      (1 : Matrix (Fin n) (Fin n) ℂ) - supportProj σ := by
    simp only [POVM.supportEmbed, Fin.lastCases_last]
  have hcastElt : ∀ i : Fin k, (POVM.supportEmbed σ N).elements i.castSucc =
      V * N.elements i * (supportIso σ).conjTranspose := by
    intro i
    simp only [POVM.supportEmbed, Fin.lastCases_castSucc, hVdef]
  have hlast : Real.sqrt
      (((POVM.supportEmbed σ N).elements (Fin.last k) * ρ.toOp).trace.re *
        ((POVM.supportEmbed σ N).elements (Fin.last k) * σ.toOp).trace.re) = 0 := by
    have hq0 : ((POVM.supportEmbed σ N).elements (Fin.last k) * σ.toOp).trace.re = 0 := by
      rw [hlastElt, trace_one_sub_supportProj_mul_sigma σ]; simp
    rw [hq0, mul_zero, Real.sqrt_zero]
  rw [hlast, add_zero]
  -- The `Fin.castSucc` outcomes match the compressed probabilities.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hp : ((POVM.supportEmbed σ N).elements i.castSucc * ρ.toOp).trace.re =
      (N.elements i * ρt.toOp).trace.re := by
    rw [hcastElt i, trace_supportEmbed_mul σ (N.elements i) ρ.toOp, hρtdef, compressedRhoPSD_toOp]
  have hq : ((POVM.supportEmbed σ N).elements i.castSucc * σ.toOp).trace.re =
      (N.elements i * σt.toOp).trace.re := by
    rw [hcastElt i, trace_supportEmbed_mul σ (N.elements i) σ.toOp, hσtdef,
      compressedSigmaDensity_toOp, supportIso_conjTranspose_mul_sigma_mul_supportIso σ]
  rw [hp, hq]

end Quantum.Metrics

end
