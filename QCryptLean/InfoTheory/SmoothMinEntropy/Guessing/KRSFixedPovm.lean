import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness
import QCryptLean.Quantum.Operators.HermitianTraceSq

/-!
# Fixed-POVM KRS Bounds — matrix Cauchy-Schwarz and collision reduction

This module contains small fixed-POVM reductions used by the
Koenig-Renner-Schaffner guessing-probability bound.  The lemmas here do not
mention von Neumann entropy; they isolate the POVM/Cauchy-Schwarz side from the
separate Gibbs variational estimate.

## Main definitions

This file declares no new definitions.

## Main statements

- `trace_effect_mul_sq_le_trace_effect_mul_ref_mul_collision`: pointwise
  matrix Cauchy-Schwarz for one POVM effect.
- `povmObjective_le_sqrt_collision_of_pointwise_bound`: aggregate a pointwise
  squared bound over a feasible POVM.
- `povmObjective_le_sqrt_collision_of_posDef_ref`: fixed-POVM collision bound
  for a positive-definite reference.
- `povmGuessingProb_le_sqrt_collision_of_posDef_ref`: optimized
  guessing-probability collision bound.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A Hermitian operator sandwiched around the inverse of a positive-definite
operator is positive semidefinite. -/
lemma hermitian_mul_inv_mul_self_posSemidef
    {n : ℕ}
    {σ A : Op n} (hσ : σ.PosDef) (hA : A.IsHermitian) :
    (A * σ⁻¹ * A).PosSemidef := by
  let S : Op n := hσ.inverseSqrt
  have hS_herm : S.IsHermitian := by
    simpa [S] using hσ.inverseSqrt_isHermitian
  have hS_sq : S * S = σ⁻¹ := by
    simpa [S] using hσ.inverseSqrt_sq
  have h0 : ((S * A).conjTranspose * (S * A)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (S * A)
  have h_eq : (S * A).conjTranspose * (S * A) = A * σ⁻¹ * A := by
    calc
      (S * A).conjTranspose * (S * A) = (A * S) * (S * A) := by
        simp [Matrix.conjTranspose_mul, hA.eq, hS_herm.eq, Matrix.mul_assoc]
      _ = A * (S * S) * A := by simp [Matrix.mul_assoc]
      _ = A * σ⁻¹ * A := by rw [hS_sq]
  rwa [h_eq] at h0

/-- The trace of `A * σ⁻¹ * A` is the inverse-square-root collision trace. -/
lemma trace_mul_inv_mul_self_eq_trace_inverseSqrt_mul_self
    {n : ℕ}
    {σ A : Op n} (hσ : σ.PosDef) :
    (A * σ⁻¹ * A).trace =
      (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace := by
  let S : Op n := hσ.inverseSqrt
  have hS_sq : S * S = σ⁻¹ := by
    simpa [S] using hσ.inverseSqrt_sq
  calc
    (A * σ⁻¹ * A).trace = (A * (S * S) * A).trace := by rw [hS_sq]
    _ = ((A * S) * (S * A)).trace := by simp [Matrix.mul_assoc]
    _ = ((S * A) * (A * S)).trace := Matrix.trace_mul_comm (A * S) (S * A)
    _ = (S * A * A * S).trace := by simp [Matrix.mul_assoc]
    _ = (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace := by
      simp [S, Matrix.mul_assoc]

/-- The Hilbert-Schmidt factorization for a fixed effect has inner product
`Tr(E * A)`. -/
lemma trace_sqrt_effect_ref_inverseSqrt_mul_eq_trace_effect_mul
    {n : ℕ}
    {σ E A : Op n} (hσ : σ.PosDef) (hE : E.PosSemidef) :
    ((CFC.sqrt E * σ * hσ.inverseSqrt) *
        (hσ.inverseSqrt * A * CFC.sqrt E)).trace =
      (E * A).trace := by
  let R : Op n := CFC.sqrt E
  let S : Op n := hσ.inverseSqrt
  have hR_sq : R * R = E := by
    simpa [R] using CFC.sqrt_mul_sqrt_self E hE.nonneg
  have hS_sq : S * S = σ⁻¹ := by
    simpa [S] using hσ.inverseSqrt_sq
  have hσ_inv_mul : σ * σ⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv σ ((Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit)
  calc
    ((CFC.sqrt E * σ * hσ.inverseSqrt) *
        (hσ.inverseSqrt * A * CFC.sqrt E)).trace =
        (R * σ * S * (S * A * R)).trace := by
      simp [R, S, Matrix.mul_assoc]
    _ = (R * σ * (S * S) * A * R).trace := by simp [Matrix.mul_assoc]
    _ = (R * σ * σ⁻¹ * A * R).trace := by rw [hS_sq]
    _ = (R * (σ * σ⁻¹) * A * R).trace := by simp [Matrix.mul_assoc]
    _ = (R * A * R).trace := by rw [hσ_inv_mul]; simp [Matrix.mul_assoc]
    _ = (R * R * A).trace := Matrix.trace_mul_cycle R A R
    _ = (E * A).trace := by rw [hR_sq]

/-- The trace of the first Hilbert-Schmidt factor times its adjoint is
`Tr(E * σ)`. -/
lemma trace_sqrt_effect_ref_inverseSqrt_mul_conjTranspose_eq_trace_effect_ref
    {n : ℕ}
    {σ E : Op n} (hσ : σ.PosDef) (hE : E.PosSemidef) :
    ((CFC.sqrt E * σ * hσ.inverseSqrt) *
        (CFC.sqrt E * σ * hσ.inverseSqrt).conjTranspose).trace =
      (E * σ).trace := by
  let R : Op n := CFC.sqrt E
  let S : Op n := hσ.inverseSqrt
  have hR_psd : R.PosSemidef := by
    simpa [R] using (CFC.sqrt_nonneg E).posSemidef
  have hR_herm : R.IsHermitian := hR_psd.isHermitian
  have hS_herm : S.IsHermitian := by
    simpa [S] using hσ.inverseSqrt_isHermitian
  have hconj :
      (CFC.sqrt E * σ * hσ.inverseSqrt).conjTranspose =
        hσ.inverseSqrt * σ * CFC.sqrt E := by
    simp [R, S, Matrix.conjTranspose_mul, hR_herm.eq, hS_herm.eq, hσ.1.eq,
      Matrix.mul_assoc]
  rw [hconj]
  exact trace_sqrt_effect_ref_inverseSqrt_mul_eq_trace_effect_mul
    (σ := σ) (E := E) (A := σ) hσ hE

/-- Dropping a POVM effect below `1` bounds the second Hilbert-Schmidt factor by
the inverse-square-root collision trace. -/
lemma trace_inverseSqrt_mul_hermitian_mul_sqrt_effect_le_collision
    {n : ℕ}
    {σ E A : Op n} (hσ : σ.PosDef)
    (hE : E.PosSemidef) (hE_le_one : opLe E (1 : Op n))
    (hA : A.IsHermitian) :
    (((hσ.inverseSqrt * A * CFC.sqrt E).conjTranspose *
        (hσ.inverseSqrt * A * CFC.sqrt E)).trace.re) ≤
      (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re := by
  let R : Op n := CFC.sqrt E
  let S : Op n := hσ.inverseSqrt
  have hR_psd : R.PosSemidef := by
    simpa [R] using (CFC.sqrt_nonneg E).posSemidef
  have hR_herm : R.IsHermitian := hR_psd.isHermitian
  have hR_sq : R * R = E := by
    simpa [R] using CFC.sqrt_mul_sqrt_self E hE.nonneg
  have hS_herm : S.IsHermitian := by
    simpa [S] using hσ.inverseSqrt_isHermitian
  have hS_sq : S * S = σ⁻¹ := by
    simpa [S] using hσ.inverseSqrt_sq
  have hC_psd : (A * σ⁻¹ * A).PosSemidef :=
    hermitian_mul_inv_mul_self_posSemidef hσ hA
  have hY_trace_eq :
      ((S * A * R).conjTranspose * (S * A * R)).trace =
        ((A * σ⁻¹ * A) * E).trace := by
    calc
      ((S * A * R).conjTranspose * (S * A * R)).trace =
          ((R * A * S) * (S * A * R)).trace := by
        simp [Matrix.conjTranspose_mul, hR_herm.eq, hS_herm.eq, hA.eq,
          Matrix.mul_assoc]
      _ = (R * A * (S * S) * A * R).trace := by simp [Matrix.mul_assoc]
      _ = (R * A * σ⁻¹ * A * R).trace := by rw [hS_sq]
      _ = (R * (A * σ⁻¹ * A) * R).trace := by simp [Matrix.mul_assoc]
      _ = (R * R * (A * σ⁻¹ * A)).trace :=
        Matrix.trace_mul_cycle R (A * σ⁻¹ * A) R
      _ = ((A * σ⁻¹ * A) * (R * R)).trace :=
        Matrix.trace_mul_comm (R * R) (A * σ⁻¹ * A)
      _ = ((A * σ⁻¹ * A) * E).trace := by rw [hR_sq]
  have hdrop :
      ((A * σ⁻¹ * A) * E).trace.re ≤
        ((A * σ⁻¹ * A) * (1 : Op n)).trace.re :=
    trace_mul_le_of_opLe hC_psd hE.isHermitian Matrix.isHermitian_one hE_le_one
  calc
    (((hσ.inverseSqrt * A * CFC.sqrt E).conjTranspose *
        (hσ.inverseSqrt * A * CFC.sqrt E)).trace.re) =
        ((A * σ⁻¹ * A) * E).trace.re := by
      simpa [S, R] using congrArg Complex.re hY_trace_eq
    _ ≤ ((A * σ⁻¹ * A) * (1 : Op n)).trace.re := hdrop
    _ = (A * σ⁻¹ * A).trace.re := by rw [Matrix.mul_one]
    _ = (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re :=
      congrArg Complex.re (trace_mul_inv_mul_self_eq_trace_inverseSqrt_mul_self hσ)

/-- Pointwise matrix Cauchy-Schwarz for a POVM effect.

If `σ` is positive definite, `E` is a POVM effect (`0 ≤ E ≤ 1`), and `A` is
Hermitian, then

`Tr(E A)^2 ≤ Tr(E σ) Tr(σ^{-1/2} A A σ^{-1/2})`.

This is the fixed-effect estimate needed before aggregating over a POVM. -/
lemma trace_effect_mul_sq_le_trace_effect_mul_ref_mul_collision
    {n : ℕ} [NeZero n]
    {σ E A : Op n} (hσ : σ.PosDef)
    (hE : E.PosSemidef) (hE_le_one : opLe E (1 : Op n))
    (hA : A.IsHermitian) :
    ((E * A).trace.re) ^ 2 ≤
      (E * σ).trace.re *
        (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re := by
  set X : Op n := CFC.sqrt E * σ * hσ.inverseSqrt with hX_def
  set Y : Op n := hσ.inverseSqrt * A * CFC.sqrt E with hY_def
  have htrace_XY : (X * Y).trace = (E * A).trace := by
    simpa [hX_def, hY_def] using
      trace_sqrt_effect_ref_inverseSqrt_mul_eq_trace_effect_mul
        (σ := σ) (E := E) (A := A) hσ hE
  have hXX_trace : (X * X.conjTranspose).trace = (E * σ).trace := by
    simpa [hX_def] using
      trace_sqrt_effect_ref_inverseSqrt_mul_conjTranspose_eq_trace_effect_ref
        (σ := σ) (E := E) hσ hE
  have hYY_trace_le :
      (Y.conjTranspose * Y).trace.re ≤
        (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re := by
    simpa [hY_def] using
      trace_inverseSqrt_mul_hermitian_mul_sqrt_effect_le_collision
        (σ := σ) (E := E) (A := A) hσ hE hE_le_one hA
  have hweight_nonneg : 0 ≤ (E * σ).trace.re := by
    exact Quantum.Operators.trace_mul_psd_nonneg E σ hE hσ.posSemidef
  have hCS :=
    Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose X Y
  have hre_sq_le_norm_sq : ((E * A).trace.re) ^ 2 ≤ ‖(X * Y).trace‖ ^ 2 := by
    rw [htrace_XY]
    have h_abs : |(E * A).trace.re| ≤ ‖(E * A).trace‖ :=
      Complex.abs_re_le_norm (E * A).trace
    have h_norm_abs : |‖(E * A).trace‖| = ‖(E * A).trace‖ :=
      abs_of_nonneg (norm_nonneg _)
    exact sq_le_sq.mpr (by rwa [h_norm_abs])
  have h_rhs_le :
      (X * X.conjTranspose).trace.re * (Y.conjTranspose * Y).trace.re ≤
        (E * σ).trace.re *
          (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re := by
    rw [hXX_trace]
    exact mul_le_mul_of_nonneg_left hYY_trace_le hweight_nonneg
  exact hre_sq_le_norm_sq.trans (hCS.trans h_rhs_le)

/-- Fixed-POVM collision reduction under a pointwise squared Cauchy-Schwarz
estimate.

For a positive-definite reference `σ`, if each block satisfies the pointwise
estimate

`Tr(M_x ρ_x)^2 ≤ Tr(M_x σ) Tr(σ^{-1/2} ρ_x^2 σ^{-1/2})`,

then the whole POVM objective is bounded by the square root of the summed
collision expression.  The proof is the real Cauchy-Schwarz aggregation plus
the feasible-POVM trace budget. -/
lemma povmObjective_le_sqrt_collision_of_pointwise_bound
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (hσ_pd : σ.toOp.PosDef)
    {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n)))
    (h_sq : ∀ x : X,
      (((M x) * (ρ.stateMap x).toOp).trace.re) ^ 2 ≤
        ((M x) * σ.toOp).trace.re *
          (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re) :
    povmObjective ρ M ≤
      Real.sqrt
        (∑ x : X,
          (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re) := by
  refine povmObjective_le_sqrt_sum_of_sq_le_trace_mul ρ σ hM
    (fun x : X =>
      (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
        (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re)
    ?_ h_sq
  intro x
  exact trace_sandwich_sq_nonneg hσ_pd (ρ.stateMap x).toOp
    (ρ.stateMap x).isHermitian

/-- Entropy-free fixed-POVM collision bound for a positive-definite reference.

This specializes the pointwise matrix Cauchy-Schwarz estimate to every feasible
Hermitian POVM effect and then aggregates over the POVM. -/
lemma povmObjective_le_sqrt_collision_of_posDef_ref
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (hσ_pd : σ.toOp.PosDef)
    {M : X → Op n}
    (hM : M ∈ (povmFeasibleHerm : Set (X → Op n))) :
    povmObjective ρ M ≤
      Real.sqrt
        (∑ x : X,
          (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re) := by
  refine povmObjective_le_sqrt_collision_of_pointwise_bound ρ σ hσ_pd hM ?_
  intro x
  exact trace_effect_mul_sq_le_trace_effect_mul_ref_mul_collision hσ_pd
    (hM.1 x) (povmFeasibleHerm_opLe_one hM x) (ρ.stateMap x).isHermitian

/-- Entropy-free guessing-probability collision bound for a positive-definite
reference. -/
lemma povmGuessingProb_le_sqrt_collision_of_posDef_ref
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (hσ_pd : σ.toOp.PosDef) :
    povmGuessingProb ρ ≤
      Real.sqrt
        (∑ x : X,
          (hσ_pd.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x).toOp * hσ_pd.inverseSqrt).trace.re) := by
  refine povmGuessingProb_le_of_forall_povmFeasibleHerm_objective_le ρ ?_
  intro M hM
  exact povmObjective_le_sqrt_collision_of_posDef_ref ρ σ hσ_pd hM

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
