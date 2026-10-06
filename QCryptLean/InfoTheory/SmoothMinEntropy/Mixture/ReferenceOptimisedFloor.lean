import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ClassicalExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.SingularReferenceTransfer

/-!
# Positive-definite reference optimization

Regularizing an arbitrary reference transfers positive smooth entropy floors to a positive-
definite reference. Every strict positive level below the reference-optimized value admits such a
reference.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The γ-regularised reference -/

/-- **The γ-regularisation of a reference**: `σ^γ = (1 − γ)·σ + γ·maxMixed`.

The single-operator form of `blockFamilyRegularized` (`BlockRefRegularization.lean`).  Unlike an
additive inflation `σ + η·maxMixed` it carries no extra weight: the trace moves from `tr σ` to
`(1 − γ)·tr σ + γ`, so a reference of trace exactly `1` stays at exactly `1` and the construction is
available where no dominating reference exists at all. -/
def SubDensityOp.regularized {d : ℕ} [NeZero d] (σ : SubDensityOp d) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : SubDensityOp d where
  toOp := ((1 - γ : ℝ) : ℂ) • σ.toOp +
    ((γ : ℝ) : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp
  isHermitian :=
    (((posSemidefOp_implies_mathlib σ.toPosSemidefOp).smul
        (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))).add
      ((posSemidefOp_implies_mathlib
          (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toPosSemidefOp).smul
        (Complex.zero_le_real.mpr hγ0))).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      (((posSemidefOp_implies_mathlib σ.toPosSemidefOp).smul
          (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))).add
        ((posSemidefOp_implies_mathlib
            (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toPosSemidefOp).smul
          (Complex.zero_le_real.mpr hγ0))) v
  trace_le_one := by
    have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp.trace.re = 1 :=
      toSubDensityOp_trace (DensityOp.maxMixed d)
    have hσ : σ.toOp.trace.re ≤ 1 := σ.trace_le_one
    have hσnn : 0 ≤ σ.toOp.trace.re := σ.trace_nonneg
    rw [Matrix.trace_add, Complex.add_re, trace_real_smul_re, trace_real_smul_re, hmm]
    nlinarith

@[simp] lemma SubDensityOp.regularized_toOp {d : ℕ} [NeZero d] (σ : SubDensityOp d) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (σ.regularized γ hγ0 hγ1).toOp =
      ((1 - γ : ℝ) : ℂ) • σ.toOp +
        ((γ : ℝ) : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp := rfl

/-- The regularised reference is the rescaled one shifted by `(γ/d)·1`. -/
lemma SubDensityOp.regularized_eq_smul_add_smul_one {d : ℕ} [NeZero d] (σ : SubDensityOp d)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (σ.regularized γ hγ0 hγ1).toOp =
      ((1 - γ : ℝ) : ℂ) • σ.toOp + ((γ / (d : ℝ) : ℝ) : ℂ) • (1 : Op d) := by
  have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp = (1 / (d : ℂ)) • (1 : Op d) :=
    rfl
  rw [SubDensityOp.regularized_toOp, hmm, smul_smul]
  congr 2
  push_cast
  ring

/-- **The regularised reference is positive definite** for every `0 < γ`: its least eigenvalue is
at least `γ/d`. -/
theorem SubDensityOp.regularized_posDef {d : ℕ} [NeZero d] (σ : SubDensityOp d) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (σ.regularized γ hγ0.le hγ1).toOp.PosDef := by
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [SubDensityOp.regularized_eq_smul_add_smul_one]
  refine Matrix.PosDef.posSemidef_add ?_ ?_
  · exact (posSemidefOp_implies_mathlib σ.toPosSemidefOp).smul
      (RCLike.ofReal_nonneg.mpr (by linarith [hγ1] : (0 : ℝ) ≤ 1 - γ))
  · exact (Matrix.PosDef.one : (1 : Op d).PosDef).smul
      (a := ((γ / (d : ℝ) : ℝ) : ℂ))
      (by
        have : (0 : ℝ) < γ / (d : ℝ) := by positivity
        exact_mod_cast Complex.zero_lt_real.mpr this)

/-- **The `c = 1 − γ` Löwner domination** `(1 − γ)·σ ⪯ σ^γ`, in the exact quadratic-form shape
`smoothMinEntropy_ge_of_smul_opLe_of_floor` consumes.  The gap is exactly `(γ/d)·1`. -/
theorem opLe_smul_regularized {d : ℕ} [NeZero d] (σ : SubDensityOp d) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∀ v : Fin d → ℂ,
      (quadraticForm (((1 - γ : ℝ) : ℂ) • σ.toOp) v).re ≤
        (quadraticForm (σ.regularized γ hγ0 hγ1).toOp v).re := by
  rw [SubDensityOp.regularized_eq_smul_add_smul_one]
  refine opLe_of_posSemidef_sub ?_
  have hgap : ((1 - γ : ℝ) : ℂ) • σ.toOp + ((γ / (d : ℝ) : ℝ) : ℂ) • (1 : Op d) -
      ((1 - γ : ℝ) : ℂ) • σ.toOp = ((γ / (d : ℝ) : ℝ) : ℂ) • (1 : Op d) := by
    abel
  rw [hgap]
  exact (Matrix.PosSemidef.one).smul
    (RCLike.ofReal_nonneg.mpr (by positivity : (0 : ℝ) ≤ γ / (d : ℝ)))

/-! ## The floor transfer onto the regularisation, and its `γ → 0` reach -/

/-- Reference regularization transfers an extended entropy floor with the signed loss
`log₂(1 - γ)` inside the final cast, without a weight or positivity guard on the floor. -/
theorem smoothMinEntropy_regularized_ge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState X d) (σ : SubDensityOp d)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    ENNReal.ofReal (k + Real.log (1 - γ) / Real.log 2) ≤
      smoothMinEntropy ε ρ (σ.regularized γ hγ0.le hγ1.le) :=
  smoothMinEntropy_ge_of_smul_opLe_of_floor ε ρ σ
    (σ.regularized γ hγ0.le hγ1.le) (1 - γ) (by linarith) (by linarith)
    (opLe_smul_regularized σ γ hγ0.le hγ1.le) k hk

/-- Every coefficient strictly larger than one is feasible against a full-rank reference.
Regularizing the quantum marginal proves this without decoding a clipped zero entropy floor. -/
lemma exists_posDef_reference_isFeasible_of_one_lt
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (t : ℝ) (ht : 1 < t) :
    ∃ σ : SubDensityOp n, σ.toOp.PosDef ∧ isFeasible ρ σ t := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have hinv : 0 < t⁻¹ := inv_pos.mpr htpos
  have hinv_lt : t⁻¹ < 1 := (inv_lt_one₀ htpos).mpr ht
  let γ := 1 - t⁻¹
  have hγ : 0 < γ := sub_pos.mpr hinv_lt
  have hγle : γ ≤ 1 := by dsimp [γ]; linarith
  let σ := ρ.quantumMarginal.regularized γ hγ.le hγle
  refine ⟨σ, SubDensityOp.regularized_posDef _ γ hγ hγle, ?_⟩
  apply isFeasible_of_quantumMarginalOp_dominated ρ σ htpos.le
  have hdom := opLe_smul_nonneg htpos.le
    (opLe_smul_regularized ρ.quantumMarginal γ hγ.le hγle)
  have heq : (t : ℂ) • (((1 - γ : ℝ) : ℂ) • ρ.quantumMarginal.toOp) =
      ρ.quantumMarginalOp := by
    rw [smul_smul, ← Complex.ofReal_mul]
    simp [γ, htpos.ne', CQState.quantumMarginal]
  rwa [heq] at hdom

/-- Every real level strictly below an extended entropy floor is certified against a
positive-definite reference, including zero states and infinite smooth entropy. -/
theorem exists_posDef_smoothMinEntropy_ge_of_lt
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState X d) (σ : SubDensityOp d)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ)
    (t : ℝ) (ht : t < k) :
    ∃ σ' : SubDensityOp d, σ'.toOp.PosDef ∧ ENNReal.ofReal t ≤ smoothMinEntropy ε ρ σ' := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c : ℝ := Real.exp ((t - k) * Real.log 2) with hcdef
  have hc_pos : 0 < c := Real.exp_pos _
  have hc_lt : c < 1 := by
    have hneg : (t - k) * Real.log 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hlog2
    calc c = Real.exp ((t - k) * Real.log 2) := hcdef
      _ < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  set γ : ℝ := 1 - c with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hγ1 : γ < 1 := by rw [hγdef]; linarith
  refine ⟨σ.regularized γ hγ0.le hγ1.le, SubDensityOp.regularized_posDef σ γ hγ0 hγ1.le, ?_⟩
  have h := smoothMinEntropy_regularized_ge ε ρ σ γ hγ0 hγ1 k hk
  have hone_sub : (1 : ℝ) - γ = c := by rw [hγdef]; ring
  rw [hone_sub, hcdef, Real.log_exp] at h
  have hlevel : k + (t - k) * Real.log 2 / Real.log 2 = t := by field_simp; ring
  rwa [hlevel] at h


/-- Regularizing the reference transfers a positive input floor `k` to the signed smooth floor
`k + log (1 - γ) / log 2`. -/
theorem smoothMinEntropyReal_regularized_ge_of_pos_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X d) (σ : SubDensityOp d)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hweight : 2 * ε < ∑ x : X, (ρ.stateMap x).trace)
    (k : ℝ) (hk_pos : 0 < k)
    (hk : k ≤ smoothMinEntropyReal ε ρ σ) :
    k + Real.log (1 - γ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρ (σ.regularized γ hγ0.le hγ1.le) :=
  smoothMinEntropyReal_ge_of_smul_opLe_of_pos_floor ε hε_nn ρ σ (σ.regularized γ hγ0.le hγ1.le)
    (1 - γ) (by linarith) (by linarith) (opLe_smul_regularized σ γ hγ0.le hγ1.le)
    (SubDensityOp.regularized_posDef σ γ hγ0 hγ1.le) hweight k hk_pos hk

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
