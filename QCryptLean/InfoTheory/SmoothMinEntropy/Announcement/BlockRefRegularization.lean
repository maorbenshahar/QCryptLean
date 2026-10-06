import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernelBlockRef
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.SingularReferenceTransfer

/-!
# Regularizing block-diagonal references

A positive smooth entropy floor transfers to a regularized block-diagonal reference. The real
regularization penalty is charged before converting the floor with `ENNReal.ofReal`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Two elementary identities -/

/-- `Op.tensor · B` commutes with finite sums in its left argument. -/
lemma Op_sum_tensor_right_const {ι : Type*} [Fintype ι] {dC dE : ℕ}
    (A : ι → Op dC) (B : Op dE) :
    (∑ i, Op.tensor (A i) B) = Op.tensor (∑ i, A i) B := by
  ext p q
  simp only [Op.tensor, Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul]

/-- The announced-register projectors, tensored with `1_E`, resolve the identity on `C ⊗ E`. -/
lemma sum_stdKetProj_tensor_one_eq_one {dC dE : ℕ} :
    (∑ p : Fin dC, Op.tensor (stdKet dC p * (stdKet dC p).dag) (1 : Op dE)) =
      (1 : Op (dC * dE)) := by
  rw [Op_sum_tensor_right_const, stdKet_complete, Op.tensor_one]

/-! ## The γ-regularised block family -/

/-- **The γ-regularised block family** `ν^γ_p = (1 − γ)·ν_p + (γ/d_C)·maxMixed_E`.

An explicit convex-style mixture of the given family with the flat family `(1/d_C)·maxMixed_E`.  It
is positive definite in every block as soon as `0 < γ`, and — unlike an additive inflation
`ν_p + η·maxMixed_E` — it carries no extra weight: the total weight moves from `Σ_p tr ν_p` to
`(1 − γ)·Σ_p tr ν_p + γ`, which is again `1` when the input family already had total weight `1`. -/
def blockFamilyRegularized {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (p : Fin dC) : SubDensityOp dE where
  toOp := ((1 - γ : ℝ) : ℂ) • (ν p).toOp +
    ((γ / (dC : ℝ) : ℝ) : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp
  isHermitian :=
    (((posSemidefOp_implies_mathlib (ν p).toPosSemidefOp).smul
        (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))).add
      ((posSemidefOp_implies_mathlib
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toPosSemidefOp).smul
        (Complex.zero_le_real.mpr (div_nonneg hγ0 (Nat.cast_nonneg _))))).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      (((posSemidefOp_implies_mathlib (ν p).toPosSemidefOp).smul
          (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))).add
        ((posSemidefOp_implies_mathlib
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toPosSemidefOp).smul
          (Complex.zero_le_real.mpr (div_nonneg hγ0 (Nat.cast_nonneg _))))) v
  trace_le_one := by
    have hdC : (1 : ℝ) ≤ (dC : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne dC)
    have hdCpos : (0 : ℝ) < (dC : ℝ) := by linarith
    have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp.trace.re = 1 :=
      toSubDensityOp_trace (DensityOp.maxMixed dE)
    have hν : (ν p).toOp.trace.re ≤ 1 := (ν p).trace_le_one
    have hνnn : 0 ≤ (ν p).toOp.trace.re := (ν p).trace_nonneg
    rw [Matrix.trace_add, Complex.add_re, trace_real_smul_re, trace_real_smul_re, hmm]
    have hdiv : γ / (dC : ℝ) ≤ γ := by
      rw [div_le_iff₀ hdCpos]
      nlinarith
    nlinarith

@[simp] lemma blockFamilyRegularized_toOp {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (p : Fin dC) :
    (blockFamilyRegularized ν γ hγ0 hγ1 p).toOp =
      ((1 - γ : ℝ) : ℂ) • (ν p).toOp +
        ((γ / (dC : ℝ) : ℝ) : ℂ) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp := rfl

/-- The regularised block's weight: `(1 − γ)·tr ν_p + γ/d_C`. -/
lemma blockFamilyRegularized_trace {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (p : Fin dC) :
    (blockFamilyRegularized ν γ hγ0 hγ1 p).trace = (1 - γ) * (ν p).trace + γ / (dC : ℝ) := by
  have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp.trace.re = 1 :=
    toSubDensityOp_trace (DensityOp.maxMixed dE)
  change ((blockFamilyRegularized ν γ hγ0 hγ1 p).toOp).trace.re = _
  rw [blockFamilyRegularized_toOp, Matrix.trace_add, Complex.add_re, trace_real_smul_re,
    trace_real_smul_re, hmm, mul_one]
  rfl

/-- **The regularisation is weight-exact**: the total weight of `ν^γ` is
`(1 − γ)·(total weight of ν) + γ`.  In particular a family of total weight exactly `1` — which is
what a block-diagonal announced reference whose blocks sum to a normalised state has — stays at
exactly `1`. -/
lemma sum_blockFamilyRegularized_trace_eq {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∑ p : Fin dC, (blockFamilyRegularized ν γ hγ0 hγ1 p).trace) =
      (1 - γ) * (∑ p : Fin dC, (ν p).trace) + γ := by
  have hdC : (dC : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dC)
  simp only [blockFamilyRegularized_trace]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The sub-normalisation `blockDiagRef` consumes, for the regularised family. -/
lemma sum_blockFamilyRegularized_trace_le_one {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∑ p : Fin dC, (blockFamilyRegularized ν γ hγ0 hγ1 p).trace) ≤ 1 := by
  rw [sum_blockFamilyRegularized_trace_eq]
  nlinarith

/-! ## The assembled regularised reference -/

/-- **The assembled γ-regularised announced reference** `Σ_p |p⟩⟨p| ⊗ ν^γ_p`. -/
def blockDiagRefRegularized {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : SubDensityOp (dC * dE) :=
  blockDiagRef (blockFamilyRegularized ν γ hγ0 hγ1)
    (sum_blockFamilyRegularized_trace_le_one ν hν γ hγ0 hγ1)

@[simp] lemma blockDiagRefRegularized_toOp {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (blockDiagRefRegularized ν hν γ hγ0 hγ1).toOp =
      blockDiagRefOp (blockFamilyRegularized ν γ hγ0 hγ1) := rfl

/-- **The regularised reference is the original one shifted by `(γ/(d_C·d_E))·1`.**

`Σ_p |p⟩⟨p| ⊗ ν^γ_p = (1 − γ)·Σ_p |p⟩⟨p| ⊗ ν_p + (γ/(d_C·d_E))·1`, because the announced-register
projectors tensored with `1_E` resolve the identity on `C ⊗ E`. -/
lemma blockDiagRefOp_blockFamilyRegularized_eq {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    blockDiagRefOp (blockFamilyRegularized ν γ hγ0 hγ1) =
      ((1 - γ : ℝ) : ℂ) • blockDiagRefOp ν +
        ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ) • (1 : Op (dC * dE)) := by
  have hdC : ((dC : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne dC)))
  have hdE : ((dE : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne dE)))
  have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp =
      (1 / (dE : ℂ)) • (1 : Op dE) := rfl
  -- Split the assembled sum into the two summands of each regularised block.
  have hsplit : blockDiagRefOp (blockFamilyRegularized ν γ hγ0 hγ1) =
      (∑ p : Fin dC, ((1 - γ : ℝ) : ℂ) •
          Op.tensor (stdKet dC p * (stdKet dC p).dag) (ν p).toOp) +
        ∑ p : Fin dC, ((γ / (dC : ℝ) : ℝ) : ℂ) • (1 / (dE : ℂ)) •
          Op.tensor (stdKet dC p * (stdKet dC p).dag) (1 : Op dE) := by
    rw [blockDiagRefOp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [blockFamilyRegularized_toOp, hmm, Op.tensor_add_right, Op.tensor_smul_right,
      Op.tensor_smul_right, Op.tensor_smul_right]
  rw [hsplit, ← Finset.smul_sum, ← blockDiagRefOp]
  congr 1
  rw [← Finset.smul_sum, ← Finset.smul_sum, sum_stdKetProj_tensor_one_eq_one, smul_smul]
  congr 1
  push_cast
  field_simp

/-- **The regularised announced reference is positive definite** for every `0 < γ`.

Its least eigenvalue is at least `γ/(d_C·d_E)`: the assembled reference is a positive semidefinite
operator plus that multiple of the identity. -/
theorem blockDiagRefRegularized_posDef {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (blockDiagRefRegularized ν hν γ hγ0.le hγ1).toOp.PosDef := by
  have hdC : (0 : ℝ) < (dC : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hdE : (0 : ℝ) < (dE : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dE)
  rw [blockDiagRefRegularized_toOp, blockDiagRefOp_blockFamilyRegularized_eq]
  refine Matrix.PosDef.posSemidef_add ?_ ?_
  · exact (blockDiagRefOp_posSemidef ν).smul
      (RCLike.ofReal_nonneg.mpr (by linarith [hγ1] : (0 : ℝ) ≤ 1 - γ))
  · exact (Matrix.PosDef.one : (1 : Op (dC * dE)).PosDef).smul
      (a := ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ))
      (by
        have : (0 : ℝ) < γ / ((dC : ℝ) * (dE : ℝ)) := by positivity
        exact_mod_cast Complex.zero_lt_real.mpr this)

/-- **The `c = 1 − γ` Löwner domination**, in the exact quadratic-form shape
`smoothMinEntropy_ge_of_smul_opLe_of_floor` (`SingularReferenceTransfer.lean`) consumes:

`(1 − γ)·Σ_p |p⟩⟨p| ⊗ ν_p ⪯ Σ_p |p⟩⟨p| ⊗ ν^γ_p`.

The gap is exactly `(γ/(d_C·d_E))·1`. -/
theorem opLe_smul_blockDiagRefRegularized {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∀ v : Fin (dC * dE) → ℂ,
      (quadraticForm (((1 - γ : ℝ) : ℂ) • (blockDiagRef ν hν).toOp) v).re ≤
        (quadraticForm (blockDiagRefRegularized ν hν γ hγ0 hγ1).toOp v).re := by
  have hdC : (0 : ℝ) < (dC : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hdE : (0 : ℝ) < (dE : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dE)
  rw [blockDiagRefRegularized_toOp, blockDiagRefOp_blockFamilyRegularized_eq, blockDiagRef_toOp]
  refine opLe_of_posSemidef_sub ?_
  have hgap : ((1 - γ : ℝ) : ℂ) • blockDiagRefOp ν +
        ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ) • (1 : Op (dC * dE)) -
      ((1 - γ : ℝ) : ℂ) • blockDiagRefOp ν =
      ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ) • (1 : Op (dC * dE)) := by
    abel
  rw [hgap]
  exact (Matrix.PosSemidef.one).smul
    (RCLike.ofReal_nonneg.mpr (by positivity : (0 : ℝ) ≤ γ / ((dC : ℝ) * (dE : ℝ))))

/-! ## The packaged floor transfer -/

/-- Regularizing a block reference preserves extended smooth floors at the logarithmic
cost `log₂(1 − γ)`, without a centre-weight or positive-floor restriction. -/
theorem smoothMinEntropy_blockDiagRefRegularized_ge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ε : ℝ) (ρ : CQState X (dC * dE))
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ (blockDiagRef ν hν)) :
    ENNReal.ofReal (k + Real.log (1 - γ) / Real.log 2) ≤
      smoothMinEntropy ε ρ (blockDiagRefRegularized ν hν γ hγ0 hγ1.le) := by
  have : NeZero (dC * dE) := ⟨Nat.mul_ne_zero (NeZero.ne dC) (NeZero.ne dE)⟩
  exact smoothMinEntropy_ge_of_smul_opLe_of_floor ε ρ (blockDiagRef ν hν)
    (blockDiagRefRegularized ν hν γ hγ0 hγ1.le) (1 - γ) (by linarith) (by linarith)
    (opLe_smul_blockDiagRefRegularized ν hν γ hγ0 hγ1.le) k hk


/-- Regularizing the block-diagonal reference transfers a positive input floor `k` to the signed
floor `k + log (1 - γ) / log 2`. -/
theorem smoothMinEntropyReal_blockDiagRefRegularized_ge_of_pos_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X (dC * dE))
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hweight : 2 * ε < ∑ x : X, (ρ.stateMap x).trace)
    (k : ℝ) (hk_pos : 0 < k)
    (hk : k ≤ smoothMinEntropyReal ε ρ (blockDiagRef ν hν)) :
    k + Real.log (1 - γ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρ (blockDiagRefRegularized ν hν γ hγ0.le hγ1.le) := by
  have : NeZero (dC * dE) := ⟨Nat.mul_ne_zero (NeZero.ne dC) (NeZero.ne dE)⟩
  exact smoothMinEntropyReal_ge_of_smul_opLe_of_pos_floor ε hε_nn ρ (blockDiagRef ν hν)
    (blockDiagRefRegularized ν hν γ hγ0.le hγ1.le) (1 - γ) (by linarith) (by linarith)
    (opLe_smul_blockDiagRefRegularized ν hν γ hγ0.le hγ1.le)
    (blockDiagRefRegularized_posDef ν hν γ hγ0 hγ1.le) hweight k hk_pos hk

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
