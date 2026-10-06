import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQStateRecovery

/-!
# Product References — max-mixed tensor references and recovery feasibility

This module records the elementary algebraic identities relating the
unnormalized product reference `1_E ⊗ σR` to the maximally-mixed product
reference `M_E ⊗ σR`, where `M_E = maxMixed dE`.  It also packages the
"feasibility from a recovery channel" bridge: if a per-block completely
positive, monotone map `T` carries the `E`-marginal feasibility witness into the
extension and sends `1_E` below `polyDim · (1_E ⊗ σR)`, then each extension block
is dominated by `polyDim · λ` copies of the product reference `M_E ⊗ σR`.

These are the operator and CQ-state glue lemmas for converting a per-block
recovery-channel feasibility witness into a product-reference domination.

## Main statements
- `maxMixed_tensor_toSubDensityOp_posDef`: max-mixed product references are
  positive definite when the second factor is.
- `one_tensor_eq_dim_smul_maxMixed_tensor`: `1_E ⊗ σR = dE • (M_E ⊗ σR)`.
- `maxMixed_toOp_eq_inv_smul_one`: `M_E.toOp = (dE)⁻¹ • 1`.
- `opLe_maxMixed_tensor_of_recovery`: feasibility-from-recovery bridge.
- `isFeasible_recoveredExtension_maxMixed_tensor_of_recovery`: CQ-state
  feasibility transfer for blockwise recovered extensions.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The maximally mixed sub-density reference is positive definite.

Public replica of the `private` lemma `maxMixed_reference_posDef` in
`DimensionPenalty.lean`, exposed for the CKR-style structured extension penalty. -/
lemma maxMixed_toSubDensityOp_posDef {dE : ℕ} [NeZero dE] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp.PosDef := by
  simpa [DensityOp.toSubDensityOp, DensityOp.maxMixed] using
    ((Matrix.PosDef.one : (1 : Op dE).PosDef).smul
      (a := (1 / (dE : ℂ))) (by
        exact_mod_cast (one_div_pos.mpr
          (Nat.cast_pos.mpr (Nat.pos_of_neZero dE)))))

/-- The product of the maximally mixed reference with a positive-definite
density operator is positive definite. -/
lemma maxMixed_tensor_toSubDensityOp_posDef
    {d dE : ℕ} [NeZero dE]
    (σA : DensityOp d)
    (hσA_posDef : σA.toOp.PosDef) :
    (DensityOp.toSubDensityOp
      (DensityOp.tensor (DensityOp.maxMixed dE) σA)).toOp.PosDef := by
  have hσE_posDef :
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp.PosDef :=
    maxMixed_toSubDensityOp_posDef
  have hσA_sub_posDef :
      (DensityOp.toSubDensityOp σA).toOp.PosDef := by
    simpa only [DensityOp.toSubDensityOp] using hσA_posDef
  have htensor :
      (SubDensityOp.tensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))
        (DensityOp.toSubDensityOp σA)).toOp.PosDef :=
    SubDensityOp.tensor_posDef _ _ hσE_posDef hσA_sub_posDef
  simpa only [SubDensityOp.tensor, DensityOp.toSubDensityOp, DensityOp.tensor] using htensor

/-- The unnormalized product reference `1_E ⊗ σR` equals `dE` copies of the
maximally-mixed product reference `M_E ⊗ σR`. -/
lemma one_tensor_eq_dim_smul_maxMixed_tensor
    {dE dR : ℕ} [NeZero dE] (σR : SubDensityOp dR) :
    (Op.tensor (1 : Op dE) σR.toOp) =
      (Complex.ofReal (dE : ℝ)) •
        ((DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).tensor σR).toOp := by
  rw [← maxMixed_dim_smul_toSubDensityOp_toOp_eq_one (d := dE)]
  rw [Op.tensor_smul_left]
  rfl

/-- The maximally-mixed reference operator equals `(dE)⁻¹` times the identity. -/
lemma maxMixed_toOp_eq_inv_smul_one {dE : ℕ} [NeZero dE] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp =
      (Complex.ofReal (dE : ℝ)⁻¹) • (1 : Op dE) := by
  have h := maxMixed_dim_smul_toSubDensityOp_toOp_eq_one (d := dE)
  have hdE : (dE : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dE)
  rw [← h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hdE, Complex.ofReal_one,
    one_smul]

/-- **Feasibility from a recovery channel.** Suppose a linear map `T` on the
`E`-register (the per-block recovery channel) is monotone for the PSD order,
sends the identity below `polyDim · (1_E ⊗ σR)`, and carries an `E`-marginal
block `ρE_block` to the extension block `ρER_block`.  If `ρE_block` is feasible
for the maximally-mixed reference with scalar `lam`, then the extension block is
dominated by `polyDim · lam` copies of the product reference `M_E ⊗ σR`.

This is the operator-level glue that turns a per-block recovery-channel
construction into a product-reference feasibility domination. -/
lemma opLe_maxMixed_tensor_of_recovery
    {dE dR : ℕ} [NeZero dE]
    (T : Op dE →ₗ[ℂ] Op (dE * dR))
    (σR : SubDensityOp dR) (polyDim : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hT_mono : ∀ A B : Op dE, opLe A B → opLe (T A) (T B))
    (hT_one : opLe (T 1)
      ((Complex.ofReal (polyDim : ℝ)) • Op.tensor (1 : Op dE) σR.toOp))
    (ρE_block : Op dE) (ρER_block : Op (dE * dR))
    (hmarg : opLe ρE_block
      ((Complex.ofReal lam) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp))
    (hTρ : T ρE_block = ρER_block) :
    opLe ρER_block
      ((Complex.ofReal ((polyDim : ℝ) * lam)) •
        ((DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).tensor σR).toOp) := by
  set M_E := DensityOp.toSubDensityOp (DensityOp.maxMixed dE) with hM_E
  have hdE_inv_nn : (0 : ℝ) ≤ (dE : ℝ)⁻¹ := by positivity
  have hdE_ne : (dE : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dE)
  -- `T M_E.toOp = (dE)⁻¹ • T 1`.
  have hTM : T M_E.toOp = (Complex.ofReal (dE : ℝ)⁻¹) • T 1 := by
    rw [hM_E, maxMixed_toOp_eq_inv_smul_one, map_smul]
  -- `opLe (T M_E.toOp) (polyDim • (M_E ⊗ σR))`.
  have hTM_le : opLe (T M_E.toOp)
      ((Complex.ofReal (polyDim : ℝ)) • (M_E.tensor σR).toOp) := by
    have hscaled := opLe_smul_nonneg hdE_inv_nn hT_one
    rw [← hTM, one_tensor_eq_dim_smul_maxMixed_tensor] at hscaled
    have hRHS :
        (Complex.ofReal (dE : ℝ)⁻¹) •
            ((Complex.ofReal (polyDim : ℝ)) •
              ((Complex.ofReal (dE : ℝ)) • (M_E.tensor σR).toOp)) =
          (Complex.ofReal (polyDim : ℝ)) • (M_E.tensor σR).toOp := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp
    rw [hRHS] at hscaled
    exact hscaled
  -- `opLe ρER_block (T (lam • M_E.toOp))`.
  have hρER_le : opLe ρER_block (T ((Complex.ofReal lam) • M_E.toOp)) := by
    rw [← hTρ]
    exact hT_mono _ _ hmarg
  -- Scale the previous bound by `lam` and combine.
  have hscaled := opLe_smul_nonneg hlam hTM_le
  rw [← map_smul] at hscaled
  have hRHS2 :
      (Complex.ofReal lam) •
          ((Complex.ofReal (polyDim : ℝ)) • (M_E.tensor σR).toOp) =
        (Complex.ofReal ((polyDim : ℝ) * lam)) • (M_E.tensor σR).toOp := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_comm lam (polyDim : ℝ)]
  rw [hRHS2] at hscaled
  exact opLe_trans hρER_le hscaled

/-- Recovery maps transfer max-mixed feasibility on `E` to product-reference
feasibility on the recovered `E ⊗ R` extension. -/
lemma isFeasible_recoveredExtension_maxMixed_tensor_of_recovery
    {X : Type*} [Fintype X]
    {dR dE : ℕ} [NeZero dR] [NeZero dE] [NeZero (dE * dR)]
    (σR : DensityOp dR)
    (polyDim : ℕ)
    (ρEtilde : CQState X dE)
    (T : X → Op dE →ₗ[ℂ] Op (dE * dR))
    (hmono : ∀ x : X, ∀ A B : Op dE, opLe A B → opLe (T x A) (T x B))
    (hpos : ∀ x : X, ∀ A : Op dE, A.PosSemidef → (T x A).PosSemidef)
    (hunit : ∀ x : X, opLe (T x 1)
      ((Complex.ofReal (polyDim : ℝ)) •
        Op.tensor (1 : Op dE) (DensityOp.toSubDensityOp σR).toOp))
    (htp : ∀ x : X, Quantum.Channels.IsTracePreserving ⇑(T x))
    {t : ℝ}
    (ht : isFeasible ρEtilde (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t) :
    isFeasible (recoveredExtension ρEtilde T hpos htp)
      (DensityOp.toSubDensityOp
        (DensityOp.tensor (DensityOp.maxMixed dE) σR))
      ((polyDim : ℝ) * t) := by
  let σRsub : SubDensityOp dR := DensityOp.toSubDensityOp σR
  refine ⟨mul_nonneg (Nat.cast_nonneg polyDim) ht.1, ?_⟩
  intro x
  have hx : opLe
      ((recoveredExtension ρEtilde T hpos htp).stateMap x).toOp
      ((Complex.ofReal ((polyDim : ℝ) * t)) •
        ((DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).tensor σRsub).toOp) :=
    opLe_maxMixed_tensor_of_recovery (T x) σRsub polyDim t ht.1
      (hmono x) (hunit x) (ρEtilde.stateMap x).toOp
      ((recoveredExtension ρEtilde T hpos htp).stateMap x).toOp
      (ht.2 x) (recoveredExtension_stateMap_toOp ρEtilde T hpos htp x).symm
  simpa only [σRsub, SubDensityOp.tensor, DensityOp.toSubDensityOp,
    DensityOp.tensor] using hx

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
