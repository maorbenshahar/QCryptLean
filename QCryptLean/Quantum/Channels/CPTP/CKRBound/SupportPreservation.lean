import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Basic
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapTensorIdAncilla
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy

/-!
# Tensor-Reference Support Preservation — projector trace bounds and first-factor channels

This module records support facts for CKR-style reference registers.  The
statements are generic in the channel acting on the first tensor factor and in
the fixed first-factor block selected after that channel.

## Main statements

- `opLe_trace_smul_projector_of_left_support`: a PSD operator left-supported on
  a projector is dominated by its trace times that projector.
- `subDensityOp_le_trace_smul_tensor_projector_of_left_support`: tensor-projector
  specialization for sub-density operators.
- `mapTensorId_tensor_projector_left_support_of_opLe`: applying a first-factor
  linear map preserves left support on the reference projector.
- `firstFactorSubmatrix_tensor_projector_left_support`: first-factor principal
  blocks preserve support on the untouched second tensor factor.
- `mapTensorId_firstFactorSubmatrix_tensor_projector_support_of_opLe`: combined
  first-factor channel and fixed-block support preservation.
- `subDensityOp_le_trace_mul_polyDim_smul_tensor_sigma`: per-block CKR domination,
  converting a symmetric-subspace support bound into a scalar bound against the
  product reference `1_E ⊗ σR`.
- `mapTensorId_pairedSymmetric_support`: left and right fixedness under every
  paired permutation imply paired symmetric projector support.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Channels

/-- A PSD operator with left support in a projector is dominated by its trace
times that projector. -/
lemma opLe_trace_smul_projector_of_left_support
    {d : ℕ} [NeZero d]
    (A Q : Op d)
    (hQ_idem : Q * Q = Q)
    (hQ_herm : Qᴴ = Q)
    (hA_psd : A.PosSemidef)
    (h_support : Q * A = A) :
    opLe A ((A.trace.re : ℂ) • Q) := by
  by_cases htr : A.trace.re = 0
  · have htrace : A.trace = 0 := by
      rcases hA_psd.trace_nonneg with ⟨_, h_im⟩
      exact Complex.ext htr h_im.symm
    have hA_zero : A = 0 := hA_psd.trace_eq_zero_iff.mp htrace
    rw [hA_zero, Matrix.trace_zero, Complex.zero_re]
    intro v
    simp [quadraticForm]
  · have htr_nonneg : 0 ≤ A.trace.re := hA_psd.trace_re_nonneg
    let A₀ : Op d := ((A.trace.re : ℂ)⁻¹) • A
    have hA₀_psd : A₀.PosSemidef := by
      dsimp [A₀]
      exact hA_psd.smul
        (by
          simpa only [Complex.ofReal_inv] using
            Complex.zero_le_real.mpr (inv_nonneg.mpr htr_nonneg))
    have hA₀_trace : A₀.trace.re ≤ 1 := by
      dsimp [A₀]
      have htrace_real : A.trace = (A.trace.re : ℂ) := by
        rcases hA_psd.trace_nonneg with ⟨_, h_im⟩
        exact Complex.ext rfl h_im.symm
      rw [Matrix.trace_smul, htrace_real]
      simp only [smul_eq_mul]
      have hmul :
          ((↑(↑(A.trace.re : ℂ).re) : ℂ)⁻¹ * (A.trace.re : ℂ)) = 1 := by
        simpa using
          (inv_mul_cancel₀ (a := (A.trace.re : ℂ)) (by exact_mod_cast htr))
      rw [hmul]
      norm_num
    have hA₀_support : Q * A₀ = A₀ := by
      dsimp [A₀]
      rw [Matrix.mul_smul, h_support]
    have h_projector : (Q - A₀).PosSemidef :=
      projector_sub_psd_of_support Q A₀ hQ_idem hQ_herm hA₀_psd hA₀_trace hA₀_support
    apply opLe_of_posSemidef_sub
    have h_scaled : ((A.trace.re : ℂ) • (Q - A₀)).PosSemidef :=
      h_projector.smul (Complex.zero_le_real.mpr htr_nonneg)
    have h_scaled_eq : (A.trace.re : ℂ) • (Q - A₀) =
        (A.trace.re : ℂ) • Q - A := by
      dsimp [A₀]
      rw [smul_sub]
      congr 1
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul, htr]
    rwa [h_scaled_eq] at h_scaled

/-- A sub-density operator supported on a tensor projector is dominated by its
trace times that projector. -/
theorem subDensityOp_le_trace_smul_tensor_projector_of_left_support
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (B : SubDensityOp (dE * dR))
    (P : Op dR)
    (hP_idem : P * P = P)
    (hP_herm : Pᴴ = P)
    (h_support : (Op.tensor (1 : Op dE) P) * B.toOp = B.toOp) :
    opLe B.toOp ((B.trace : ℂ) • Op.tensor (1 : Op dE) P) := by
  have hQ_idem :
      Op.tensor (1 : Op dE) P * Op.tensor (1 : Op dE) P =
        Op.tensor (1 : Op dE) P := by
    rw [Op.tensor_mul, Matrix.one_mul, hP_idem]
  have hQ_herm : (Op.tensor (1 : Op dE) P)ᴴ = Op.tensor (1 : Op dE) P := by
    rw [Op.tensor_conjTranspose, conjTranspose_one, hP_herm]
  simpa [SubDensityOp.trace] using
    opLe_trace_smul_projector_of_left_support
      B.toOp (Op.tensor (1 : Op dE) P) hQ_idem hQ_herm
      (posSemidefOp_implies_mathlib B.toPosSemidefOp) h_support

/-- Per-block CKR domination: a sub-density operator that is left-supported on a
projector `1_E ⊗ Psym` (so it is dominated by its trace times that projector) and
whose projector `Psym` is in turn dominated by `polyDim` copies of `σR`, is
dominated by `trace · polyDim` copies of `1_E ⊗ σR`.

This is the operator-domination heart of the CKR-style structured extension
penalty: it converts a structured support bound at the symmetric subspace
projector into a scalar bound against the product reference `1_E ⊗ σR`. -/
theorem subDensityOp_le_trace_mul_polyDim_smul_tensor_sigma
    {dE dR : ℕ}
    (B : SubDensityOp (dE * dR))
    (σR : SubDensityOp dR)
    (Psym : Op dR) (polyDim : ℕ)
    (hPsym_proj : Psym * Psym = Psym ∧ Psymᴴ = Psym)
    (hσR_polyDim : opLe Psym ((polyDim : ℂ) • σR.toOp))
    (hSupp : opLe B.toOp ((B.trace : ℂ) • Op.tensor (1 : Op dE) Psym)) :
    opLe B.toOp
      (((B.trace * polyDim : ℂ)) • Op.tensor (1 : Op dE) σR.toOp) := by
  -- `Psym` is PSD (Hermitian idempotent: `Psym = Psymᴴ * Psym`).
  have hPsym_psd : Psym.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self Psym
    rwa [hPsym_proj.2, hPsym_proj.1] at h
  have hσR_psd : σR.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σR.toPosSemidefOp
  have hpolyDim_nn : (0 : ℂ) ≤ (polyDim : ℂ) := by
    exact_mod_cast Nat.cast_nonneg polyDim
  -- Tensor the trivial bound `1_E ≤ 1_E` with `Psym ≤ polyDim • σR`.
  have htensor :
      opLe (Op.tensor (1 : Op dE) Psym)
        (Op.tensor (1 : Op dE) ((polyDim : ℂ) • σR.toOp)) :=
    opLe_tensor_psd (Matrix.PosSemidef.one).isHermitian Matrix.PosSemidef.one
      hPsym_psd (hσR_psd.smul hpolyDim_nn).isHermitian
      (fun _ => le_refl _) hσR_polyDim
  rw [Op.tensor_smul_right] at htensor
  -- Scale the bound by the (nonnegative) trace and chain with the support bound.
  have hscaled := opLe_smul_nonneg B.trace_nonneg htensor
  have hchain := opLe_trans hSupp hscaled
  rwa [smul_smul] at hchain

/-- An operator that is positive semidefinite together with its negation is zero. -/
lemma posSemidef_eq_zero_of_neg_posSemidef
    {d : ℕ} {A : Op d} (hA : A.PosSemidef) (hNeg : (-A).PosSemidef) :
    A = 0 := by
  have h_tr_ge : 0 ≤ A.trace.re := hA.trace_re_nonneg
  have h_tr_neg_ge : 0 ≤ (-A).trace.re := hNeg.trace_re_nonneg
  have h_tr_le : A.trace.re ≤ 0 := by
    rw [Matrix.trace_neg, Complex.neg_re] at h_tr_neg_ge
    linarith
  have h_tr_re : A.trace.re = 0 := le_antisymm h_tr_le h_tr_ge
  have h_tr_im : A.trace.im = 0 := by
    rcases hA.trace_nonneg with ⟨_, him⟩
    exact him.symm
  exact hA.trace_eq_zero_iff.mp (Complex.ext h_tr_re h_tr_im)

/-- For a PSD operator `X`, the Gram identity `Rᴴ * X * R = 0` forces `X * R = 0`. -/
lemma posSemidef_mul_eq_zero_of_conjTranspose_mul_mul_eq_zero
    {d : ℕ} (X R : Op d) (hX_psd : X.PosSemidef)
    (h : Rᴴ * X * R = 0) :
    X * R = 0 := by
  have hSqrt_sq : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX_psd.nonneg
  have hSqrt_herm : (CFC.sqrt X)ᴴ = CFC.sqrt X :=
    (CFC.sqrt_nonneg X).posSemidef.isHermitian
  have hfactor : (CFC.sqrt X * R)ᴴ * (CFC.sqrt X * R) = Rᴴ * X * R := by
    rw [conjTranspose_mul, hSqrt_herm, mul_assoc,
      ← mul_assoc (CFC.sqrt X) (CFC.sqrt X) R, hSqrt_sq, ← mul_assoc]
  have hSqrtR : CFC.sqrt X * R = 0 :=
    Matrix.conjTranspose_mul_self_eq_zero.mp (by rw [hfactor, h])
  rw [← hSqrt_sq, mul_assoc, hSqrtR, Matrix.mul_zero]

/-- If `X` is PSD and `opLe X (1 ⊗ P)` with `P` a projector on the second factor,
then `X` is sandwich-fixed by the projector: `(1 ⊗ P) · X · (1 ⊗ P) = X`. -/
private lemma opLe_tensor_one_projector_sandwich_fixed_aux
    {dIn dR : ℕ} [NeZero dIn] [NeZero dR]
    (X : Op (dIn * dR)) (P : Op dR)
    (hP_idem : P * P = P) (hP_herm : Pᴴ = P)
    (hX_psd : X.PosSemidef)
    (hX_supp_bound : opLe X (Op.tensor (1 : Op dIn) P)) :
    Op.tensor (1 : Op dIn) P * X * Op.tensor (1 : Op dIn) P = X := by
  -- Q := 1 ⊗ P (projector on the joint register).
  set Q : Op (dIn * dR) := Op.tensor (1 : Op dIn) P with hQ_def
  have hQ_idem : Q * Q = Q := by
    simp only [hQ_def, Op.tensor_mul, Matrix.one_mul, hP_idem]
  have hQ_herm : Qᴴ = Q := by
    simp only [hQ_def, Op.tensor_conjTranspose, conjTranspose_one, hP_herm]
  have hQ_isHerm : Q.IsHermitian := hQ_herm
  have hX_isHerm : X.IsHermitian := hX_psd.isHermitian
  -- (Q - X) is Mathlib-PSD via the `opLe` bridge.
  have hQX_psd : (Q - X).PosSemidef :=
    Quantum.Operators.opLe.posSemidef_sub hX_isHerm hQ_isHerm hX_supp_bound
  -- R := 1 - Q is Hermitian, and R * Q = 0.
  set R : Op (dIn * dR) := 1 - Q with hR_def
  have hR_herm : Rᴴ = R := by
    simp only [hR_def, conjTranspose_sub, conjTranspose_one, hQ_herm]
  have hRQ : R * Q = 0 := by
    simp only [hR_def, sub_mul, Matrix.one_mul, hQ_idem, sub_self]
  -- R · X · R is PSD (Hermitian conjugation of a PSD operator).
  have hRXR_psd : (R * X * R).PosSemidef := by
    have h := hX_psd.conjTranspose_mul_mul_same R
    rwa [hR_herm] at h
  -- R · (Q - X) · R is PSD likewise.
  have hRQXR_psd : (R * (Q - X) * R).PosSemidef := by
    have h := hQX_psd.conjTranspose_mul_mul_same R
    rwa [hR_herm] at h
  -- R · (Q - X) · R = -(R · X · R) because R · Q = 0.
  have hRQXR_eq : R * (Q - X) * R = -(R * X * R) := by
    have hexp : R * (Q - X) * R = R * Q * R - R * X * R := by
      rw [mul_sub R Q X, sub_mul (R * Q) (R * X) R]
    rw [hexp, hRQ, Matrix.zero_mul, zero_sub]
  have hNeg_psd : (-(R * X * R)).PosSemidef := hRQXR_eq ▸ hRQXR_psd
  -- Both `R · X · R` and its negation are PSD, hence it is zero.
  have hRXR_zero : R * X * R = 0 :=
    posSemidef_eq_zero_of_neg_posSemidef hRXR_psd hNeg_psd
  -- `R · X · R = 0` with `X` PSD forces `X · R = 0`.
  have hXR_zero : X * R = 0 :=
    posSemidef_mul_eq_zero_of_conjTranspose_mul_mul_eq_zero X R hX_psd
      (by rw [hR_herm]; exact hRXR_zero)
  -- From `X * (1 - Q) = 0` deduce `X * Q = X`.
  have hXQ : X * Q = X := by
    have h : X * (1 - Q) = 0 := by rw [← hR_def]; exact hXR_zero
    rw [mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  -- Take adjoints to get `Q * X = X`.
  have hQX : Q * X = X := by
    have h := congrArg Matrix.conjTranspose hXQ
    rw [conjTranspose_mul, hQ_herm] at h
    have hXh : Xᴴ = X := hX_isHerm
    rw [hXh] at h
    exact h
  -- Conclude.
  calc Q * X * Q
      = Q * (X * Q) := by rw [mul_assoc]
    _ = Q * X := by rw [hXQ]
    _ = X := hQX

/-- **Marginal → operator left support.**

For a PSD operator `τ` on `E ⊗ R` and a projector `P` on the second (`R`) factor,
if the `R`-marginal `partialTraceA τ` is left-supported on `P`, then `τ` itself is
left-supported on `1_E ⊗ P`.

This is the marginal→operator direction of support preservation: the PSD "no
leakage off the marginal support" principle.  The proof restricts to the orthogonal
complement `1_E ⊗ (1 - P)`, observes that the resulting conjugate has vanishing
partial trace (hence zero trace, hence is itself zero as a PSD operator), and then
runs the Gram/`CFC.sqrt` argument to push the support back to the joint register. -/
theorem tensor_one_projector_left_support_of_partialTraceA_support
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (τ : Op (dE * dR)) (P : Op dR)
    (_hP_idem : P * P = P) (hP_herm : Pᴴ = P)
    (hτ_psd : τ.PosSemidef)
    (h_marg : P * partialTraceA τ = partialTraceA τ) :
    Op.tensor (1 : Op dE) P * τ = τ := by
  have hτ_herm : τᴴ = τ := hτ_psd.isHermitian
  -- complement projector on the R factor
  set Pc : Op dR := 1 - P with hPc_def
  have hPc_herm : Pcᴴ = Pc := by
    rw [hPc_def, conjTranspose_sub, conjTranspose_one, hP_herm]
  -- R := 1 ⊗ (1 - P) on the joint register
  set R : Op (dE * dR) := Op.tensor (1 : Op dE) Pc with hR_def
  have hR_herm : Rᴴ = R := by
    rw [hR_def, Op.tensor_conjTranspose, conjTranspose_one, hPc_herm]
  -- R τ R is PSD
  have hRτR_psd : (R * τ * R).PosSemidef := by
    have h := hτ_psd.conjTranspose_mul_mul_same R
    rwa [hR_herm] at h
  -- Pc · partialTraceA τ = 0 from the marginal hypothesis
  have hPc_marg : Pc * partialTraceA τ = 0 := by
    rw [hPc_def, sub_mul, one_mul, h_marg, sub_self]
  -- partialTraceA (R τ R) = Pc · partialTraceA τ · Pc = 0
  have hpt_zero : partialTraceA (R * τ * R) = 0 := by
    rw [hR_def, partialTraceA_one_tensor_sandwich, hPc_marg, Matrix.zero_mul]
  -- hence trace (R τ R) = 0
  have htr_zero : (R * τ * R).trace = 0 := by
    rw [← trace_partialTraceA, hpt_zero, Matrix.trace_zero]
  -- a PSD operator with zero trace is zero
  have hRτR_zero : R * τ * R = 0 := hRτR_psd.trace_eq_zero_iff.mp htr_zero
  -- `R · τ · R = 0` with `τ` PSD forces `τ · R = 0`.
  have hτR_zero : τ * R = 0 :=
    posSemidef_mul_eq_zero_of_conjTranspose_mul_mul_eq_zero τ R hτ_psd
      (by rw [hR_herm]; exact hRτR_zero)
  -- τ R = 0 means τ (1 - 1⊗P) = 0, so τ (1⊗P) = τ
  have hR_eq : R = 1 - Op.tensor (1 : Op dE) P := by
    rw [hR_def, hPc_def, Op.tensor_sub_right, Op.tensor_one]
  have hτQ : τ * Op.tensor (1 : Op dE) P = τ := by
    rw [hR_eq, mul_sub, Matrix.mul_one, sub_eq_zero] at hτR_zero
    exact hτR_zero.symm
  -- take adjoints to obtain (1⊗P) τ = τ
  have h := congrArg Matrix.conjTranspose hτQ
  rw [conjTranspose_mul, Op.tensor_conjTranspose, conjTranspose_one, hP_herm,
      hτ_herm] at h
  exact h

/-- If a PSD operator is PSD-bounded by `1 ⊗ P`, then applying a completely
positive linear map to the first tensor factor preserves left support on the
reference projector `P`. -/
theorem mapTensorId_tensor_projector_left_support_of_opLe
    {dIn dOut dR : ℕ} [NeZero dIn] [NeZero dOut] [NeZero dR]
    (Φ : Op dIn →ₗ[ℂ] Op dOut)
    (X : Op (dIn * dR))
    (P : Op dR)
    (hP_idem : P * P = P)
    (hP_herm : Pᴴ = P)
    (hX_psd : X.PosSemidef)
    (hX_supp_bound : opLe X (Op.tensor (1 : Op dIn) P))
    (hΦ_cp : IsCompletelyPositive ⇑Φ) :
    (Op.tensor (1 : Op dOut) P) * mapTensorId Φ X =
      mapTensorId Φ X := by
  -- (1) X sandwich-fixed by 1⊗P
  have hX_sand :
      Op.tensor (1 : Op dIn) P * X * Op.tensor (1 : Op dIn) P = X :=
    opLe_tensor_one_projector_sandwich_fixed_aux X P hP_idem hP_herm
      hX_psd hX_supp_bound
  -- (2) Transport the sandwich through `Φ ⊗ id` using ancilla commutation.
  have hΦX_sand :
      Op.tensor (1 : Op dOut) P * mapTensorId Φ X * Op.tensor (1 : Op dOut) P =
        mapTensorId Φ X := by
    calc Op.tensor (1 : Op dOut) P * mapTensorId Φ X * Op.tensor (1 : Op dOut) P
        = mapTensorId Φ (Op.tensor (1 : Op dIn) P * X) *
            Op.tensor (1 : Op dOut) P :=
          by rw [← Quantum.Metrics.KitaevWatrousContraction.kw_mapTensorId_left_ancilla_mul Φ P X]
      _ = mapTensorId Φ
            (Op.tensor (1 : Op dIn) P * X * Op.tensor (1 : Op dIn) P) :=
          by rw [← Quantum.Metrics.KitaevWatrousContraction.kw_mapTensorId_right_ancilla_mul Φ P
                  (Op.tensor (1 : Op dIn) P * X)]
      _ = mapTensorId Φ X := by rw [hX_sand]
  -- (3) (Φ⊗id) X is PSD
  have hΦX_psd : (mapTensorId Φ X).PosSemidef :=
    mapTensorId_posSemidef Φ X hX_psd hΦ_cp
  -- (4) Projector sandwich + PSD ⟹ one-sided support
  have hQ_idem :
      Op.tensor (1 : Op dOut) P * Op.tensor (1 : Op dOut) P =
        Op.tensor (1 : Op dOut) P := by
    rw [Op.tensor_mul, Matrix.one_mul, hP_idem]
  have hQ_herm :
      (Op.tensor (1 : Op dOut) P)ᴴ = Op.tensor (1 : Op dOut) P := by
    rw [Op.tensor_conjTranspose, conjTranspose_one, hP_herm]
  exact (Quantum.Symmetry.projector_sandwich_oneSided hQ_idem hQ_herm
    hΦX_psd hΦX_sand).1

/-- A first-factor submatrix commutes with left multiplication by an operator on
the unchanged second tensor factor. -/
lemma firstFactorSubmatrix_one_tensor_left_mul
    {dOut dBlock dR : ℕ} [NeZero dOut] [NeZero dBlock] [NeZero dR]
    (Y : Op (dOut * dR))
    (P : Op dR)
    (embedFirst : Fin dBlock → Fin dOut) :
    let embed : Fin (dBlock * dR) → Fin (dOut * dR) :=
      fun er => finProdFinEquiv
        (embedFirst (finProdFinEquiv.symm er).1, (finProdFinEquiv.symm er).2)
    ((Op.tensor (1 : Op dOut) P) * Y).submatrix embed embed =
      (Op.tensor (1 : Op dBlock) P) * Y.submatrix embed embed := by
  intro embed
  ext er er'
  simp only [embed, Op.tensor, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Equiv.symm_apply_apply]
  conv_lhs => rw [← Equiv.sum_comp finProdFinEquiv]
  conv_rhs => rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp

/-- Taking a principal block along the first tensor factor preserves left
support on the untouched second tensor factor. -/
theorem firstFactorSubmatrix_tensor_projector_left_support
    {dOut dBlock dR : ℕ} [NeZero dOut] [NeZero dBlock] [NeZero dR]
    (Y : Op (dOut * dR))
    (P : Op dR)
    (embedFirst : Fin dBlock → Fin dOut)
    (hY_support : (Op.tensor (1 : Op dOut) P) * Y = Y) :
    let embed : Fin (dBlock * dR) → Fin (dOut * dR) :=
      fun er => finProdFinEquiv
        (embedFirst (finProdFinEquiv.symm er).1, (finProdFinEquiv.symm er).2)
    (Op.tensor (1 : Op dBlock) P) * Y.submatrix embed embed =
      Y.submatrix embed embed := by
  intro embed
  rw [← firstFactorSubmatrix_one_tensor_left_mul
    (Y := Y) (P := P) (embedFirst := embedFirst)]
  rw [hY_support]

/-- Applying a completely positive first-factor channel and then selecting a
fixed first-factor block preserves tensor-projector support on the reference
register. -/
theorem mapTensorId_firstFactorSubmatrix_tensor_projector_support_of_opLe
    {dIn dOut dBlock dR : ℕ}
    [NeZero dIn] [NeZero dOut] [NeZero dBlock] [NeZero dR]
    (Φ : Op dIn →ₗ[ℂ] Op dOut)
    (X : Op (dIn * dR))
    (P : Op dR)
    (embedFirst : Fin dBlock → Fin dOut)
    (hP_idem : P * P = P)
    (hP_herm : Pᴴ = P)
    (hX_psd : X.PosSemidef)
    (hX_supp_bound : opLe X (Op.tensor (1 : Op dIn) P))
    (hΦ_cp : IsCompletelyPositive ⇑Φ) :
    let embed : Fin (dBlock * dR) → Fin (dOut * dR) :=
      fun er => finProdFinEquiv
        (embedFirst (finProdFinEquiv.symm er).1, (finProdFinEquiv.symm er).2)
    (Op.tensor (1 : Op dBlock) P) *
        (mapTensorId Φ X).submatrix embed embed =
      (mapTensorId Φ X).submatrix embed embed := by
  intro embed
  exact
    firstFactorSubmatrix_tensor_projector_left_support
      (Y := mapTensorId Φ X) (P := P) (embedFirst := embedFirst)
      (mapTensorId_tensor_projector_left_support_of_opLe
        Φ X P hP_idem hP_herm hX_psd hX_supp_bound hΦ_cp)

/-- **Paired-symmetric support from one-sided fixedness.**

If a joint operator is fixed on the left and on the right by every paired
permutation representation, then it is fixed by the paired symmetric-projector
sandwich.  Paired conjugation invariance alone is not enough for this support
identity; callers must supply one-sided fixedness or an explicit support
hypothesis from their construction. -/
theorem mapTensorId_pairedSymmetric_support
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (hτ_left : ∀ σ : Equiv.Perm (Fin n),
      let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
      Op.tensor U U * τ.toOp = τ.toOp)
    (hτ_right : ∀ σ : Equiv.Perm (Fin n),
      let U : Op (d ^ n) := Math.RepresentationTheory.permutationRepresentation d n σ
      τ.toOp * Op.tensor U U = τ.toOp) :
    symmetricProjectorPaired d n * τ.toOp * symmetricProjectorPaired d n =
      τ.toOp := by
  have hleft :
      symmetricProjectorPaired d n * τ.toOp = τ.toOp :=
    InfoTheory.DeFinetti.symmetricProjectorPaired_mul_eq_of_perm_left_invariant
      (d := d) (n := n) (A := τ.toOp) hτ_left
  have hright :
      τ.toOp * symmetricProjectorPaired d n = τ.toOp :=
    InfoTheory.DeFinetti.mul_symmetricProjectorPaired_eq_of_perm_right_invariant
      (d := d) (n := n) (A := τ.toOp) hτ_right
  calc
    symmetricProjectorPaired d n * τ.toOp * symmetricProjectorPaired d n
        = τ.toOp * symmetricProjectorPaired d n := by rw [hleft]
    _ = τ.toOp := hright

end Quantum.Channels

end -- noncomputable section
