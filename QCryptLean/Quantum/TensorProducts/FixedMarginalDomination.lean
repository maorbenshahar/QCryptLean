import QCryptLean.Quantum.Operators.InverseSqrtSandwichIff
import QCryptLean.Quantum.Operators.MatrixSqrt
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Basic
import QCryptLean.Quantum.TensorProducts.Rpow
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Domination by locally normalized projections

A positive operator supported on a projection is bounded by its trace times that
projection. Local inverse square roots evaluate the trace of a normalized bipartite
operator using only its prescribed marginal.
-/

open Quantum.Operators Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- Partial trace intertwines left multiplication by a system operator. -/
lemma partialTraceB_tensor_one_mul {a b : ℕ} (X : Op a) (T : Op (a * b)) :
    partialTraceB (Op.tensor X (1 : Op b) * T) = X * partialTraceB T := by
  simpa only [Op.tensor_one, mul_one] using
    partialTraceB_sandwich_tensor_one X (1 : Op a) T

/-- A local multiple of an operator with invertible marginal is determined by its marginal. -/
lemma eq_tensor_inverse_marginal_mul_of_local {a b : ℕ} (Q T : Op (a * b))
    (hΩ : IsUnit (partialTraceB Q))
    (hlocal : ∃ X : Op a, T = Op.tensor X (1 : Op b) * Q) :
    T = Op.tensor (partialTraceB T * (partialTraceB Q)⁻¹) (1 : Op b) * Q := by
  obtain ⟨X, rfl⟩ := hlocal
  rw [partialTraceB_tensor_one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hΩ), mul_one]

/-- Normalizing the Alice marginal by its inverse square root and then applying
`√A` gives the prescribed marginal `A`. -/
lemma partialTraceB_local_sqrt_normalization {a b : ℕ} {A K : Op a}
    (hA : A.PosSemidef) (hK : K.PosDef) (X : Op (a * b))
    (hKinv : K⁻¹ = partialTraceB X) :
    let S := Op.tensor (CFC.sqrt A) (1 : Op b)
    let W := Op.tensor (CFC.sqrt K) (1 : Op b)
    partialTraceB (S * (W * X * W) * S) = A := by
  dsimp only
  rw [partialTraceB_sandwich_tensor_one, partialTraceB_sandwich_tensor_one, ← hKinv,
    ← hK.inverseSqrt_sq, ← mul_assoc (CFC.sqrt K), hK.sqrt_mul_inverseSqrt, one_mul,
    hK.inverseSqrt_mul_sqrt, mul_one,
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)]

/-- Local normalization of a positive definite marginal, followed by a second local
filter, evaluates the trace as the trace of the inverse filter weight. -/
lemma trace_local_inverseSqrt_normalization {a b : ℕ} {A K : Op a}
    (hA : A.PosDef) (hK : K.PosDef) (X : Op (a * b))
    (hmarg : partialTraceB X = A) :
    (Op.tensor (hK.inverseSqrt * hA.inverseSqrt) (1 : Op b) * X *
      Op.tensor (hA.inverseSqrt * hK.inverseSqrt) (1 : Op b)).trace = K⁻¹.trace := by
  rw [← trace_partialTraceB, partialTraceB_sandwich_tensor_one, hmarg]
  have hmid : hK.inverseSqrt * hA.inverseSqrt * A * (hA.inverseSqrt * hK.inverseSqrt)
      = hK.inverseSqrt * hK.inverseSqrt := by
    calc hK.inverseSqrt * hA.inverseSqrt * A * (hA.inverseSqrt * hK.inverseSqrt)
        = hK.inverseSqrt * (hA.inverseSqrt * A * hA.inverseSqrt) * hK.inverseSqrt := by
            simp only [mul_assoc]
      _ = hK.inverseSqrt * hK.inverseSqrt := by
        rw [hA.inverseSqrt_sandwich_eq_one, mul_one]
  rw [hmid, hK.inverseSqrt_sq]

/-- A supported positive operator of trace `g > 0` is bounded by `g` times its
supporting orthogonal projection. -/
lemma trace_smul_projection_sub_posSemidef {d g : ℕ} [NeZero d]
    (Q X : Op d) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hX : X.PosSemidef) (hQX : Q * X = X)
    (htr : X.trace = (g : ℂ)) (hg : g ≠ 0) :
    ((g : ℂ) • Q - X).PosSemidef := by
  have hgc : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hbound : (Q - (g : ℂ)⁻¹ • X).PosSemidef := by
    refine Quantum.Channels.projector_sub_psd_of_support Q _ hQQ hQ
      (hX.smul (by positivity)) ?_ ?_
    · rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hgc, Complex.one_re]
    · rw [Matrix.mul_smul, hQX]
  have h := hbound.smul (show (0 : ℂ) ≤ (g : ℂ) by positivity)
  rwa [smul_sub, smul_smul, mul_inv_cancel₀ hgc, one_smul] at h

/-- An orthogonal projection supporting a state with positive definite marginal
has positive definite marginal itself. -/
lemma partialTraceB_projection_posDef_of_supported {a b : ℕ} [NeZero (a * b)]
    (Q : Op (a * b)) (ρ : DensityOp (a * b))
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (hQρ : Q * ρ.toOp = ρ.toOp)
    (hρ : (partialTraceB ρ.toOp).PosDef) : (partialTraceB Q).PosDef := by
  haveI : NeZero a := ⟨left_ne_zero_of_mul (NeZero.ne (a * b))⟩
  haveI : NeZero b := ⟨right_ne_zero_of_mul (NeZero.ne (a * b))⟩
  have hbound : (Q - ρ.toOp).PosSemidef := by
    simpa using trace_smul_projection_sub_posSemidef (g := 1) Q ρ.toOp hQ hQQ
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) hQρ (by simpa using ρ.trace_one) one_ne_zero
  have hmono := Quantum.Channels.partialTraceB_psd_mono Q ρ.toOp hbound
  simpa only [sub_add_cancel] using Matrix.PosDef.posSemidef_add hmono hρ

/-- Conjugating a supported positive operator into coordinates where its trace is
`g` gives domination by the correspondingly conjugated projection. -/
lemma projection_conjugation_bound {d g : ℕ} [NeZero d]
    (Q X C D : Op d) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hX : X.PosSemidef) (hQX : Q * X = X)
    (hDQ : D * Q = Q * D) (hCD : C * D = 1)
    (htr : (D * X * Dᴴ).trace = (g : ℂ)) (hg : g ≠ 0) :
    ((g : ℂ) • (C * Q * Cᴴ) - X).PosSemidef := by
  have hsupp : Q * (D * X * Dᴴ) = D * X * Dᴴ := by
    rw [← mul_assoc, ← mul_assoc, ← hDQ, mul_assoc D Q X, hQX]
  have hbound := trace_smul_projection_sub_posSemidef Q (D * X * Dᴴ) hQ hQQ
    (hX.mul_mul_conjTranspose_same D) hsupp htr hg
  have hcancel : C * (D * X * Dᴴ) * Cᴴ = X := by
    calc C * (D * X * Dᴴ) * Cᴴ = (C * D) * X * (C * D)ᴴ := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = X := by rw [hCD, Matrix.conjTranspose_one, one_mul, mul_one]
  have h := hbound.mul_mul_conjTranspose_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hcancel] at h

/-- A local positive square root commutes with every operator commuting with
the original local positive operator. -/
lemma tensor_sqrt_one_commute {a b : ℕ} {A : Op a} {X : Op (a * b)}
    (hA : A.PosSemidef) (h : Commute (Op.tensor A (1 : Op b)) X) :
    Commute (Op.tensor (CFC.sqrt A) (1 : Op b)) X := by
  rw [← Op.tensorRightOne_sqrt A hA]
  exact Quantum.Operators.sqrt_commute h.eq

/-- Inverting an invertible local operator preserves commutation. -/
lemma tensor_inv_one_commute {a b : ℕ} {A : Op a} {X : Op (a * b)}
    (hA : IsUnit A) (h : Commute (Op.tensor A (1 : Op b)) X) :
    Commute (Op.tensor A⁻¹ (1 : Op b)) X := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  let U : (Op (a * b))ˣ :=
    ⟨Op.tensor A 1, Op.tensor A⁻¹ 1,
      by rw [Op.tensor_mul, Matrix.mul_nonsing_inv A hdet, one_mul, Op.tensor_one],
      by rw [Op.tensor_mul, Matrix.nonsing_inv_mul A hdet, one_mul, Op.tensor_one]⟩
  exact Commute.units_inv_left (u := U) h

/-- Local square-root filters preserve positivity. -/
lemma local_sqrt_normalization_posSemidef {a b : ℕ} (A K : Op a)
    {X : Op (a * b)} (hX : X.PosSemidef) :
    let S := Op.tensor (CFC.sqrt A) (1 : Op b)
    let W := Op.tensor (CFC.sqrt K) (1 : Op b)
    (S * (W * X * W) * S).PosSemidef := by
  dsimp only
  have hS : (Op.tensor (CFC.sqrt A) (1 : Op b)).IsHermitian :=
    (Op.tensor_posSemidef_mathlib (CFC.sqrt_nonneg A).posSemidef
      Matrix.PosSemidef.one).isHermitian
  have hW : (Op.tensor (CFC.sqrt K) (1 : Op b)).IsHermitian :=
    (Op.tensor_posSemidef_mathlib (CFC.sqrt_nonneg K).posSemidef
      Matrix.PosSemidef.one).isHermitian
  simpa only [hS.eq, hW.eq] using
    (hX.mul_mul_conjTranspose_same (Op.tensor (CFC.sqrt K) (1 : Op b))).mul_mul_conjTranspose_same
      (Op.tensor (CFC.sqrt A) (1 : Op b))

/-- A positive operator with prescribed positive definite marginal is dominated by
its locally normalized support projection, with cost equal to the projection's
trace. Both local weights must commute with the projection. -/
lemma fixedMarginal_projection_domination {a b g : ℕ} [NeZero (a * b)]
    (Q X : Op (a * b)) {A K : Op a} (hA : A.PosDef) (hK : K.PosDef)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hX : X.PosSemidef) (hQX : Q * X = X) (hmarg : partialTraceB X = A)
    (hAcomm : Commute (Op.tensor A (1 : Op b)) Q)
    (hKcomm : Commute (Op.tensor K (1 : Op b)) Q)
    (hKinv : K⁻¹ = partialTraceB Q) (htr : Q.trace = (g : ℂ)) (hg : g ≠ 0) :
    let S := Op.tensor (CFC.sqrt A) (1 : Op b)
    let W := Op.tensor (CFC.sqrt K) (1 : Op b)
    (S * (W * Q * W) * S).PosSemidef ∧
      ((g : ℂ) • (S * (W * Q * W) * S) - X).PosSemidef := by
  dsimp only
  have hQpsd : Q.PosSemidef := by
    have h : Qᴴ * Q = Q := by rw [hQ, hQQ]
    rw [← h]
    exact Matrix.posSemidef_conjTranspose_mul_self Q
  -- conjugators: `S = √A ⊗ 1`, `W = √K ⊗ 1` and their inverses
  set S : Op (a * b) :=
    Op.tensor (CFC.sqrt A) (1 : Op b) with hS_def
  set Si : Op (a * b) :=
    Op.tensor hA.inverseSqrt (1 : Op b) with hSi_def
  set W : Op (a * b) :=
    Op.tensor (CFC.sqrt K) (1 : Op b) with hW_def
  set Wi : Op (a * b) :=
    Op.tensor hK.inverseSqrt (1 : Op b) with hWi_def
  -- two-sided inverse identities
  have hSSi : S * Si = 1 := by
    rw [hS_def, hSi_def, Op.tensor_mul, hA.sqrt_mul_inverseSqrt, Matrix.one_mul,
      Op.tensor_one]
  have hSiS : Si * S = 1 := by
    rw [hSi_def, hS_def, Op.tensor_mul, hA.inverseSqrt_mul_sqrt, Matrix.one_mul,
      Op.tensor_one]
  have hWWi : W * Wi = 1 := by
    rw [hW_def, hWi_def, Op.tensor_mul, hK.sqrt_mul_inverseSqrt, Matrix.one_mul,
      Op.tensor_one]
  have hWiW : Wi * W = 1 := by
    rw [hWi_def, hW_def, Op.tensor_mul, hK.inverseSqrt_mul_sqrt, Matrix.one_mul,
      Op.tensor_one]
  -- Hermitian facts
  have hsA_herm : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hsκ_herm : (CFC.sqrt K)ᴴ = CFC.sqrt K :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian
  have hS_herm : Sᴴ = S := by
    rw [hS_def, Op.tensor_conjTranspose, hsA_herm, Matrix.conjTranspose_one]
  have hSi_herm : Siᴴ = Si := by
    rw [hSi_def, Op.tensor_conjTranspose, hA.inverseSqrt_isHermitian.eq,
      Matrix.conjTranspose_one]
  have hW_herm : Wᴴ = W := by
    rw [hW_def, Op.tensor_conjTranspose, hsκ_herm, Matrix.conjTranspose_one]
  have hWi_herm : Wiᴴ = Wi := by
    rw [hWi_def, Op.tensor_conjTranspose, hK.inverseSqrt_isHermitian.eq,
      Matrix.conjTranspose_one]
  -- Functional calculus preserves commutation with the support projection.
  have hW_commQ : W * Q = Q * W := by
    exact (tensor_sqrt_one_commute hK.posSemidef hKcomm).eq
  have hS_commQ : S * Q = Q * S := by
    exact (tensor_sqrt_one_commute hA.posSemidef hAcomm).eq
  have hSi_commQ : Si * Q = Q * Si :=
    (Commute.units_inv_left (u := ⟨S, Si, hSSi, hSiS⟩) hS_commQ).eq
  have hWi_commQ : Wi * Q = Q * Wi :=
    (Commute.units_inv_left (u := ⟨W, Wi, hWWi, hWiW⟩) hW_commQ).eq
  set T := S * (W * Q * W) * S with hT_def
  have hT_psd : T.PosSemidef := local_sqrt_normalization_posSemidef A K hQpsd
  have hD_comm : (Wi * Si) * Q = Q * (Wi * Si) :=
    (Commute.mul_left hWi_commQ hSi_commQ).eq
  have hCD : (S * W) * (Wi * Si) = 1 := by
    rw [mul_assoc, ← mul_assoc W Wi Si, hWWi, one_mul, hSSi]
  have hnormalized_trace : ((Wi * Si) * X * (Wi * Si)ᴴ).trace = (g : ℂ) := by
    rw [Matrix.conjTranspose_mul, hSi_herm, hWi_herm,
      hWi_def, hSi_def, Op.tensor_mul, Op.tensor_mul, one_mul]
    rw [trace_local_inverseSqrt_normalization hA hK X hmarg,
      hKinv, trace_partialTraceB, htr]
  have hdom : ((g : ℂ) • T - X).PosSemidef := by
    have h := projection_conjugation_bound Q X (S * W) (Wi * Si)
      hQ hQQ hX hQX hD_comm hCD hnormalized_trace
      hg
    simpa only [hT_def, Matrix.conjTranspose_mul, hS_herm, hW_herm, mul_assoc] using h
  exact ⟨hT_psd, hdom⟩

end Quantum.TensorProducts
