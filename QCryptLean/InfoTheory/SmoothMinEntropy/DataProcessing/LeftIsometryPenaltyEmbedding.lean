import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.SmoothPartialTrace
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.IsometryConjugation
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order

/-!
# Smooth Min-Entropy Left Isometry Embeddings — block embeddings and feasibility transport

Construction layer of the blockwise rectangular left-isometry embedding of CQ
states: the tensor identity embedding `I ⊗ V`, its action on sub-density and CQ
states, purified-distance invariance, and the feasibility transport of a
max-mixed reference through the embedding with its dimension factor.

## Main definitions
- `kronIdLeftIso`: the matrix `I ⊗ V` for a rectangular map on the right factor.
- `subDensityOpLeftIsometryEmbed` / `cqStateLeftIsometryEmbed`: the embedded states.

## Main statements
- `kronIdLeftIso_left_iso`: `I ⊗ V` is a left-isometry when `V` is.
- `cqState_purifiedDistance_left_isometry_embed_le`: the embedding does not increase
  purified distance.
- `isFeasible_maxMixed_left_isometry_embed_of_isFeasible`: feasible max-mixed
  domination transfers through a blockwise left-isometry with a dimension factor.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The Kronecker product of the identity on `dH` dimensions with a rectangular map V.

For any matrices `V : Matrix (Fin dTgt) (Fin dSrc) ℂ`, this produces
`I_{dH} ⊗ V : Matrix (Fin (dH * dTgt)) (Fin (dH * dSrc)) ℂ`, the action
of `V` on the "right" register of the bipartite space `ℂ^dH ⊗ ℂ^{dSrc}`.
When `V` is a left-isometry (`Vᴴ * V = 1`), so is `I_{dH} ⊗ V`. -/
noncomputable def kronIdLeftIso
    {dH dSrc dTgt : ℕ}
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ) :
    Matrix (Fin (dH * dTgt)) (Fin (dH * dSrc)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dH) (Fin dH) ℂ) V)

/-- If `V` is a left-isometry (`Vᴴ * V = 1`), then `I_{dH} ⊗ V` is also a
left-isometry: `(I_{dH} ⊗ V)ᴴ * (I_{dH} ⊗ V) = 1`.

This follows from `(I ⊗ V)ᴴ = I ⊗ Vᴴ` and then
`(I ⊗ Vᴴ) * (I ⊗ V) = I ⊗ (Vᴴ * V) = I ⊗ 1 = 1`,
using mixed-product identity for Kronecker products. -/
theorem kronIdLeftIso_left_iso
    {dH dSrc dTgt : ℕ}
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ)) :
    (kronIdLeftIso (dH := dH) V)ᴴ * kronIdLeftIso (dH := dH) V =
      (1 : Matrix (Fin (dH * dSrc)) (Fin (dH * dSrc)) ℂ) := by
  dsimp [kronIdLeftIso, Matrix.reindex]
  rw [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.conjTranspose_one, Matrix.one_mul, hV_iso]
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- Entry formula for `kronIdLeftIso V` on product indices:
`(I ⊗ V)_{(a,t),(b,s)} = δ_{a,b} · V_{t,s}`. -/
lemma kronIdLeftIso_apply
    {dH dSrc dTgt : ℕ}
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (a b : Fin dH) (t : Fin dTgt) (s : Fin dSrc) :
    kronIdLeftIso (dH := dH) V (finProdFinEquiv (a, t)) (finProdFinEquiv (b, s)) =
      (1 : Matrix (Fin dH) (Fin dH) ℂ) a b * V t s := by
  simp [kronIdLeftIso, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]

/-- **A right-factor rectangular left-isometry preserves the left partial trace.**

For `V` with `Vᴴ V = 1`, conjugating an operator on `H ⊗ R'` by `I_H ⊗ V`
(embedding `R'` isometrically into `R`) does not change the `H`-marginal:
`Tr_R ((I⊗V) · M · (I⊗V)ᴴ) = Tr_{R'} M`. -/
lemma partialTraceB_kronIdLeftIso_conj
    {dH dSrc dTgt : ℕ}
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hV : Vᴴ * V = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (M : Op (dH * dSrc)) :
    partialTraceB
        (kronIdLeftIso (dH := dH) V * M * (kronIdLeftIso (dH := dH) V)ᴴ) =
      partialTraceB M := by
  classical
  ext i j
  simp only [partialTraceB, Matrix.of_apply]
  -- Expand the conjugation entrywise: collapse the two `Fin dH` deltas from the
  -- left/right `(I⊗V)` factors, leaving `∑ u ∑ s V t s · conj(V t u) · M_{(i,s),(j,u)}`.
  have hentry : ∀ t : Fin dTgt,
      (kronIdLeftIso (dH := dH) V * M * (kronIdLeftIso (dH := dH) V)ᴴ)
          (finProdFinEquiv (i, t)) (finProdFinEquiv (j, t)) =
        ∑ u : Fin dSrc, ∑ s : Fin dSrc,
          V t s * (starRingEnd ℂ) (V t u) *
            M (finProdFinEquiv (i, s)) (finProdFinEquiv (j, u)) := by
    intro t
    rw [Matrix.mul_apply]
    rw [← Equiv.sum_comp finProdFinEquiv
      (fun q' => (kronIdLeftIso (dH := dH) V * M) (finProdFinEquiv (i, t)) q' *
        (kronIdLeftIso (dH := dH) V)ᴴ q' (finProdFinEquiv (j, t)))]
    rw [Fintype.sum_prod_type]
    -- Collapse the outer `Fin dH` index `b` against `δ_{j,b}` from the right `(I⊗V)ᴴ`.
    rw [Finset.sum_eq_single j]
    rotate_left
    · intro b _ hbj
      apply Finset.sum_eq_zero
      intro u _
      rw [Matrix.conjTranspose_apply, kronIdLeftIso_apply, Matrix.one_apply,
        ite_eq_right (fun h => hbj h.symm)]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
    -- `b = j`: collapse the inner `Fin dH` index `a` against `δ_{i,a}`, per `u`.
    apply Finset.sum_congr rfl
    intro u _
    rw [Matrix.conjTranspose_apply, kronIdLeftIso_apply, Matrix.one_apply_eq, one_mul,
      ← starRingEnd_apply]
    rw [Matrix.mul_apply]
    rw [← Equiv.sum_comp finProdFinEquiv
      (fun p' => kronIdLeftIso (dH := dH) V (finProdFinEquiv (i, t)) p' *
        M p' (finProdFinEquiv (j, u)))]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    rotate_left
    · intro a _ hai
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro s _
      rw [kronIdLeftIso_apply, Matrix.one_apply, ite_eq_right (fun h => hai h.symm)]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
    -- `a = i`: clean inner `∑ s`.
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [kronIdLeftIso_apply, Matrix.one_apply_eq, one_mul]
    ring
  -- Assemble: sum the entry formula over `t`, reorder `t` innermost, collapse via `Vᴴ V`.
  rw [Finset.sum_congr rfl (fun t _ => hentry t)]
  have hreorder :
      (∑ t : Fin dTgt, ∑ u : Fin dSrc, ∑ s : Fin dSrc,
          V t s * (starRingEnd ℂ) (V t u) *
            M (finProdFinEquiv (i, s)) (finProdFinEquiv (j, u))) =
        ∑ u : Fin dSrc, ∑ s : Fin dSrc, ∑ t : Fin dTgt,
          V t s * (starRingEnd ℂ) (V t u) *
            M (finProdFinEquiv (i, s)) (finProdFinEquiv (j, u)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
  rw [hreorder]
  -- per `(u, s)`: the `∑ t` factor is `(Vᴴ V)_{u,s} = δ_{u,s}`.
  have hcol : ∀ u s : Fin dSrc,
      (∑ t : Fin dTgt, V t s * (starRingEnd ℂ) (V t u) *
          M (finProdFinEquiv (i, s)) (finProdFinEquiv (j, u))) =
        (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ) u s *
          M (finProdFinEquiv (i, s)) (finProdFinEquiv (j, u)) := by
    intro u s
    rw [← Finset.sum_mul]
    congr 1
    rw [← hV, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [Matrix.conjTranspose_apply, starRingEnd_apply, mul_comm]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun s _ => hcol u s))]
  -- collapse the inner `∑ s` against `δ_{u,s}`.
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single u]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro s _ hsu
    rw [Matrix.one_apply, ite_eq_right (fun h => hsu h.symm)]
    simp
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- **The range projection of `I_H ⊗ V` is `I_H ⊗ (V Vᴴ)`.**

`(I⊗V)(I⊗V)ᴴ = I ⊗ (V Vᴴ)`, an `Op.tensor` of the identity with the range
projector `V Vᴴ` of the right-factor isometry. -/
lemma kronIdLeftIso_mul_conjTranspose
    {dH dSrc dTgt : ℕ}
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ) :
    kronIdLeftIso (dH := dH) V * (kronIdLeftIso (dH := dH) V)ᴴ =
      Op.tensor (1 : Op dH) (V * Vᴴ) := by
  dsimp [kronIdLeftIso, Op.tensor, Matrix.reindex]
  rw [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.conjTranspose_one, Matrix.mul_one]

/-- A rectangular left-isometry preserves trace under conjugation. -/
theorem trace_rect_conj_of_left_isometry
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (A : Matrix (Fin dSrc) (Fin dSrc) ℂ) :
    (K * A * Kᴴ).trace = A.trace := by
  calc
    (K * A * Kᴴ).trace
        = ((K * A) * Kᴴ).trace := rfl
    _ = (Kᴴ * (K * A)).trace :=
        Matrix.trace_mul_comm (K * A) Kᴴ
    _ = ((Kᴴ * K) * A).trace := by rw [Matrix.mul_assoc]
    _ = (1 * A).trace := by rw [hK_iso]
    _ = A.trace := by rw [Matrix.one_mul]

/-- Conjugate a sub-density operator by a rectangular left-isometry.

If `Kᴴ * K = 1`, then `K * σ * Kᴴ` is positive semidefinite and has the same
trace as `σ`, hence remains sub-normalized. -/
noncomputable def subDensityOpLeftIsometryEmbed
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (σ : SubDensityOp dSrc) :
    SubDensityOp dTgt where
  toOp := K * σ.toOp * Kᴴ
  isHermitian := by
    calc
      (K * σ.toOp * Kᴴ)ᴴ
          = K * σ.toOpᴴ * Kᴴ := by
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_conjTranspose]
              simp [Matrix.mul_assoc]
      _ = K * σ.toOp * Kᴴ := by rw [σ.isHermitian]
  pos_semidef := by
    intro x
    have hσ_psd : σ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
    have hKσK_psd : (K * σ.toOp * Kᴴ).PosSemidef := by
      simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
        hσ_psd.conjTranspose_mul_mul_same Kᴴ
    exact Quantum.Operators.posSemidef_re_quadraticForm_nonneg hKσK_psd x
  trace_le_one := by
    simpa [trace_rect_conj_of_left_isometry K hK_iso σ.toOp] using σ.trace_le_one

lemma subDensityOpLeftIsometryEmbed_trace
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (σ : SubDensityOp dSrc) :
    (subDensityOpLeftIsometryEmbed K hK_iso σ).trace = σ.trace := by
  unfold subDensityOpLeftIsometryEmbed SubDensityOp.trace
  rw [trace_rect_conj_of_left_isometry K hK_iso σ.toOp]

/-- Blockwise CQ-state embedding by a rectangular left-isometry. -/
noncomputable def cqStateLeftIsometryEmbed
    {α : Type*} [Fintype α]
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc) :
    CQState α dTgt where
  stateMap x := subDensityOpLeftIsometryEmbed K hK_iso (ρ.stateMap x)
  weight_le_one := by
    simpa [subDensityOpLeftIsometryEmbed_trace K hK_iso] using ρ.weight_le_one

/-- Purified distance is non-increasing when both CQ states are embedded blockwise
by the same rectangular left-isometry. -/
theorem cqState_purifiedDistance_left_isometry_embed_le
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (ε : ℝ)
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ ρ' : CQState α dSrc)
    (ρ_embed ρ'_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * Kᴴ)
    (hρ'_embed : ∀ x : α,
      (ρ'_embed.stateMap x).toOp =
        K * (ρ'.stateMap x).toOp * Kᴴ)
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε) :
    CQState.purifiedDistance ρ_embed ρ'_embed ≤ ε := by
  exact le_trans
    (CQState.purifiedDistance_left_isometry_embed_le
      K hK_iso ρ ρ' ρ_embed ρ'_embed hρ_embed hρ'_embed)
    hd

lemma opLe_left_isometry_range_projection
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ)) :
    opLe (K * Kᴴ) (1 : Op dTgt) := by
  let P : Op dTgt := K * Kᴴ
  have hP_herm : Pᴴ = P := by
    dsimp [P]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hP_idem : P * P = P := by
    dsimp [P]
    calc
      (K * Kᴴ) * (K * Kᴴ)
          = K * (Kᴴ * K) * Kᴴ := by
              simp [Matrix.mul_assoc]
      _ = K * (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ) * Kᴴ := by rw [hK_iso]
      _ = K * Kᴴ := by simp
  have hcomp_eq : (1 - P) * (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
    noncomm_ring [hP_idem]
  have hcomp_psd : (1 - P).PosSemidef := by
    have hself : ((1 - P) * (1 - P)ᴴ).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose (1 - P)
    rw [hcomp_eq] at hself
    exact hself
  exact opLe_of_posSemidef_sub (by simpa [P] using hcomp_psd)

private lemma maxMixed_toSubDensityOp_toOp_eq_inv_smul_one
    {d : ℕ} [NeZero d] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp =
      (Complex.ofReal ((d : ℝ)⁻¹)) • (1 : Op d) := by
  have hdim :=
    maxMixed_dim_smul_toSubDensityOp_toOp_eq_one (d := d)
  calc
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp
        = (Complex.ofReal ((d : ℝ)⁻¹ * (d : ℝ))) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp := by
            have hd_ne : (d : ℝ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (NeZero.ne d)
            have hmul : (d : ℝ)⁻¹ * (d : ℝ) = 1 := by
              field_simp [hd_ne]
            rw [hmul, Complex.ofReal_one, one_smul]
    _ = (Complex.ofReal ((d : ℝ)⁻¹)) •
          ((Complex.ofReal (d : ℝ)) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp) := by
            rw [smul_smul, ← Complex.ofReal_mul]
    _ = (Complex.ofReal ((d : ℝ)⁻¹)) • (1 : Op d) := by
            rw [hdim]

private lemma scaled_maxMixed_toSubDensityOp_toOp_eq_inv_smul_one
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt] :
    (Complex.ofReal ((dTgt : ℝ) / (dSrc : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp =
      (Complex.ofReal ((dSrc : ℝ)⁻¹)) • (1 : Op dTgt) := by
  have hdim :=
    maxMixed_dim_smul_toSubDensityOp_toOp_eq_one (d := dTgt)
  calc
    (Complex.ofReal ((dTgt : ℝ) / (dSrc : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp
        = (Complex.ofReal ((dSrc : ℝ)⁻¹)) •
            ((Complex.ofReal (dTgt : ℝ)) •
              (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp) := by
            rw [smul_smul, ← Complex.ofReal_mul]
            congr 1
            rw [div_eq_mul_inv, mul_comm]
    _ = (Complex.ofReal ((dSrc : ℝ)⁻¹)) • (1 : Op dTgt) := by
            rw [hdim]

private lemma maxMixed_left_isometry_embed_opLe_scaled_maxMixed
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ)) :
    opLe
      (K * (DensityOp.toSubDensityOp (DensityOp.maxMixed dSrc)).toOp * Kᴴ)
      ((Complex.ofReal ((dTgt : ℝ) / (dSrc : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp) := by
  have hproj := opLe_left_isometry_range_projection K hK_iso
  have hinv_nonneg : 0 ≤ (dSrc : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg dSrc)
  have hscaled := opLe_smul_nonneg hinv_nonneg hproj
  have hsrc :=
    maxMixed_toSubDensityOp_toOp_eq_inv_smul_one (d := dSrc)
  have htgt :=
    scaled_maxMixed_toSubDensityOp_toOp_eq_inv_smul_one
      (dSrc := dSrc) (dTgt := dTgt)
  have hscaled' : opLe
      ((Complex.ofReal ((dSrc : ℝ)⁻¹)) • (K * Kᴴ))
      ((Complex.ofReal ((dTgt : ℝ) / (dSrc : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp) := by
    rw [htgt]
    exact hscaled
  simpa [hsrc, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    using hscaled'

/-- Candidate-level feasibility transfer from the source max-mixed reference to
the ambient max-mixed reference under `I_E ⊗ V`.

If a source candidate is feasible with scalar `t` against
`maxMixed (dE * dR₁)`, then its blockwise `K = I_E ⊗ V` embedding is feasible
against `maxMixed (dE * dR₂)` with scalar `(dR₂ / dR₁) * t`. -/
theorem isFeasible_maxMixed_left_isometry_embed_of_isFeasible
    (Xcl : Type) [Fintype Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (_hdim : dR₁ ≤ dR₂)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ)
    {t : ℝ}
    (ht : isFeasible ρ
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) t) :
    isFeasible ρ_embed
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂)))
      (((dR₂ : ℝ) / (dR₁ : ℝ)) * t) := by
  let K := kronIdLeftIso (dH := dE) V
  have hK_iso :
      Kᴴ * K = (1 : Matrix (Fin (dE * dR₁)) (Fin (dE * dR₁)) ℂ) := by
    simpa [K] using kronIdLeftIso_left_iso (dH := dE) V hV_iso
  have hratio_nonneg : 0 ≤ (dR₂ : ℝ) / (dR₁ : ℝ) :=
    div_nonneg (Nat.cast_nonneg dR₂) (Nat.cast_nonneg dR₁)
  refine ⟨mul_nonneg hratio_nonneg ht.1, fun x => ?_⟩
  have hblock := Quantum.Channels.opLe_kraus_sandwich K (ht.2 x)
  have hratio_eq :
      (dE : ℝ) * (dR₂ : ℝ) / ((dE : ℝ) * (dR₁ : ℝ)) =
        (dR₂ : ℝ) / (dR₁ : ℝ) := by
    have hdE_ne : (dE : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne dE)
    have hdR₁_ne : (dR₁ : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne dR₁)
    field_simp [hdE_ne, hdR₁_ne]
  have href : opLe
      (K *
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))).toOp *
        Kᴴ)
      ((Complex.ofReal ((dR₂ : ℝ) / (dR₁ : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))).toOp) := by
    simpa [K, Nat.cast_mul, hratio_eq] using
      maxMixed_left_isometry_embed_opLe_scaled_maxMixed
        (dSrc := dE * dR₁) (dTgt := dE * dR₂) K hK_iso
  have hscaled := opLe_smul_nonneg ht.1 href
  have hscaled' : opLe
      (K *
        ((Complex.ofReal t) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))).toOp) *
        Kᴴ)
      ((Complex.ofReal (((dR₂ : ℝ) / (dR₁ : ℝ)) * t)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))).toOp) := by
    simpa [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul,
      Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hchain := opLe_trans hblock hscaled'
  rw [h_embed x]
  simpa [K] using hchain

/-- A rectangular isometry transports a feasible maximally mixed coefficient with the
ratio of target and source dimensions. -/
theorem isFeasible_maxMixed_left_isometry_embed_bare_of_isFeasible
    {X : Type*} [Fintype X] {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (ρ : CQState X dSrc) (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK : Kᴴ * K = 1) (ρ_embed : CQState X dTgt)
    (h_embed : ∀ x, (ρ_embed.stateMap x).toOp = K * (ρ.stateMap x).toOp * Kᴴ)
    {t : ℝ} (ht : isFeasible ρ (DensityOp.toSubDensityOp (DensityOp.maxMixed dSrc)) t) :
    isFeasible ρ_embed (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt))
      (((dTgt : ℝ) / (dSrc : ℝ)) * t) := by
  refine ⟨mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ht.1,
    fun x => ?_⟩
  have href := opLe_smul_nonneg ht.1 (maxMixed_left_isometry_embed_opLe_scaled_maxMixed K hK)
  have hscaled : opLe
      (K * (Complex.ofReal t •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dSrc)).toOp) * Kᴴ)
      (Complex.ofReal (((dTgt : ℝ) / (dSrc : ℝ)) * t) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dTgt)).toOp) := by
    simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_mul, mul_comm] using href
  rw [h_embed x]
  exact opLe_trans (Quantum.Channels.opLe_kraus_sandwich K (ht.2 x)) hscaled

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
