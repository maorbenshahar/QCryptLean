import QCryptLean.Quantum.Channels.CPTP.CKRBound.HermitianContractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapTensorIdAdjoint
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Metrics.KitaevWatrousContraction
import QCryptLean.Quantum.Metrics.KitaevWatrousPurification
import QCryptLean.Quantum.Metrics.TraceNorm.Cartesian

/-!
# Kitaev-Watrous PSD Maximization — PSD scaling, Hermitian and Cartesian reductions, square ancilla

Reductions of a trace-norm bound for `Φ ⊗ id` from positive semidefinite inputs of trace at
most `1` to all inputs of trace norm at most `1`. For every linear `Φ`, PSD scaling and the
Jordan decomposition give the bound for Hermitian inputs with no loss, and the Cartesian
decomposition `X = Re X + i · Im X` extends it to all inputs at the cost of a factor `2`.
For a Hermitian-preserving `Φ`, the Kitaev-Watrous self-adjoint dilation extends it to all
inputs with no loss. The non-Hermitian contraction machinery is isolated in
`KitaevWatrousContraction.lean`.

## Main statements
- `nonneg_of_psd_bound`: a PSD trace-norm bound is nonnegative
- `kw_psd_scaling`: PSD trace scaling for `mapTensorId` and arbitrary ancilla
- `kw_hermitian_bound`: Hermitian Kitaev-Watrous reduction without factor loss
- `traceNorm_mapTensorId_le_two_mul_of_psd_bound`: reduction to all inputs for an arbitrary
  linear map, with factor `2`
- `diamondNorm_le_two_mul_of_psd_bound`: the resulting diamond-norm bound
- `kw_psd_ancilla_lift`: the PSD bound at the square ancilla holds at every ancilla
- `traceNorm_mapTensorId_le_two_mul_of_square_psd_bound`: factor-`2` reduction at every
  ancilla from the square-ancilla PSD bound
- `kw_nonhermitian_reduction`: square-ancilla reduction from PSD inputs to all inputs for a
  Hermitian-preserving map, without factor loss

## References
- Kitaev (1997), "Quantum computations: algorithms and error correction"
- Watrous (2002), "Semidefinite programs for completely bounded norms"
- Watrous (2018), "Theory of Quantum Information", Proposition 3.47
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrous

private lemma trace_im_eq_zero_of_posSemidef {d : ℕ} {A : Op d}
    (hA : A.PosSemidef) :
    A.trace.im = 0 := by
  have h0 := hA.trace_nonneg
  rw [Complex.le_def] at h0
  exact h0.2.symm

private lemma trace_re_pos_of_posSemidef_trace_ne_zero {d : ℕ} {A : Op d}
    (hA : A.PosSemidef) (htr : A.trace ≠ 0) :
    0 < A.trace.re := by
  have h0 := hA.trace_nonneg
  rw [Complex.le_def] at h0
  exact lt_of_le_of_ne h0.1 (fun h =>
    htr (Complex.ext h.symm h0.2.symm))

private lemma norm_eq_re_of_nonneg {c : ℂ} (hre : 0 ≤ c.re) (him : c.im = 0) :
    ‖c‖ = c.re := by
  rw [show ‖c‖ = Real.sqrt (c.normSq) from rfl,
    show c.normSq = c.re ^ 2 from by
      rw [Complex.normSq_apply, him, mul_zero, add_zero, sq],
    Real.sqrt_sq hre]

/-- A PSD trace-norm bound is nonnegative: the hypothesis at `ρ = 0` reads `0 ≤ B`. -/
lemma nonneg_of_psd_bound {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    {Φ : Op n →ₗ[ℂ] Op m} {B : ℝ}
    (hPSD : ∀ (ρ : Op (n * k)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B) :
    0 ≤ B := by
  simpa [mapTensorId_zero, traceNorm_zero] using hPSD 0 Matrix.PosSemidef.zero (by simp)

/-- PSD trace scaling for `mapTensorId`: for PSD `ρ`,
    `traceNorm (mapTensorId Φ ρ) ≤ Tr(ρ).re * B`.
    Generalizes the unit-trace PSD bound to arbitrary PSD inputs. -/
lemma kw_psd_scaling {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * k)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (ρ : Op (n * k)) (hρ : ρ.PosSemidef) :
    traceNorm (mapTensorId Φ ρ) ≤ ρ.trace.re * B := by
  by_cases htr : ρ.trace = 0
  · have hρ_zero : ρ = 0 := hρ.trace_eq_zero_iff.mp htr
    rw [hρ_zero, mapTensorId_zero, traceNorm_zero, Matrix.trace_zero,
      Complex.zero_re, zero_mul]
  · set c := ρ.trace
    set P := (c⁻¹ • ρ : Op (n * k)) with hP_def
    have hc_re_pos : 0 < c.re := by
      simpa [c] using trace_re_pos_of_posSemidef_trace_ne_zero hρ htr
    have hc_ne : c ≠ 0 := htr
    have hc_im_zero : c.im = 0 := by
      simpa [c] using trace_im_eq_zero_of_posSemidef hρ
    have hP_psd : P.PosSemidef := by
      apply hρ.smul
      rw [Complex.le_def]
      constructor
      · simp only [Complex.inv_re, hc_im_zero, Complex.normSq_apply,
            mul_zero, add_zero, Complex.zero_re]
        positivity
      · simp only [Complex.inv_im, hc_im_zero, neg_zero, zero_div,
            Complex.zero_im]
    have hP_trace : P.trace = 1 := by
      rw [hP_def, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hc_ne]
    have hP_bound : traceNorm (mapTensorId Φ P) ≤ B := by
      apply hPSD P hP_psd
      rw [hP_trace, Complex.one_re]
    have hρ_eq : ρ = c • P := by
      rw [hP_def, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
    rw [hρ_eq, mapTensorId_smul_basic, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
    have hc_norm : ‖c‖ = c.re :=
      norm_eq_re_of_nonneg hc_re_pos.le hc_im_zero
    rw [hc_norm]
    exact mul_le_mul_of_nonneg_left hP_bound hc_re_pos.le

/-- Hermitian Kitaev-Watrous reduction: the PSD hypothesis implies the same
    bound for Hermitian inputs with trace norm at most `1`, with no factor loss. -/
lemma kw_hermitian_bound {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hPSD : ∀ (ρ : Op (n * k)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (H : Op (n * k)) (hH : H.IsHermitian) (hH_norm : traceNorm H ≤ 1) :
    traceNorm (mapTensorId Φ H) ≤ B := by
  obtain ⟨Hpos, Hneg, hpos_psd, hneg_psd, hH_eq, hH_tn⟩ :=
    Quantum.Metrics.traceNormHermitian_eq_trace_pos_neg
      H hH
  have hH_tn_eq : traceNorm H = (Hpos.trace + Hneg.trace).re := by
    rwa [traceNorm_hermitian_eq H hH]
  calc traceNorm (mapTensorId Φ H)
      = traceNorm (mapTensorId Φ Hpos - mapTensorId Φ Hneg) := by
          rw [hH_eq, mapTensorId_sub]
    _ ≤ traceNorm (mapTensorId Φ Hpos) + traceNorm (mapTensorId Φ Hneg) :=
        traceNorm_sub_le _ _
    _ ≤ Hpos.trace.re * B + Hneg.trace.re * B := by
        gcongr
        · exact kw_psd_scaling Φ B hPSD Hpos hpos_psd
        · exact kw_psd_scaling Φ B hPSD Hneg hneg_psd
    _ = (Hpos.trace.re + Hneg.trace.re) * B := by ring
    _ = (Hpos.trace + Hneg.trace).re * B := by rw [Complex.add_re]
    _ = traceNorm H * B := by rw [hH_tn_eq]
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hH_norm hB
    _ = B := one_mul B

/-! ## Arbitrary linear maps: the Cartesian reduction

For an arbitrary linear `Φ`, the Hermitian parts in `X = Re X + i · Im X` have trace norm at
most `‖X‖₁` (`traceNorm_realPart_le`, `traceNorm_imaginaryPart_le`), so the Hermitian bound
extends to all inputs at the cost of a factor `2`. No Hermiticity preservation is assumed.
-/

/-- **PSD-to-all-input reduction for an arbitrary linear map, with factor `2`.**
If `‖(Φ ⊗ id_k)(ρ)‖₁ ≤ B` for every positive semidefinite `ρ` on `n ⊗ k` of trace at most `1`,
then `‖(Φ ⊗ id_k)(X)‖₁ ≤ 2 * B` for every `X` on `n ⊗ k` with `‖X‖₁ ≤ 1`.

`Φ` need not be Hermitian-preserving. Each Cartesian part of `X` is bounded by
`kw_hermitian_bound`, and the factor `2` comes from adding the two parts. For a
Hermitian-preserving `Φ` at the square ancilla, `kw_nonhermitian_reduction` gives the bound
`B` itself. -/
theorem traceNorm_mapTensorId_le_two_mul_of_psd_bound {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * k)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (X : Op (n * k)) (hX : traceNorm X ≤ 1) :
    traceNorm (mapTensorId Φ X) ≤ 2 * B := by
  have hB := nonneg_of_psd_bound hPSD
  have hRe := kw_hermitian_bound Φ B hB hPSD _ (realPart X).2
    ((traceNorm_realPart_le X).trans hX)
  have hIm := kw_hermitian_bound Φ B hB hPSD _ (imaginaryPart X).2
    ((traceNorm_imaginaryPart_le X).trans hX)
  have hX_eq : mapTensorId Φ X =
      mapTensorId Φ (realPart X : Op (n * k)) +
        Complex.I • mapTensorId Φ (imaginaryPart X : Op (n * k)) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
    rw [mapTensorId_add_basic, mapTensorId_smul_basic]
  calc traceNorm (mapTensorId Φ X)
      ≤ traceNorm (mapTensorId Φ (realPart X : Op (n * k))) +
          traceNorm (Complex.I • mapTensorId Φ (imaginaryPart X : Op (n * k))) := by
        rw [hX_eq]
        exact traceNorm_add_le _ _
    _ = traceNorm (mapTensorId Φ (realPart X : Op (n * k))) +
          traceNorm (mapTensorId Φ (imaginaryPart X : Op (n * k))) := by
        rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, Complex.norm_I, one_mul]
    _ ≤ 2 * B := by linarith

/-- The diamond norm of an arbitrary linear map is at most `2 * B` when `B` bounds
`‖(Φ ⊗ id_n)(ρ)‖₁` over positive semidefinite `ρ` on `n ⊗ n` of trace at most `1`.
For a Hermitian-preserving map `kw_nonhermitian_reduction` gives `B` instead. -/
theorem diamondNorm_le_two_mul_of_psd_bound {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B) :
    diamondNorm Φ ≤ 2 * B := by
  unfold diamondNorm
  apply csSup_le
  · exact ⟨0, 0, by rw [traceNorm_zero]; exact zero_le_one,
      by rw [mapTensorId_zero, traceNorm_zero]⟩
  · rintro t ⟨X, hX, rfl⟩
    exact traceNorm_mapTensorId_le_two_mul_of_psd_bound Φ B hPSD X hX

/-- Lift the PSD bound from the square ancilla `n` to an arbitrary ancilla `k`
    by purifying the reduced state and applying substate extraction. This holds for every
    linear `Φ`: the extraction map is completely positive and trace non-increasing, hence
    trace-norm contractive on all inputs (`traceNorm_mapIdTensor_contractive`). -/
lemma kw_psd_ancilla_lift {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (ρ : Op (n * k)) (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace.re ≤ 1) :
    traceNorm (mapTensorId Φ ρ) ≤ B := by
  by_cases htr : ρ.trace = 0
  · have hρ_zero : ρ = 0 := hρ.trace_eq_zero_iff.mp htr
    rw [hρ_zero, mapTensorId_zero, traceNorm_zero]
    exact hB
  · set α : ℝ := ρ.trace.re
    have hρ_im_zero : ρ.trace.im = 0 := by
      exact trace_im_eq_zero_of_posSemidef hρ
    have hα_pos : 0 < α := by
      simpa [α] using trace_re_pos_of_posSemidef_trace_ne_zero hρ htr
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    set A : Op n := partialTraceB ρ
    have hA_psd : A.PosSemidef := by
      exact partialTraceB_posSemidef_mathlib ρ hρ
    have hA_trace : A.trace = (α : ℂ) := by
      change (partialTraceB ρ).trace = (α : ℂ)
      rw [trace_partialTraceB]
      exact Complex.ext (by simp [α]) hρ_im_zero
    let σH : DensityOp n := by
      refine ⟨⟨⟨(((α⁻¹ : ℝ) : ℂ) • A), ?_⟩, ?_⟩, ?_⟩
      · unfold Matrix.IsHermitian
        rw [conjTranspose_smul, hA_psd.isHermitian.eq]
        simp
      · intro x
        have hscaled_psd : ((((α⁻¹ : ℝ) : ℂ) • A) : Op n).PosSemidef := by
          apply hA_psd.smul
          rw [Complex.le_def]
          constructor
          · exact inv_nonneg.mpr hα_pos.le
          · simp
        have h :=
          hscaled_psd.dotProduct_mulVec_nonneg x
        have heq : star x ⬝ᵥ ((((α⁻¹ : ℝ) : ℂ) • A) *ᵥ x) =
            quadraticForm ((((α⁻¹ : ℝ) : ℂ) • A) : Op n) x := rfl
        rw [heq, Complex.nonneg_iff] at h
        exact h.1
      · rw [Matrix.trace_smul, hA_trace]
        norm_num [hα_ne]
    let τ : DensityOp (n * n) :=
      Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σH
    have hτ_pure : τ.IsPure := by
      simpa [τ] using
        Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure σH
    have hτ_purifies : τ.partialTraceB = σH := by
      apply DensityOp.ext
      simpa [τ] using
        Quantum.Metrics.KitaevWatrousPurification.partialTraceB_sameAncillaPurificationDensity σH
    have hρ_sub : (((α : ℂ) • σH.toOp) - partialTraceB ρ).PosSemidef := by
      rw [show σH.toOp = (((α⁻¹ : ℝ) : ℂ) • A) by rfl]
      rw [show A = partialTraceB ρ by rfl]
      rw [smul_smul]
      have hmul : ((α : ℂ) * (((α⁻¹ : ℝ) : ℂ))) = 1 := by
        norm_num [hα_ne]
      rw [hmul, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
    obtain ⟨T, hT_cp, hT_contr, hρ_eq⟩ :=
      substate_map_exists ρ hρ σH α hα_pos hρ_sub τ hτ_pure hτ_purifies
    have hτ_psd : τ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib τ.toPosSemidefOp
    have hτ_bound : traceNorm (mapTensorId Φ τ.toOp) ≤ B := by
      apply hPSD τ.toOp hτ_psd
      rw [τ.trace_one, Complex.one_re]
    have h_contr :=
      traceNorm_mapIdTensor_contractive T hT_cp hT_contr (mapTensorId Φ τ.toOp)
    have hα_le_one : α ≤ 1 := by
      simpa [α] using hρ_tr
    have hα_norm : ‖((α : ℂ))‖ = α := by
      simp [abs_of_nonneg hα_pos.le]
    rw [hρ_eq, mapTensorId_smul_basic, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq,
      mapTensorId_compose_different_factors Φ T τ.toOp]
    rw [hα_norm]
    calc α * traceNorm (mapIdTensor T (mapTensorId Φ τ.toOp))
        ≤ α * traceNorm (mapTensorId Φ τ.toOp) :=
          mul_le_mul_of_nonneg_left h_contr hα_pos.le
      _ ≤ α * B := mul_le_mul_of_nonneg_left hτ_bound hα_pos.le
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hα_le_one hB
      _ = B := one_mul B

/-- The factor-`2` reduction at every ancilla from the PSD bound at the square ancilla alone:
`kw_psd_ancilla_lift` carries that bound to the ancilla `k`, and
`traceNorm_mapTensorId_le_two_mul_of_psd_bound` applies there. `Φ` need not be
Hermitian-preserving. -/
theorem traceNorm_mapTensorId_le_two_mul_of_square_psd_bound {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (X : Op (n * k)) (hX : traceNorm X ≤ 1) :
    traceNorm (mapTensorId Φ X) ≤ 2 * B :=
  traceNorm_mapTensorId_le_two_mul_of_psd_bound Φ B
    (kw_psd_ancilla_lift Φ B (nonneg_of_psd_bound hPSD) hPSD) X hX

private def ancillaDilationEquiv (d k : ℕ) :
    Fin (d * (k + k)) ≃ Fin ((d * k) + (d * k)) :=
  finProdFinEquiv.symm.trans
    (((Equiv.refl _).prodCongr finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib _ _ _).trans
        ((finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv)))

private lemma fpfe_divNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).divNat = z.1 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.fst h).symm

private lemma fpfe_modNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).modNat = z.2 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.snd h).symm

@[simp] private lemma finSumFinEquiv_symm_apply_addNat_self {N : ℕ} (x : Fin N) :
    finSumFinEquiv.symm (x.addNat N) = Sum.inr x := by
  rw [show x.addNat N = Fin.natAdd N x by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]]
  exact finSumFinEquiv_symm_apply_natAdd (m := N) (x := x)

private lemma mapTensorId_selfAdjointDilation_reindex {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * n)) :
    mapTensorId (k := n + n) Φ
        ((selfAdjointDilation X).submatrix
          (ancillaDilationEquiv n n) (ancillaDilationEquiv n n)) =
      (blockMap (mapTensorId (k := n) Φ) (selfAdjointDilation X)).submatrix
        (ancillaDilationEquiv m n) (ancillaDilationEquiv m n) := by
  ext p q
  rcases hp : finProdFinEquiv.symm p with ⟨a, s⟩
  rcases hq : finProdFinEquiv.symm q with ⟨b, t⟩
  rw [show p = finProdFinEquiv (a, s) by
        simpa [hp] using (finProdFinEquiv.apply_symm_apply p).symm,
      show q = finProdFinEquiv (b, t) by
        simpa [hq] using (finProdFinEquiv.apply_symm_apply q).symm]
  rcases hs : finSumFinEquiv.symm s with s' | s' <;>
    rcases ht : finSumFinEquiv.symm t with t' | t' <;>
    simp [mapTensorId, blockMap, extractBlock, selfAdjointDilation, ancillaDilationEquiv,
      hs, ht, fpfe_divNat, fpfe_modNat, Equiv.prodCongr_apply,
      Equiv.sumCongr_apply, Matrix.of_apply, finSumFinEquiv_symm_apply_castAdd]

/-! ## Non-Hermitian reduction (Watrous TQI Theorem 3.51)

The non-Hermitian step requires Φ to be **Hermitian-preserving** (HP):
`Φ(A†) = Φ(A)†`. This is needed so that the Hermitianizing trick
`H = ½(X ⊗ |0⟩⟨1| + X† ⊗ |1⟩⟨0|)` produces a Hermitian output when
mapped by `Φ ⊗ id`, which avoids the factor-of-2 loss from Cartesian
decomposition.

The proof uses:
1. Hermitianizing trick: embed non-Hermitian X into Hermitian H in ℂ²-extended space
2. `kw_hermitian_bound` (Jordan decomposition) on H
3. Ancilla pullback (Lemma 3.45): reduce the PSD bound from the extended
   ancilla back to the original dimension via Schmidt decomposition.
-/

/-- Square-ancilla Kitaev-Watrous reduction from PSD inputs to arbitrary inputs.

    Requires Φ to be Hermitian-preserving (HP): `Φ(A†) = Φ(A)†`.
    HP makes the dilation step lossless; for an arbitrary linear `Φ` the Cartesian
    reduction `traceNorm_mapTensorId_le_two_mul_of_psd_bound` gives `2 * B` instead. -/
lemma kw_nonhermitian_reduction {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hHP : ∀ (M : Op n), Φ M.conjTranspose = (Φ M).conjTranspose)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (X : Op (n * n)) (hX : traceNorm X ≤ 1) :
    traceNorm (mapTensorId Φ X) ≤ B := by
  by_cases hH : X.IsHermitian
  · exact kw_hermitian_bound Φ B hB hPSD X hH hX
  · -- Non-Hermitian case: Hermitianizing trick (Watrous TQI Theorem 3.51)
    let H0 : Op (n * (n + n)) :=
      (selfAdjointDilation X).submatrix
        (ancillaDilationEquiv n n) (ancillaDilationEquiv n n)
    let H : Op (n * (n + n)) := ((1 / 2 : ℂ) • H0)
    have hH0_herm : H0.IsHermitian := by
      exact (selfAdjointDilation_isHermitian X).submatrix (ancillaDilationEquiv n n)
    have hH0_tn : traceNorm H0 = traceNorm (selfAdjointDilation X) := by
      simpa [H0] using
        traceNorm_submatrix_equiv (selfAdjointDilation X) (ancillaDilationEquiv n n)
    have hH_herm : H.IsHermitian := by
      simp [H, Matrix.IsHermitian, hH0_herm.eq]
    have hH_eq : traceNorm H = traceNorm X := by
      rw [show traceNorm H = ‖(1 / 2 : ℂ)‖ * traceNorm H0 by
            simp [H, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq],
        hH0_tn,
        traceNorm_selfAdjointDilation]
      norm_num
      ring_nf
    have hH_norm : traceNorm H ≤ 1 := by
      simpa [hH_eq] using hX
    have hPSD_lift := kw_psd_ancilla_lift (k := n + n) Φ B hB hPSD
    have h_bound := kw_hermitian_bound (k := n + n) Φ B hB hPSD_lift H hH_herm hH_norm
    have h_map_conj : ∀ M : Op (n * n),
        mapTensorId (k := n) Φ M.conjTranspose =
          (mapTensorId (k := n) Φ M).conjTranspose := by
      intro M
      exact mapTensorId_preserves_conjTranspose_of_preserves_conj Φ hHP M
    have h_block :
        blockMap (mapTensorId (k := n) Φ) (selfAdjointDilation X) =
          selfAdjointDilation (mapTensorId (k := n) Φ X) := by
      exact Quantum.Metrics.blockMap_selfAdjointDilation_of_preserves_conj
        (Ψ := mapTensorId (k := n) Φ)
        (by
          ext p q
          simp [mapTensorId, Matrix.of_apply])
        h_map_conj X
    have h_map_H0 :
        mapTensorId (k := n + n) Φ H0 =
          (selfAdjointDilation (mapTensorId (k := n) Φ X)).submatrix
            (ancillaDilationEquiv m n) (ancillaDilationEquiv m n) := by
      have h_block_sub :
          (blockMap (mapTensorId (k := n) Φ) (selfAdjointDilation X)).submatrix
              (ancillaDilationEquiv m n) (ancillaDilationEquiv m n) =
            (selfAdjointDilation (mapTensorId (k := n) Φ X)).submatrix
              (ancillaDilationEquiv m n) (ancillaDilationEquiv m n) := by
        exact congrArg (fun M =>
          M.submatrix (ancillaDilationEquiv m n) (ancillaDilationEquiv m n)) h_block
      simpa [H0] using
        (mapTensorId_selfAdjointDilation_reindex Φ X).trans h_block_sub
    have h_target_eq :
        traceNorm (mapTensorId (k := n + n) Φ H) =
          traceNorm (mapTensorId (k := n) Φ X) := by
      rw [show traceNorm (mapTensorId (k := n + n) Φ H) =
            ‖(1 / 2 : ℂ)‖ * traceNorm (mapTensorId (k := n + n) Φ H0) by
            simp [H, mapTensorId_smul_basic,
              Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq],
          h_map_H0, traceNorm_submatrix_equiv, traceNorm_selfAdjointDilation]
      norm_num
      ring_nf
    rw [h_target_eq] at h_bound
    simpa using h_bound

end Quantum.Metrics.KitaevWatrous
