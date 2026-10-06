import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Channels.CPTP.CKRBound.HermitianContractivity

/-!
# General Trace-Norm Contractivity for id ⊗ T

Extends `traceNorm_mapIdTensor_contractive_hermitian` to arbitrary
(non-Hermitian) operators via the self-adjoint dilation argument. It also
collects CP-map adjoint-preservation helpers used by the CKR reductions.

## Main statements
- `cp_linear_preserves_conjTranspose`: CP linear maps commute with `conjTranspose`.
- `cp_linear_sub_preserves_conjTranspose`: differences of CP linear maps commute
  with `conjTranspose`.
- `traceNorm_mapIdTensor_contractive`: trace-norm contractivity for `id ⊗ T`.

## References
- Watrous (2018) "TQI", Theorem 3.33, §2.2
- Ruskai (1994) "Beyond strong subadditivity"
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

namespace Quantum.Channels

/-! ## CP linear map helpers -/

/-- CP linear maps preserve conjugate transpose.
    Proof via Kraus form: T(A†) = Σ K A† K† = (Σ K A K†)†. -/
lemma cp_linear_preserves_conjTranspose {n m : ℕ}
    [NeZero n] [NeZero m]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (A : Op n) :
    T A.conjTranspose = (T A).conjTranspose := by
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum T hT_cp
  rw [hK A, hK A.conjTranspose, conjTranspose_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The difference of two completely positive linear maps preserves conjugate transpose. -/
lemma cp_linear_sub_preserves_conjTranspose {n m : ℕ}
    [NeZero n] [NeZero m]
    (Φ Ψ : Op n →ₗ[ℂ] Op m)
    (hΦ : IsCompletelyPositive (⇑Φ))
    (hΨ : IsCompletelyPositive (⇑Ψ)) :
    ∀ M : Op n, (Φ - Ψ) M.conjTranspose = ((Φ - Ψ) M).conjTranspose := by
  intro M
  simp only [LinearMap.sub_apply]
  rw [cp_linear_preserves_conjTranspose Φ hΦ,
    cp_linear_preserves_conjTranspose Ψ hΨ]
  simp only [Matrix.conjTranspose_sub]

/-- CP linear maps preserve PSD.
    Proof via Kraus form: T(P) = Σ K P K† is PSD. -/
lemma cp_linear_preserves_posSemidef {n m : ℕ}
    [NeZero n] [NeZero m]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (P : Op n) (hP : P.PosSemidef) :
    (T P).PosSemidef := by
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum T hT_cp
  rw [hK P]
  apply Matrix.posSemidef_sum; intro k _
  have h := hP.conjTranspose_mul_mul_same (K k)ᴴ
  simp only [conjTranspose_conjTranspose] at h
  exact h

/-- `(Φ ⊗ id_{dR}) X` is PSD whenever `Φ` is completely positive and `X` is PSD
on the joint `dIn * dR` register. -/
lemma mapTensorId_posSemidef
    {dIn dOut dR : ℕ} [NeZero dIn] [NeZero dOut] [NeZero dR]
    (Φ : Op dIn →ₗ[ℂ] Op dOut)
    (X : Op (dIn * dR))
    (hX_psd : X.PosSemidef)
    (hΦ_cp : IsCompletelyPositive ⇑Φ) :
    (mapTensorId Φ X).PosSemidef := by
  have hTensor_cp :
      IsCompletelyPositive (⇑(mapTensorIdLinear (k := dR) Φ)) := by
    simpa [mapTensorIdLinear] using
      (mapTensorId_isCompletelyPositive (k := dR) Φ hΦ_cp)
  have h :=
    cp_linear_preserves_posSemidef
      (mapTensorIdLinear (k := dR) Φ) hTensor_cp X hX_psd
  simpa [mapTensorIdLinear] using h

/-! ## Hermitian contractivity for blockMap Ψ -/

/-- Diagonal blocks of a PSD matrix are PSD. -/
private lemma extractBlock_diag_posSemidef {N : ℕ}
    (X : Op (N + N)) (hX : X.PosSemidef)
    (b : Fin 2) :
    (extractBlock X b b).PosSemidef := by
  -- extractBlock X b b = X.submatrix e e where e embeds Fin N
  let e : Fin N → Fin (N + N) := fun i =>
    finSumFinEquiv (if b = 0 then Sum.inl i else Sum.inr i)
  suffices h : extractBlock X b b = X.submatrix e e by
    rw [h]; exact hX.submatrix e
  ext i j
  simp [extractBlock, Matrix.submatrix, Matrix.of_apply, e]

/-- blockMap Ψ is TNI on PSD inputs when Ψ is TNI on PSD. -/
private lemma blockMap_tni_of_tni {N M : ℕ}
    (Ψ : Op N → Op M)
    (hΨ_tni : ∀ P : Op N, P.PosSemidef →
      (Ψ P).trace.re ≤ P.trace.re)
    (X : Op (N + N)) (hX : X.PosSemidef) :
    (blockMap Ψ X).trace.re ≤ X.trace.re := by
  -- Trace of blockMap = Tr(Ψ(X₀₀)) + Tr(Ψ(X₁₁))
  have h_bm_trace : (blockMap Ψ X).trace =
      (Ψ (extractBlock X 0 0)).trace +
      (Ψ (extractBlock X 1 1)).trace := by
    simp only [blockMap, Matrix.trace, Matrix.diag,
      Matrix.submatrix_apply]
    trans (∑ s : Fin M ⊕ Fin M,
      (Matrix.fromBlocks
        (Ψ (extractBlock X 0 0))
        (Ψ (extractBlock X 0 1))
        (Ψ (extractBlock X 1 0))
        (Ψ (extractBlock X 1 1))) s s)
    · exact Fintype.sum_equiv finSumFinEquiv.symm _ _
        (fun _ => rfl)
    · rw [Fintype.sum_sum_type]; congr 1
  -- Trace of X = Tr(X₀₀) + Tr(X₁₁)
  have h_x_trace : X.trace =
      (extractBlock X 0 0).trace +
      (extractBlock X 1 1).trace := by
    simp only [Matrix.trace, Matrix.diag, extractBlock,
      Matrix.of_apply]
    trans (∑ s : Fin N ⊕ Fin N,
      X (finSumFinEquiv s) (finSumFinEquiv s))
    · exact Fintype.sum_equiv finSumFinEquiv.symm _ _
        (fun x => by simp [Equiv.apply_symm_apply])
    · rw [Fintype.sum_sum_type]; congr 1
  rw [h_bm_trace, h_x_trace, Complex.add_re, Complex.add_re]
  exact add_le_add
    (hΨ_tni _ (extractBlock_diag_posSemidef X hX 0))
    (hΨ_tni _ (extractBlock_diag_posSemidef X hX 1))

/-- `fromBlocks` distributes over `Finset.sum`. -/
private lemma fromBlocks_finset_sum {r M : ℕ}
    (A : Fin r → Op M)
    (B : Fin r → Op M)
    (C : Fin r → Op M)
    (D : Fin r → Op M) :
    Matrix.fromBlocks (∑ i, A i) (∑ i, B i)
      (∑ i, C i) (∑ i, D i) =
    ∑ i, Matrix.fromBlocks (A i) (B i)
      (C i) (D i) := by
  ext (a | a) (b | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,
      Matrix.sum_apply]

/-- The reassembled blocks of X equal X reindexed. -/
private lemma fromBlocks_extractBlock_eq {N : ℕ}
    (X : Op (N + N)) :
    Matrix.fromBlocks (extractBlock X 0 0) (extractBlock X 0 1)
      (extractBlock X 1 0) (extractBlock X 1 1) =
    X.submatrix finSumFinEquiv finSumFinEquiv := by
  ext (a | a) (b | b) <;>
    simp [extractBlock, Matrix.fromBlocks,
      Matrix.submatrix, Matrix.of_apply]

/-- Block-diagonal conjugation: blockDiag(K) · M · blockDiag(K)† =
    fromBlocks(K Mᵢⱼ K†). -/
private lemma fromBlocks_blockDiag_mul {N M : ℕ}
    (K : Matrix (Fin M) (Fin N) ℂ)
    (A B C D : Op N) :
    Matrix.fromBlocks K 0 0 K *
      Matrix.fromBlocks A B C D *
      (Matrix.fromBlocks K 0 0 K)ᴴ =
    Matrix.fromBlocks (K * A * Kᴴ) (K * B * Kᴴ)
      (K * C * Kᴴ) (K * D * Kᴴ) := by
  simp only [Matrix.fromBlocks_conjTranspose,
    conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_assoc]

/-- blockMap Ψ preserves PSD when Ψ is CP+linear. -/
private lemma blockMap_preserves_posSemidef {N M : ℕ}
    [NeZero N] [NeZero M]
    (Ψ : Op N →ₗ[ℂ] Op M)
    (hΨ_cp : IsCompletelyPositive ⇑Ψ)
    (X : Op (N + N)) (hX : X.PosSemidef) :
    (blockMap ⇑Ψ X).PosSemidef := by
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum Ψ hΨ_cp
  rw [blockMap]; apply Matrix.PosSemidef.submatrix
  simp_rw [hK]; rw [fromBlocks_finset_sum]
  apply Matrix.posSemidef_sum; intro k _
  have h_psd := hX.submatrix finSumFinEquiv
  convert h_psd.conjTranspose_mul_mul_same
    (Matrix.fromBlocks (K k) 0 0 (K k))ᴴ using 1
  rw [conjTranspose_conjTranspose,
    ← fromBlocks_extractBlock_eq X, fromBlocks_blockDiag_mul]

/-- extractBlock distributes over subtraction. -/
private lemma extractBlock_sub {N : ℕ}
    (X Y : Op (N + N)) (bi bj : Fin 2) :
    extractBlock (X - Y) bi bj =
      extractBlock X bi bj - extractBlock Y bi bj := by
  ext i j
  simp [extractBlock, Matrix.of_apply, Matrix.sub_apply]

private instance neZero_add_self (N : ℕ) [NeZero N] :
    NeZero (N + N) :=
  ⟨by have := NeZero.ne N; omega⟩

/-- Hermitian contractivity for blockMap Ψ when Ψ is
    CP+linear+TNI. Uses Jordan decomposition. -/
private lemma traceNorm_blockMap_contractive_hermitian
    {N M : ℕ} [NeZero N] [NeZero M]
    (Ψ : Op N →ₗ[ℂ] Op M)
    (hΨ_cp : IsCompletelyPositive ⇑Ψ)
    (hΨ_contr : ∀ P : Op N, P.PosSemidef →
      (Ψ P).trace.re ≤ P.trace.re)
    (X : Op (N + N)) (hX : X.IsHermitian) :
    traceNorm (blockMap ⇑Ψ X) ≤ traceNorm X := by
  open Quantum.Metrics in
  obtain ⟨Dp, Dm, hDp, hDm, hDecomp, hNorm⟩ :=
    traceNormHermitian_eq_trace_pos_neg X hX
  have hLinSub : blockMap ⇑Ψ X =
      blockMap ⇑Ψ Dp - blockMap ⇑Ψ Dm := by
    rw [hDecomp]; ext a b
    simp only [blockMap, Matrix.sub_apply,
      Matrix.submatrix_apply, extractBlock_sub, map_sub]
    rcases finSumFinEquiv.symm a with a' | a' <;>
    rcases finSumFinEquiv.symm b with b' | b' <;>
    simp [Matrix.fromBlocks, Matrix.sub_apply]
  have hBDp :=
    blockMap_preserves_posSemidef Ψ hΨ_cp Dp hDp
  have hBDm :=
    blockMap_preserves_posSemidef Ψ hΨ_cp Dm hDm
  have hDiff_herm :
    (blockMap ⇑Ψ Dp - blockMap ⇑Ψ Dm).IsHermitian :=
    hBDp.isHermitian.sub hBDm.isHermitian
  calc traceNorm (blockMap ⇑Ψ X)
      = traceNorm (blockMap ⇑Ψ Dp -
          blockMap ⇑Ψ Dm) := by rw [hLinSub]
    _ = traceNormHermitian _ hDiff_herm := by
          rw [traceNorm_hermitian_eq]
    _ ≤ ((blockMap ⇑Ψ Dp).trace +
          (blockMap ⇑Ψ Dm).trace).re :=
          traceNormHermitian_le_trace_posSemidef_sub
            _ _ _ hDiff_herm hBDp hBDm rfl
    _ ≤ (Dp.trace + Dm.trace).re := by
          rw [Complex.add_re, Complex.add_re]
          exact add_le_add
            (blockMap_tni_of_tni ⇑Ψ hΨ_contr Dp hDp)
            (blockMap_tni_of_tni ⇑Ψ hΨ_contr Dm hDm)
    _ = traceNormHermitian X hX := hNorm.symm
    _ = traceNorm X := by rw [traceNorm_hermitian_eq]

/-! ## Main theorem -/

/-- (id ⊗ T)(A†) = ((id ⊗ T)(A))† for CP linear T. -/
lemma mapIdTensor_preserves_conjTranspose
    {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (A : Op (k * n)) :
    mapIdTensor T A.conjTranspose =
      (mapIdTensor T A).conjTranspose := by
  -- mapIdTensor T is itself a CP linear map, so it preserves †
  haveI : NeZero (k * n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne n)⟩
  haveI : NeZero (k * m) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne m)⟩
  let Φ : Op (k * n) →ₗ[ℂ] Op (k * m) :=
    { toFun := mapIdTensor T
      map_add' := (mapIdTensor_isLinearMap T).1
      map_smul' := fun c x =>
        (mapIdTensor_isLinearMap T).2 c x }
  have hΦ_cp : IsCompletelyPositive ⇑Φ :=
    mapIdTensor_isCompletelyPositive T hT_cp
  exact cp_linear_preserves_conjTranspose Φ hΦ_cp A

/-- **Trace-norm contractivity of id ⊗ T (general operators).**

    For CP trace-non-increasing T and any A:
      ‖(id ⊗ T)(A)‖₁ ≤ ‖A‖₁

    Proof: form the self-adjoint dilation of A, apply the CP block map and Hermitian
    contractivity to that dilation, then use its exact doubled trace norm.
    See Watrous (2018) TQI, §3.3 for general background on trace-norm contraction. -/
theorem traceNorm_mapIdTensor_contractive {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (hT_contr : ∀ A : Op n, A.PosSemidef →
      (T A).trace.re ≤ A.trace.re)
    (A : Op (k * n)) :
    traceNorm (mapIdTensor T A) ≤ traceNorm A := by
  -- NeZero instances for product dimensions
  haveI hkn : NeZero (k * n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne n)⟩
  haveI hkm : NeZero (k * m) :=
    ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne m)⟩
  -- Wrap mapIdTensor T as a LinearMap
  let Ψ : Op (k * n) →ₗ[ℂ] Op (k * m) :=
    { toFun := mapIdTensor T
      map_add' := (mapIdTensor_isLinearMap T).1
      map_smul' := fun c x => by
        have := (mapIdTensor_isLinearMap T).2 c x
        exact this }
  -- mapIdTensor T preserves conjTranspose (from CP)
  have hΨ_conj : ∀ B : Op (k * n),
      Ψ B.conjTranspose = (Ψ B).conjTranspose :=
    fun B =>
      mapIdTensor_preserves_conjTranspose T hT_cp B
  -- blockMap(Ψ)(H_A) = H_{Ψ(A)}
  have h_block_dil :=
    Quantum.Metrics.blockMap_selfAdjointDilation_of_preserves_conj
      ⇑Ψ
      (by change mapIdTensor T 0 = 0
          ext p q; simp [mapIdTensor, Matrix.of_apply])
      hΨ_conj A
  -- H_A is Hermitian
  have h_herm := selfAdjointDilation_isHermitian A
  -- blockMap Ψ is CP+TNI → Hermitian contractive
  have hΨ_cp : IsCompletelyPositive ⇑Ψ :=
    mapIdTensor_isCompletelyPositive T hT_cp
  have hΨ_contr : ∀ P : Op (k * n), P.PosSemidef →
      (Ψ P).trace.re ≤ P.trace.re :=
    fun P hP => trace_mapIdTensor_psd_le T hT_contr P hP
  haveI : NeZero (k * n + (k * n)) := neZero_add_self _
  haveI : NeZero (k * m + (k * m)) := neZero_add_self _
  have h_contract :=
    traceNorm_blockMap_contractive_hermitian Ψ hΨ_cp
      hΨ_contr (selfAdjointDilation A) h_herm
  -- Rewrite and cancel factor 2
  change traceNorm (Ψ A) ≤ traceNorm A
  rw [show blockMap ⇑Ψ (selfAdjointDilation A) =
    selfAdjointDilation (Ψ A) from h_block_dil] at h_contract
  rw [traceNorm_selfAdjointDilation A] at h_contract
  rw [traceNorm_selfAdjointDilation (Ψ A)] at h_contract
  linarith

/-- Substate extraction plus `mapTensorId` contractivity. -/
lemma traceNorm_mapTensorId_substate_bound {nH nOut nK nR : ℕ}
    [NeZero nH] [NeZero nOut] [NeZero nK] [NeZero nR]
    (Δ : Op nH →ₗ[ℂ] Op nOut)
    (ρ : Op (nH * nK))
    (hρ_psd : ρ.PosSemidef)
    (Ψ : DensityOp (nH * nR))
    (hΨ_pure : Ψ.IsPure)
    (α : ℝ) (hα_pos : 0 < α)
    (h_dom : (((α : ℂ) • Ψ.partialTraceB.toOp) - partialTraceB ρ).PosSemidef) :
    traceNorm (mapTensorId Δ ρ) ≤ α * traceNorm (mapTensorId Δ Ψ.toOp) := by
  obtain ⟨T, hT_cp, hT_contr, hρ_eq⟩ :=
    substate_map_exists ρ hρ_psd Ψ.partialTraceB α hα_pos h_dom Ψ hΨ_pure rfl
  rw [hρ_eq, mapTensorId_smul_basic]
  rw [mapTensorId_compose_different_factors Δ T Ψ.toOp]
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  have h_contr := traceNorm_mapIdTensor_contractive T hT_cp hT_contr
    (mapTensorId Δ Ψ.toOp)
  have h_norm : ‖(↑α : ℂ)‖ = α := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hα_pos)]
  rw [h_norm]
  exact mul_le_mul_of_nonneg_left h_contr (le_of_lt hα_pos)

end Quantum.Channels
