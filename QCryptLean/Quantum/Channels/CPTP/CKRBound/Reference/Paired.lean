import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Basic
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.Quantum.Metrics.KitaevWatrous
import QCryptLean.InfoTheory.DeFinetti.Theorem.Interleaving

/-!
# CKR Paired Reference States — paired projector, marginal domination, per-operator bound

Paired reference-state infrastructure for the Christandl-Konig-Renner
postselection argument. This file defines the normalized paired symmetric
projector, its CKR marginal, pure CKR purification predicates, and the generic
paired-support CKR bounds.

## Main definitions
- `pairedDeFinettiState`: normalized paired symmetric projector on `(ℂ^d)^⊗n ⊗ (ℂ^d)^⊗n`
- `ckrDeFinettiState`: CKR Hilbert-Schmidt de Finetti state on `H^n`
- `IsCKRDeFinettiPurification`: pure state whose `H^n` marginal is `ckrDeFinettiState`

## Main statements
- `symmetricProjectorPaired_trace_eq`: paired symmetric-projector dimension formula
- `pairedDeFinettiState_partialTraceA_eq_ckrDeFinettiState`: both paired marginals agree
- `ckrDeFinettiState_toOp_transpose`: the CKR marginal is fixed by transpose
- `ckrDeFinetti_traceNorm_le_ckrTensorTraceNorm`: tracing out the reference
  contracts the CKR tensor trace norm to the CKR marginal trace norm
- `partial_trace_paired_symmetric_bound`: paired marginal domination
- `ckr_psd_bound_paired_support`: paired-support PSD CKR bound
- `Quantum.Channels.ckr_per_operator_bound_paired_core`: generic paired-reference per-operator CKR
bound
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The paired symmetric projector is a projector. -/
lemma symmetricProjectorPaired_is_projector' (d n : ℕ) [NeZero d] [NeZero n] :
    let P := symmetricProjectorPaired d n
    P * P = P ∧ Pᴴ = P := by
  intro P
  set e := interleavingEquiv d n
  set Q := symmetricProjector (d * d) n
  have h_reindex_eq : (Matrix.reindex e e) P = Q :=
    interleavingEquiv_conjugates_projector
  have ⟨hQ_idem, hQ_herm⟩ := symmetricProjector_is_projector (d * d) n
  have h_inj : Function.Injective
      ((Matrix.reindex e e : Op (d ^ n * d ^ n) ≃ Op ((d * d) ^ n))) :=
    Equiv.injective _
  have h_reindex_mul : (Matrix.reindex e e) (P * P) =
      (Matrix.reindex e e) P * (Matrix.reindex e e) P := by
    have := Matrix.reindexAlgEquiv_mul ℂ ℂ e P P
    simp only [Matrix.reindexAlgEquiv_apply] at this
    exact this
  have h_reindex_conj : (Matrix.reindex e e) Pᴴ = ((Matrix.reindex e e) P)ᴴ :=
    (Matrix.conjTranspose_reindex e e P).symm
  constructor
  · apply h_inj
    rw [h_reindex_mul, h_reindex_eq, hQ_idem]
  · apply h_inj
    rw [h_reindex_conj, h_reindex_eq, hQ_herm]

/-- The paired symmetric projector is Hermitian. -/
lemma symmetricProjectorPaired_isHermitian' (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjectorPaired d n).IsHermitian :=
  (symmetricProjectorPaired_is_projector' d n).2

/-- The trace of the paired symmetric projector is self-adjoint. -/
lemma symmetricProjectorPaired_trace_selfAdjoint (d n : ℕ) [NeZero d] [NeZero n] :
    starRingEnd ℂ (Matrix.trace (symmetricProjectorPaired d n)) =
      Matrix.trace (symmetricProjectorPaired d n) := by
  have hP := symmetricProjectorPaired_isHermitian' d n
  change star (Matrix.trace (symmetricProjectorPaired d n)) = _
  rw [← Matrix.trace_conjTranspose]
  exact congrArg Matrix.trace hP

/-- The paired symmetric projector is positive semidefinite. -/
lemma symmetricProjectorPaired_posSemidef (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjectorPaired d n).PosSemidef := by
  have ⟨hidp, hherm⟩ := symmetricProjectorPaired_is_projector' d n
  rw [show symmetricProjectorPaired d n =
    (symmetricProjectorPaired d n)ᴴ * symmetricProjectorPaired d n
    from by rw [hherm, hidp]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the paired symmetric projector has positive real part. -/
lemma symmetricProjectorPaired_trace_re_pos (d n : ℕ) [NeZero d] [NeZero n] :
    0 < ((symmetricProjectorPaired d n).trace).re := by
  have h_trace_eq : (symmetricProjectorPaired d n).trace =
      (Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n)
        (symmetricProjectorPaired d n)).trace := by
    have := Matrix.trace_map (Matrix.reindexAlgEquiv ℂ ℂ (interleavingEquiv d n))
      (symmetricProjectorPaired d n)
    simp only [Matrix.reindexAlgEquiv_apply] at this
    exact this.symm
  rw [h_trace_eq, interleavingEquiv_conjugates_projector]
  exact symmetricProjector_trace_re_pos (d * d) n

/-- The trace of the paired symmetric projector is nonzero. -/
lemma symmetricProjectorPaired_trace_ne_zero (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix.trace (symmetricProjectorPaired d n) ≠ 0 := by
  intro h
  have := symmetricProjectorPaired_trace_re_pos d n
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- The paired symmetric projector trace equals the operator-space symmetric-subspace dimension. -/
lemma symmetricProjectorPaired_trace_eq (d n : ℕ) [NeZero d] [NeZero n] :
    (symmetricProjectorPaired d n).trace =
      (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℂ) := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d))⟩
  simpa [pow_two] using symmetricProjectorPaired_trace (d := d) (n := n)

/-- The paired CKR polynomial dimension factor is positive. -/
lemma ckr_paired_dim_choose_pos (d n : ℕ) :
    0 < Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) :=
  Nat.choose_pos (Nat.le_add_left _ _)

private lemma symmetricProjectorPaired_normalized_isHermitian (d n : ℕ)
    [NeZero d] [NeZero n] :
    IsHermitian ((1 / (symmetricProjectorPaired d n).trace) • symmetricProjectorPaired d n) := by
  exact (IsSelfAdjoint.smul
    (IsSelfAdjoint.div (.one ℂ)
      (symmetricProjectorPaired_trace_selfAdjoint d n))
    (symmetricProjectorPaired_isHermitian' d n).isSelfAdjoint).isHermitian

private lemma symmetricProjectorPaired_normalized_posSemidef (d n : ℕ)
    [NeZero d] [NeZero n] :
    ∀ x : Fin (d ^ n * d ^ n) → ℂ,
      0 ≤
        (quadraticForm
          ((1 / (symmetricProjectorPaired d n).trace) • symmetricProjectorPaired d n) x).re := by
  intro x
  apply InfoTheory.DeFinetti.quadraticForm_re_nonneg_of_nonnegReal_smul _ _ _
    (symmetricProjectorPaired_posSemidef d n)
  · rw [one_div, Complex.inv_re]
    exact div_nonneg (symmetricProjectorPaired_trace_re_pos d n).le (Complex.normSq_nonneg _)
  · rw [one_div, Complex.inv_im,
      Complex.conj_eq_iff_im.mp (symmetricProjectorPaired_trace_selfAdjoint d n)]
    ring

private lemma symmetricProjectorPaired_normalized_trace_one (d n : ℕ)
    [NeZero d] [NeZero n] :
    Matrix.trace ((1 / (symmetricProjectorPaired d n).trace) • symmetricProjectorPaired d n) =
      1 := by
  rw [Matrix.trace_smul, smul_eq_mul, one_div]
  exact inv_mul_cancel₀ (symmetricProjectorPaired_trace_ne_zero d n)

/-- The normalized paired symmetric projector in the nonzero-round case. -/
noncomputable def pairedDeFinettiStateOfNeZero (d n : ℕ) [NeZero d] [NeZero n] :
    DensityOp (d ^ n * d ^ n) where
  toOp :=
    let P := symmetricProjectorPaired d n
    (1 / P.trace) • P
  isHermitian := symmetricProjectorPaired_normalized_isHermitian d n
  pos_semidef := symmetricProjectorPaired_normalized_posSemidef d n
  trace_one := symmetricProjectorPaired_normalized_trace_one d n

/-- The normalized paired symmetric projector on `(ℂ^d)^⊗n ⊗ (ℂ^d)^⊗n`. -/
noncomputable def pairedDeFinettiState (d n : ℕ) [NeZero d] :
    DensityOp (d ^ n * d ^ n) := by
  by_cases hn : n = 0
  · subst n
    simpa using
      (DensityOp.castDim (by simp : 1 = d ^ 0 * d ^ 0) DensityOp.trivial)
  · haveI : NeZero n := ⟨hn⟩
    exact pairedDeFinettiStateOfNeZero d n

/-- The total paired reference agrees with the normalized paired projector when `n ≠ 0`. -/
lemma pairedDeFinettiState_eq_of_neZero (d n : ℕ) [NeZero d] [NeZero n] :
    pairedDeFinettiState d n = pairedDeFinettiStateOfNeZero d n := by
  unfold pairedDeFinettiState
  simp [NeZero.ne n]

/-- CKR 2009 eq. (1): τ_{H^n} = ∫ σ^⊗n dμ_HS(σ), the Hilbert-Schmidt integral of product
    density operators on H. This equals the partial trace of `pairedDeFinettiState d n`
    over the K^n factor.

    This is **not** equal in general to `InfoTheory.DeFinetti.deFinettiState d n`,
    which is the Haar-pure integral ∫ |ψ⟩⟨ψ|^⊗n dHaar(ψ) / normalized P_sym on Sym^n(H).
    The two differ for n ≥ 2: at n = 2, d = 2, the Haar-pure state is I/6 + swap/6
    while the HS-density state is I/5 + swap/10. -/
noncomputable def ckrDeFinettiState (d n : ℕ) [NeZero d] :
    DensityOp (d ^ n) := (pairedDeFinettiState d n).partialTraceB

/-- The CKR marginal is the normalized partial trace of the paired symmetric projector. -/
lemma ckrDeFinettiState_toOp_eq_normalized_partialTraceB_symmetricProjectorPaired
    (d n : ℕ) [NeZero d] [NeZero n] :
    (ckrDeFinettiState d n).toOp =
      (1 / (symmetricProjectorPaired d n).trace) •
        partialTraceB (symmetricProjectorPaired d n) := by
  simp only [ckrDeFinettiState, DensityOp.partialTraceB, PosSemidefOp.partialTraceB]
  rw [pairedDeFinettiState_eq_of_neZero (d := d) (n := n)]
  exact partialTraceB_smul _ _

/-- The unnormalized paired CKR marginal is fixed by matrix transpose. -/
lemma partialTraceB_symmetricProjectorPaired_transpose
    (d n : ℕ) [NeZero d] [NeZero n] :
    (partialTraceB (symmetricProjectorPaired d n)).transpose =
      partialTraceB (symmetricProjectorPaired d n) := by
  rw [partialTraceB_symmetricProjectorPaired_eq_weighted_sum, Matrix.transpose_smul]
  congr 1
  exact sum_permRep_trace_smul_transpose d n

/-- The CKR de Finetti marginal is fixed by matrix transpose. -/
theorem ckrDeFinettiState_toOp_transpose
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    (ckrDeFinettiState d n).toOp.transpose = (ckrDeFinettiState d n).toOp := by
  rw [ckrDeFinettiState_toOp_eq_normalized_partialTraceB_symmetricProjectorPaired d n,
    Matrix.transpose_smul, partialTraceB_symmetricProjectorPaired_transpose d n]

/-- The two paired marginals of the symmetric projector agree: tracing out either
copy of `Sym^n` gives the same reference-register operator (the projector is a
sum of self-tensors `R_σ ⊗ R_σ`). -/
lemma partialTraceA_symmetricProjectorPaired_eq_partialTraceB
    (d n : ℕ) [NeZero d] [NeZero n] :
    partialTraceA (symmetricProjectorPaired d n) =
      partialTraceB (symmetricProjectorPaired d n) := by
  simp only [symmetricProjectorPaired, partialTraceA_smul, partialTraceB_smul,
    partialTraceA_finset_sum, partialTraceB_finset_sum, partialTraceA_tensor_self_eq,
    partialTraceB_tensor_self_eq]

/-- The normalized paired CKR reference has the CKR marginal on either tensor factor. -/
lemma pairedDeFinettiState_partialTraceA_eq_ckrDeFinettiState
    (d n : ℕ) [NeZero d] [NeZero n] :
    (pairedDeFinettiState d n).partialTraceA = ckrDeFinettiState d n := by
  apply DensityOp.ext
  change partialTraceA (pairedDeFinettiState d n).toOp =
    partialTraceB (pairedDeFinettiState d n).toOp
  rw [pairedDeFinettiState_eq_of_neZero d n]
  change partialTraceA ((1 / (symmetricProjectorPaired d n).trace) •
      symmetricProjectorPaired d n) =
    partialTraceB ((1 / (symmetricProjectorPaired d n).trace) •
      symmetricProjectorPaired d n)
  rw [partialTraceA_smul, partialTraceB_smul,
    partialTraceA_symmetricProjectorPaired_eq_partialTraceB]

/-- The unnormalized paired CKR marginal is invariant under permutation conjugation. -/
lemma partialTraceB_symmetricProjectorPaired_perm_conj_eq
    (d n : ℕ) [NeZero d] [NeZero n] (π : Equiv.Perm (Fin n)) :
    permutationRepresentation d n π *
      partialTraceB (symmetricProjectorPaired d n) *
      (permutationRepresentation d n π)† =
    partialTraceB (symmetricProjectorPaired d n) := by
  simp only [symmetricProjectorPaired, partialTraceB_smul, partialTraceB_finset_sum,
    partialTraceB_tensor_self_eq]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact sum_permRep_trace_smul_conj_eq d n π

/-- The CKR de Finetti state is invariant under tensor-factor permutations. -/
lemma ckrDeFinettiState_isPermutationInvariant_gen (d n : ℕ) [NeZero d] [NeZero n] :
    IsPermutationInvariant (ckrDeFinettiState d n) := by
  intro π
  change permutationRepresentation d n π * (ckrDeFinettiState d n).toOp *
      (permutationRepresentation d n π)ᴴ = (ckrDeFinettiState d n).toOp
  rw [ckrDeFinettiState_toOp_eq_normalized_partialTraceB_symmetricProjectorPaired d n,
    mul_smul_comm, smul_mul_assoc]
  congr 1
  exact partialTraceB_symmetricProjectorPaired_perm_conj_eq d n π

/-- A pure state whose `H^n` marginal is the CKR de Finetti state. -/
structure IsCKRDeFinettiPurification {d n dimR : ℕ} [NeZero d]
    (τ : DensityOp ((d ^ n) * dimR)) : Prop where
  isPure : τ.IsPure
  marginal : τ.partialTraceB = ckrDeFinettiState d n

/-- Tracing out the CKR reference after applying `Δ ⊗ id` contracts trace norm,
and the CKR purification marginal identifies the result with `Δ` on the
de Finetti source. -/
lemma ckrDeFinetti_traceNorm_le_ckrTensorTraceNorm
    {d n dimOut dimR : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ) :
    Quantum.Metrics.traceNorm (Δ (ckrDeFinettiState d n).toOp) ≤
      ckrTensorTraceNorm Δ τ := by
  have hmarg : partialTraceB τ.toOp = (ckrDeFinettiState d n).toOp :=
    congrArg (fun ρ => ρ.toOp) hτ.marginal
  have hpartial :
      partialTraceB (mapTensorId Δ τ.toOp) = Δ (ckrDeFinettiState d n).toOp := by
    rw [partialTraceB_mapTensorId, hmarg]
  have hcontract :=
    Quantum.Metrics.traceNorm_cptp_contractive_general
      (partialTraceB : Op (dimOut * dimR) → Op dimOut)
      Quantum.Channels.isCPTP_partialTraceB
      (mapTensorId Δ τ.toOp)
  simpa [ckrTensorTraceNorm, hpartial] using hcontract

/-- The rank of the paired symmetric projector equals the paired symmetric-subspace
dimension `C(n + d²-1, d²-1)`.  This is the dimension of the symmetric subspace `V`
(the support of any permutation-invariant paired state); it is the register whose
log charges the smooth-min-entropy register-extension penalty in Nahar, Tupkary, Zhao, Lütkenhaus,
Tan App. B (B17),
identified there with the `[47, Eq. 8]` dimension bound. -/
lemma symmetricProjectorPaired_rank_eq_polyDim
    (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix.rank (symmetricProjectorPaired d n) =
      Nat.choose (n + d ^ 2 - 1) (d ^ 2 - 1) := by
  have ⟨hP_idem, hP_herm⟩ := symmetricProjectorPaired_is_projector' d n
  have h_trace_re_eq_rank :=
    Math.SpectralTheory.hermitian_idempotent_trace_re_eq_rank
      (symmetricProjectorPaired d n) hP_herm hP_idem
  have h_trace_eq := symmetricProjectorPaired_trace_eq d n
  have h_choose_eq : Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) =
      Nat.choose (n + d ^ 2 - 1) (d ^ 2 - 1) := by
    congr 1
    have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow 2 d (NeZero.pos d)
    exact (Nat.add_sub_assoc hd2 n).symm
  have h_re : (symmetricProjectorPaired d n).trace.re =
      (Nat.choose (n + d ^ 2 - 1) (d ^ 2 - 1) : ℝ) := by
    rw [h_trace_eq, ← h_choose_eq]
    simp [Complex.natCast_re]
  exact_mod_cast h_trace_re_eq_rank.symm.trans h_re

/-- The paired de Finetti state's rank is bounded by the paired symmetric-subspace
dimension `C(n + d²-1, d²-1)`. -/
lemma pairedDeFinettiState_rank_le_polyDim
    (d n : ℕ) [NeZero d] [NeZero n] :
    Matrix.rank (pairedDeFinettiState d n).toOp ≤
      Nat.choose (n + d ^ 2 - 1) (d ^ 2 - 1) := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  haveI : NeZero (d ^ n * d ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  set P := symmetricProjectorPaired d n with hP_def
  have h_toOp : (pairedDeFinettiState d n).toOp = (1 / P.trace) • P := by
    rw [pairedDeFinettiState_eq_of_neZero]; rfl
  rw [h_toOp]
  have hc : 1 / P.trace ≠ 0 :=
    div_ne_zero one_ne_zero (symmetricProjectorPaired_trace_ne_zero d n)
  rw [Math.SpectralTheory.rank_smul_of_ne_zero _ _ hc]
  exact (symmetricProjectorPaired_rank_eq_polyDim d n).le

/-- The CKR de Finetti state has a pure purification with reference dimension `d^n`. -/
lemma ckrDeFinetti_dn_purification_exists
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    ∃ (τ : DensityOp ((d ^ n) * (d ^ n))),
      IsCKRDeFinettiPurification τ :=
  ⟨purificationDensityOp (ckrDeFinettiState d n),
   ⟨purificationDensityOp_isPure _, purificationDensityOp_partialTraceB _⟩⟩

/-- Signal-side permutation conjugation preserves the CKR de Finetti marginal. -/
lemma ckrDeFinetti_signalPermConj_partialTraceB {d n dimR : ℕ}
    [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (σ : Equiv.Perm (Fin n)) :
    partialTraceB
      (Op.tensor (permutationRepresentation d n σ) (1 : Op dimR) * τ.toOp *
        (Op.tensor (permutationRepresentation d n σ) (1 : Op dimR))†) =
    (ckrDeFinettiState d n).toOp := by
  rw [Op.tensor_conjTranspose, conjTranspose_one, partialTraceB_sandwich_tensor_one]
  have hmarg : partialTraceB τ.toOp = (ckrDeFinettiState d n).toOp :=
    congrArg (fun σ => σ.toOp) hτ.marginal
  rw [hmarg]
  exact ckrDeFinettiState_isPermutationInvariant_gen d n σ

/-- There is a pure CKR de Finetti purification invariant under paired permutations. -/
lemma ckrDeFinetti_dn_equivariant_purification_exists
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    ∃ (τ : DensityOp ((d ^ n) * (d ^ n))),
      IsCKRDeFinettiPurification τ ∧ IsPairedPermInvariant τ := by
  obtain ⟨τ, hτ_pure, hτ_paired, _hτ_support, hτ_marginal⟩ :=
    InfoTheory.DeFinetti.symmetric_purification_with_pure
      (ckrDeFinettiState d n) (ckrDeFinettiState_isPermutationInvariant_gen d n)
  refine ⟨τ, ⟨hτ_pure, ?_⟩, hτ_paired⟩
  apply DensityOp.ext
  change partialTraceB τ.toOp = (ckrDeFinettiState d n).toOp
  exact hτ_marginal

/-- A paired-permutation-invariant CKR de Finetti purification can be chosen at
reference dimension `d^n`. -/
lemma ckrDeFinetti_dn_purification_can_be_pairedPermInvariant
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (_hExists : ∃ τ : DensityOp ((d ^ n) * (d ^ n)),
        IsCKRDeFinettiPurification τ) :
    ∃ (τ : DensityOp ((d ^ n) * (d ^ n))),
      IsCKRDeFinettiPurification τ ∧ IsPairedPermInvariant τ :=
  ckrDeFinetti_dn_equivariant_purification_exists d n

/-- Scaling the CKR marginal by the paired symmetric-subspace dimension gives
the partial trace of the unnormalized paired symmetric projector. -/
lemma choose_smul_ckrDeFinettiState_eq_partialTraceB_symmetricProjectorPaired
    (d n : ℕ) [NeZero d] [NeZero n] :
    (↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) •
      (ckrDeFinettiState d n).toOp =
    partialTraceB (symmetricProjectorPaired d n) := by
  rw [ckrDeFinettiState_toOp_eq_normalized_partialTraceB_symmetricProjectorPaired d n,
    smul_smul]
  have h_trace : (symmetricProjectorPaired d n).trace =
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) := by
    exact symmetricProjectorPaired_trace_eq d n
  rw [h_trace]
  have hC_ne : (↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (ckr_paired_dim_choose_pos d n).ne'
  rw [mul_one_div_cancel hC_ne, one_smul]

/-- The paired symmetric projector dominates every subnormalized PSD operator
supported in the paired symmetric subspace. -/
lemma symmetricProjectorPaired_sub_psd_of_support
    (d n : ℕ) [NeZero d] [NeZero n]
    (ρ' : Op (d ^ n * d ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (hρ'_trace : ρ'.trace.re ≤ 1)
    (hρ'_support : symmetricProjectorPaired d n * ρ' * symmetricProjectorPaired d n = ρ') :
    (symmetricProjectorPaired d n - ρ').PosSemidef := by
  have ⟨hP_idem, hP_herm⟩ := symmetricProjectorPaired_is_projector' d n
  have ⟨hPρ', _⟩ :=
    projector_sandwich_oneSided hP_idem hP_herm hρ'_psd hρ'_support
  exact projector_sub_psd_of_support (symmetricProjectorPaired d n) ρ'
    hP_idem hP_herm hρ'_psd hρ'_trace hPρ'

/-- The paired-reference marginal domination used by the generic CKR core.

    Only the marginal equality is needed; purity is used only in the subsequent
    `ckr_psd_bound_paired_support` which needs substate extraction. -/
lemma partial_trace_paired_symmetric_bound {d n dimR : ℕ}
    [NeZero d] [NeZero n]
    (ρ' : Op (d ^ n * d ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (hρ'_trace : ρ'.trace.re ≤ 1)
    (hρ'_support : symmetricProjectorPaired d n * ρ' * symmetricProjectorPaired d n = ρ')
    (τ : DensityOp ((d ^ n) * dimR))
    (hmarginal : τ.partialTraceB = ckrDeFinettiState d n) :
    (((↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) • τ.partialTraceB.toOp) -
      partialTraceB ρ').PosSemidef := by
  have h_sub_psd :=
    symmetricProjectorPaired_sub_psd_of_support d n ρ'
      hρ'_psd hρ'_trace hρ'_support
  have h_ptrace_psd :=
    partialTraceB_psd_mono (symmetricProjectorPaired d n) ρ' h_sub_psd
  rw [show τ.partialTraceB.toOp = (ckrDeFinettiState d n).toOp from
      congr_arg (·.toOp) hmarginal,
    choose_smul_ckrDeFinettiState_eq_partialTraceB_symmetricProjectorPaired d n]
  exact h_ptrace_psd

/-- The generic paired-reference PSD CKR bound under paired support. -/
lemma ckr_psd_bound_paired_support {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (ρ' : Op (d ^ n * d ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (hρ'_trace : ρ'.trace.re ≤ 1)
    (hρ'_support : symmetricProjectorPaired d n * ρ' * symmetricProjectorPaired d n = ρ')
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ) :
    traceNorm (mapTensorId Δ ρ') ≤
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) * traceNorm (mapTensorId Δ τ.toOp) := by
  have h_dom :=
    partial_trace_paired_symmetric_bound ρ' hρ'_psd hρ'_trace hρ'_support τ hτ.marginal
  have hC_nat_pos : 0 < Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) :=
    ckr_paired_dim_choose_pos d n
  have hC_pos : (0 : ℝ) < ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) :=
    Nat.cast_pos.mpr hC_nat_pos
  exact traceNorm_mapTensorId_substate_bound Δ ρ' hρ'_psd τ hτ.isPure
    (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℝ) hC_pos h_dom

private lemma ckrDeFinettiState_zero_toOp (d : ℕ) [NeZero d] :
    (ckrDeFinettiState d 0).toOp = (1 : Op (d ^ 0)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [ckrDeFinettiState, pairedDeFinettiState, DensityOp.castDim, DensityOp.trivial,
    DensityOp.partialTraceB, PosSemidefOp.partialTraceB, partialTraceB]

private lemma ckr_psd_bound_paired_core_zero {d dimOut dimR : ℕ}
    [NeZero d] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ 0) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ 0) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (ρ : Op (d ^ 0 * d ^ 0))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1) :
    traceNorm (mapTensorId Δ ρ) ≤ traceNorm (mapTensorId Δ τ.toOp) := by
  have hτ_ptrace : τ.partialTraceB.toOp = (1 : Op (d ^ 0)) := by
    have hτ_toOp := congrArg (fun σ => σ.toOp) hτ.marginal
    simpa [ckrDeFinettiState_zero_toOp d] using hτ_toOp
  have h_dom : (((1 : ℝ) : ℂ) • τ.partialTraceB.toOp - partialTraceB ρ).PosSemidef := by
    rw [Complex.ofReal_one, one_smul, hτ_ptrace, partialTraceB_dim1_op]
    simpa using Quantum.Operators.psd_le_one_of_trace_le_one ρ hρ_psd hρ_trace
  simpa using
    traceNorm_mapTensorId_substate_bound Δ ρ hρ_psd τ hτ.isPure 1 one_pos h_dom

private lemma trace_re_pos_of_posSemidef_of_ne_zero {d : ℕ} {A : Op d}
    (hA : A.PosSemidef) (hA_ne : A ≠ 0) :
    0 < A.trace.re := by
  rcases hA.trace_nonneg with ⟨h_re, h_im⟩
  rcases lt_or_eq_of_le h_re with h_re_pos | h_re_zero
  · exact h_re_pos
  · exfalso
    exact hA_ne (hA.trace_eq_zero_iff.mp (Complex.ext h_re_zero.symm h_im.symm))

private lemma paired_ckr_bound_nonneg {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR)) :
    0 ≤ ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
      traceNorm (mapTensorId Δ τ.toOp) :=
  mul_nonneg (Nat.cast_nonneg _) (Quantum.Metrics.traceNorm_nonneg _)

private lemma ckr_psd_bound_paired_square_ancilla {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (ρ : Op (d ^ n * d ^ n))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1) :
    traceNorm (mapTensorId Δ ρ) ≤
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
        traceNorm (mapTensorId Δ τ.toOp) := by
  by_cases hρ_zero : ρ = 0
  · rw [hρ_zero, mapTensorId_zero, traceNorm_zero]
    exact paired_ckr_bound_nonneg Δ τ
  · haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
    have hρ_trace_pos : 0 < ρ.trace.re :=
      trace_re_pos_of_posSemidef_of_ne_zero hρ_psd hρ_zero
    obtain ⟨σ_norm, hσ_norm_eq⟩ :=
      densityOp_of_psd_pos_trace (partialTraceB ρ)
        (partialTraceB_posSemidef_mathlib _ hρ_psd)
        (by rw [trace_partialTraceB]; exact hρ_trace_pos)
    rw [trace_partialTraceB] at hσ_norm_eq
    set σ_sym := Quantum.Symmetry.symmetrize σ_norm
    have hσ_sym_inv : IsPermutationInvariant σ_sym :=
      symmetrize_isPermutationInvariant σ_norm
    obtain ⟨Ψ, hΨ_pure, _hΨ_paired_inv, hΨ_support, hΨ_marginal⟩ :=
      symmetric_purification_with_pure σ_sym hσ_sym_inv
    have h_reduce : traceNorm (mapTensorId Δ ρ) ≤ traceNorm (mapTensorId Δ Ψ.toOp) := by
      exact block_diagonal_purification_bound Δ hΔ_cov ρ hρ_psd hρ_trace hρ_zero
        σ_norm hσ_norm_eq Ψ hΨ_pure (by simpa [σ_sym] using hΨ_marginal)
    have h_pair := ckr_psd_bound_paired_support Δ Ψ.toOp
      (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp)
      (by rw [Ψ.trace_one, Complex.one_re])
      hΨ_support τ hτ
    exact le_trans h_reduce h_pair

private lemma ckr_per_operator_bound_paired_core_zero {d dimOut dimR : ℕ}
    [NeZero d] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ 0) →ₗ[ℂ] Op dimOut)
    (X : Op (d ^ 0 * d ^ 0))
    (hX_norm : traceNorm X ≤ 1)
    (τ : DensityOp ((d ^ 0) * dimR))
    (hΔ_conj : ∀ M : Op (d ^ 0), Δ M.conjTranspose = (Δ M).conjTranspose)
    (hτ : IsCKRDeFinettiPurification τ) :
    traceNorm (mapTensorId Δ X) ≤ traceNorm (mapTensorId Δ τ.toOp) := by
  have hB : 0 ≤ traceNorm (mapTensorId Δ τ.toOp) := Quantum.Metrics.traceNorm_nonneg _
  have h_psd :
      ∀ (ρ : Op (d ^ 0 * d ^ 0)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
        traceNorm (mapTensorId Δ ρ) ≤ traceNorm (mapTensorId Δ τ.toOp) := by
    intro ρ hρ_psd hρ_trace
    exact ckr_psd_bound_paired_core_zero Δ τ hτ ρ hρ_psd hρ_trace
  simpa using
    Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction
      Δ (traceNorm (mapTensorId Δ τ.toOp)) hB hΔ_conj h_psd X hX_norm

private lemma ckr_per_operator_bound_paired_core_of_neZero {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (X : Op (d ^ n * (d ^ n)))
    (hX_norm : traceNorm X ≤ 1)
    (τ : DensityOp ((d ^ n) * dimR))
    (hΔ_conj : ∀ M : Op (d ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (hτ : IsCKRDeFinettiPurification τ) :
    traceNorm (mapTensorId Δ X) ≤
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
        traceNorm (mapTensorId Δ τ.toOp) := by
  have hB :
      0 ≤ ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
        traceNorm (mapTensorId Δ τ.toOp) :=
    paired_ckr_bound_nonneg Δ τ
  have h_psd :
      ∀ (ρ : Op ((d ^ n) * (d ^ n))), ρ.PosSemidef → ρ.trace.re ≤ 1 →
        traceNorm (mapTensorId Δ ρ) ≤
          ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
            traceNorm (mapTensorId Δ τ.toOp) := by
    intro ρ hρ_psd hρ_trace
    exact ckr_psd_bound_paired_square_ancilla Δ hΔ_cov τ hτ ρ hρ_psd hρ_trace
  exact Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction
    Δ _ hB hΔ_conj h_psd X hX_norm

/-- Generic paired-reference CKR per-operator bound from permutation covariance
and a CKR de Finetti purification. -/
theorem ckr_per_operator_bound_paired_core {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (X : Op (d ^ n * (d ^ n)))
    (hX_norm : traceNorm X ≤ 1)
    (τ : DensityOp ((d ^ n) * dimR))
    (hΔ_conj : ∀ M : Op (d ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (hτ : IsCKRDeFinettiPurification τ) :
    traceNorm (mapTensorId Δ X) ≤
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) *
        traceNorm (mapTensorId Δ τ.toOp) := by
  by_cases hn : n = 0
  · subst n
    simpa using ckr_per_operator_bound_paired_core_zero Δ X hX_norm τ hΔ_conj hτ
  · haveI : NeZero n := ⟨hn⟩
    exact ckr_per_operator_bound_paired_core_of_neZero Δ X hX_norm τ hΔ_conj hΔ_cov hτ

end Quantum.Channels

end
