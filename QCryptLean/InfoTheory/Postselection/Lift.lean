import QCryptLean.Math.Combinatorics.FinProductEquiv
import QCryptLean.InfoTheory.Postselection.Framework
import QCryptLean.InfoTheory.Postselection.FixedMarginalReduction
import QCryptLean.InfoTheory.Postselection.GroupTwirl
import QCryptLean.InfoTheory.Postselection.GroupSymmetricDeFinetti
import QCryptLean.InfoTheory.Postselection.SymmetrizeIIDInvariance
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Postselection from IID security

`HasIIDSecurityProof` records acceptance-test and privacy-amplification data. Reference secrecy
follows from an extended mixture entropy floor, a hashing bound, and the accepted-state
decomposition. The channel postselection bound then transfers reference secrecy to coherent
attacks.
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open Quantum.Symmetry
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

-- Frobenius normed structure on matrices, needed to integrate operator-valued functions
-- (same local instances as `InfoTheory.DeFinetti.IntegralPurification`).
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-! ## Reindexing helpers -/

/-- Numeric dimension identity `(d_A d_B)^n · (d_A d_B)^n = (d_A^n d_B^n) · (d_A^n d_B^n)`,
    used to view the mixture purification `τ_R` (built on `(d_A d_B)^n`) on the input register
    `AⁿBⁿ = d_A^n d_B^n` of the protocol difference map. -/
theorem referenceDimEq (dA dB n : ℕ) :
    (dA * dB) ^ n * (dA * dB) ^ n = (dA ^ n * dB ^ n) * (dA ^ n * dB ^ n) := by
  rw [mul_pow]

/-- The `finProdFinEquiv`-compatible tensor product of two index equivalences `e₁, e₂`: reindexing
    an `(b₁·b₂)`-register along `finProdCongr e₁ e₂` is the same as reindexing the `b₁`-factor
    along `e₁` and the `b₂`-factor along `e₂` independently. -/
def finProdCongr {b₁ a₁ b₂ a₂ : ℕ} (e₁ : Fin b₁ ≃ Fin a₁) (e₂ : Fin b₂ ≃ Fin a₂) :
    Fin (b₁ * b₂) ≃ Fin (a₁ * a₂) :=
  finProdFinEquiv.symm.trans ((e₁.prodCongr e₂).trans finProdFinEquiv)

@[simp] lemma finProdCongr_apply {b₁ a₁ b₂ a₂ : ℕ} (e₁ : Fin b₁ ≃ Fin a₁) (e₂ : Fin b₂ ≃ Fin a₂)
    (i : Fin b₁) (s : Fin b₂) :
    finProdCongr e₁ e₂ (finProdFinEquiv (i, s)) = finProdFinEquiv (e₁ i, e₂ s) := by
  simp [finProdCongr]

@[simp] lemma finProdCongr_symm_apply {b₁ a₁ b₂ a₂ : ℕ} (e₁ : Fin b₁ ≃ Fin a₁)
    (e₂ : Fin b₂ ≃ Fin a₂) (i : Fin a₁) (s : Fin a₂) :
    (finProdCongr e₁ e₂).symm (finProdFinEquiv (i, s)) =
      finProdFinEquiv (e₁.symm i, e₂.symm s) := by
  simp [finProdCongr]

/-- `mapTensorId` naturality: tensor-extending a *reindexing* linear equivalence is exactly
    reindexing the ancilla-extended register along the ancilla-extended equivalence
    `Equiv.finProdCongrExt`. -/
theorem mapTensorId_reindexLinearEquiv {b a k : ℕ} [NeZero b] [NeZero a] [NeZero k]
    (e : Fin b ≃ Fin a) (Y : Op (b * k)) :
    mapTensorId (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap Y =
      Matrix.reindex (Equiv.finProdCongrExt e k) (Equiv.finProdCongrExt e k) Y := by
  ext p q
  rw [mapTensorId_apply_eq_apply_block, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [LinearEquiv.coe_toLinearMap, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.of_apply]
  simp [Equiv.finProdCongrExt, Equiv.prodCongr_symm, Equiv.prodCongr_apply]

/-- Tracing out the untouched ancilla commutes with reindexing the system register
along `Equiv.finProdCongrExt`. -/
theorem partialTraceB_reindex_finProdCongrExt {b a k : ℕ} (e : Fin b ≃ Fin a) (Y : Op (b * k)) :
    partialTraceB (Matrix.reindex (Equiv.finProdCongrExt e k) (Equiv.finProdCongrExt e k) Y) =
      Matrix.reindex e e (partialTraceB Y) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.finProdCongrExt_symm_apply]

/-- The difference map viewed on the round-grouped register `(AB)^{⊗n}` of dimension `(d_A d_B)^n`,
    obtained from `P.differenceMap l'` (typed on the block register `AⁿBⁿ = d_A^n d_B^n`) by
    reindexing along the **genuine round-regrouping equivalence** `roundGroupEquiv` (the digit
    regrouping `(x₀,b₀,…,x_{n-1},b_{n-1}) ↦ ((x₀,…,x_{n-1}),(b₀,…,b_{n-1}))`, *not* the bare
    numeric identity `finCongr (mul_pow …)` — the two differ (they disagree already at
    `dA = dB = n = 2`), and only the structural `roundGroupEquiv` matches the convention used by
    `roundwiseAliceMarginal` / the fixed-marginal de Finetti reduction. This is the form on which
    Nahar et al.'s permutation-invariance (Def. 5) acts. -/
def PMQKDProtocol.roundDifferenceMap (P : PMQKDProtocol dA dB n) (l' : ℕ) :
    Op ((dA * dB) ^ n) →ₗ[ℂ] Op (P.keyDim * P.annDim) :=
  (P.differenceMap l').comp
    (Matrix.reindexLinearEquiv ℂ ℂ (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)).toLinearMap

/-- The round-grouped difference map is supported on the accepted branch. -/
lemma PMQKDProtocol.acceptProj_comp_roundDifferenceMap
    (P : PMQKDProtocol dA dB n) (l' : ℕ) :
    P.acceptProj.comp (P.roundDifferenceMap l') = P.roundDifferenceMap l' := by
  rw [PMQKDProtocol.roundDifferenceMap, ← LinearMap.comp_assoc,
    P.acceptProj_comp_differenceMap]

/-- The round-grouped difference is the difference of the two reindexed variants. -/
lemma PMQKDProtocol.roundDifferenceMap_eq_sub (P : PMQKDProtocol dA dB n) (l' : ℕ) :
    P.roundDifferenceMap l' =
      (P.variantReal l').comp (Matrix.reindexLinearEquiv ℂ ℂ
        (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)).toLinearMap -
      (P.variantIdeal l').comp (Matrix.reindexLinearEquiv ℂ ℂ
        (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)).toLinearMap := by
  exact LinearMap.sub_comp _ _ _

/-- Tensoring the round difference factors through the accepted real-minus-ideal output. -/
lemma PMQKDProtocol.mapTensorId_roundDifferenceMap_eq_acceptProj_sub
    (P : PMQKDProtocol dA dB n) (l' : ℕ) (k : ℕ) [NeZero k]
    (X : Op ((dA * dB) ^ n * k)) :
    haveI := P.keyDim_neZero
    haveI := P.annDim_neZero
    mapTensorId (k := k) (P.roundDifferenceMap l') X =
      mapTensorId (k := k) P.acceptProj
        (mapTensorId (k := k) (P.variantReal l')
          (Matrix.reindex (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) k)
            (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) k) X) -
        mapTensorId (k := k) (P.variantIdeal l')
          (Matrix.reindex (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) k)
            (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) k) X)) := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  conv_lhs => rw [← P.acceptProj_comp_roundDifferenceMap l']
  rw [← mapTensorId_comp, PMQKDProtocol.roundDifferenceMap_eq_sub,
    mapTensorId_linearMap_sub, mapTensorId_sub,
    ← mapTensorId_comp, ← mapTensorId_comp]
  simp only [mapTensorId_reindexLinearEquiv, mapTensorId_sub]

/-- **The round-difference map is trace-annihilating** (Nahar et al. main.tex:1397–:1405 (unlabeled;
the leftover-hashing hash-length reduction)/(B19): the real and ideal
    hash-length variants are both trace-preserving channels on the same round-grouped input
    register, so their difference annihilates the trace of *every* operator — no normalization of
    the input is required). This is the "`tr X = 0`" half of the raw-key-measurement bridge. -/
theorem PMQKDProtocol.mapTensorId_roundDifferenceMap_trace_zero
    (P : PMQKDProtocol dA dB n) (l' : ℕ) (Y : Op ((dA * dB) ^ n * (dA * dB) ^ n)) :
    haveI := P.keyDim_neZero
    haveI := P.annDim_neZero
    haveI : NeZero (P.keyDim * P.annDim) :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
    haveI : NeZero ((dA * dB) ^ n) :=
      ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
    (mapTensorId (k := (dA * dB) ^ n) (P.roundDifferenceMap l') Y).trace = 0 := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI : NeZero (dA ^ n * dB ^ n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n))⟩
  let e := roundGroupEquiv dA dB n
  rw [P.roundDifferenceMap_eq_sub, mapTensorId_linearMap_sub, Matrix.trace_sub]
  have hR : IsTracePreserving
      (⇑((P.variantReal l').comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap)) := by
    intro A
    change (P.variantReal l' ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap A)).trace = A.trace
    rw [LinearEquiv.coe_toLinearMap, Matrix.reindexLinearEquiv_apply,
      (P.variantReal_isCPTP l').2.2 (Matrix.reindex e e A)]
    exact Matrix.trace_reindex_self e A
  have hI : IsTracePreserving
      (⇑((P.variantIdeal l').comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap)) := by
    intro A
    change (P.variantIdeal l' ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap A)).trace = A.trace
    rw [LinearEquiv.coe_toLinearMap, Matrix.reindexLinearEquiv_apply,
      (P.variantIdeal_isCPTP l').2.2 (Matrix.reindex e e A)]
    exact Matrix.trace_reindex_self e A
  have hRtr := mapTensorId_isTracePreserving _ hR Y
  have hItr := mapTensorId_isTracePreserving _ hI Y
  rw [hRtr, hItr, sub_self]

/-- Real and ideal accepted outputs have equal trace, also in the presence of a reference. -/
lemma PMQKDProtocol.re_trace_acceptIdeal_eq_re_trace_acceptReal
    (P : PMQKDProtocol dA dB n) (l' : ℕ) (Y : Op ((dA * dB) ^ n * (dA * dB) ^ n)) :
    haveI := P.keyDim_neZero
    haveI := P.annDim_neZero
    let Y' := Matrix.reindex
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n)) Y
    (mapTensorId P.acceptProj (mapTensorId (P.variantIdeal l') Y')).trace.re =
      (mapTensorId P.acceptProj (mapTensorId (P.variantReal l') Y')).trace.re := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  have h := P.mapTensorId_roundDifferenceMap_trace_zero l' Y
  rw [P.mapTensorId_roundDifferenceMap_eq_acceptProj_sub, mapTensorId_sub,
    Matrix.trace_sub] at h
  exact (congrArg Complex.re (sub_eq_zero.mp h)).symm

/-- The difference map preserves the conjugate transpose: `Δ(M†) = Δ(M)†`. Both `variantReal l'`
    and `variantIdeal l'` are CPTP, so each preserves the adjoint
    (`cptp_preserves_conjTranspose`), and the identity is linear in the difference. -/
theorem PMQKDProtocol.differenceMap_conjTranspose (P : PMQKDProtocol dA dB n) (l' : ℕ)
    (M : Op (dA ^ n * dB ^ n)) :
    haveI : NeZero (dA ^ n * dB ^ n) :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n))⟩
    haveI := P.keyDim_neZero
    haveI := P.annDim_neZero
    haveI : NeZero (P.keyDim * P.annDim) :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
    P.differenceMap l' Mᴴ = (P.differenceMap l' M)ᴴ := by
  haveI : NeZero (dA ^ n * dB ^ n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n))⟩
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  simp only [PMQKDProtocol.differenceMap, LinearMap.sub_apply, Matrix.conjTranspose_sub]
  rw [cptp_preserves_conjTranspose _ (P.variantReal_isCPTP l') M,
    cptp_preserves_conjTranspose _ (P.variantIdeal_isCPTP l') M]

/-- The round-regrouped difference map preserves the conjugate transpose: composing
    `differenceMap_conjTranspose` with the reindex-conjTranspose commutation
    (`Matrix.conjTranspose_reindex`, same equivalence on both sides). -/
theorem PMQKDProtocol.roundDifferenceMap_conjTranspose (P : PMQKDProtocol dA dB n) (l' : ℕ)
    (M : Op ((dA * dB) ^ n)) :
    haveI := P.keyDim_neZero
    haveI := P.annDim_neZero
    haveI : NeZero (P.keyDim * P.annDim) :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
    P.roundDifferenceMap l' Mᴴ = (P.roundDifferenceMap l' M)ᴴ := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  exact P.differenceMap_conjTranspose l' (Matrix.reindex (roundGroupEquiv dA dB n)
    (roundGroupEquiv dA dB n) M)

/-! ## The IID secrecy parameter and the de Finetti reference secrecy (main.tex:487–:490 (unlabeled;
the conclusion of `\label{thm:maintheorem}` :481–:491)) -/

/-- **Nahar et al. Theorem 3 / Corollary 3.1 secrecy parameter** `ε_PA + 2ε̄ + 2√(2ε_AT)`
    (arXiv:2403.11851, main.tex:487–:490 (unlabeled; the conclusion of `\label{thm:maintheorem}`
    :481–:491) / line 568). -/
def coherentIIDSecrecy (εAT εPA εbar : ℝ) : ℝ :=
  εPA + 2 * εbar + 2 * Real.sqrt (2 * εAT)

/-- The protocol's real-minus-ideal output on the de Finetti reference purification. -/
def PMQKDProtocol.referenceDifference (P : PMQKDProtocol dA dB n) (l' : ℕ)
    (μ : DensityMeasure (dA * dB)) : Op (P.keyDim * P.annDim * (dA * dB) ^ n) :=
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  mapTensorId (k := (dA * dB) ^ n) (P.roundDifferenceMap l')
    (deFinettiMixturePurification dA dB n μ).toOp

/-- Half the trace norm of the protocol difference on the de Finetti reference. -/
def referenceSecrecy (P : PMQKDProtocol dA dB n) (l' : ℕ)
    (μ : DensityMeasure (dA * dB)) : ℝ :=
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  (1 / 2 : ℝ) * traceNorm (P.referenceDifference l' μ)

/-- **Nahar et al. Theorem 3 conclusion** (main.tex:487–:490 (unlabeled; the conclusion of
`\label{thm:maintheorem}` :481–:491)) as a predicate: the length-`l'` variant's de Finetti
    reference secrecy is at most `bound`. Corollary 3.1 lifts this to coherent secrecy. -/
def SatisfiesReferenceBound (P : PMQKDProtocol dA dB n) (l' : ℕ)
    (μ : DensityMeasure (dA * dB)) (bound : ℝ) : Prop :=
  referenceSecrecy P l' μ ≤ bound

/-! ## The IID security proof (Nahar et al. `\label{eq:condS}` (main.tex:457–:459) and
`\label{eq:condLHL}` (main.tex:462–:467)) -/

/-- IID acceptance and privacy-amplification data with extended smooth entropy.
The accepting set may be empty, and the hashing budget may be zero. -/
structure HasIIDSecurityProof (P : PMQKDProtocol dA dB n) (εAT εPA εbar : ℝ) where
  /-- The single-round state index. -/
  ι : Type
  /-- The states satisfying the fixed-marginal constraint. -/
  Sσhat : Set ι
  /-- The accepting subset of the fixed-marginal states. -/
  S : Set ι
  /-- Acceptance probability for each component. -/
  pAcc : ι → ℝ
  /-- Conditioned real-versus-ideal output trace distance. -/
  condTraceDist : ι → ℝ
  /-- Dimension of the conditioning register. -/
  condDim : ℕ
  /-- The conditioning register is nonzero. -/
  condDim_neZero : NeZero condDim
  /-- The accepted raw-key CQ state for each component. -/
  rawKeyCQ : ι → CQState (Fin P.rawKeyDim) condDim
  /-- The entropy reference for each component. -/
  ref : ι → SubDensityOp condDim
  /-- Acceptance-test bound on the complement of the accepting set. -/
  eq10 : SatisfiesAcceptTestBound Sσhat S pAcc εAT
  /-- The extended-entropy privacy-amplification bound. -/
  eq11 :
    haveI := P.rawKeyDim_neZero
    haveI := condDim_neZero
    SatisfiesPrivacyAmplificationBound (rawKeyDim := P.rawKeyDim) (condDim := condDim)
      S pAcc condTraceDist rawKeyCQ ref P.l εPA εbar

/-- Extended IID entropy bounds imply reference secrecy after the de Finetti key reduction.
The additive mixture penalty preserves infinite entropy and allows a zero hashing budget. -/
theorem postselection_referenceBound_of_iidSecurityProof
    (P : PMQKDProtocol dA dB n) (μ : DensityMeasure (dA * dB))
    (εAT εPA εbar : ℝ) (l' g : ℕ)
    (hproof : HasIIDSecurityProof P εAT εPA εbar)
    (hl' : (l' : ℝ) ≤ (P.l : ℝ) - 2 * Real.logb 2 (g : ℝ))
    {mixCondDim : ℕ} (hmixCondDim : NeZero mixCondDim)
    (mixCQ : CQState (Fin P.rawKeyDim) mixCondDim) (mixRef : SubDensityOp mixCondDim)
    (hMixFloor :
      haveI := P.rawKeyDim_neZero
      haveI := hproof.condDim_neZero
      haveI := hmixCondDim
      (⨅ σ : hproof.S, smoothMinEntropy εbar (hproof.rawKeyCQ σ) (hproof.ref σ)) ≤
        smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) mixCQ mixRef +
          ENNReal.ofReal (2 * Real.logb 2 (g : ℝ)))
    (hLeftover :
      haveI := P.rawKeyDim_neZero
      haveI := hmixCondDim
      referenceSecrecy P l' μ ≤
        hashingError l' (smoothMinEntropy (εbar + Real.sqrt (2 * εAT)) mixCQ mixRef) +
          2 * (εbar + Real.sqrt (2 * εAT))) :
    SatisfiesReferenceBound P l' μ (coherentIIDSecrecy εAT εPA εbar) := by
  haveI := P.rawKeyDim_neZero
  haveI := hproof.condDim_neZero
  haveI := hmixCondDim
  have hpa : hashingError P.l
      (⨅ σ : hproof.S, smoothMinEntropy εbar (hproof.rawKeyCQ σ) (hproof.ref σ)) ≤
        εPA := by
    apply hashingError_iInf_le _ _ hproof.eq11.1
    intro σ
    have h := (hproof.eq11.2.2 σ σ.2).2
    linarith only [h]
  have hp : 0 ≤ 2 * Real.logb 2 (g : ℝ) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · exact mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) (by exact_mod_cast hg))
  have herr := hashingError_le_of_le_add P.l l' (2 * Real.logb 2 (g : ℝ)) _ _
    hp hMixFloor hl'
  change referenceSecrecy P l' μ ≤ coherentIIDSecrecy εAT εPA εbar
  unfold coherentIIDSecrecy
  linarith [herr.trans hpa]

/-! ## Theorem 3 (Postselection Theorem, Nahar et al. main.tex:487–:490 (unlabeled; the conclusion
of `\label{thm:maintheorem}` :481–:491)) -/

/-! ## The group-symmetric fixed-marginal reduction and group-invariant lift

The group-symmetric analogue of the fixed-marginal reduction and of Corollary 3.1, at the
group-symmetric de Finetti prefactor `deFinettiPrefactor (∑ i, ∑ j, (mA i)² (mB j)²) n`
(they live here, upstream of the plain theorems, so that the plain theorems below are their
trivial-group corollaries). -/

/-- **Group-symmetric fixed-marginal reduction**: the group-symmetric analogue of
`deFinetti_fixedMarginal_traceNorm_le` (FixedMarginalReduction.lean:197). If `Δ` is both
permutation-covariant (`hΔ_perm`, Def. 5) and IID-`G`-covariant for `prodRep πA πB`
(`hΔ_G`, Def. 6), then a state `ρ` with an arbitrary Eve ancilla and round-wise Alice
marginal `σA^⊗n` is dominated in `mapTensorId Δ`-trace norm by
`g_{n,x} · ‖(Δ ⊗ id) τ_R‖₁`, where `τ_R` purifies the de Finetti mixture of a
**group-invariant** fixed-marginal measure `μ` and
`x = ∑ i, ∑ j, (mA i)² (mB j)²`. Chain: ancilla fold + group block-diagonal twirl
(`purification_bound_of_groupTwirl`), permutation symmetrization
(`block_diagonal_purification_bound`), then the substate bound at `α = g_{n,x}` against the
domination produced by `deFinetti_groupSymmetric_fixedMarginal_op_le` applied to
`symmetrize (groupTwirl ρ.partialTraceB)`, which is permutation-invariant
(`symmetrize_isPermutationInvariant`), still IID-`G`-invariant
(`symmetrize_iidGroupInvariant`), and has the same round-wise Alice marginal
(`roundwiseAliceMarginal_symmetrize`). -/
theorem deFinetti_groupSymmetric_traceNorm_le
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n kA kB dimOut eveDim : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero dimOut]
    [NeZero eveDim]
    (Δ : Op ((dA * dB) ^ n) →ₗ[ℂ] Op dimOut)
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (hΔ_perm : IsPermutationInvariantMap Δ)
    (hΔ_G : ∀ (W : (G_A × G_B) → UnitaryOp (dA * dB)), (∀ g : G_A × G_B,
        (W g).toOp = prodRep πA πB g) → IsIIDGroupInvariantMap W Δ)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) (hσinv : IsGroupInvariantState πA σA)
    (ρ : DensityOp ((dA * dB) ^ n * eveDim))
    (hmarg : roundwiseAliceMarginal ρ.partialTraceB = σA.tensorPowGen n) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      IsGroupInvariantMeasure (prodRep πA πB) μ ∧
      Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ ρ.toOp) ≤
        (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) *
          Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ
            (deFinettiMixturePurification dA dB n μ).toOp) := by
  haveI hABn : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI hAn : NeZero (dA ^ n) := ⟨pow_ne_zero n (NeZero.ne dA)⟩
  have hπG : IsUnitaryRep (prodRep πA πB) := prodRep_isUnitaryRep πA hπA πB hπB
  -- the group twirl of the round marginal, and a purification of it
  set σg : DensityOp ((dA * dB) ^ n) :=
    groupTwirlDensity πA hπA πB hπB ρ.partialTraceB with hσg_def
  set Ψg : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n) := purificationDensityOp σg with hΨg_def
  have hΨg_pure : Ψg.IsPure := purificationDensityOp_isPure _
  have hΨg_ptB : partialTraceB Ψg.toOp = σg.toOp :=
    congrArg (fun d : DensityOp ((dA * dB) ^ n) => d.toOp)
      (purificationDensityOp_partialTraceB σg)
  -- the twirl has the same round-wise Alice marginal (`roundwiseAliceMarginal_groupTwirl`)
  -- and is IID-G-invariant (`isIIDGroupInvariant_groupTwirlDensity`)
  have hσg_marg : roundwiseAliceMarginal σg = σA.tensorPowGen n := by
    apply DensityOp.ext
    change partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n)
        (roundGroupEquiv dA dB n) σg.toOp) = (σA.tensorPowGen n).toOp
    rw [hσg_def]
    exact roundwiseAliceMarginal_groupTwirl πA hπA πB hπB σA hσinv ρ.partialTraceB.toOp
      (by change (roundwiseAliceMarginal ρ.partialTraceB).toOp = (σA.tensorPowGen n).toOp
          exact congrArg (fun d : DensityOp (dA ^ n) => d.toOp) hmarg)
  have hσg_iid : IsIIDGroupInvariant (prodRep πA πB) σg :=
    isIIDGroupInvariant_groupTwirlDensity πA hπA πB hπB ρ.partialTraceB
  -- the symmetrized twirl: permutation-invariant, still IID-G-invariant, same marginal
  set σsym : DensityOp ((dA * dB) ^ n) := symmetrize σg with hσsym_def
  have hσsym_perm : IsPermutationInvariant σsym := symmetrize_isPermutationInvariant σg
  have hσsym_iid : IsIIDGroupInvariant (prodRep πA πB) σsym := by
    intro h
    exact symmetrize_iidGroupInvariant (prodRepUnitary πA hπA πB hπB) σg hσg_iid h
  have hσsym_marg : roundwiseAliceMarginal σsym = σA.tensorPowGen n :=
    roundwiseAliceMarginal_symmetrize σg σA hσg_marg
  -- STEP A: fold the ancilla and pass to the group-twirled purification
  have stepA : Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ ρ.toOp) ≤
      Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ Ψg.toOp) :=
    purification_bound_of_groupTwirl Δ πA hπA πB hπB hΔ_G ρ Ψg hΨg_pure
      (by rw [hΨg_ptB, hσg_def]; rfl)
  -- STEP B: permutation block-diagonal symmetrization of the twirled purification
  obtain ⟨Ψsym, hΨsym_pure, _, _, hΨsym_marg⟩ :=
    symmetric_purification_with_pure σsym hσsym_perm
  have hΨg_nz : Ψg.toOp ≠ 0 := by
    intro h
    have h1 := Ψg.trace_one
    rw [h] at h1
    simp at h1
  have hΨg_trace : Ψg.toOp.trace.re ≤ 1 := by rw [Ψg.trace_one]; simp
  have hσg_rel : σg.toOp = (1 / Ψg.toOp.trace) • partialTraceB Ψg.toOp := by
    rw [hΨg_ptB, Ψg.trace_one]; simp
  have stepB : Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ Ψg.toOp) ≤
      Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ Ψsym.toOp) :=
    Quantum.Channels.block_diagonal_purification_bound Δ hΔ_perm.covariance Ψg.toOp
      (posSemidefOp_implies_mathlib Ψg.toPosSemidefOp) hΨg_trace hΨg_nz σg hσg_rel Ψsym
      hΨsym_pure (by rw [hΨsym_marg])
  -- STEP C: substate bound at α = g_{n,x} against the group-symmetric de Finetti reference
  obtain ⟨μ, hμ_marg, hμ_grp, hμ_op⟩ :=
    deFinetti_groupSymmetric_fixedMarginal_op_le πA hπA πB hπB mA mB hxA hxB σA hσA σsym
      hσsym_perm hσsym_iid hσsym_marg
  set τR : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n) :=
    deFinettiMixturePurification dA dB n μ with hτR_def
  have hτR_pure : τR.IsPure := purificationDensityOp_isPure _
  have hτR_marg : τR.partialTraceB.toOp = (deFinettiMixtureFixedMarginal dA dB n μ).toOp :=
    congrArg (fun d : DensityOp ((dA * dB) ^ n) => d.toOp)
      (deFinettiMixturePurification_partialTraceB dA dB n μ)
  have hg_pos : 0 <
      (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) :=
    by exact_mod_cast deFinettiPrefactor_pos _ _
  have h_dom : (((deFinettiPrefactor
          (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) :
        ℂ) • τR.partialTraceB.toOp - partialTraceB Ψsym.toOp).PosSemidef := by
    rw [hΨsym_marg, hτR_marg]
    have hcast : ((deFinettiPrefactor
            (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) :
          ℂ) = (deFinettiPrefactor
            (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact hμ_op
  refine ⟨μ, hμ_marg, hμ_grp, ?_⟩
  refine le_trans stepA (le_trans stepB ?_)
  exact Quantum.Channels.traceNorm_mapTensorId_substate_bound Δ Ψsym.toOp
    (posSemidefOp_implies_mathlib Ψsym.toPosSemidefOp) τR hτR_pure _ hg_pos h_dom

/-- **Intermediate step toward Corollary `cor:liftToCoherentSymmetries`**
(Nahar et al., arXiv:2403.11851, main.tex:527): the group-invariant analogue of
`permInvariant_postselection_security_of_referenceBound` (below).

If the round-grouped difference map `P.roundDifferenceMap l'` is
permutation-invariant (`hperm`, Def. 5) *and* IID-`G`-invariant (`hG`, Def. 6)
for the product representation `prodRep πA πB` of the finite group
`G_A × G_B` on the per-round `AB` register, then the fixed-marginal reduction
holds with the group-symmetric de Finetti prefactor
`deFinettiPrefactor (∑ i, ∑ j, (mA i)² (mB j)²) n` instead of the generic
`deFinettiPrefactor (dA² dB²) n`.

Proof plan (paper sketch, main.tex:527–529): combine
(i) a psLemma-twirling reduction from the map symmetries `hperm`/`hG` to
permutation- and IID-`G`-invariance of the (round-grouped) input state — the
library only has the permutation half of this inside
`deFinetti_fixedMarginal_traceNorm_le` (FixedMarginalReduction.lean:197) —
with (ii) the group-symmetric de Finetti reduction
`deFinetti_groupSymmetric_fixedMarginal_op_le` (GroupSymmetricDeFinetti.lean:151),
which *requires* both state symmetries as hypotheses, unlike the generic
`deFinetti_fixedMarginal_traceNorm_le`.

The `hW` hypothesis ties the map-symmetry group action to the representation
used on the state side; `W g` is then forced to be `prodRep πA πB g`, which is
unitary by `prodRep_isUnitaryRep` (FiniteGroupUnitaryRep.lean:176).

**Extra hypothesis `hσinv` (`σA` must be `πA`-invariant):** the
promised marginal `σA` is required to satisfy `IsGroupInvariantState πA σA`,
i.e. `∀ g, πA g * σA.toOp * (πA g)ᴴ = σA.toOp` (the library's predicate,
GroupInvariantStates.lean:27). Reason: the paper's promise is a `G_A`-invariant
marginal — in `cor:symmetryDeFinetti` (main.tex:362–369) the states fed to the
de Finetti reduction are IID-`G`-invariant, whose round-wise Alice marginal is
`πA`-invariant (`sigmaA_tensorPowGen_invariant`, GroupInvariantStates.lean:123).
Without `hσinv` the statement overclaims: if `σA` is *not* `πA`-invariant, no
measure can simultaneously be fixed-marginal (`IsFixedMarginalMeasure σA μ`) and
`G`-invariant (`IsGroupInvariantMeasure (prodRep πA πB) μ`) — both hold a.e.
under the probability measure `μ.measure`, so some state would have Alice
marginal `σA` yet be `prodRep`-invariant, and tracing out `B` in the
`(πA g ⊗ πB 1)`-conjugation (the unitary `B`-half cancels, cf.
`roundwiseAliceMarginal_conj`, GroupInvariantStates.lean:95) would force
`πA g * σA.toOp * (πA g)ᴴ = σA.toOp`, a contradiction. `href` would then be
vacuously true for *every* `bound` (e.g. `bound = 0`) while `hperm`/`hG` remain
satisfiable by protocols with nonzero difference map, so the conclusion
`P.IsSecretAt l' σA 0` fails.

**`href` is restricted to `G`-invariant measures:** the proof produces its
reference measure as the output of
`deFinetti_groupSymmetric_fixedMarginal_op_le` (GroupSymmetricDeFinetti.lean:151),
whose second conjunct is exactly `IsGroupInvariantMeasure (prodRep πA πB) μ`
(GroupSymmetricDeFinetti.lean:164–166), so quantifying over `G`-invariant `μ`
suffices and matches the paper, where the restated Theorem 3 is applied to the
symmetric states produced by the psLemma-twirling step (main.tex:527–529).
Quantifying over *all* fixed-marginal `μ` instead would require an additional
unproved invariance property of `SatisfiesReferenceBound` under twirling. -/
theorem groupInvariant_postselection_security_of_referenceBound
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ}
    (P : PMQKDProtocol dA dB n) (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (hσinv : IsGroupInvariantState πA σA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (bound : ℝ) (l' : ℕ)
    (href : ∀ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ →
      IsGroupInvariantMeasure (prodRep πA πB) μ →
      SatisfiesReferenceBound P l' μ bound)
    (hperm :
      haveI := P.keyDim_neZero
      haveI := P.annDim_neZero
      haveI : NeZero (P.keyDim * P.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
      IsPermutationInvariantMap (P.roundDifferenceMap l'))
    (hG :
      haveI := P.keyDim_neZero
      haveI := P.annDim_neZero
      haveI : NeZero (P.keyDim * P.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
      ∀ (W : (G_A × G_B) → UnitaryOp (dA * dB)), (∀ g : G_A × G_B,
        (W g).toOp = prodRep πA πB g) →
        IsIIDGroupInvariantMap W (P.roundDifferenceMap l')) :
    P.IsSecretAt l' σA
      ((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) *
        bound) := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  set e := roundGroupEquiv dA dB n with he_def
  set Δ := P.roundDifferenceMap l' with hΔ_def
  intro eveDim _ ρ hρmarg
  set ρround : DensityOp ((dA * dB) ^ n * eveDim) :=
    densityOp_reindex (Equiv.finProdCongrExt e eveDim).symm ρ with hρround_def
  have hρround_toOp : ρround.toOp =
      Matrix.reindex (Equiv.finProdCongrExt e eveDim).symm
        (Equiv.finProdCongrExt e eveDim).symm ρ.toOp := rfl
  -- transport the difference map through the round-grouping reindex
  have hb' : Quantum.Channels.mapTensorId Δ ρround.toOp =
      Quantum.Channels.mapTensorId (P.differenceMap l') ρ.toOp := by
    rw [hρround_toOp, hΔ_def, PMQKDProtocol.roundDifferenceMap,
      ← Quantum.Channels.mapTensorId_comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap
        (P.differenceMap l'),
      mapTensorId_reindexLinearEquiv]
    congr 1
    ext p q
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  -- the round-grouped state has round-wise Alice marginal `σA^⊗n`
  have hd : roundwiseAliceMarginal ρround.partialTraceB = σA.tensorPowGen n := by
    apply DensityOp.ext
    change partialTraceB (Matrix.reindex e e ρround.partialTraceB.toOp) = (σA.tensorPowGen n).toOp
    have hpb : ρround.partialTraceB.toOp = partialTraceB ρround.toOp := rfl
    rw [hpb, hρround_toOp, Equiv.finProdCongrExt_symm,
      partialTraceB_reindex_finProdCongrExt e.symm ρ.toOp]
    rw [show Matrix.reindex e e (Matrix.reindex e.symm e.symm (partialTraceB ρ.toOp)) =
        Matrix.reindex (e.symm.trans e) (e.symm.trans e) (partialTraceB ρ.toOp) from rfl]
    simp only [Equiv.symm_trans_self, Matrix.reindex_refl_refl]
    exact hρmarg
  -- the group-symmetric fixed-marginal reduction (`deFinetti_groupSymmetric_traceNorm_le`)
  obtain ⟨μ, hμ_marg, hμ_grp, hbound⟩ :=
    deFinetti_groupSymmetric_traceNorm_le Δ πA hπA πB hπB hperm
      (fun W hW => hG W hW) mA mB hxA hxB σA hσA hσinv ρround hd
  rw [hb'] at hbound
  -- the trace norm of the de Finetti purification computes to `2 · referenceSecrecy`
  have hc : Quantum.Metrics.traceNorm
      (Quantum.Channels.mapTensorId Δ (deFinettiMixturePurification dA dB n μ).toOp) =
      2 * referenceSecrecy P l' μ := by
    rw [hΔ_def]
    unfold referenceSecrecy PMQKDProtocol.referenceDifference
    ring
  rw [hc] at hbound
  have hle : referenceSecrecy P l' μ ≤ bound := href μ hμ_marg hμ_grp
  have : Quantum.Metrics.traceNorm
      (Quantum.Channels.mapTensorId (P.differenceMap l') ρ.toOp) ≤
      (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) *
        (2 * bound) :=
    hbound.trans (by
      have hg_nonneg : (0:ℝ) ≤ (deFinettiPrefactor
          (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle hg_nonneg])
  linarith

/-! ## Corollary 3.1 (Nahar et al. lines 560–568) -/

/-- A permutation-invariant difference map with reference secrecy at most `bound` on every
fixed-marginal de Finetti mixture is secret with error `g · bound` on all inputs with that
marginal. Permutation invariance is needed only at the chosen key length `l'`.

This is the fixed-marginal reduction used in Nahar et al., `cor:liftToCoherent`
(main.tex:495–499). The full-rank assumption corresponds to main.tex:1097. It is the
**trivial-group instance** of `groupInvariant_postselection_security_of_referenceBound`
(above): at `G_A = G_B = Unit` with the constant-identity representations there is a single
trivial irrep of multiplicity `d` (`kA = kB = 1`, `mA i = dA`, `mB j = dB`), so the
group-symmetric prefactor sum collapses to `dA² · dB²`; the group-invariance hypotheses hold
trivially (`isGroupInvariantState_const_one`,
`isIIDGroupInvariantMap_const_of_toOp_eq_one` with `prodRep_const_one`). -/
theorem permInvariant_postselection_security_of_referenceBound
    (P : PMQKDProtocol dA dB n) (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (bound : ℝ) (l' : ℕ)
    (href : ∀ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ →
      SatisfiesReferenceBound P l' μ bound)
    (hperm :
      haveI := P.keyDim_neZero
      haveI := P.annDim_neZero
      haveI : NeZero (P.keyDim * P.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
      IsPermutationInvariantMap (P.roundDifferenceMap l')) :
    P.IsSecretAt l' σA ((deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) * bound) := by
  -- the trivial representations: one trivial irrep of multiplicity `d`, twirl projector `1`
  have hxA : (groupTwirlProjector (fun _ : Unit => (1 : Op dA))).trace =
      ∑ i : Fin 1, (((((fun _ : Fin 1 => dA) i : ℕ) : ℂ)) ^ 2) := by
    rw [groupTwirlProjector_unit_const_one_trace, Fin.sum_univ_one]
  have hxB : (groupTwirlProjector (fun _ : Unit => (1 : Op dB))).trace =
      ∑ j : Fin 1, (((((fun _ : Fin 1 => dB) j : ℕ) : ℂ)) ^ 2) := by
    rw [groupTwirlProjector_unit_const_one_trace, Fin.sum_univ_one]
  -- apply the group-invariant lift at the trivial groups
  have key := groupInvariant_postselection_security_of_referenceBound P σA hσA
    (fun _ : Unit => (1 : Op dA)) isUnitaryRep_const_one (isGroupInvariantState_const_one σA)
    (fun _ : Unit => (1 : Op dB)) isUnitaryRep_const_one
    (fun _ : Fin 1 => dA) (fun _ : Fin 1 => dB) hxA hxB bound l'
    (fun μ hμ _ => href μ hμ) hperm
    (fun W hW => by
      haveI := P.keyDim_neZero
      haveI := P.annDim_neZero
      haveI : NeZero (P.keyDim * P.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
      exact isIIDGroupInvariantMap_const_of_toOp_eq_one
        (Δ := P.roundDifferenceMap l') W
        fun g => by rw [hW g, prodRep_const_one])
  -- the multiplicity sum collapses to the plain de Finetti exponent `dA² · dB²`
  rw [show (∑ i : Fin 1, ∑ j : Fin 1,
      ((fun _ : Fin 1 => dA) i) ^ 2 * ((fun _ : Fin 1 => dB) j) ^ 2) = dA ^ 2 * dB ^ 2 from
    by simp] at key
  exact key

/-! ## The linear IID secrecy parameter and its dominance by the coherent one -/

/-- **Codebase-original: the linear-accept-test secrecy parameter** `ε_PA + 2ε̄ + 2ε_AT`
    (the `postselection_linear_referenceBound_of_iidSecurityProof` bound), which charges the
    accept-test defect linearly at the operational trace level.

    ⚠️ **This is NOT Nahar et al.'s Theorem-3 parameter and must not be cited as it.** Their
    accept-test charge is the FvdG smoothing move `√(2ε_AT)` —
    arXiv:2403.11851, `main.tex`,
    Appendix B around `\label{eq:tausplit}`, where the trace-distance bound `ε_AT` is converted to
    purified distance as `P ≤ √(2·ε_AT)` (citing Tomamichel Lemma 3.5). That quantity is
    `coherentIIDSecrecy`. Ours replaces the `√` with a linear charge and is *never worse*:
    `linearIIDSecrecy_le_coherentIIDSecrecy` proves `linear ≤ coherent` for `ε_AT ≤ 2`, so a
    quantity that provably differs from — and improves on — theirs cannot carry their
    attribution. -/
def linearIIDSecrecy (εAT εPA εbar : ℝ) : ℝ := εPA + 2 * εbar + 2 * εAT

/-- **The linear parameter dominates the coherent one** for `ε_AT ≤ 2`:
    `ε_PA + 2ε̄ + 2ε_AT ≤ ε_PA + 2ε̄ + 2√(2ε_AT)`, since `ε_AT ≤ √(2ε_AT) ⟺ ε_AT² ≤ 2ε_AT
    ⟺ ε_AT ≤ 2` for `ε_AT ≥ 0`, with equality only at `ε_AT ∈ {0}`. So the min-with-Nahar et al.
    composite
    `min (linear, coherent) = linear` on the whole security range `ε_AT ≤ 1/2 < 2`; the linear
    bound is never worse than Nahar et al.'s `√`-form. -/
theorem linearIIDSecrecy_le_coherentIIDSecrecy
    (εAT εPA εbar : ℝ) (hεAT_nonneg : 0 ≤ εAT) (hεAT_le_two : εAT ≤ 2) :
    linearIIDSecrecy εAT εPA εbar ≤ coherentIIDSecrecy εAT εPA εbar := by
  unfold linearIIDSecrecy coherentIIDSecrecy
  have h1 : εAT ^ 2 ≤ 2 * εAT := by nlinarith [hεAT_nonneg, hεAT_le_two]
  have h : εAT ≤ Real.sqrt (2 * εAT) :=
    calc εAT = Real.sqrt (εAT ^ 2) := (Real.sqrt_sq hεAT_nonneg).symm
      _ ≤ Real.sqrt (2 * εAT) := Real.sqrt_le_sqrt h1
  linarith

/-- **The bb84-level comparison of the two secrecy bounds**: after the de Finetti prefactor
    `g_{n,x}`, the linear bound still dominates the coherent one,
    `g_{n,x}·(ε_PA + 2ε̄ + 2ε_AT) ≤ g_{n,x}·(ε_PA + 2ε̄ + 2√(2ε_AT))` for `0 ≤ ε_AT ≤ 2` —
    `linearIIDSecrecy_le_coherentIIDSecrecy` multiplied by the nonnegative prefactor. -/
theorem linearSecrecyBound_le_coherentSecrecyBound (x n : ℕ) (εAT εPA εbar : ℝ)
    (hεAT_nonneg : 0 ≤ εAT) (hεAT_le_two : εAT ≤ 2) :
    (deFinettiPrefactor x n : ℝ) * linearIIDSecrecy εAT εPA εbar ≤
      (deFinettiPrefactor x n : ℝ) * coherentIIDSecrecy εAT εPA εbar :=
  mul_le_mul_of_nonneg_left
    (linearIIDSecrecy_le_coherentIIDSecrecy εAT εPA εbar hεAT_nonneg hεAT_le_two)
    (by positivity)

end InfoTheory.Postselection

end
