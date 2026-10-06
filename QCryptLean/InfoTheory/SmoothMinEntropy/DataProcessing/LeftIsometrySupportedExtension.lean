import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.LeftIsometryPenaltyEmbedding
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.CQExtensionFiber

/-!
# Supported isometric extensions

Supported states admit inverse isometric transport of feasible coefficients and purified-distance
witnesses. This gives a canonical smooth entropy comparison for arbitrary references, alongside
signed conditional entropy identities.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The real-part trace of a rectangular conjugation `W · A · Wᴴ` of a PSD
operator is bounded by that of `A` when `Wᴴ W ≤ 1`. -/
lemma trace_re_rectConj_le_of_opLe
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (A : Op dIn) (hA : A.PosSemidef) :
    (W * A * Wᴴ).trace.re ≤ A.trace.re := by
  have heq : (W * A * Wᴴ).trace = (A * (Wᴴ * W)).trace := by
    calc
      (W * A * Wᴴ).trace = (Wᴴ * (W * A)).trace :=
        Matrix.trace_mul_comm (W * A) Wᴴ
      _ = (Wᴴ * W * A).trace := by rw [← Matrix.mul_assoc]
      _ = (A * (Wᴴ * W)).trace := Matrix.trace_mul_comm (Wᴴ * W) A
  have hWW_herm : (Wᴴ * W).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self W
  have hbound : (A * (Wᴴ * W)).trace.re ≤ (A * 1).trace.re :=
    Quantum.Operators.trace_mul_le_of_opLe hA hWW_herm Matrix.isHermitian_one hW
  rw [Matrix.mul_one] at hbound
  rw [heq]; exact hbound

/-- Conjugate a sub-density operator by a rectangular `W` with `Wᴴ W ≤ 1`.

The result `W · σ · Wᴴ` is positive semidefinite and trace non-increasing, hence
remains sub-normalized. -/
def subDensityOpRectConj
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (σ : SubDensityOp dIn) :
    SubDensityOp dOut where
  toOp := W * σ.toOp * Wᴴ
  isHermitian := by
    change (W * σ.toOp * Wᴴ)ᴴ = W * σ.toOp * Wᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, σ.isHermitian, Matrix.mul_assoc]
  pos_semidef := by
    intro x
    have hσ_psd : σ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
    have hWσW_psd : (W * σ.toOp * Wᴴ).PosSemidef := by
      simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
        hσ_psd.conjTranspose_mul_mul_same Wᴴ
    exact Quantum.Operators.posSemidef_re_quadraticForm_nonneg hWσW_psd x
  trace_le_one := by
    have hσ_psd : σ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
    exact le_trans (trace_re_rectConj_le_of_opLe W hW σ.toOp hσ_psd) σ.trace_le_one

@[simp]
lemma subDensityOpRectConj_toOp
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (σ : SubDensityOp dIn) :
    (subDensityOpRectConj W hW σ).toOp = W * σ.toOp * Wᴴ := rfl

lemma subDensityOpRectConj_trace_le
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (σ : SubDensityOp dIn) :
    (subDensityOpRectConj W hW σ).trace ≤ σ.trace := by
  have hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  exact trace_re_rectConj_le_of_opLe W hW σ.toOp hσ_psd

/-- Blockwise CQ-state conjugation by a rectangular `W` with `Wᴴ W ≤ 1`. -/
def cqStateRectConj
    {α : Type*} [Fintype α]
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (ρ : CQState α dIn) :
    CQState α dOut where
  stateMap x := subDensityOpRectConj W hW (ρ.stateMap x)
  weight_le_one :=
    le_trans
      (Finset.sum_le_sum fun x _ => subDensityOpRectConj_trace_le W hW (ρ.stateMap x))
      ρ.weight_le_one

@[simp]
lemma cqStateRectConj_stateMap_toOp
    {α : Type*} [Fintype α]
    {dIn dOut : ℕ}
    (W : Matrix (Fin dOut) (Fin dIn) ℂ)
    (hW : opLe (Wᴴ * W) (1 : Op dIn))
    (ρ : CQState α dIn) (x : α) :
    ((cqStateRectConj W hW ρ).stateMap x).toOp = W * (ρ.stateMap x).toOp * Wᴴ := rfl

@[simp]
lemma cqStateLeftIsometryEmbed_stateMap_toOp
    {α : Type*} [Fintype α]
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc) (x : α) :
    ((cqStateLeftIsometryEmbed K hK_iso ρ).stateMap x).toOp =
      K * (ρ.stateMap x).toOp * Kᴴ := rfl

/-- **Restrict-then-Uhlmann supported extension** (Renner `rem:Hinfex`).

Given a center CQ state on `E ⊗ R` whose every block is fixed by the image-support
projector `1_E ⊗ (V Vᴴ)` of a right-factor rectangular isometry `V`
(`Vᴴ V = 1`), and an Eve candidate `ω` within purified distance `ε` of the
center's `E`-marginal, there is an `E ⊗ R` extension `ρhat` of `ω` that

* stays within `ε` of the center,
* has the exact blockwise `E`-marginal `ω`, and
* is blockwise fixed by the image-support projector `1_E ⊗ (V Vᴴ)`. -/
theorem CQState.exists_left_isometry_supported_extension
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {dE dR dSrc : ℕ} [NeZero dE] [NeZero dR] [NeZero dSrc]
    (V : Matrix (Fin dR) (Fin dSrc) ℂ)
    (hV : Vᴴ * V = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (center : CQState α (dE * dR))
    (hfix : ∀ x : α,
      Op.tensor (1 : Op dE) (V * Vᴴ) * (center.stateMap x).toOp *
          Op.tensor (1 : Op dE) (V * Vᴴ) = (center.stateMap x).toOp)
    (ω : CQState α dE) (ε : ℝ)
    (hdist : CQState.purifiedDistance center.partialTraceB ω ≤ ε) :
    ∃ ρhat : CQState α (dE * dR),
      CQState.purifiedDistance center ρhat ≤ ε ∧
      (∀ x : α, Quantum.TensorProducts.partialTraceB (ρhat.stateMap x).toOp =
        (ω.stateMap x).toOp) ∧
      (∀ x : α,
        Op.tensor (1 : Op dE) (V * Vᴴ) * (ρhat.stateMap x).toOp *
            Op.tensor (1 : Op dE) (V * Vᴴ) = (ρhat.stateMap x).toOp) := by
  classical
  have : NeZero (dE * dSrc) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dSrc)⟩
  have : NeZero (dE * dR) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  set K : Matrix (Fin (dE * dR)) (Fin (dE * dSrc)) ℂ :=
    kronIdLeftIso (dH := dE) V with hK_def
  have hK_iso : Kᴴ * K = (1 : Matrix (Fin (dE * dSrc)) (Fin (dE * dSrc)) ℂ) := by
    simpa [hK_def] using kronIdLeftIso_left_iso (dH := dE) V hV
  have hKKt : K * Kᴴ = Op.tensor (1 : Op dE) (V * Vᴴ) := by
    simpa [hK_def] using kronIdLeftIso_mul_conjTranspose (dH := dE) V
  -- compression hypothesis `Kᴴᴴ Kᴴ = K Kᴴ ≤ 1`
  have hWW : opLe (Kᴴᴴ * Kᴴ) (1 : Op (dE * dR)) := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact opLe_left_isometry_range_projection K hK_iso
  -- compressed center over `E ⊗ S`
  set ρ' : CQState α (dE * dSrc) := cqStateRectConj Kᴴ hWW center with hρ'_def
  have hρ'_block : ∀ x : α, (ρ'.stateMap x).toOp = Kᴴ * (center.stateMap x).toOp * K := by
    intro x
    rw [hρ'_def, cqStateRectConj_stateMap_toOp, Matrix.conjTranspose_conjTranspose]
  -- the center is the `K`-embed of `ρ'`
  have hcenter_embed : ∀ x : α,
      (center.stateMap x).toOp = K * (ρ'.stateMap x).toOp * Kᴴ := by
    intro x
    rw [hρ'_block x]
    have hassoc :
        K * (Kᴴ * (center.stateMap x).toOp * K) * Kᴴ =
          (K * Kᴴ) * (center.stateMap x).toOp * (K * Kᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc, hKKt, hfix x]
  -- the compressed center has the same `E`-marginal as the center
  have hmarg : ρ'.partialTraceB = center.partialTraceB := by
    apply CQState.partialTraceB_eq_of_stateMap_toOp
    intro x
    rw [CQState.partialTraceB_stateMap_toOp]
    have hcm :
        Quantum.TensorProducts.partialTraceB (K * (ρ'.stateMap x).toOp * Kᴴ) =
          Quantum.TensorProducts.partialTraceB (ρ'.stateMap x).toOp := by
      rw [hK_def]
      exact partialTraceB_kronIdLeftIso_conj (dH := dE) V hV (ρ'.stateMap x).toOp
    rw [← hcm, ← hcenter_embed x]
  -- Uhlmann achievability in the compressed register
  obtain ⟨ρhat', hdER, hpartial'⟩ :=
    CQState.exists_extension_of_partialTraceB_purifiedDistance_stateMap_toOp_eq
      ρ' ω ε (by rw [hmarg]; exact hdist)
  -- embed the Uhlmann extension back to `E ⊗ R`
  refine ⟨cqStateLeftIsometryEmbed K hK_iso ρhat', ?_, ?_, ?_⟩
  · -- conjunct (i): purified distance preserved by the left-isometry embed
    exact cqState_purifiedDistance_left_isometry_embed_le
      α ε K hK_iso ρ' ρhat' center (cqStateLeftIsometryEmbed K hK_iso ρhat')
      hcenter_embed
      (fun x => cqStateLeftIsometryEmbed_stateMap_toOp K hK_iso ρhat' x)
      hdER
  · -- conjunct (ii): exact `E`-marginal `ω`
    intro x
    rw [cqStateLeftIsometryEmbed_stateMap_toOp]
    have hcm2 :
        Quantum.TensorProducts.partialTraceB (K * (ρhat'.stateMap x).toOp * Kᴴ) =
          Quantum.TensorProducts.partialTraceB (ρhat'.stateMap x).toOp := by
      rw [hK_def]
      exact partialTraceB_kronIdLeftIso_conj (dH := dE) V hV (ρhat'.stateMap x).toOp
    rw [hcm2, hpartial' x]
  · -- conjunct (iii): image-support fixed by `1_E ⊗ (V Vᴴ) = K Kᴴ`
    intro x
    rw [cqStateLeftIsometryEmbed_stateMap_toOp, ← hKKt]
    have hassoc :
        (K * Kᴴ) * (K * (ρhat'.stateMap x).toOp * Kᴴ) * (K * Kᴴ) =
          K * (Kᴴ * K) * (ρhat'.stateMap x).toOp * (Kᴴ * K) * Kᴴ := by
      simp only [Matrix.mul_assoc]
    rw [hassoc, hK_iso, Matrix.mul_one, Matrix.mul_one]

/-- **Real conditional min-entropy is invariant under blockwise rectangular left-isometry
conjugation against the conjugated reference.**

For a rectangular left-isometry `K` (`Kᴴ K = 1`), the blockwise conjugation `ρ ↦ K ρ Kᴴ`,
`σ ↦ K σ Kᴴ` preserves `conditionalMinEntropyReal`: it is `−log₂` of `minFeasibleLambda`, which is
invariant by `minFeasibleLambda_left_isometry_embed_eq` (feasibility transfers bijectively under
isometric conjugation, `isFeasible_left_isometry_embed_iff`).  This is the conditional-min-entropy
companion of the trace-distance invariance `traceDistanceGen_leftIsometryEmbed_eq`. -/
theorem conditionalMinEntropyReal_left_isometry_embed_eq
    {α : Type*} [Fintype α]
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc) (σ : SubDensityOp dSrc)
    (ρ_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α, (ρ_embed.stateMap x).toOp = K * (ρ.stateMap x).toOp * Kᴴ)
    (σ_embed : SubDensityOp dTgt)
    (hσ_embed : σ_embed.toOp = K * σ.toOp * Kᴴ) :
    conditionalMinEntropyReal ρ_embed σ_embed = conditionalMinEntropyReal ρ σ := by
  unfold conditionalMinEntropyReal
  rw [minFeasibleLambda_left_isometry_embed_eq α K hK_iso ρ σ ρ_embed hρ_embed σ_embed hσ_embed]

/-- Isometrically embedding each smoothing witness and its reference increases extended
smooth entropy, including singular references and zero witnesses. -/
theorem smoothMinEntropy_left_isometry_embed_arbitraryRef_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ε : ℝ) (ρ : CQState α dSrc) (σ : SubDensityOp dSrc)
    (ρ_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α, (ρ_embed.stateMap x).toOp = K * (ρ.stateMap x).toOp * Kᴴ)
    (σ_embed : SubDensityOp dTgt) (hσ_embed : σ_embed.toOp = K * σ.toOp * Kᴴ) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε ρ_embed σ_embed := by
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨cqStateLeftIsometryEmbed K hK_iso τ, ?_, fun t ht => ?_⟩
  · exact cqState_purifiedDistance_left_isometry_embed_le α ε K hK_iso
      ρ τ ρ_embed (cqStateLeftIsometryEmbed K hK_iso τ) hρ_embed (fun _ => rfl) hd
  · exact (isFeasible_left_isometry_embed_iff α K hK_iso τ σ
      (cqStateLeftIsometryEmbed K hK_iso τ) (fun _ => rfl) σ_embed hσ_embed t).mpr ht


/-- Embedding both state and reference by an isometry does not decrease signed smooth
min-entropy when the target ball is bounded above. -/
theorem smoothMinEntropyReal_left_isometry_embed_arbitraryRef_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (ρ : CQState α dSrc) (σ : SubDensityOp dSrc)
    (ρ_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α, (ρ_embed.stateMap x).toOp = K * (ρ.stateMap x).toOp * Kᴴ)
    (σ_embed : SubDensityOp dTgt)
    (hσ_embed : σ_embed.toOp = K * σ.toOp * Kᴴ)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ_embed))) :
    smoothMinEntropyReal ε ρ σ ≤ smoothMinEntropyReal ε ρ_embed σ_embed := by
  unfold smoothMinEntropyReal
  apply csSup_le_csSup hbdd
  · exact ⟨conditionalMinEntropyReal ρ σ, ρ, rfl, by
      rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  · intro h hh
    obtain ⟨ρtilde, hh_eq, hd⟩ := hh
    refine ⟨cqStateLeftIsometryEmbed K hK_iso ρtilde, ?_, ?_⟩
    · -- same conditional min-entropy: `h = cMER ρtilde σ = cMER (embed ρtilde) σ_embed`
      rw [hh_eq, conditionalMinEntropyReal_left_isometry_embed_eq K hK_iso ρtilde σ
        (cqStateLeftIsometryEmbed K hK_iso ρtilde)
        (fun x => cqStateLeftIsometryEmbed_stateMap_toOp K hK_iso ρtilde x)
        σ_embed hσ_embed]
    · -- purified distance non-increasing under the embed
      exact cqState_purifiedDistance_left_isometry_embed_le
        α ε K hK_iso ρ ρtilde ρ_embed (cqStateLeftIsometryEmbed K hK_iso ρtilde)
        hρ_embed (fun x => cqStateLeftIsometryEmbed_stateMap_toOp K hK_iso ρtilde x) hd

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
