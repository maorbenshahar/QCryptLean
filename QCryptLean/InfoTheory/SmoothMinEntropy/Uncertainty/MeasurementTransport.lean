import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilationChannel
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension

/-!
# Measurement transport of the conditional min-entropy: the `ε = 0` uncertainty relation

This file lifts the operator-level feasibility transport of `MeasurementDilation.lean`
(`measDilation_mo6`) and the recovery identity of `PureCoreUncertainty.lean` (`eqn:mo10`) to the
level of the **guarded reference-optimized bipartite conditional min-entropy**
`bipartiteMinEntropyOptReal` (`BipartiteMinMax.lean`), giving the `ε = 0` entropic uncertainty
relation

```
H_min(Z|Z′AB)_{V ρ Vᴴ}  ≤  H_min(X|B)_{ρ_XB} − q ,        q = log₂(1/c) ,
```

for two rank-one projective measurements `P` (the `X`-basis) and `Q` (the `Z`-basis) of `ℂ^d`,
their overlap `c = overlapConst P Q`, and an arbitrary sub-normalized `ρ_AB` on `A ⊗ B`.

## Relation to the cited textbook

This is the inequality arXiv:1504.00233, `apps.tex:198`, `\label{eq:ucr-dual}`, at
`α = ∞`:

```
H↑_α(X|B)_{M_X(ρ)}  ≥  H↑_α(Y|Y′B)_{U_Y(ρ)} − log c .
```

The proof there routes through the Rényi duality `pr:dual-new`; the proof here is the explicit
`U`, `V`, `W = U Vᴴ` operator algebra of Tomamichel–Renner (arXiv:1009.2015), which for the
min-entropy needs no duality.  The load-bearing operator step — the evaluation and domination
`M_X(U_Y(1_Y ⊗ σ)) ⪯ c · 1_X ⊗ σ_B` of `apps.tex:209–213` — is
`measConjTraceMap_one_tensor_reference_opLe`.

**What is *not* claimed.** The tripartite uncertainty relation `apps.tex:183–192`,
`\label{th:ur}` (`H↑_α(X|B) + H↑_β(Y|C) ≥ −log c` for two *separate* memories `B`, `C`) is a
strictly stronger statement: deriving it from `eq:ucr-dual` consumes the min–max duality
`pr:dual-new`, which the library does not have.  Nothing here should be read as `th:ur`; both
entropies below are conditioned on registers derived from the *same* memory.

## Two layers, and why the regularity is derived rather than assumed

* **General-state layer.** For an *arbitrary* sub-normalized `τ` on the Z-side register
  `Z ⊗ Z′AB`, the state-level transport `measDilateTransport P Q τ = Ξ(τ)` is the definitional
  image of the measurement sub-channel `Ξ = measConjTraceMap (U Vᴴ)`, and
  `bipartiteMinEntropyOptReal_measDilateTransport_ge` reads
  `H_min(τ) + q ≤ H_min(Ξ τ)`.  No recovery identity is used here.
* **Pure-core layer.** Specializing to `τ = zDilatedState Q ρ_AB`, the recovery identity
  `eqn:mo10` identifies `Ξ(τ)` with the `X`-measured marginal, giving `measDilation_pure_core`.

The ℝ-valued encoding of `H_min` uses the `Real.log 0 = 0` sentinel for an infeasible or
degenerate optimum, so an honest statement has to exclude it.  Both side-conditions reduce to a
*nonvanishing* hypothesis rather than an opaque regularity certificate:

* nonemptiness and boundedness of the two reference-optimization sets are unconditional
  (`bipartiteMinEntropyOptSet_nonempty`, `bipartiteMinEntropyOptSet_bddAbove`); and
* strict positivity of the two `D_max` scalars follows from `Tr ρ / dA ≤ dmaxFeasibleLambda`
  (`dmaxFeasibleLambda_pos_of_ne_zero`), so it is implied by `τ ≠ 0` resp. `Ξ τ ≠ 0`.

For the pure core even those reduce further: the dilation, the layout cast and the `X`-measured
marginal are all trace-preserving (`zDilatedState_trace`, `xMeasuredMarginal_trace`), so the only
hypothesis left is `ρ_AB ≠ 0`.  The overlap positivity `0 < c` is likewise a theorem
(`overlapConst_pos`) and not a hypothesis.

`Ξ(τ) ≠ 0` genuinely *is* needed in the general-state layer: `W = U Vᴴ` annihilates the orthogonal
complement of the range of the `Z`-dilation, so a `τ` supported there has `Ξ(τ) = 0`, where the
sentinel makes the ℝ-valued left side unrelated to the right.

## Main statements

* `InfoTheory.SmoothMinEntropy.partialIsometryW_kron_opLe_one` — `(W ⊗ 1_B)ᴴ (W ⊗ 1_B) ⪯ 1`;
* `InfoTheory.SmoothMinEntropy.measDilateTransport` and
  `measDilateTransport_zDilatedState_eq_xMeasuredMarginal` — the state-level transport and the
  state form of the recovery `eqn:mo10`;
* `InfoTheory.SmoothMinEntropy.measDilateTransport_purifiedDistance_le` — its purified-distance
  data-processing inequality;
* `InfoTheory.SmoothMinEntropy.bipartiteMinEntropyOptReal_measDilateTransport_ge` — the
  general-state entropy transport;
* `InfoTheory.SmoothMinEntropy.measDilation_pure_core` — the `ε = 0` uncertainty relation.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## The measurement sub-isometry bound
-/

/-- The **measurement co-projector** `1 − V Vᴴ` is positive semidefinite: `V Vᴴ` is a Hermitian
idempotent (`(V Vᴴ)(V Vᴴ) = V (Vᴴ V) Vᴴ = V Vᴴ` by the isometry certificate `Vᴴ V = 1`,
`dilationIso_isometry`), so its complement `1 − V Vᴴ` is a projector, hence PSD. -/
lemma RankOneProjectiveBasis.dilationCoprojector_posSemidef {d : ℕ}
    (Q : RankOneProjectiveBasis d) :
    (1 - Q.dilationIso * (Q.dilationIso)ᴴ).PosSemidef := by
  set VVd : Op (d * d * d) := Q.dilationIso * (Q.dilationIso)ᴴ with hVVd
  have hVVherm : VVdᴴ = VVd := by
    rw [hVVd, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hVVidem : VVd * VVd = VVd := by
    rw [hVVd, Matrix.mul_assoc, ← Matrix.mul_assoc (Q.dilationIso)ᴴ, Q.dilationIso_isometry,
      Matrix.one_mul]
  have key : ((1 - VVd)ᴴ * (1 - VVd)) = 1 - VVd := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hVVherm]
    have expand : (1 - VVd) * (1 - VVd) = 1 - VVd - VVd + VVd * VVd := by noncomm_ring
    rw [expand, hVVidem]; abel
  have psd := Matrix.posSemidef_conjTranspose_mul_self (1 - VVd)
  rwa [key] at psd

/-- **The measurement sub-isometry bound** `(W ⊗ 1_B)ᴴ (W ⊗ 1_B) ⪯ 1`, `W = U Vᴴ`. Computes
`(W ⊗ 1)ᴴ (W ⊗ 1) = (Wᴴ W) ⊗ 1 = (V Vᴴ) ⊗ 1` (`partialIsometryW_dagger_mul_self_eq`), which is
dominated by `1 = 1 ⊗ 1` because `1 − V Vᴴ` is PSD (`dilationCoprojector_posSemidef`) and
tensoring with the PSD identity preserves the Löwner order. This is the certificate that turns the
measurement conjugation into a sub-density-operator map. -/
lemma partialIsometryW_kron_opLe_one {d dB : ℕ} (P Q : RankOneProjectiveBasis d) :
    opLe ((Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ *
          (Op.tensor (P.partialIsometryW Q) (1 : Op dB)))
      (1 : Op (d * d * d * dB)) := by
  have hWW : (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ *
      (Op.tensor (P.partialIsometryW Q) (1 : Op dB)) =
      Op.tensor (Q.dilationIso * (Q.dilationIso)ᴴ) (1 : Op dB) := by
    rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one, Op.tensor_mul,
      P.partialIsometryW_dagger_mul_self_eq Q, Matrix.one_mul]
  rw [hWW]
  apply opLe_of_posSemidef_sub
  have h1 : (1 : Op (d * d * d * dB)) =
      Op.tensor (1 : Op (d * d * d)) (1 : Op dB) := Op.tensor_one.symm
  rw [h1, ← Op.tensor_sub_left]
  exact Op.tensor_posSemidef_mathlib Q.dilationCoprojector_posSemidef Matrix.PosSemidef.one

/-!
## The state-level transport `Ξ = measConjTraceMap (U Vᴴ)`

The conjugation-trace map of `MeasurementDilation.lean` lifted to a map of **sub-density
operators** between the two entropy layouts: an arbitrary state `τ` on `Z ⊗ Z′AB`
(`d·(d·d·dB)`) is cast to the raw dilated register `d·d·d·dB`, conjugated by the measurement
sub-isometry `W ⊗ 1_B`, reordered, and traced over `X′ ⊗ A`, landing on `X ⊗ B` (`d·dB`).
Sub-normalization is inherited from the composed constructors; the only new certificate is the
sub-isometry bound `partialIsometryW_kron_opLe_one`.
-/

/-- **The state-level measurement transport** `Ξ(τ) = Tr_{X′A}( (W ⊗ 1_B) τ (W ⊗ 1_B)ᴴ )` on
`X ⊗ B`, for a state `τ` on `Z ⊗ Z′AB` and `W = U Vᴴ`. Its underlying operator is exactly
`measConjTraceMap (U Vᴴ)` of the cast state (`measDilateTransport_toOp`); this is the sub-channel
that carries a `Z`-side purified-distance ball member to an `X`-side ball member. -/
noncomputable def measDilateTransport {d dB : ℕ} (P Q : RankOneProjectiveBasis d)
    (τ : SubDensityOp (d * (d * d * dB))) : SubDensityOp (d * dB) :=
  SubDensityOp.partialTraceB
    (SubDensityOp.reindexHetero (measTraceReindex d dB)
      (SubDensityOp.subIsometryConjugate (Op.tensor (P.partialIsometryW Q) (1 : Op dB))
        (partialIsometryW_kron_opLe_one P Q)
        (SubDensityOp.castDim (by ring : d * (d * d * dB) = d * d * d * dB) τ)))

@[simp]
lemma measDilateTransport_toOp {d dB : ℕ} (P Q : RankOneProjectiveBasis d)
    (τ : SubDensityOp (d * (d * d * dB))) :
    (measDilateTransport P Q τ).toOp =
      measConjTraceMap (P.partialIsometryW Q)
        (Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB) τ.toOp) := by
  unfold measDilateTransport measConjTraceMap
  rw [SubDensityOp.partialTraceB_toOp, SubDensityOp.reindexHetero_toOp,
    SubDensityOp.subIsometryConjugate_toOp, SubDensityOp.castDim_toOp]

/-- **State-form recovery `eqn:mo10`.** The transport of the Z-dilated state is the `X`-measured
marginal: `Ξ(ρ_ZZ′AB) = ρ_XB`. This is the operator recovery
`measConjTraceMap_measDilate_eq_xMeasuredMarginal` after casting the entropy layout of
`zDilatedState` back to the raw dilated register. -/
theorem measDilateTransport_zDilatedState_eq_xMeasuredMarginal {d dB : ℕ}
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB)) :
    measDilateTransport P Q (zDilatedState Q ρAB) = xMeasuredMarginal P ρAB := by
  apply SubDensityOp.ext
  rw [measDilateTransport_toOp]
  have hcast : Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB)
      (zDilatedState Q ρAB).toOp = (measDilate Q ρAB).toOp := by
    unfold zDilatedState
    rw [SubDensityOp.castDim_toOp, Op.castDim_cancel]
  rw [hcast, measConjTraceMap_measDilate_eq_xMeasuredMarginal]

/-!
## Metric transport — the purified-distance DPI of the measurement sub-channel
-/

/-- **Purified-distance data processing under the measurement sub-channel `Ξ`.**

`P(Ξ ρ, Ξ τ) ≤ P(ρ, τ)`: the purified distance does not increase under the completely positive,
trace-non-increasing map `Ξ = measConjTraceMap (U Vᴴ)`.

Reduction: by `purifiedDistance_le_of_fidelityGen_ge` it suffices to prove the generalized-fidelity
DPI `fidelityGen ρ τ ≤ fidelityGen (Ξ ρ) (Ξ τ)`, which is
`SubDensityOp.fidelityGen_le_fidelityGen_cp_tni` applied to the raw map
`Φ = measConjTraceMap (U Vᴴ) ∘ castDim`. Its three channel certificates come from
`MeasurementDilationChannel.lean`, with the operator content
`partialIsometryW_kron_opLe_one` driving the trace non-increase. Because the repository's
purified distance is sub-density-native, no purification and no Uhlmann ball-lift is used here, so
no purifying-register dimension bookkeeping arises; the Uhlmann corner belongs to the distinct
conditioning-register invariance of `ConditioningIsometryInvariance.lean`. -/
theorem measDilateTransport_purifiedDistance_le {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (ρ τ : SubDensityOp (d * (d * d * dB))) :
    purifiedDistance (measDilateTransport P Q ρ) (measDilateTransport P Q τ) ≤
      purifiedDistance ρ τ := by
  have h : d * (d * d * dB) = d * d * d * dB := by ring
  set W : Op (d * d * d) := P.partialIsometryW Q with hW
  set Φ : Op (d * (d * d * dB)) → Op (d * dB) := fun A => measConjTraceMap W (Op.castDim h A)
    with hΦ
  have hΦlin : IsLinearMap ℂ Φ := by
    refine ⟨fun A B => ?_, fun c A => ?_⟩
    · simp only [hΦ]
      rw [Op.castDim_add, (measConjTraceMap_isLinearMap W).map_add]
    · simp only [hΦ]
      rw [Quantum.TensorProducts.Op.castDim_smul, (measConjTraceMap_isLinearMap W).map_smul]
  have hΦcp : Quantum.Channels.IsCompletelyPositive Φ := by
    have hcastCP : Quantum.Channels.IsCompletelyPositive (Op.castDim h) :=
      (Quantum.Channels.castDimLinear_isCPTP h).2.1
    exact Quantum.Channels.isCompletelyPositive_comp (measConjTraceMap W) (Op.castDim h)
      (measConjTraceMap_isCompletelyPositive W) hcastCP (measConjTraceMap_isLinearMap W)
  have hΦtni : ∀ A : Op (d * (d * d * dB)), A.PosSemidef → (Φ A).trace.re ≤ A.trace.re := by
    intro A hA
    have hWbound : opLe ((Op.tensor W (1 : Op dB))ᴴ * (Op.tensor W (1 : Op dB))) 1 :=
      partialIsometryW_kron_opLe_one P Q
    have hcastPSD : (Op.castDim h A).PosSemidef := Op.castDim_posSemidef h A hA
    calc (Φ A).trace.re = (measConjTraceMap W (Op.castDim h A)).trace.re := rfl
      _ ≤ (Op.castDim h A).trace.re := measConjTraceMap_trace_le W hWbound _ hcastPSD
      _ = A.trace.re := by rw [Op.castDim_trace]
  have hρ' : (measDilateTransport P Q ρ).toOp = Φ ρ.toOp := measDilateTransport_toOp P Q ρ
  have hτ' : (measDilateTransport P Q τ).toOp = Φ τ.toOp := measDilateTransport_toOp P Q τ
  have hfg := SubDensityOp.fidelityGen_le_fidelityGen_cp_tni Φ hΦlin hΦcp hΦtni
    ρ τ (measDilateTransport P Q ρ) (measDilateTransport P Q τ) hρ' hτ'
  exact purifiedDistance_le_of_fidelityGen_ge _ _ _ _ hfg

/-- **Ball transport at the same radius.** A state `τ` at purified distance `r` from the Z-dilated
state maps to a state at distance at most `r` from the `X`-measured marginal:

`P(ρ_XB, Ξ τ) = P(Ξ ρ_ZZ′AB, Ξ τ) ≤ P(ρ_ZZ′AB, τ)` .

Recovery (`measDilateTransport_zDilatedState_eq_xMeasuredMarginal`) followed by the data-processing
inequality. The radius is not inflated, so an ε-smoothing budget is not doubled by the transport. -/
theorem purifiedDistance_xMeasuredMarginal_measDilateTransport_le {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB))
    (τ : SubDensityOp (d * (d * d * dB))) :
    purifiedDistance (xMeasuredMarginal P ρAB) (measDilateTransport P Q τ) ≤
      purifiedDistance (zDilatedState Q ρAB) τ := by
  calc purifiedDistance (xMeasuredMarginal P ρAB) (measDilateTransport P Q τ)
      = purifiedDistance (measDilateTransport P Q (zDilatedState Q ρAB))
          (measDilateTransport P Q τ) := by
        rw [measDilateTransport_zDilatedState_eq_xMeasuredMarginal]
    _ ≤ purifiedDistance (zDilatedState Q ρAB) τ :=
        measDilateTransport_purifiedDistance_le P Q _ _

/-!
## The `D_max` transport
-/

/-- **Per-reference feasibility transport.** If `s` is `D_max`-feasible for a state `τ` on the
Z-side against `1_Z ⊗ σ`, then `s · c` is `D_max`-feasible for its transport `Ξ(τ)` against
`1_X ⊗ σ_B` (`σ_B = Tr_{Z′A} σ`, `c = overlapConst P Q`). Casts the entropy-layout feasibility to
the raw dilated register and applies `measDilation_mo6` to the definitional image. -/
lemma dmaxIsFeasible_measDilateTransport_of_feasible {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (τ : SubDensityOp (d * (d * d * dB)))
    (σ : Op (d * d * dB)) (hσ : σ.PosSemidef) {s : ℝ}
    (ht : dmaxIsFeasible τ.toOp (Op.tensor (1 : Op d) σ) s) :
    dmaxIsFeasible (measDilateTransport P Q τ).toOp
      (Op.tensor (1 : Op d) (Quantum.TensorProducts.partialTraceA σ)) (s * P.overlapConst Q) := by
  obtain ⟨hs, hle⟩ := ht
  set h : d * (d * d * dB) = d * d * d * dB := by ring
  refine ⟨mul_nonneg hs (P.overlapConst_nonneg Q), ?_⟩
  have hcast : opLe (Op.castDim h τ.toOp)
      (Complex.ofReal s • Op.castDim h (Op.tensor (1 : Op d) σ)) := by
    rw [← Quantum.TensorProducts.Op.castDim_smul]
    exact (opLe_castDim_iff h).mpr hle
  have hmo6 := measDilation_mo6 P Q hs σ hσ (Op.castDim h τ.toOp) hcast
  rwa [measDilateTransport_toOp]

/-- **`D_max` scalar transport.** `dmax_X(Ξ τ) ≤ c · dmax_Z(τ)`: the transported `D_max` scalar is
at most `c` times the Z-side one, for a genuinely feasible Z-side reference. Together with
`0 < c` (`overlapConst_pos`) this is the scalar form of the uncertainty relation; `−log₂` turns it
into the entropy statement. -/
lemma dmaxFeasibleLambda_measDilateTransport_le {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (τ : SubDensityOp (d * (d * d * dB)))
    (σ : Op (d * d * dB)) (hσ : σ.PosSemidef)
    (hZ : hasDmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ)) :
    dmaxFeasibleLambda (measDilateTransport P Q τ).toOp
        (Op.tensor (1 : Op d) (Quantum.TensorProducts.partialTraceA σ)) ≤
      P.overlapConst Q * dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ) := by
  have hc : 0 < P.overlapConst Q := P.overlapConst_pos Q
  set dmaxX := dmaxFeasibleLambda (measDilateTransport P Q τ).toOp
    (Op.tensor (1 : Op d) (Quantum.TensorProducts.partialTraceA σ)) with hXdef
  have key : ∀ s, dmaxIsFeasible τ.toOp (Op.tensor (1 : Op d) σ) s →
      dmaxX ≤ s * P.overlapConst Q := by
    intro s hsf
    rw [hXdef]
    exact dmaxFeasibleLambda_le_of_feasible _ _
      (dmaxIsFeasible_measDilateTransport_of_feasible P Q τ σ hσ hsf)
  have hle : dmaxX / P.overlapConst Q ≤ dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ) := by
    refine le_csInf hZ ?_
    intro s hsf
    rw [div_le_iff₀ hc]
    exact key s hsf
  rw [div_le_iff₀ hc] at hle
  rwa [mul_comm] at hle

/-- **The `X`-side reference is admissible.** A `D_max`-feasible Z-side reference `σ` transports to
the feasible `X`-side reference `σ_B = Tr_{Z′A} σ`, so `σ_B` participates in the guarded
`X`-side optimization. -/
lemma hasDmaxFeasibleLambda_measDilateTransport {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (τ : SubDensityOp (d * (d * d * dB)))
    (σ : Op (d * d * dB)) (hσ : σ.PosSemidef)
    (hZ : hasDmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ)) :
    hasDmaxFeasibleLambda (measDilateTransport P Q τ).toOp
      (Op.tensor (1 : Op d) (Quantum.TensorProducts.partialTraceA σ)) := by
  obtain ⟨s, hsf⟩ := hZ
  exact ⟨s * P.overlapConst Q, dmaxIsFeasible_measDilateTransport_of_feasible P Q τ σ hσ hsf⟩

/-!
## The entropy-level transport
-/

/-- **Per-reference entropy lift.** `H_min(Z|Z′AB)_{τ|σ} + q ≤ H_min(X|B)_{Ξτ|σ_B}`, for a
genuinely feasible Z-side reference and finite-positive `D_max` on both sides (the ℝ-encoding
excluding the `Real.log 0 = 0` sentinel). It is `−log₂` of the scalar transport
`dmaxFeasibleLambda_measDilateTransport_le`. -/
theorem bipartiteMinEntropyReal_measDilateTransport_ge {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (τ : SubDensityOp (d * (d * d * dB)))
    (σ : SubDensityOp (d * d * dB))
    (hZfeas : hasDmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ.toOp))
    (hposZ : 0 < dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ.toOp))
    (hposX : 0 < dmaxFeasibleLambda (measDilateTransport P Q τ).toOp
      (Op.tensor (1 : Op d) (SubDensityOp.partialTraceA σ).toOp)) :
    bipartiteMinEntropyReal τ σ + P.preparationQuality Q ≤
      bipartiteMinEntropyReal (measDilateTransport P Q τ) (SubDensityOp.partialTraceA σ) := by
  have hc : 0 < P.overlapConst Q := P.overlapConst_pos Q
  have hσpsd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hkey : dmaxFeasibleLambda (measDilateTransport P Q τ).toOp
      (Op.tensor (1 : Op d) (SubDensityOp.partialTraceA σ).toOp) ≤
      P.overlapConst Q * dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ.toOp) := by
    simpa only [SubDensityOp.partialTraceA_toOp] using
      dmaxFeasibleLambda_measDilateTransport_le P Q τ σ.toOp hσpsd hZfeas
  have hlog : Real.log (dmaxFeasibleLambda (measDilateTransport P Q τ).toOp
        (Op.tensor (1 : Op d) (SubDensityOp.partialTraceA σ).toOp)) ≤
      Real.log (dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op d) σ.toOp)) +
        Real.log (P.overlapConst Q) := by
    rw [← Real.log_mul (ne_of_gt hposZ) (ne_of_gt hc)]
    apply Real.log_le_log hposX
    rw [mul_comm (P.overlapConst Q)] at hkey
    exact hkey
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold bipartiteMinEntropyReal RankOneProjectiveBasis.preparationQuality
  rw [← add_div, div_le_div_iff_of_pos_right h2]
  linarith [hlog]

/-- **The general-state entropy transport (OPT level).**

`H_min(Z|Z′AB)_τ ≤ H_min(X|B)_{Ξτ} − q` on the guarded reference-optimized bipartite conditional
min-entropies, for an arbitrary Z-side state `τ` and its measurement transport `Ξ(τ)`.

The two hypotheses are exactly the nondegeneracy the ℝ-valued encoding needs: `τ ≠ 0` and
`Ξ τ ≠ 0` exclude the `Real.log 0 = 0` sentinel on the two sides
(`dmaxFeasibleLambda_pos_of_ne_zero`). Nonemptiness of the Z-side and boundedness of the X-side
optimization set are unconditional (`bipartiteMinEntropyOptSet_nonempty`,
`bipartiteMinEntropyOptSet_bddAbove`), and the overlap positivity `0 < c` is a theorem
(`overlapConst_pos`), so none of these is carried as a hypothesis. -/
theorem bipartiteMinEntropyOptReal_measDilateTransport_ge {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (τ : SubDensityOp (d * (d * d * dB)))
    (hτ : τ.toOp ≠ 0) (hΞτ : (measDilateTransport P Q τ).toOp ≠ 0) :
    bipartiteMinEntropyOptReal τ ≤
      bipartiteMinEntropyOptReal (measDilateTransport P Q τ) - P.preparationQuality Q := by
  rw [bipartiteMinEntropyOptReal_eq_sSup, bipartiteMinEntropyOptReal_eq_sSup]
  apply csSup_le (bipartiteMinEntropyOptSet_nonempty τ)
  rintro hZval ⟨σ, hσfeas, rfl⟩
  have hσpsd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hXadmiss : hasDmaxFeasibleLambda (measDilateTransport P Q τ).toOp
      (Op.tensor (1 : Op d) (SubDensityOp.partialTraceA σ).toOp) := by
    simpa only [SubDensityOp.partialTraceA_toOp] using
      hasDmaxFeasibleLambda_measDilateTransport P Q τ σ.toOp hσpsd hσfeas
  have hXmem : bipartiteMinEntropyReal (measDilateTransport P Q τ) (SubDensityOp.partialTraceA σ) ∈
      bipartiteMinEntropyOptSet (measDilateTransport P Q τ) :=
    ⟨SubDensityOp.partialTraceA σ, hXadmiss, rfl⟩
  have hlift := bipartiteMinEntropyReal_measDilateTransport_ge P Q τ σ hσfeas
    (dmaxFeasibleLambda_pos_of_ne_zero τ hτ σ hσfeas)
    (dmaxFeasibleLambda_pos_of_ne_zero (measDilateTransport P Q τ) hΞτ
      (SubDensityOp.partialTraceA σ) hXadmiss)
  have hXle : bipartiteMinEntropyReal (measDilateTransport P Q τ) (SubDensityOp.partialTraceA σ) ≤
      sSup (bipartiteMinEntropyOptSet (measDilateTransport P Q τ)) :=
    le_csSup (bipartiteMinEntropyOptSet_bddAbove (measDilateTransport P Q τ)) hXmem
  linarith [hlift, hXle]

/-- A sub-density operator with positive trace is nonzero. -/
private lemma subDensity_ne_zero_of_trace_pos {n : ℕ} (ρ : SubDensityOp n) (h : 0 < ρ.trace) :
    ρ.toOp ≠ 0 := by
  intro h0
  rw [SubDensityOp.trace, h0, Matrix.trace_zero, Complex.zero_re] at h
  exact lt_irrefl 0 h

/-- **The `ε = 0` entropic uncertainty relation** (arXiv:1504.00233, `apps.tex:198`,
`\label{eq:ucr-dual}`, at `α = ∞`):

`H_min(Z|Z′AB)_ρ ≤ H_min(X|B)_ρ − q` ,   `q = log₂(1/c)` ,   `c = overlapConst P Q` ,

on the guarded reference-optimized bipartite conditional min-entropies, for the `Z`-dilated state
and the `X`-measured marginal of an arbitrary sub-normalized `ρ_AB`.

Only `ρ_AB ≠ 0` is assumed. Both `D_max` nondegeneracy conditions follow from it, because the
dilation and the measured marginal are trace-preserving (`zDilatedState_trace`,
`xMeasuredMarginal_trace`); the overlap positivity `0 < c` is `overlapConst_pos`; and the
nonemptiness/boundedness of the two optimization sets are unconditional. This is *not* the
tripartite relation `th:ur`: the two conditioning registers here come from the same memory (see
the module docstring). -/
theorem measDilation_pure_core {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB)) (hρ : ρAB.toOp ≠ 0) :
    bipartiteMinEntropyOptReal (zDilatedState Q ρAB) ≤
      bipartiteMinEntropyOptReal (xMeasuredMarginal P ρAB) - P.preparationQuality Q := by
  have htr : 0 < ρAB.trace := subDensity_trace_re_pos ρAB hρ
  have hrec : measDilateTransport P Q (zDilatedState Q ρAB) = xMeasuredMarginal P ρAB :=
    measDilateTransport_zDilatedState_eq_xMeasuredMarginal P Q ρAB
  have hZ : (zDilatedState Q ρAB).toOp ≠ 0 :=
    subDensity_ne_zero_of_trace_pos _ (by rw [zDilatedState_trace]; exact htr)
  have hX : (measDilateTransport P Q (zDilatedState Q ρAB)).toOp ≠ 0 := by
    rw [hrec]
    exact subDensity_ne_zero_of_trace_pos _ (by rw [xMeasuredMarginal_trace]; exact htr)
  have h := bipartiteMinEntropyOptReal_measDilateTransport_ge P Q (zDilatedState Q ρAB) hZ hX
  rwa [hrec] at h

/-!
## The nonvanishing hypothesis cannot be dropped

At `ρ_AB = 0` the ℝ-valued encoding returns the `Real.log 0 = 0` sentinel on *both* sides —
the true value is `H_min = +∞` — so the inequality would read `0 ≤ 0 − q`, which fails for every
pair of bases with `q > 0`, i.e. whenever the two measurements are not identical up to phases.
Concrete witnesses with `q > 0` are supplied by `ConcreteMeasurementBases.lean`
(`preparationQuality_computational_walsh`, `q = n`), so the counterexample is not vacuous.
-/

/-- The zero state has guarded reference-optimized min-entropy `0`: every reference is feasible
with scalar `0`, so `dmaxFeasibleLambda = 0` and the `Real.log 0 = 0` sentinel fires uniformly. -/
theorem bipartiteMinEntropyOptReal_zero {dA dC : ℕ} [NeZero dA] [NeZero dC] :
    bipartiteMinEntropyOptReal (0 : SubDensityOp (dA * dC)) = 0 := by
  have hval : ∀ σ : SubDensityOp dC,
      bipartiteMinEntropyReal (0 : SubDensityOp (dA * dC)) σ = 0 := by
    intro σ
    have hfeas : dmaxIsFeasible (0 : SubDensityOp (dA * dC)).toOp
        (Op.tensor (1 : Op dA) σ.toOp) 0 := by
      refine ⟨le_refl 0, ?_⟩
      change opLe (0 : Op (dA * dC)) _
      rw [Complex.ofReal_zero, zero_smul]
      exact opLe_refl 0
    have hzero : dmaxFeasibleLambda (0 : SubDensityOp (dA * dC)).toOp
        (Op.tensor (1 : Op dA) σ.toOp) = 0 :=
      le_antisymm (dmaxFeasibleLambda_le_of_feasible _ _ hfeas) (dmaxFeasibleLambda_nonneg _ _)
    unfold bipartiteMinEntropyReal
    rw [hzero, Real.log_zero, neg_zero, zero_div]
  rw [bipartiteMinEntropyOptReal_eq_sSup]
  obtain ⟨v, hv⟩ := bipartiteMinEntropyOptSet_nonempty (0 : SubDensityOp (dA * dC))
  have hset : bipartiteMinEntropyOptSet (0 : SubDensityOp (dA * dC)) = {0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    obtain ⟨σ, hσ, rfl⟩ := hv
    exact ⟨⟨σ, hσ, (hval σ).symm⟩, by rintro h ⟨σ', hσ', rfl⟩; exact hval σ'⟩
  rw [hset, csSup_singleton]

/-- **The `ε = 0` uncertainty relation genuinely needs `ρ_AB ≠ 0`.** For any pair of measurements
with positive preparation quality the conclusion of `measDilation_pure_core` fails at
`ρ_AB = 0`: both sides collapse to the `Real.log 0 = 0` sentinel, leaving `0 ≤ −q`. -/
theorem measDilation_pure_core_fails_at_zero {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (hq : 0 < P.preparationQuality Q) :
    ¬ (bipartiteMinEntropyOptReal (zDilatedState Q (0 : SubDensityOp (d * dB))) ≤
        bipartiteMinEntropyOptReal (xMeasuredMarginal P (0 : SubDensityOp (d * dB)))
          - P.preparationQuality Q) := by
  have hcast0 : ∀ {n m : ℕ} (h : n = m), Op.castDim h (0 : Op n) = (0 : Op m) := by
    intro n m h; subst h; rfl
  have hzeroOp : ((0 : SubDensityOp (d * dB)) : SubDensityOp (d * dB)).toOp
      = (0 : Op (d * dB)) := rfl
  have hZ : zDilatedState Q (0 : SubDensityOp (d * dB)) = 0 := by
    apply SubDensityOp.ext
    rw [zDilatedState, SubDensityOp.castDim_toOp, measDilate_toOp, hzeroOp,
      Matrix.mul_zero, Matrix.zero_mul, hcast0]
    rfl
  have hX : xMeasuredMarginal P (0 : SubDensityOp (d * dB)) = 0 := by
    apply SubDensityOp.ext
    rw [xMeasuredMarginal, SubDensityOp.partialTraceB_toOp, SubDensityOp.reindexHetero_toOp,
      measDilate_toOp, hzeroOp, Matrix.mul_zero, Matrix.zero_mul]
    have hre : Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB)
        (0 : Op (d * d * d * dB)) = 0 := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hre]
    ext i j
    simp [Quantum.TensorProducts.partialTraceB]
  rw [hZ, hX, bipartiteMinEntropyOptReal_zero, bipartiteMinEntropyOptReal_zero]
  push_neg
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
