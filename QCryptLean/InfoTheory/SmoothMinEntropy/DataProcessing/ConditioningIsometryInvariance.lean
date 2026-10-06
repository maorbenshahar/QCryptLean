import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothBipartite
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.IsometryConjugation
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.LeftIsometryPenaltyEmbedding
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.FidelityGenCPTNI
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order
import QCryptLean.Quantum.TensorProducts.CastDim

/-!
# Min-entropy invariance under left-isometry embedding of the conditioning register

The purification-independence workhorse for the Tomamichel–Renner duality-defined smooth
max-entropy (as used in the duality-defined smooth max-entropy construction): any two purifications
`ρ_ABC`, `ρ_ABC'` of the same
`ρ_AB` differ by a left-isometry embedding `V : C → C'` of the conditioning register
(`|ψ'⟩ = (1_AB ⊗ V)|ψ⟩`, Uhlmann), under which `ρ_AC' = (1_A ⊗ V) ρ_AC (1_A ⊗ V)ᴴ`. This module
proves that the conditional min-entropy `H_min(A|C)`, and its ε-smooth form, are invariant under
that embedding — so `H_max^ε(A|B) := −H_min^ε(A|C)` does not depend on the choice of purification.

## Layering

* **Operator layer (proved, from the `IsometryConjugation.lean` family).** The `D_max` SDP
  scalar `dmaxFeasibleLambda` is invariant under conjugation by any left isometry `K` (`Kᴴ K = 1`):
  `dmaxFeasibleLambda (K ρ Kᴴ) (K Q Kᴴ) = dmaxFeasibleLambda ρ Q`
  (`dmaxFeasibleLambda_leftIsometryConjugate_eq`), the feasible-set-equality core.
* **Fixed-reference layer.** `bipartiteMinEntropyReal` is invariant under embedding the
  conditioning register `C` by `V` with the reference transported as `σ ↦ V σ Vᴴ`
  (`bipartiteMinEntropyReal_conditioning_leftIsometryEmbed_eq`).
* **Metric layer.** Generalized fidelity and purified distance are invariant under
  left-isometry conjugation (`purifiedDistance_leftIsometryConjugate_eq`), via the
  `fidelity_isometry_conj_of_toOp_eq`.
* **Reference-optimized layer.** The σ-optimized
  `bipartiteMinEntropyOptReal` invariance
  (`bipartiteMinEntropyOptReal_conditioning_leftIsometryEmbed_eq`): the `≤` direction (every
  reference on `C` lifts to `C'`) is elementary from the fixed-reference layer; the `≥` direction
  projects an arbitrary reference `τ` on `C'` down to `Vᴴ τ V` on `C` via the `D_max`-monotone
  co-isometry pullback (`bipartiteMinEntropyOptReal_le_pullback`).
* **Smooth layer.** The workhorse
  `smoothBipartiteMinEntropyOptReal_conditioning_leftIsometryEmbed_eq`: the isometry-lift `≤`
  direction reduces to the reference-optimized `≤` over the purified-distance ball (using metric
  invariance); the `≥` direction pulls back an arbitrary ball element `τ` by the `Π = 1_A ⊗ V Vᴴ`
  pinch (purified-distance data-processing), with the support-orthogonal degenerate subcase
  (`ρpb = 0`) handled by the orthogonal-support generalized-fidelity computation and a scaled
  maximally-mixed ball witness.

## Dimension hypotheses

All statements carry explicit source/target dimension arguments `dC`, `dC'` and the explicit
left-isometry hypothesis `Vᴴ V = 1`. No smooth-isometry invariance is imported wholesale; the
smooth layer's genuine analytic content (`co:smooth-iso`) is proved from named operator/metric
lemmas, not assumed.

Application: purification-independence for the duality-free finite-key smooth EUR
(TLGR, arXiv:1103.4130); it certifies that `smoothMaxEntropyDual` is
well-defined regardless of the choice of purification.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Rectangular left-isometry conjugation of a sub-density operator
-/

/-- Conjugate a sub-density operator by a rectangular left isometry `K` (`Kᴴ K = 1`):
`ρ ↦ K · ρ · Kᴴ`. The result is again sub-normalized: conjugation preserves positive
semidefiniteness, and `Tr(K ρ Kᴴ) = Tr(ρ Kᴴ K) = Tr(ρ) ≤ 1` by the isometry identity. This is the
rectangular generalization of `SubDensityOp.unitaryConjugate`, used to embed the conditioning
register of a bipartite state. -/
noncomputable def SubDensityOp.leftIsometryConjugate {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ : SubDensityOp dSrc) :
    SubDensityOp dTgt where
  toOp := K * ρ.toOp * Kᴴ
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same K).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same K) v
  trace_le_one := by
    have htr : (K * ρ.toOp * Kᴴ).trace = ρ.toOp.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hK, Matrix.one_mul]
    change (K * ρ.toOp * Kᴴ).trace.re ≤ 1
    rw [htr]
    exact ρ.trace_le_one

@[simp]
lemma SubDensityOp.leftIsometryConjugate_toOp {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ : SubDensityOp dSrc) :
    (ρ.leftIsometryConjugate K hK).toOp = K * ρ.toOp * Kᴴ :=
  rfl

/-- The real-valued trace is preserved under left-isometry conjugation:
`Tr(K ρ Kᴴ) = Tr(ρ)`. -/
lemma SubDensityOp.leftIsometryConjugate_trace {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ : SubDensityOp dSrc) :
    (ρ.leftIsometryConjugate K hK).trace = ρ.trace := by
  change (K * ρ.toOp * Kᴴ).trace.re = ρ.toOp.trace.re
  congr 1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hK, Matrix.one_mul]

/-- Conjugate a sub-density operator by a rectangular sub-isometry `K` (`Kᴴ K ≤ 1`):
`ρ ↦ K · ρ · Kᴴ`. Sub-normalized: conjugation preserves positive semidefiniteness, and the trace
is non-increasing because `Tr(K ρ Kᴴ) = Tr(ρ · Kᴴ K) ≤ Tr(ρ · 1) = Tr ρ`. Generalizes
`SubDensityOp.leftIsometryConjugate` (which needs `Kᴴ K = 1`) to the trace-non-increasing case.
This is the co-isometry pullback `ρ̃ = (1_A ⊗ Vᴴ) τ̃ (1_A ⊗ V)` used by the pinch `≥` direction of
the conditioning-register invariance. -/
noncomputable def SubDensityOp.subIsometryConjugate {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : opLe (Kᴴ * K) 1) (ρ : SubDensityOp dSrc) :
    SubDensityOp dTgt where
  toOp := K * ρ.toOp * Kᴴ
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same K).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same K) v
  trace_le_one := by
    have hρpsd : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    have hcyc : (K * ρ.toOp * Kᴴ).trace = (ρ.toOp * (Kᴴ * K)).trace := by
      rw [Matrix.trace_mul_cycle K ρ.toOp Kᴴ, Matrix.trace_mul_comm]
    rw [hcyc]
    calc (ρ.toOp * (Kᴴ * K)).trace.re
        ≤ (ρ.toOp * (1 : Op dSrc)).trace.re :=
          trace_mul_le_of_opLe hρpsd
            (Matrix.posSemidef_conjTranspose_mul_self K).isHermitian Matrix.isHermitian_one hK
      _ = ρ.toOp.trace.re := by rw [Matrix.mul_one]
      _ ≤ 1 := ρ.trace_le_one

@[simp]
lemma SubDensityOp.subIsometryConjugate_toOp {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : opLe (Kᴴ * K) 1) (ρ : SubDensityOp dSrc) :
    (ρ.subIsometryConjugate K hK).toOp = K * ρ.toOp * Kᴴ :=
  rfl

/-- The rectangular embedding `1_A ⊗ V` of a left isometry `V` (`kronIdLeftIso`, the matrix
`I_{dA} ⊗ V : Matrix (Fin (dA·dC')) (Fin (dA·dC)) ℂ`) is again a left isometry — this is the
`kronIdLeftIso_left_iso`. **Reference-transport mixed-product identity:** the transported
reference `1_A ⊗ (V M Vᴴ)` (a square `Op.tensor`) equals the `(1_A ⊗ V)`-conjugate of `1_A ⊗ M`:
`1_A ⊗ (V M Vᴴ) = (1_A ⊗ V) (1_A ⊗ M) (1_A ⊗ V)ᴴ`,
the Kronecker mixed-product identity that lets the fixed-reference embedding reuse the general
left-isometry `D_max` invariance. -/
lemma tensor_one_conj_reference {dA dC dC' : ℕ}
    (V : Matrix (Fin dC') (Fin dC) ℂ) (M : Op dC) :
    Quantum.TensorProducts.Op.tensor (1 : Op dA) (V * M * Vᴴ) =
      kronIdLeftIso (dH := dA) V * Quantum.TensorProducts.Op.tensor (1 : Op dA) M *
        (kronIdLeftIso (dH := dA) V)ᴴ := by
  simp only [kronIdLeftIso, Quantum.TensorProducts.Op.tensor, Matrix.reindex_apply]
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]

/-- The conjugate transpose commutes with `1_A ⊗ ·`: `(1_A ⊗ V)ᴴ = 1_A ⊗ Vᴴ`. -/
lemma kronIdLeftIso_conjTranspose {dH dSrc dTgt : ℕ} (V : Matrix (Fin dTgt) (Fin dSrc) ℂ) :
    (kronIdLeftIso (dH := dH) V)ᴴ = kronIdLeftIso (dH := dH) Vᴴ := by
  dsimp [kronIdLeftIso, Matrix.reindex]
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- **Reference-transport mixed-product identity for the co-isometry pullback.** The transported
reference `1_A ⊗ (Vᴴ M V)` equals the `(1_A ⊗ V)ᴴ`-conjugate (pullback) of `1_A ⊗ M`:
`1_A ⊗ (Vᴴ M V) = (1_A ⊗ V)ᴴ (1_A ⊗ M) (1_A ⊗ V)`.
Dual to `tensor_one_conj_reference`, obtained from it by `kronIdLeftIso_conjTranspose`. -/
lemma tensor_one_pullback_reference {dA dC dC' : ℕ}
    (V : Matrix (Fin dC') (Fin dC) ℂ) (M : Op dC') :
    Quantum.TensorProducts.Op.tensor (1 : Op dA) (Vᴴ * M * V) =
      (kronIdLeftIso (dH := dA) V)ᴴ * Quantum.TensorProducts.Op.tensor (1 : Op dA) M *
        kronIdLeftIso (dH := dA) V := by
  have h := tensor_one_conj_reference (dA := dA) Vᴴ M
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [h, kronIdLeftIso_conjTranspose, kronIdLeftIso_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

/-!
## Operator layer: `D_max` invariance under left-isometry conjugation
-/

/-- **`D_max`-feasibility transfer under left-isometry conjugation.** For a rectangular left
isometry `K` (`Kᴴ K = 1`), a scalar `t` is `D_max`-feasible for `(K ρ Kᴴ, K Q Kᴴ)` iff it is
`D_max`-feasible for `(ρ, Q)`. The forward direction reflects the Löwner bound through `K`
(`opLe_of_conj_opLe`), the reverse pushes it through `K` (`Quantum.Channels.opLe_kraus_sandwich`);
both are provided in
the `IsometryConjugation.lean` family. -/
lemma dmaxIsFeasible_leftIsometryConjugate_iff {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ Q : Op dSrc) (t : ℝ) :
    dmaxIsFeasible (K * ρ * Kᴴ) (K * Q * Kᴴ) t ↔ dmaxIsFeasible ρ Q t := by
  have hsmul : Complex.ofReal t • (K * Q * Kᴴ) = K * (Complex.ofReal t • Q) * Kᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rintro ⟨ht_nn, hle⟩
    refine ⟨ht_nn, ?_⟩
    rw [hsmul] at hle
    exact opLe_of_conj_opLe K hK hle
  · rintro ⟨ht_nn, hle⟩
    refine ⟨ht_nn, ?_⟩
    have h := Quantum.Channels.opLe_kraus_sandwich K hle
    rwa [← hsmul] at h

/-- **`D_max` SDP-scalar invariance under left-isometry conjugation.** For a rectangular left
isometry `K` (`Kᴴ K = 1`), the `D_max`-feasible sets of `(K ρ Kᴴ, K Q Kᴴ)` and `(ρ, Q)` coincide,
hence so do their infima:
`dmaxFeasibleLambda (K ρ Kᴴ) (K Q Kᴴ) = dmaxFeasibleLambda ρ Q`. -/
theorem dmaxFeasibleLambda_leftIsometryConjugate_eq {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ Q : Op dSrc) :
    dmaxFeasibleLambda (K * ρ * Kᴴ) (K * Q * Kᴴ) = dmaxFeasibleLambda ρ Q := by
  have hset : Set.ofPred (dmaxIsFeasible (K * ρ * Kᴴ) (K * Q * Kᴴ)) =
      Set.ofPred (dmaxIsFeasible ρ Q) := by
    ext t
    exact dmaxIsFeasible_leftIsometryConjugate_iff K hK ρ Q t
  unfold dmaxFeasibleLambda
  rw [hset]

/-!
## Fixed-reference layer: `H_min(A|C)_{ρ|σ}` invariance
-/

/-- **Fixed-reference min-entropy invariance under conditioning-register embedding.** Embedding the
conditioning register `C ↪ C'` of a bipartite state `ρ_AC` by a left isometry `V` (`Vᴴ V = 1`),
while transporting the reference `σ ↦ V σ Vᴴ`, leaves the fixed-reference conditional min-entropy
unchanged:
`H_min(A|C')_{(1⊗V)ρ(1⊗V)ᴴ | VσVᴴ} = H_min(A|C)_{ρ|σ}`.
This is the `D_max` invariance (`dmaxFeasibleLambda_leftIsometryConjugate_eq`, `K = 1_A ⊗ V`) after
identifying the transported reference `1_A ⊗ VσVᴴ = (1_A⊗V)(1_A⊗σ)(1_A⊗V)ᴴ`. -/
theorem bipartiteMinEntropyReal_conditioning_leftIsometryEmbed_eq {dA dC dC' : ℕ}
    (V : Matrix (Fin dC') (Fin dC) ℂ) (hV : Vᴴ * V = 1)
    (ρ : SubDensityOp (dA * dC)) (σ : SubDensityOp dC) :
    bipartiteMinEntropyReal
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV))
        (σ.leftIsometryConjugate V hV) =
      bipartiteMinEntropyReal ρ σ := by
  unfold bipartiteMinEntropyReal
  rw [SubDensityOp.leftIsometryConjugate_toOp, SubDensityOp.leftIsometryConjugate_toOp,
    tensor_one_conj_reference V σ.toOp,
    dmaxFeasibleLambda_leftIsometryConjugate_eq
      (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV)
      ρ.toOp (Quantum.TensorProducts.Op.tensor (1 : Op dA) σ.toOp)]

/-!
## Metric layer: purified-distance invariance under left-isometry conjugation
-/

/-- **Generalized-fidelity invariance under left-isometry conjugation.** For a left isometry `K`
(`Kᴴ K = 1`), `F*(K ρ Kᴴ, K σ Kᴴ) = F*(ρ, σ)`: the Uhlmann fidelity is invariant by the
`fidelity_isometry_conj_of_toOp_eq`, and the sub-normalization correction is invariant because the
trace is preserved (`SubDensityOp.leftIsometryConjugate_trace`). -/
theorem fidelityGen_leftIsometryConjugate_eq {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ σ : SubDensityOp dSrc) :
    fidelityGen (ρ.leftIsometryConjugate K hK) (σ.leftIsometryConjugate K hK) =
      fidelityGen ρ σ := by
  unfold fidelityGen
  rw [SubDensityOp.leftIsometryConjugate_trace, SubDensityOp.leftIsometryConjugate_trace]
  congr 1
  exact Quantum.Metrics.fidelity_isometry_conj_of_toOp_eq K ρ.toPosSemidefOp σ.toPosSemidefOp
    (ρ.leftIsometryConjugate K hK).toPosSemidefOp (σ.leftIsometryConjugate K hK).toPosSemidefOp
    hK rfl rfl

/-- **Purified-distance invariance under left-isometry conjugation.** For a left isometry `K`
(`Kᴴ K = 1`), `P(K ρ Kᴴ, K σ Kᴴ) = P(ρ, σ)`. Immediate from
`fidelityGen_leftIsometryConjugate_eq`. This is the metric input for the smooth-layer isometry-lift
direction: an ε-ball element of `ρ` maps to an ε-ball element of the embedded state. -/
theorem purifiedDistance_leftIsometryConjugate_eq {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : Kᴴ * K = 1) (ρ σ : SubDensityOp dSrc) :
    purifiedDistance (ρ.leftIsometryConjugate K hK) (σ.leftIsometryConjugate K hK) =
      purifiedDistance ρ σ := by
  unfold purifiedDistance
  rw [fidelityGen_leftIsometryConjugate_eq]

/-- **Generalized fidelity is non-decreasing under sub-isometry conjugation.** For a rectangular
sub-isometry `K` (`Kᴴ K ≤ 1`), conjugation `ρ ↦ K ρ Kᴴ` is a completely-positive
trace-non-increasing map (single Kraus `K`, trace non-increase from `Kᴴ K ≤ 1`), so generalized
fidelity does not decrease: `F*(ρ, σ) ≤ F*(K ρ Kᴴ, K σ Kᴴ)`. Direct instance of the CP-TNI
DPI `SubDensityOp.fidelityGen_le_fidelityGen_cp_tni`; this is the co-isometry-pullback analogue of
the left-isometry equality `fidelityGen_leftIsometryConjugate_eq`. -/
theorem fidelityGen_le_subIsometryConjugate {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : opLe (Kᴴ * K) 1) (ρ σ : SubDensityOp dSrc) :
    fidelityGen ρ σ ≤
      fidelityGen (ρ.subIsometryConjugate K hK) (σ.subIsometryConjugate K hK) := by
  set Φ : Op dSrc → Op dTgt := fun A => K * A * Kᴴ with hΦ
  have hΦlin : IsLinearMap ℂ Φ := by
    refine ⟨fun A B => ?_, fun c A => ?_⟩
    · simp only [hΦ, Matrix.mul_add, Matrix.add_mul]
    · simp only [hΦ, Matrix.mul_smul, Matrix.smul_mul]
  have hΦcp : Quantum.Channels.IsCompletelyPositive Φ :=
    isCompletelyPositive_of_kraus_sum (fun _ : Unit => K) Φ (fun A => by simp [hΦ])
  have hΦtni : ∀ A : Op dSrc, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re := by
    intro A hA
    have hcyc : (K * A * Kᴴ).trace = (A * (Kᴴ * K)).trace := by
      rw [Matrix.trace_mul_cycle K A Kᴴ, Matrix.trace_mul_comm]
    calc (Φ A).trace.re = (A * (Kᴴ * K)).trace.re := by rw [hΦ]; rw [hcyc]
      _ ≤ (A * (1 : Op dSrc)).trace.re :=
          trace_mul_le_of_opLe hA (Matrix.posSemidef_conjTranspose_mul_self K).isHermitian
            Matrix.isHermitian_one hK
      _ = A.trace.re := by rw [Matrix.mul_one]
  exact SubDensityOp.fidelityGen_le_fidelityGen_cp_tni Φ hΦlin hΦcp hΦtni ρ σ _ _ rfl rfl

/-- **Purified distance is non-increasing under sub-isometry conjugation.** For a rectangular
sub-isometry `K` (`Kᴴ K ≤ 1`), `P(K ρ Kᴴ, K σ Kᴴ) ≤ P(ρ, σ)`. Immediate from
`fidelityGen_le_subIsometryConjugate` and `purifiedDistance_le_of_fidelityGen_ge`. This is the
metric input for the smooth-layer pinch `≥` direction: an ε-ball element of the embedded state
pulls back to an ε-ball element of `ρ`. -/
theorem purifiedDistance_subIsometryConjugate_le {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (hK : opLe (Kᴴ * K) 1) (ρ σ : SubDensityOp dSrc) :
    purifiedDistance (ρ.subIsometryConjugate K hK) (σ.subIsometryConjugate K hK) ≤
      purifiedDistance ρ σ :=
  purifiedDistance_le_of_fidelityGen_ge _ _ _ _ (fidelityGen_le_subIsometryConjugate K hK ρ σ)

/-!
## Reference-optimized layer: the `≤` direction and the `≥` co-isometry pullback (both proved)
-/

/-- The guarded reference-optimization set behind `bipartiteMinEntropyOptReal ρ`: the values
`H_min(A|C)_{ρ|σ}` ranging over `D_max`-feasible references `σ`. Named as an abbreviation to keep
the invariance statements legible. -/
def bipartiteMinEntropyOptSet {dA dB : ℕ} (ρ : SubDensityOp (dA * dB)) : Set ℝ :=
  {h | ∃ σ : SubDensityOp dB,
    hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) ∧
    h = bipartiteMinEntropyReal ρ σ}

lemma bipartiteMinEntropyOptReal_eq_sSup {dA dB : ℕ} (ρ : SubDensityOp (dA * dB)) :
    bipartiteMinEntropyOptReal ρ = sSup (bipartiteMinEntropyOptSet ρ) :=
  rfl

/-!
### General regularity of the reference-optimized set

Two analytic facts about `bipartiteMinEntropyOptSet`, needed to discharge the side-conditions of
the invariance without new hypotheses: the set is always nonempty (the maximally-mixed reference is
`D_max`-feasible), and it is always bounded above (`H_min(A|C) ≤ log₂ dA`, the ℝ-encoding of the
finite min-entropy). Both rest on a single uniform lower bound for the `D_max` scalar against a
sub-density reference: `Tr ρ / dA ≤ dmaxFeasibleLambda ρ (1_A ⊗ σ)`, independent of `σ`.
-/

/-- The real trace of `1_A ⊗ σ` is `dA · Tr σ`. -/
lemma trace_re_tensor_one_left {dA dC : ℕ} (σ : Op dC) :
    (Op.tensor (1 : Op dA) σ).trace.re = (dA : ℝ) * σ.trace.re := by
  rw [Op.trace_tensor, Matrix.trace_one, Fintype.card_fin]
  simp [Complex.mul_re]

/-- A sub-density reference tensored with the identity is dominated by the identity:
`1_A ⊗ σ ≼ 1`. -/
lemma tensor_one_subDensity_opLe_one {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (σ : SubDensityOp dC) :
    opLe (Op.tensor (1 : Op dA) σ.toOp) (1 : Op (dA * dC)) := by
  have h := Quantum.Operators.opLe_tensor_psd (A := (1 : Op dA)) (B := (1 : Op dA))
    (C := σ.toOp) (D := (1 : Op dC)) Matrix.isHermitian_one Matrix.PosSemidef.one
    (posSemidefOp_implies_mathlib σ.toPosSemidefOp) Matrix.isHermitian_one
    (fun v => le_refl _) σ.opLe_one
  rwa [Op.tensor_one] at h

/-- **Uniform lower bound for the `D_max` scalar against a tensored sub-density reference.** For a
bipartite state `ρ` and any `D_max`-feasible sub-density reference `σ`, the `D_max` scalar is
bounded below by `Tr(ρ)/dA`, a bound *independent of `σ`*. This is the trace domination
`Tr ρ ≤ t · Tr(1_A ⊗ σ) ≤ t · dA` (using `1_A ⊗ σ ≼ 1`), which yields the boundedness above and the
positivity of the guarded min-entropy without extra hypotheses. -/
lemma trace_div_dim_le_dmaxFeasibleLambda {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) (σ : SubDensityOp dC)
    (hfeas : hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    ρ.toOp.trace.re / (dA : ℝ) ≤
      dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) := by
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  refine le_csInf hfeas ?_
  rintro t ⟨htn, hle⟩
  rw [div_le_iff₀ hdA]
  -- `Tr ρ ≤ t · Tr(1 ⊗ σ)`
  have hherm : (Complex.ofReal t • Op.tensor (1 : Op dA) σ.toOp).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Op.tensor_conjTranspose,
      Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
    rw [show σ.toOpᴴ = σ.toOp from σ.isHermitian]
  have htr := trace_mul_le_of_opLe (M := (1 : Op (dA * dC))) Matrix.PosSemidef.one
    ρ.isHermitian hherm hle
  rw [Matrix.one_mul, Matrix.one_mul] at htr
  -- Compute the RHS trace: `t · dA · Tr σ`.
  have hσle : σ.toOp.trace.re ≤ 1 := σ.trace_le_one
  have hrhs : (Complex.ofReal t • Op.tensor (1 : Op dA) σ.toOp).trace.re =
      t * ((dA : ℝ) * σ.toOp.trace.re) := by
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, trace_re_tensor_one_left]
  rw [hrhs] at htr
  calc ρ.toOp.trace.re ≤ t * ((dA : ℝ) * σ.toOp.trace.re) := htr
    _ ≤ t * ((dA : ℝ) * 1) := by
        apply mul_le_mul_of_nonneg_left _ htn
        exact mul_le_mul_of_nonneg_left hσle (le_of_lt hdA)
    _ = t * (dA : ℝ) := by rw [mul_one]

/-- **The reference-optimized set is always nonempty.** The maximally-mixed reference is
positive definite, hence `D_max`-feasible (`hasDmaxFeasibleLambda_of_posDef_reference`). -/
lemma bipartiteMinEntropyOptSet_nonempty {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) : (bipartiteMinEntropyOptSet ρ).Nonempty := by
  set σ := DensityOp.toSubDensityOp (DensityOp.maxMixed dC) with hσ
  have hσpd : σ.toOp.PosDef := by
    simpa [hσ, DensityOp.toSubDensityOp, DensityOp.maxMixed] using
      ((Matrix.PosDef.one : (1 : Op dC).PosDef).smul (a := (1 / (dC : ℂ)))
        (by
          exact_mod_cast (one_div_pos.mpr
            (Nat.cast_pos.mpr (Nat.pos_of_neZero dC)))))
  have hpd : (Op.tensor (1 : Op dA) σ.toOp).PosDef := by
    unfold Quantum.TensorProducts.Op.tensor
    rw [Matrix.reindex_apply]
    exact (Matrix.PosDef.kronecker Matrix.PosDef.one hσpd).submatrix finProdFinEquiv.symm.injective
  exact ⟨bipartiteMinEntropyReal ρ σ, σ,
    hasDmaxFeasibleLambda_of_posDef_reference
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) hpd, rfl⟩

/-- A nonzero sub-density operator has strictly positive real trace. -/
lemma subDensity_trace_re_pos {d : ℕ} (ρ : SubDensityOp d) (hρ0 : ρ.toOp ≠ 0) :
    0 < ρ.toOp.trace.re := by
  have hpsd := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have htr_nn := hpsd.trace_nonneg
  rw [Complex.le_def] at htr_nn
  have hne : ρ.toOp.trace ≠ 0 := fun h => hρ0 (hpsd.trace_eq_zero_iff.mp h)
  rcases lt_or_eq_of_le htr_nn.1 with h | h
  · exact h
  · exact absurd (Complex.ext_iff.mpr ⟨h.symm, htr_nn.2.symm⟩) hne

/-- **The `D_max` scalar is strictly positive for a nonzero state against a feasible reference.**
Directly from the uniform lower bound `Tr ρ / dA ≤ dmaxFeasibleLambda` and `Tr ρ > 0`. Excludes the
`D_max = 0` sentinel (`H_min = +∞`) for the `−log` step of the pinch direction. -/
lemma dmaxFeasibleLambda_pos_of_ne_zero {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) (hρ0 : ρ.toOp ≠ 0) (σ : SubDensityOp dC)
    (hfeas : hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    0 < dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) := by
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  exact lt_of_lt_of_le (div_pos (subDensity_trace_re_pos ρ hρ0) hdA)
    (trace_div_dim_le_dmaxFeasibleLambda ρ σ hfeas)

/-- **The reference-optimized set is always bounded above.** The ℝ-encoding of
`H_min(A|C) ≤ log₂ dA`,
discharged without hypotheses: for a nonzero state the uniform `D_max` lower bound `Tr ρ/dA` gives
`bipartiteMinEntropyReal ρ σ ≤ -log₂(Tr ρ/dA)`; the zero state has all values equal to `0`. -/
lemma bipartiteMinEntropyOptSet_bddAbove {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) : BddAbove (bipartiteMinEntropyOptSet ρ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hρ0 : ρ.toOp = 0
  · refine ⟨0, ?_⟩
    rintro h ⟨σ, hfeas, rfl⟩
    have hlam0 : dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) = 0 := by
      refine le_antisymm ?_ (dmaxFeasibleLambda_nonneg _ _)
      refine dmaxFeasibleLambda_le_of_feasible _ _ ⟨le_refl 0, ?_⟩
      rw [hρ0, Complex.ofReal_zero, zero_smul]
      exact fun v => le_refl _
    change bipartiteMinEntropyReal ρ σ ≤ 0
    unfold bipartiteMinEntropyReal
    rw [hlam0, Real.log_zero, neg_zero, zero_div]
  · set c := ρ.toOp.trace.re / (dA : ℝ) with hc
    have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
    have hcpos : 0 < c := div_pos (subDensity_trace_re_pos ρ hρ0) hdA
    refine ⟨-Real.log c / Real.log 2, ?_⟩
    rintro h ⟨σ, hfeas, rfl⟩
    have hlam : c ≤ dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) :=
      trace_div_dim_le_dmaxFeasibleLambda ρ σ hfeas
    unfold bipartiteMinEntropyReal
    rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
    exact Real.log_le_log hcpos hlam

/-- **`bipartiteMinEntropyReal` is antitone in the `D_max` scalar.** If the (positive) `D_max`
scalar of `(ρ', σ')` is at most that of `(ρ, σ)`, then `H_min(ρ|σ) ≤ H_min(ρ'|σ')` (the `−log₂`
flip). The positivity of the smaller scalar excludes the `Real.log 0 = 0` sentinel. -/
lemma bipartiteMinEntropyReal_le_of_dmax_le {dA dC dA' dC' : ℕ}
    (ρ : SubDensityOp (dA * dC)) (σ : SubDensityOp dC)
    (ρ' : SubDensityOp (dA' * dC')) (σ' : SubDensityOp dC')
    (hpos : 0 < dmaxFeasibleLambda ρ'.toOp (Op.tensor (1 : Op dA') σ'.toOp))
    (hle : dmaxFeasibleLambda ρ'.toOp (Op.tensor (1 : Op dA') σ'.toOp) ≤
      dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) :
    bipartiteMinEntropyReal ρ σ ≤ bipartiteMinEntropyReal ρ' σ' := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold bipartiteMinEntropyReal
  rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
  exact Real.log_le_log hpos hle

/-- **OPT-level value non-decrease under the co-isometry pullback.** For a left isometry `V` and a
state `τ` on `A ⊗ C'` whose pullback `ρ̃ = (1_A ⊗ Vᴴ) τ (1_A ⊗ V)` to `A ⊗ C` is nonzero,
`H_min(A|C')_τ ≤ H_min(A|C)_ρ̃`. The engine is `dmaxFeasibleLambda_mono_of_orderPreserving` applied
to the fixed-matrix conjugation `Φ(A) = K A Kᴴ`, `K = (1_A ⊗ V)ᴴ`: it maps every `D_max`-feasible
reference `σ'` of `τ` to the projected reference `Vᴴ σ' V` of `ρ̃` with a `D_max` scalar that does
not increase, and the `−log₂` flip turns that into the min-entropy `≥`. This is the pinch/pullback
content of the `≥` direction. -/
lemma bipartiteMinEntropyOptReal_le_pullback {dA dC dC' : ℕ}
    [NeZero dA] [NeZero dC] [NeZero dC']
    (V : Matrix (Fin dC') (Fin dC) ℂ) (hV : Vᴴ * V = 1)
    (τ : SubDensityOp (dA * dC'))
    (hpb : opLe (((kronIdLeftIso (dH := dA) V)ᴴ)ᴴ * (kronIdLeftIso (dH := dA) V)ᴴ) 1)
    (hne0 : (τ.subIsometryConjugate ((kronIdLeftIso (dH := dA) V)ᴴ) hpb).toOp ≠ 0) :
    bipartiteMinEntropyOptReal τ ≤
      bipartiteMinEntropyOptReal
        (τ.subIsometryConjugate ((kronIdLeftIso (dH := dA) V)ᴴ) hpb) := by
  let K := (kronIdLeftIso (dH := dA) V)ᴴ
  have hKdef : K = (kronIdLeftIso (dH := dA) V)ᴴ := rfl
  set ρpb := τ.subIsometryConjugate K hpb with hρpbdef
  set Ψ : Op (dA * dC') → Op (dA * dC) := fun A => K * A * Kᴴ with hΨdef
  have hσb : opLe ((Vᴴ)ᴴ * Vᴴ) 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact opLe_left_isometry_range_projection V hV
  have hΨmono : ∀ A B : Op (dA * dC'), opLe A B → opLe (Ψ A) (Ψ B) :=
    fun A B hAB => Quantum.Channels.opLe_kraus_sandwich K hAB
  have hΨsmul : ∀ (t : ℝ) (Q : Op (dA * dC')),
      Ψ (Complex.ofReal t • Q) = Complex.ofReal t • Ψ Q := by
    intro t Q; simp only [hΨdef, Matrix.mul_smul, Matrix.smul_mul]
  have hΨτ : Ψ τ.toOp = ρpb.toOp := rfl
  have hΨref : ∀ σ' : SubDensityOp dC',
      Ψ (Op.tensor (1 : Op dA) σ'.toOp) =
        Op.tensor (1 : Op dA) (σ'.subIsometryConjugate Vᴴ hσb).toOp := by
    intro σ'
    simp only [hΨdef, hKdef, Matrix.conjTranspose_conjTranspose]
    rw [← tensor_one_pullback_reference V σ'.toOp, SubDensityOp.subIsometryConjugate_toOp,
      Matrix.conjTranspose_conjTranspose]
  rw [bipartiteMinEntropyOptReal_eq_sSup, bipartiteMinEntropyOptReal_eq_sSup]
  apply csSup_le (bipartiteMinEntropyOptSet_nonempty τ)
  rintro h ⟨σ', hfeas, rfl⟩
  set σproj := σ'.subIsometryConjugate Vᴴ hσb with hσprojdef
  -- feasibility of the projected reference for `ρpb`
  have hfeasρpb : hasDmaxFeasibleLambda ρpb.toOp (Op.tensor (1 : Op dA) σproj.toOp) := by
    obtain ⟨t, htn, htle⟩ := hfeas
    refine ⟨t, htn, ?_⟩
    have himg := hΨmono _ _ htle
    rwa [hΨsmul, hΨτ, hΨref σ'] at himg
  -- `D_max` non-increase and positivity
  have hmono := dmaxFeasibleLambda_mono_of_orderPreserving Ψ hΨmono hΨsmul τ.toOp
    (Op.tensor (1 : Op dA) σ'.toOp) hfeas
  rw [hΨτ, hΨref σ'] at hmono
  have hpos : 0 < dmaxFeasibleLambda ρpb.toOp (Op.tensor (1 : Op dA) σproj.toOp) :=
    dmaxFeasibleLambda_pos_of_ne_zero ρpb hne0 σproj hfeasρpb
  -- value flip and land under the pullback supremum
  have hval : bipartiteMinEntropyReal τ σ' ≤ bipartiteMinEntropyReal ρpb σproj :=
    bipartiteMinEntropyReal_le_of_dmax_le τ σ' ρpb σproj hpos hmono
  exact le_trans hval
    (le_csSup (bipartiteMinEntropyOptSet_bddAbove ρpb) ⟨σproj, hfeasρpb, rfl⟩)

/-- **The source optimization set embeds into the target's under conditioning-register embedding.**
Every `D_max`-feasible reference `σ` on `C` lifts to `V σ Vᴴ` on `C'` with the same min-entropy
value (`bipartiteMinEntropyReal_conditioning_leftIsometryEmbed_eq`) and preserved feasibility
(`dmaxIsFeasible_leftIsometryConjugate_iff`). This is the isometry-lift content behind the `≤`
direction of the reference-optimized invariance. -/
lemma bipartiteMinEntropyOptSet_conditioning_leftIsometryEmbed_subset {dA dC dC' : ℕ}
    (V : Matrix (Fin dC') (Fin dC) ℂ) (hV : Vᴴ * V = 1) (ρ : SubDensityOp (dA * dC)) :
    bipartiteMinEntropyOptSet ρ ⊆
      bipartiteMinEntropyOptSet
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV)) := by
  rintro h ⟨σ, hguard, rfl⟩
  refine ⟨σ.leftIsometryConjugate V hV, ?_,
    (bipartiteMinEntropyReal_conditioning_leftIsometryEmbed_eq V hV ρ σ).symm⟩
  obtain ⟨t, htf⟩ := hguard
  refine ⟨t, ?_⟩
  rw [SubDensityOp.leftIsometryConjugate_toOp, SubDensityOp.leftIsometryConjugate_toOp,
    tensor_one_conj_reference V σ.toOp]
  exact (dmaxIsFeasible_leftIsometryConjugate_iff (kronIdLeftIso (dH := dA) V)
    (kronIdLeftIso_left_iso V hV) ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) t).mpr htf

/-- **Reference-optimized min-entropy invariance under conditioning-register embedding.** Embedding
the conditioning register `C ↪ C'` of `ρ_AC` by a left isometry `V` (`Vᴴ V = 1`) leaves the
σ-optimized conditional min-entropy `H_min(A|C)` unchanged.

The statement carries the genuine regularity side-conditions: the source optimization set is
nonempty (`hne`; a feasible reference exists, e.g. the maximally-mixed one) and both optimization
sets are bounded above (`hbdd_src`, `hbdd_tgt`; the ℝ-encoding of `H_min(A|C) ≤ log dA`).

The `≤` direction (`bipartiteMinEntropyOptReal ρ ≤ bipartiteMinEntropyOptReal (embed ρ)`) is
proved from the set embedding
`bipartiteMinEntropyOptSet_conditioning_leftIsometryEmbed_subset`.

The `≥` direction is proved by the co-isometry pullback: an arbitrary reference `τ` on `C'` projects
to `Vᴴ τ V` on `C` (a valid sub-density operator since `V Vᴴ ≤ 1`), and the `D_max`-monotone
pullback engine `bipartiteMinEntropyOptReal_le_pullback` transfers the value (the degenerate
zero-state branch being handled directly). -/
theorem bipartiteMinEntropyOptReal_conditioning_leftIsometryEmbed_eq {dA dC dC' : ℕ}
    (V : Matrix (Fin dC') (Fin dC) ℂ) (hV : Vᴴ * V = 1)
    (ρ : SubDensityOp (dA * dC))
    (hne : (bipartiteMinEntropyOptSet ρ).Nonempty)
    (hbdd_src : BddAbove (bipartiteMinEntropyOptSet ρ))
    (hbdd_tgt : BddAbove (bipartiteMinEntropyOptSet
      (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV)))) :
    bipartiteMinEntropyOptReal
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)) =
      bipartiteMinEntropyOptReal ρ := by
  rw [bipartiteMinEntropyOptReal_eq_sSup, bipartiteMinEntropyOptReal_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- `≥` direction (`sSup S' ≤ sSup S`): the reference-projection / pullback content.
    by_cases hρ0 : ρ.toOp = 0
    · -- Degenerate: both sets collapse to the value `0`.
      have hembed0 : (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)).toOp = 0 := by
        rw [SubDensityOp.leftIsometryConjugate_toOp, hρ0, Matrix.mul_zero, Matrix.zero_mul]
      apply csSup_le
        (Set.Nonempty.mono
          (bipartiteMinEntropyOptSet_conditioning_leftIsometryEmbed_subset V hV ρ) hne)
      rintro h ⟨σ', hfeas, rfl⟩
      obtain ⟨s0, hs0mem⟩ := hne
      have hval0 : bipartiteMinEntropyReal (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)) σ' = 0 := by
        unfold bipartiteMinEntropyReal
        have : dmaxFeasibleLambda (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
            (kronIdLeftIso_left_iso V hV)).toOp (Op.tensor (1 : Op dA) σ'.toOp) = 0 := by
          refine le_antisymm ?_ (dmaxFeasibleLambda_nonneg _ _)
          refine dmaxFeasibleLambda_le_of_feasible _ _ ⟨le_refl 0, ?_⟩
          rw [hembed0, Complex.ofReal_zero, zero_smul]
          exact fun v => le_refl _
        rw [this, Real.log_zero, neg_zero, zero_div]
      rw [hval0]
      -- every element of `S` is `0`, so `0 ≤ sSup S`
      have hs0val : s0 = 0 := by
        obtain ⟨σ0, _, rfl⟩ := hs0mem
        unfold bipartiteMinEntropyReal
        have : dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ0.toOp) = 0 := by
          refine le_antisymm ?_ (dmaxFeasibleLambda_nonneg _ _)
          refine dmaxFeasibleLambda_le_of_feasible _ _ ⟨le_refl 0, ?_⟩
          rw [hρ0, Complex.ofReal_zero, zero_smul]
          exact fun v => le_refl _
        rw [this, Real.log_zero, neg_zero, zero_div]
      calc (0 : ℝ) = s0 := hs0val.symm
        _ ≤ sSup (bipartiteMinEntropyOptSet ρ) := le_csSup hbdd_src hs0mem
    · -- Nonzero: derive the dimension nonvanishing, then use the pullback engine.
      have hdAC : dA * dC ≠ 0 := by
        intro h
        exact hρ0 (Matrix.ext fun i _ => absurd i.isLt (by omega))
      have hdA : dA ≠ 0 := (Nat.mul_ne_zero_iff.mp hdAC).1
      have hdC : dC ≠ 0 := (Nat.mul_ne_zero_iff.mp hdAC).2
      have : NeZero dA := ⟨hdA⟩
      have : NeZero dC := ⟨hdC⟩
      have hdC' : dC' ≠ 0 := by
        intro h
        have hVV : (Vᴴ * V) = (0 : Matrix (Fin dC) (Fin dC) ℂ) := by
          subst h
          exact Matrix.ext fun i j => by simp [Matrix.mul_apply]
        rw [hV] at hVV
        have h10 := congrFun (congrFun hVV ⟨0, Nat.pos_of_ne_zero hdC⟩)
          ⟨0, Nat.pos_of_ne_zero hdC⟩
        rw [Matrix.one_apply_eq, Matrix.zero_apply] at h10
        exact one_ne_zero h10
      have : NeZero dC' := ⟨hdC'⟩
      have hpb : opLe (((kronIdLeftIso (dH := dA) V)ᴴ)ᴴ * (kronIdLeftIso (dH := dA) V)ᴴ) 1 := by
        rw [Matrix.conjTranspose_conjTranspose]
        exact opLe_left_isometry_range_projection (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)
      have hpull_eq : (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)).subIsometryConjugate ((kronIdLeftIso (dH := dA) V)ᴴ) hpb
          = ρ := by
        apply SubDensityOp.ext
        rw [SubDensityOp.subIsometryConjugate_toOp, SubDensityOp.leftIsometryConjugate_toOp,
          Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          kronIdLeftIso_left_iso V hV, Matrix.one_mul, Matrix.mul_assoc,
          kronIdLeftIso_left_iso V hV, Matrix.mul_one]
      have hne0 : ((ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)).subIsometryConjugate
            ((kronIdLeftIso (dH := dA) V)ᴴ) hpb).toOp ≠ 0 := by
        rw [hpull_eq]; exact hρ0
      have hkey := bipartiteMinEntropyOptReal_le_pullback V hV
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV))
        hpb hne0
      rw [hpull_eq] at hkey
      exact hkey
  · -- `≤` direction (`sSup S ≤ sSup S'`): proved from the set embedding.
    exact csSup_le_csSup hbdd_tgt hne
      (bipartiteMinEntropyOptSet_conditioning_leftIsometryEmbed_subset V hV ρ)

/-!
### Support-orthogonal (pinch-degenerate) subcase of the pinch `≥` direction

When the co-isometry pullback `ρpb = (1⊗Vᴴ) τ (1⊗V)` of a ball element `τ` of `embed ρ` vanishes,
`τ` is supported off `range(1⊗V) = supp(embed ρ)`, so `embed ρ` and `τ` have orthogonal supports.
The single-Kraus pullback engine (`bipartiteMinEntropyOptReal_le_pullback`) degenerates here (its
`D_max` comparison bottoms out on the `Real.log 0` sentinel). Instead the orthogonality forces the
generalized fidelity to reduce to its pure sub-normalization correction, bounding `Tr τ`, and a
scaled maximally-mixed member of `ρ`'s ε-ball realizes the required `H_min` value.
-/

/-- **Left multiplication vanishes under a vanishing sub-isometry conjugation.** For positive
semidefinite `M` and any rectangular `K`, if `K M Kᴴ = 0` then `K M = 0`: writing `M = √M √M`,
`(K √M)(K √M)ᴴ = K M Kᴴ = 0` forces `K √M = 0`, hence `K M = K √M √M = 0`. -/
lemma leftMul_eq_zero_of_conj_eq_zero {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ) (M : PosSemidefOp dSrc)
    (h : K * M.toOp * Kᴴ = 0) : K * M.toOp = 0 := by
  have hSherm : (Quantum.Metrics.sqrtPosSemidefOp M)ᴴ = Quantum.Metrics.sqrtPosSemidefOp M :=
    Quantum.Metrics.sqrtPosSemidefOp_isHermitian M
  have hSsq : Quantum.Metrics.sqrtPosSemidefOp M * Quantum.Metrics.sqrtPosSemidefOp M = M.toOp :=
    Quantum.Metrics.sqrtPosSemidefOp_sq M
  have hzero : (K * Quantum.Metrics.sqrtPosSemidefOp M) *
      (K * Quantum.Metrics.sqrtPosSemidefOp M)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hSherm, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Quantum.Metrics.sqrtPosSemidefOp M) (Quantum.Metrics.sqrtPosSemidefOp M)
        Kᴴ, hSsq, ← Matrix.mul_assoc]
    exact h
  have hKS : K * Quantum.Metrics.sqrtPosSemidefOp M = 0 :=
    Matrix.self_mul_conjTranspose_eq_zero.mp hzero
  rw [← hSsq, ← Matrix.mul_assoc, hKS, Matrix.zero_mul]

/-- **Uhlmann fidelity of two positive-semidefinite operators with orthogonal supports is zero.**
If `A B = 0` (equivalently `supp A ⊥ supp B`), then `√A B √A = 0` (from
`(√A B)ᴴ(√A B) = B A B = 0`), so `F(A, B) = Tr √0 = 0`. -/
lemma fidelity_eq_zero_of_mul_eq_zero {n : ℕ} [NeZero n] (A B : PosSemidefOp n)
    (h : A.toOp * B.toOp = 0) : Quantum.Metrics.fidelity A B = 0 := by
  have hSherm : (Quantum.Metrics.sqrtPosSemidefOp A)ᴴ = Quantum.Metrics.sqrtPosSemidefOp A :=
    Quantum.Metrics.sqrtPosSemidefOp_isHermitian A
  have hSsq : Quantum.Metrics.sqrtPosSemidefOp A * Quantum.Metrics.sqrtPosSemidefOp A = A.toOp :=
    Quantum.Metrics.sqrtPosSemidefOp_sq A
  have hBherm : B.toOpᴴ = B.toOp := (posSemidefOp_implies_mathlib B).isHermitian
  have hSB : Quantum.Metrics.sqrtPosSemidefOp A * B.toOp = 0 := by
    have hzero : (Quantum.Metrics.sqrtPosSemidefOp A * B.toOp)ᴴ *
        (Quantum.Metrics.sqrtPosSemidefOp A * B.toOp) = 0 := by
      rw [Matrix.conjTranspose_mul, hSherm, hBherm, Matrix.mul_assoc,
        ← Matrix.mul_assoc (Quantum.Metrics.sqrtPosSemidefOp A) (Quantum.Metrics.sqrtPosSemidefOp A)
          B.toOp, hSsq, h, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  have hinner : Quantum.Metrics.sqrtPosSemidefOp A * B.toOp *
      Quantum.Metrics.sqrtPosSemidefOp A = 0 := by
    rw [hSB, Matrix.zero_mul]
  unfold Quantum.Metrics.fidelity
  simp only [hinner, CFC.sqrt_zero, Matrix.trace_zero, Complex.zero_re]

/-- **`H_min(A|C)` upper bound at a nonzero state.** For a nonzero bipartite state `τ`, the
reference-optimized value is bounded by `−log₂(Tr τ / dA)`, the ℝ-encoding of `H_min(A|C) ≤ log dA`
(the same content as `bipartiteMinEntropyOptSet_bddAbove`, exposed as a value bound). -/
lemma bipartiteMinEntropyOptReal_le_neg_logb_trace {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (τ : SubDensityOp (dA * dC)) (hτ0 : τ.toOp ≠ 0) :
    bipartiteMinEntropyOptReal τ ≤ -Real.log (τ.toOp.trace.re / dA) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  have hcpos : 0 < τ.toOp.trace.re / dA := div_pos (subDensity_trace_re_pos τ hτ0) hdA
  rw [bipartiteMinEntropyOptReal_eq_sSup]
  apply csSup_le (bipartiteMinEntropyOptSet_nonempty τ)
  rintro h ⟨σ, hfeas, rfl⟩
  have hlam : τ.toOp.trace.re / dA ≤
      dmaxFeasibleLambda τ.toOp (Op.tensor (1 : Op dA) σ.toOp) :=
    trace_div_dim_le_dmaxFeasibleLambda τ σ hfeas
  unfold bipartiteMinEntropyReal
  rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
  exact Real.log_le_log hcpos hlam

/-- **`BddAbove` for the bipartite optimization set from normalization.** For a normalized bipartite
center and `0 ≤ ε < 1`, `Set.ofPred (isInSmoothBipartiteMinSet ε ρ)` is bounded above by
`-log₂((1-ε²)/dA)` — the ℝ-encoding of `H_min(A|C) ≤ log₂ dA`, via the ε-ball weight floor `1-ε²`
(`SubDensityOp.trace_ge_of_purifiedDistance_of_normalized`) and the value bound
`bipartiteMinEntropyOptReal_le_neg_logb_trace`. -/
lemma isInSmoothBipartiteMinSet_bddAbove_of_normalized {dA dC : ℕ} [NeZero dA] [NeZero dC]
    [NeZero (dA * dC)] {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (ρ : SubDensityOp (dA * dC)) (hρ : ρ.trace = 1) :
    BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε ρ)) := by
  have hηpos : (0 : ℝ) < 1 - ε ^ 2 := by nlinarith
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨-Real.log ((1 - ε ^ 2) / (dA : ℝ)) / Real.log 2, ?_⟩
  rintro h ⟨ρ', hd, rfl⟩
  have hweight : 1 - ε ^ 2 ≤ ρ'.trace :=
    SubDensityOp.trace_ge_of_purifiedDistance_of_normalized ρ ρ' hρ hε hd
  have hρ'0 : ρ'.toOp ≠ 0 := by
    intro h0
    have hz : ρ'.trace = 0 := by change ρ'.toOp.trace.re = 0; rw [h0]; simp
    rw [hz] at hweight; linarith
  refine le_trans (bipartiteMinEntropyOptReal_le_neg_logb_trace ρ' hρ'0) ?_
  have harg_pos : (0 : ℝ) < (1 - ε ^ 2) / (dA : ℝ) := div_pos hηpos hdA
  have hle_arg : (1 - ε ^ 2) / (dA : ℝ) ≤ ρ'.toOp.trace.re / (dA : ℝ) := by
    gcongr
    exact hweight
  rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
  exact Real.log_le_log harg_pos hle_arg

/-- **`H_min(A|C)` of a scaled maximally-mixed state lower bound.** For `0 < s ≤ 1`, the state
`s · maxMixed(dA·dC)` has reference-optimized value at least `−log₂(s / dA)`, witnessed by the
maximally-mixed reference `maxMixed(dC)` (against which the `D_max` scalar is exactly `s / dA`). -/
lemma neg_logb_trace_le_bipartiteMinEntropyOptReal_scaledMaxMixed
    {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (s : ℝ) (hs_nn : 0 ≤ s) (hs_le : s ≤ 1) (hs_pos : 0 < s) :
    -Real.log (s / dA) / Real.log 2 ≤
      bipartiteMinEntropyOptReal
        ((DensityOp.toSubDensityOp (DensityOp.maxMixed (dA * dC))).smul s hs_nn hs_le) := by
  have : NeZero (dA * dC) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dC)⟩
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdA : (0 : ℝ) < dA := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)
  set μ := (DensityOp.toSubDensityOp (DensityOp.maxMixed (dA * dC))).smul s hs_nn hs_le with hμdef
  set σ0 := DensityOp.toSubDensityOp (DensityOp.maxMixed dC) with hσ0def
  -- scalar identity: `(s/dA) • (1 ⊗ maxMixed dC) = μ`
  have hscalar : Complex.ofReal (s / (dA : ℝ)) * (1 / (dC : ℂ))
      = (s : ℂ) * (1 / ((dA * dC : ℕ) : ℂ)) := by
    have hdA' : (dA : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne dA)).ne'
    have hdC' : (dC : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne dC)).ne'
    push_cast
    field_simp
  have hrhs : Complex.ofReal (s / (dA : ℝ)) • Op.tensor (1 : Op dA) σ0.toOp = μ.toOp := by
    change Complex.ofReal (s / (dA : ℝ)) • Op.tensor (1 : Op dA) ((1 / (dC : ℂ)) • (1 : Op dC))
        = (s : ℂ) • ((1 / ((dA * dC : ℕ) : ℂ)) • (1 : Op (dA * dC)))
    rw [Quantum.TensorProducts.Op.tensor_smul_right, Op.tensor_one, smul_smul, smul_smul, hscalar]
  -- feasibility of the maximally-mixed reference with scalar `s/dA`
  have hfeas_t : dmaxIsFeasible μ.toOp (Op.tensor (1 : Op dA) σ0.toOp) (s / dA) := by
    refine ⟨le_of_lt (div_pos hs_pos hdA), ?_⟩
    rw [hrhs]
    exact fun v => le_refl _
  have hfeasσ0 : hasDmaxFeasibleLambda μ.toOp (Op.tensor (1 : Op dA) σ0.toOp) :=
    ⟨s / dA, hfeas_t⟩
  have hle : dmaxFeasibleLambda μ.toOp (Op.tensor (1 : Op dA) σ0.toOp) ≤ s / dA :=
    dmaxFeasibleLambda_le_of_feasible _ _ hfeas_t
  have htrμ : μ.toOp.trace.re = s := by
    have h := SubDensityOp.smul_trace
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dA * dC))) s hs_nn hs_le
    rw [toSubDensityOp_trace, mul_one] at h
    exact h
  have hge : s / dA ≤ dmaxFeasibleLambda μ.toOp (Op.tensor (1 : Op dA) σ0.toOp) := by
    have h := trace_div_dim_le_dmaxFeasibleLambda μ σ0 hfeasσ0
    rwa [htrμ] at h
  have hdmax_pos : 0 < dmaxFeasibleLambda μ.toOp (Op.tensor (1 : Op dA) σ0.toOp) :=
    lt_of_lt_of_le (div_pos hs_pos hdA) hge
  have hval : -Real.log (s / dA) / Real.log 2 ≤ bipartiteMinEntropyReal μ σ0 := by
    unfold bipartiteMinEntropyReal
    rw [div_le_div_iff_of_pos_right hlog2, neg_le_neg_iff]
    exact Real.log_le_log hdmax_pos hle
  calc -Real.log (s / dA) / Real.log 2 ≤ bipartiteMinEntropyReal μ σ0 := hval
    _ ≤ bipartiteMinEntropyOptReal μ := by
        rw [bipartiteMinEntropyOptReal_eq_sSup]
        exact le_csSup (bipartiteMinEntropyOptSet_bddAbove μ) ⟨σ0, hfeasσ0, rfl⟩

/-- **`H_min(A|C)` of the zero state is `0`.** All reference values collapse to `−log₂ 0 = 0`, and
the optimization set is the singleton `{0}`. -/
lemma bipartiteMinEntropyOptReal_eq_zero_of_toOp_zero {dA dC : ℕ} [NeZero dA] [NeZero dC]
    (ρ : SubDensityOp (dA * dC)) (h0 : ρ.toOp = 0) :
    bipartiteMinEntropyOptReal ρ = 0 := by
  have hval : ∀ σ : SubDensityOp dC, bipartiteMinEntropyReal ρ σ = 0 := by
    intro σ
    unfold bipartiteMinEntropyReal
    have hd0 : dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) = 0 := by
      refine le_antisymm ?_ (dmaxFeasibleLambda_nonneg _ _)
      refine dmaxFeasibleLambda_le_of_feasible _ _ ⟨le_refl 0, ?_⟩
      rw [h0, Complex.ofReal_zero, zero_smul]
      exact fun v => le_refl _
    rw [hd0, Real.log_zero, neg_zero, zero_div]
  rw [bipartiteMinEntropyOptReal_eq_sSup]
  have hset : bipartiteMinEntropyOptSet ρ = {0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨v, σ, hfeas, hv⟩ := bipartiteMinEntropyOptSet_nonempty ρ
      exact ⟨σ, hfeas, (hval σ).symm⟩
    · rintro h ⟨σ, hfeas, rfl⟩
      exact hval σ
  rw [hset, csSup_singleton]

/-- **Smooth reference-optimized min-entropy invariance under conditioning-register embedding — the
purification-independence workhorse.** Embedding the conditioning register `C ↪ C'` of `ρ_AC` by a
left isometry `V` (`Vᴴ V = 1`) leaves the ε-smooth σ-optimized conditional min-entropy
`H_min^ε(A|C)` unchanged. Together with the pure-state relation
`ρ_AC' = (1_A ⊗ V) ρ_AC (1_A ⊗ V)ᴴ` between any two
purifications, this is exactly the statement that `H_max^ε(A|B) := −H_min^ε(A|C)` is
purification-independent.

Statement carries the `BddAbove` regularity side-conditions on both smooth optimization sets.

Both smooth directions are proved:
* isometry-lift `≤`: every purified-distance ε-ball element `ρ̃` of `ρ` maps to a ball element
  `(1⊗V)ρ̃(1⊗V)ᴴ` of the embedded state with the same distance
  (`purifiedDistance_leftIsometryConjugate_eq`), reducing to the reference-optimized `≤` over the
  ball (`bipartiteMinEntropyOptReal_conditioning_leftIsometryEmbed_eq`);
* pinch `≥`: an arbitrary ε-ball element `τ̃` of the embedded state is pulled back to `C` by the
  co-isometry `1_A ⊗ Vᴴ` — the pullback does not increase purified distance
  (`purifiedDistance_subIsometryConjugate_le`) and does not decrease `H_min`
  (`bipartiteMinEntropyOptReal_le_pullback`). The support-orthogonal degenerate subcase (`ρpb = 0`,
  i.e. `τ̃ ⊥ range(1⊗V)`) is closed by the orthogonal-support generalized-fidelity computation
  (`fidelity_eq_zero_of_mul_eq_zero`) plus a scaled maximally-mixed ball witness. -/
theorem smoothBipartiteMinEntropyOptReal_conditioning_leftIsometryEmbed_eq {dA dC dC' : ℕ}
    [NeZero (dA * dC)] [NeZero (dA * dC')]
    (V : Matrix (Fin dC') (Fin dC) ℂ) (hV : Vᴴ * V = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (ρ : SubDensityOp (dA * dC))
    (hbdd : BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε ρ)))
    (hbdd' : BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε
      (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
        (kronIdLeftIso_left_iso V hV))))) :
    smoothBipartiteMinEntropyOptReal ε
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV)) =
      smoothBipartiteMinEntropyOptReal ε ρ := by
  have hneA : NeZero dA := ⟨(Nat.mul_ne_zero_iff.mp (NeZero.ne (dA * dC))).1⟩
  have hneC : NeZero dC := ⟨(Nat.mul_ne_zero_iff.mp (NeZero.ne (dA * dC))).2⟩
  have hneC' : NeZero dC' := ⟨(Nat.mul_ne_zero_iff.mp (NeZero.ne (dA * dC'))).2⟩
  have hpb : opLe (((kronIdLeftIso (dH := dA) V)ᴴ)ᴴ * (kronIdLeftIso (dH := dA) V)ᴴ) 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact opLe_left_isometry_range_projection (kronIdLeftIso (dH := dA) V)
      (kronIdLeftIso_left_iso V hV)
  have hpull_eq : (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
      (kronIdLeftIso_left_iso V hV)).subIsometryConjugate ((kronIdLeftIso (dH := dA) V)ᴴ) hpb
      = ρ := by
    apply SubDensityOp.ext
    rw [SubDensityOp.subIsometryConjugate_toOp, SubDensityOp.leftIsometryConjugate_toOp,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      kronIdLeftIso_left_iso V hV, Matrix.one_mul, Matrix.mul_assoc,
      kronIdLeftIso_left_iso V hV, Matrix.mul_one]
  refine le_antisymm ?_ ?_
  · -- **Pinch `≥` direction:** `H_min^ε(embed ρ) ≤ H_min^ε(ρ)`.
    apply csSup_le (smoothBipartiteMinSet_nonempty hε _)
    rintro v ⟨τ, hd, rfl⟩
    set ρpb := τ.subIsometryConjugate ((kronIdLeftIso (dH := dA) V)ᴴ) hpb with hρpb
    -- The pullback lands in the ε-ball of `ρ` (metric data-processing + `pullback(embed ρ) = ρ`).
    have hdist : purifiedDistance ρ ρpb ≤ ε := by
      have h := purifiedDistance_subIsometryConjugate_le ((kronIdLeftIso (dH := dA) V)ᴴ) hpb
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV)) τ
      rw [hpull_eq] at h
      exact le_trans h hd
    have hball : bipartiteMinEntropyOptReal ρpb ≤ smoothBipartiteMinEntropyOptReal ε ρ :=
      smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε ρ ρpb hbdd hdist
    by_cases hz : ρpb.toOp = 0
    · -- Support-orthogonal subcase: `τ ⊥ range(1 ⊗ V) = supp(embed ρ)`. The pullback `ρpb`
      -- vanishes, so the single-Kraus pullback engine degenerates; instead the orthogonal supports
      -- force the generalized fidelity to be the pure sub-normalization correction, bounding
      -- `Tr τ`; a scaled maximally-mixed member of `ρ`'s ε-ball realizes the `H_min` value.
      set eρ := ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
        (kronIdLeftIso_left_iso V hV) with heρdef
      -- `(1 ⊗ Vᴴ) τ = 0` from the vanishing pullback (`τ` orthogonal to `range(1 ⊗ V)`).
      have hKτ : (kronIdLeftIso (dH := dA) V)ᴴ * τ.toOp = 0 := by
        have hconj : (kronIdLeftIso (dH := dA) V)ᴴ * τ.toOp
            * ((kronIdLeftIso (dH := dA) V)ᴴ)ᴴ = 0 := by
          have hzz := hz
          rw [hρpb, SubDensityOp.subIsometryConjugate_toOp] at hzz
          exact hzz
        exact leftMul_eq_zero_of_conj_eq_zero ((kronIdLeftIso (dH := dA) V)ᴴ)
          τ.toPosSemidefOp hconj
      -- `embed ρ` and `τ` have orthogonal supports: `(embed ρ) τ = 0`.
      have hEτ : eρ.toOp * τ.toOp = 0 := by
        rw [heρdef, SubDensityOp.leftIsometryConjugate_toOp, Matrix.mul_assoc, hKτ,
          Matrix.mul_zero]
      -- Uhlmann fidelity vanishes, so the generalized fidelity is the pure correction term.
      have hfid0 : Quantum.Metrics.fidelity eρ.toPosSemidefOp τ.toPosSemidefOp = 0 :=
        fidelity_eq_zero_of_mul_eq_zero eρ.toPosSemidefOp τ.toPosSemidefOp hEτ
      have hfgen : fidelityGen eρ τ = Real.sqrt ((1 - eρ.trace) * (1 - τ.trace)) := by
        unfold fidelityGen
        rw [hfid0, zero_add]
      have htreρ : eρ.trace = ρ.trace :=
        SubDensityOp.leftIsometryConjugate_trace (kronIdLeftIso (dH := dA) V)
          (kronIdLeftIso_left_iso V hV) ρ
      -- The ε-ball constraint forces `(1 − Tr ρ)(1 − Tr τ) ≥ 1 − ε²`.
      have hconstraint : 1 - ε ^ 2 ≤ (1 - ρ.trace) * (1 - τ.trace) := by
        have hPnn := purifiedDistance_nonneg eρ τ
        have hPsq : purifiedDistance eρ τ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hPnn hd 2
        have hPsqeq : purifiedDistance eρ τ ^ 2 = 1 - fidelityGen eρ τ ^ 2 :=
          purifiedDistance_sq eρ τ
        have hfg2 : fidelityGen eρ τ ^ 2 = (1 - ρ.trace) * (1 - τ.trace) := by
          rw [hfgen, htreρ, Real.sq_sqrt (by
            have h1 := ρ.one_sub_trace_nonneg; have h2 := τ.one_sub_trace_nonneg; positivity)]
        linarith only [hPsq, hPsqeq, hfg2]
      by_cases hτ0 : τ.toOp = 0
      · -- `τ = 0`: both optimized values are `0`, and `smooth ρ ≥ 0`.
        have h1 : bipartiteMinEntropyOptReal τ = 0 :=
          bipartiteMinEntropyOptReal_eq_zero_of_toOp_zero τ hτ0
        have h2 : bipartiteMinEntropyOptReal ρpb = 0 :=
          bipartiteMinEntropyOptReal_eq_zero_of_toOp_zero ρpb hz
        rw [h1, ← h2]; exact hball
      · -- `τ ≠ 0`: `s = Tr τ > 0`; use the scaled maximally-mixed ball witness `μ`.
        have hspos : 0 < τ.toOp.trace.re := subDensity_trace_re_pos τ hτ0
        have hsnn : 0 ≤ τ.toOp.trace.re := le_of_lt hspos
        have hsle : τ.toOp.trace.re ≤ 1 := τ.trace_le_one
        set μ := (DensityOp.toSubDensityOp (DensityOp.maxMixed (dA * dC))).smul
          (τ.toOp.trace.re) hsnn hsle with hμdef
        have hμtr : μ.trace = τ.trace := by
          rw [hμdef, SubDensityOp.smul_trace, toSubDensityOp_trace, mul_one]
          rfl
        -- `μ` lies in the ε-ball of `ρ`, from the correction lower bound on generalized fidelity.
        have hμball : purifiedDistance ρ μ ≤ ε := by
          have hcorr_eq : (1 - ρ.trace) * (1 - μ.trace) = (1 - ρ.trace) * (1 - τ.trace) := by
            rw [hμtr]
          have hfg_ge : Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) ≤ fidelityGen ρ μ := by
            unfold fidelityGen
            have hfid_nn := Quantum.Metrics.fidelity_nonneg_posSemidefOp
              ρ.toPosSemidefOp μ.toPosSemidefOp
            rw [hcorr_eq]
            exact le_add_of_nonneg_left hfid_nn
          have hfg2_ge : 1 - ε ^ 2 ≤ fidelityGen ρ μ ^ 2 := by
            have hsqrt_sq : Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) ^ 2
                = (1 - ρ.trace) * (1 - τ.trace) :=
              Real.sq_sqrt (by
                have h1 := ρ.one_sub_trace_nonneg; have h2 := τ.one_sub_trace_nonneg; positivity)
            calc 1 - ε ^ 2 ≤ (1 - ρ.trace) * (1 - τ.trace) := hconstraint
              _ = Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) ^ 2 := hsqrt_sq.symm
              _ ≤ fidelityGen ρ μ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hfg_ge 2
          have hstep : purifiedDistance ρ μ ≤ Real.sqrt (ε ^ 2) := by
            unfold purifiedDistance
            exact Real.sqrt_le_sqrt (by linarith only [hfg2_ge])
          rwa [Real.sqrt_sq hε] at hstep
        -- `H_min(τ) ≤ −log₂(Tr τ / dA) ≤ H_min(μ) ≤ H_min^ε(ρ)`.
        have hopt_le : bipartiteMinEntropyOptReal τ ≤ bipartiteMinEntropyOptReal μ :=
          le_trans (bipartiteMinEntropyOptReal_le_neg_logb_trace τ hτ0)
            (neg_logb_trace_le_bipartiteMinEntropyOptReal_scaledMaxMixed
              (τ.toOp.trace.re) hsnn hsle hspos)
        exact le_trans hopt_le
          (smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε ρ μ hbdd hμball)
    · exact le_trans (bipartiteMinEntropyOptReal_le_pullback V hV τ hpb hz) hball
  · -- **Isometry-lift `≤` direction:** `H_min^ε(ρ) ≤ H_min^ε(embed ρ)`.
    apply csSup_le (smoothBipartiteMinSet_nonempty hε ρ)
    rintro v ⟨ρt, hd, rfl⟩
    set eρt := ρt.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
      (kronIdLeftIso_left_iso V hV) with heρt
    have hdist : purifiedDistance (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V)
        (kronIdLeftIso_left_iso V hV)) eρt ≤ ε := by
      rw [heρt, purifiedDistance_leftIsometryConjugate_eq]; exact hd
    have hle1 : bipartiteMinEntropyOptReal ρt ≤ bipartiteMinEntropyOptReal eρt := by
      rw [bipartiteMinEntropyOptReal_eq_sSup, bipartiteMinEntropyOptReal_eq_sSup]
      exact csSup_le_csSup (bipartiteMinEntropyOptSet_bddAbove eρt)
        (bipartiteMinEntropyOptSet_nonempty ρt)
        (bipartiteMinEntropyOptSet_conditioning_leftIsometryEmbed_subset V hV ρt)
    have hle2 : bipartiteMinEntropyOptReal eρt ≤ smoothBipartiteMinEntropyOptReal ε
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV)) :=
      smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε
        (ρ.leftIsometryConjugate (kronIdLeftIso (dH := dA) V) (kronIdLeftIso_left_iso V hV))
        eρt hbdd' hdist
    exact le_trans hle1 hle2

end InfoTheory.SmoothMinEntropy

end -- noncomputable section

-- Dimension casts preserve trace and positive semidefiniteness by
-- `Quantum.TensorProducts.Op.castDim_trace` and `Quantum.TensorProducts.Op.castDim_posSemidef`.
