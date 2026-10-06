import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilation
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ConditioningIsometryInvariance

/-!
# The recovery identity of the Tomamichel–Renner uncertainty relation

The entropy-level statement of the Tomamichel–Renner smooth entropic-uncertainty proof
(arXiv:1009.2015, `tr.tex:295–362`, ε = 0 pure case) was the min-entropy inequality `eqn:mo3`

  `H_min(Z|Z′AB) ≤ H_min(X|B) − q` ,   `q := −log₂ c` ,   `c := max_{x,z} |⟨x|z⟩|²` ,

on the coherent dilated states, lifting the *operator* feasibility transport
(`MeasurementDilation.lean`, `measDilation_mo6`) to the *entropy* level, over the guarded general
bipartite conditional min-entropy of `BipartiteMinMax.lean`.

This file carries the shared **object layer** (the dilated state `measDilate`, the `X`-measured
marginal `xMeasuredMarginal`, the entropy-layout `zDilatedState`) and the **recovery identity**
`eqn:mo10`. The `D_max` and entropy-level lifts built on top of it — `measDilation_pure_core`
(`eqn:mo3`) and the state-level transport — live in `MeasurementTransport.lean`, and their
ε-smooth form in `SmoothUncertaintyRelation.lean`.

## References

The recovery identity uses Tomamichel–Renner, arXiv:1009.2015, `tr.tex:338–341`, `eqn:mo10`.
The overlap-derived quantity `preparationQuality` (`q := −log₂ c`, `tr.tex:305`) uses the
constant `c := max_{x,z} |⟨x|z⟩|²` from arXiv:1504.00233, `apps.tex:174`, `\label{eq:defc}`
(`c = max_{x,y} |⟨φ_x|ϑ_y⟩|²`). Both are defined in `MeasurementDilation.lean`.

The dual-form inequality in arXiv:1504.00233, `apps.tex:198`, `\label{eq:ucr-dual}`,
`H↑_α(X|B)_{M_X(ρ)} ≥ H↑_α(Y|Y'B)_{U_Y(ρ)} − log c`, has the shape of
`measDilation_pure_core` at `α = ∞`, via a CPTP data-processing proof.
The tripartite Theorem `th:ur`, `apps.tex:183–192` (label at `apps.tex:185`), additionally
requires the min–max duality `pr:dual-new` and is not claimed here. These entropy statements
do not replace the operator recovery identity `eqn:mo10`.

## What TR does at the entropy level (`tr.tex:298–362`)

Applied to the Z-dilated pure state, the min–max duality `eqn:mo1` gives
`H_max(Z|C)_ρ + H_min(Z|Z′AB)_ρ = 0`. Comparing with the theorem statement, it
remains to prove `eqn:mo3`, `H_min(Z|Z′AB)_ρ ≤ H_min(X|B)_ρ − q`, which TR obtains from the
per-reference feasibility transport (`tr.tex:310–326`)

  `2^{-λ} · 1_Z ⊗ σ_{Z′AB} ≥ ρ_{ZZ′AB}  ⟹  2^{-λ} · c · 1_X ⊗ σ_B ≥ ρ_{XB}` ,

together with the recovery identity `eqn:mo10` (`tr.tex:338–341`)

  `Tr_{X′A}( W (ρ_{ZZ′AB}) Wᴴ ) = ρ_{XB}` ,

where `W = U Vᴴ` is the partial isometry (`tr.tex:335`), `U`, `V` the `X`- resp. `Z`-basis
Stinespring dilations, and `ρ_{XB}` is the `X`-measured marginal. The transport at the reference
level is `measDilation_mo6`; the recovery `eqn:mo10` is this module; the `D_max` and
entropy-level lifts built on both are `MeasurementTransport.lean`.

## The recovery `eqn:mo10` is an operator identity, not a partial-trace evaluation

The `measConjTraceMap` map `Ξ(τ) := Tr_{X′A}((W ⊗ 1_B) τ (W ⊗ 1_B)ᴴ)` factors as
`partialTraceB ∘ reindex`. Both `Ξ(ρ_{ZZ′AB})` and `ρ_{XB}` are built by applying that *same*
`partialTraceB ∘ reindex` wrapper, so the recovery reduces to the inner operator identity

  `(W ⊗ 1_B) (V ⊗ 1_B) ρ_{AB} (V ⊗ 1_B)ᴴ (W ⊗ 1_B)ᴴ = (U ⊗ 1_B) ρ_{AB} (U ⊗ 1_B)ᴴ` ,

i.e. `W V = U`, i.e. `U Vᴴ V = U`, consuming the `Z`-dilation isometry certificate `Vᴴ V = 1`
(Q.dilationIso_isometry). No evaluation of the non-adjacent partial trace `Tr_{X′A}` is needed —
that evaluation (`eqn:mo8/mo9`) is required only for the *bound* on the reference,
`measConjTraceMap_one_tensor_reference_opLe`, which is itself proved.

## Scope: per-round / single-system

`q = −log₂ c` for a **general** overlap constant `c = overlapConst P Q` of the two rank-1 projective
bases (`MeasurementDilation.lean`, `overlapConst`). The per-round mutually-unbiased qubit value
`c = 1/2` (`q = 1`) is an instantiation (`ConcreteMeasurementBases.lean`), not proved here. This is
the **per-round / single-system** statement: the n-fold tensor lift `q ↦ n·q` (the per-round `c =
1/2`
cannot substitute for the n-fold quantity) is `TensorBasis.lean`'s
`overlapConst_tensorPow` / `preparationQuality_tensorPow`, not this module.

## The factor-swap bridge

The `n·|X| ↔ |X|·n` factor-swap bridge relates the CQ and bipartite layouts. The lift
below is **bipartite-native** — both sides use `bipartiteMinEntropyOptReal` on the standard
system-first `X ⊗ B` / `Z ⊗ Z′AB` layouts — so it does not consume the swap. The bridge is provided
here anyway, as the missing member of the CQ-agreement seam (`BipartiteMinMax.lean`), relating
`bipartiteMinEntropyReal` on the reindexed (system-first) joint density to the CQ
`conditionalMinEntropyReal` (quantum-first). See `bipartiteMinEntropyReal_reindexSwap_eq_cq`.

## Layering

* **Object layer.** The leading-factor left isometry `V ⊗ 1_B` (`kronLeftIsoId`), the
  measurement dilation of a state (`measDilate`), the heterogeneous sub-density reindex
  (`SubDensityOp.reindexHetero`), the `X`-measured marginal (`xMeasuredMarginal`) and the Z-dilated
  state in the entropy layout (`zDilatedState`).
* **Recovery layer.** `measConjTraceMap_measDilate_eq_xMeasuredMarginal` (`eqn:mo10`).
* **Reference-side helpers.** `SubDensityOp.partialTraceA` (the `B`-marginal of a
  reference on `Z′A ⊗ B`) and the `Op.castDim`/reindex invariances of `dmaxFeasibleLambda`.

The `D_max` transport layer and the OPT-level pure core (`eqn:mo3`, `measDilation_pure_core`) are
`MeasurementTransport.lean`; their ε-smooth lift is `SmoothUncertaintyRelation.lean`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## The leading-factor rectangular left isometry `V ⊗ 1_R`

Mirror of `kronIdLeftIso` (`1_H ⊗ V`) with the rectangular map on the **left** factor. This is the
isometry that dilates the measured register `A` (leading factor of `ρ_AB`) while carrying the
spectator `B` along.
-/

/-- The Kronecker product of a rectangular map `V` with the identity on `dR` dimensions:
`V ⊗ 1_{dR} : Matrix (Fin (dTgt * dR)) (Fin (dSrc * dR)) ℂ`, acting on the **left** register of the
bipartite space `ℂ^{dSrc} ⊗ ℂ^{dR}`. When `V` is a left isometry (`Vᴴ V = 1`), so is `V ⊗ 1_{dR}`
(`kronLeftIsoId_left_iso`). For square `V` it is definitionally `Op.tensor V 1`. -/
noncomputable def kronLeftIsoId {dSrc dTgt : ℕ} (dR : ℕ)
    (V : Matrix (Fin dTgt) (Fin dSrc) ℂ) :
    Matrix (Fin (dTgt * dR)) (Fin (dSrc * dR)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) V (1 : Matrix (Fin dR) (Fin dR) ℂ))

/-- For a square map, `V ⊗ 1_{dR}` is exactly `Op.tensor V 1`. -/
lemma Op.tensor_one_eq_kronLeftIsoId {n dR : ℕ} (V : Op n) :
    Op.tensor V (1 : Op dR) = kronLeftIsoId dR V :=
  rfl

/-- Conjugate transpose distributes: `(V ⊗ 1)ᴴ = Vᴴ ⊗ 1`. -/
lemma kronLeftIsoId_conjTranspose {dSrc dTgt dR : ℕ} (V : Matrix (Fin dTgt) (Fin dSrc) ℂ) :
    (kronLeftIsoId dR V)ᴴ = kronLeftIsoId dR Vᴴ := by
  dsimp [kronLeftIsoId, Matrix.reindex]
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Mixed-product identity: `(A ⊗ 1)(B ⊗ 1) = (A B) ⊗ 1`. -/
lemma kronLeftIsoId_mul {dR a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) :
    kronLeftIsoId dR A * kronLeftIsoId dR B = kronLeftIsoId dR (A * B) := by
  dsimp [kronLeftIsoId, Matrix.reindex]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- `V ⊗ 1_{dR}` is a left isometry when `V` is: `(V ⊗ 1)ᴴ (V ⊗ 1) = 1`. -/
theorem kronLeftIsoId_left_iso {dSrc dTgt dR : ℕ} (V : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hV : Vᴴ * V = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ)) :
    (kronLeftIsoId dR V)ᴴ * kronLeftIsoId dR V =
      (1 : Matrix (Fin (dSrc * dR)) (Fin (dSrc * dR)) ℂ) := by
  rw [kronLeftIsoId_conjTranspose, kronLeftIsoId_mul, hV]
  dsimp [kronLeftIsoId, Matrix.reindex]
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-!
## Heterogeneous sub-density reindex

`SubDensityOp.reindex` (`PurifiedDistanceReindex.lean`) is homogeneous (`Fin n ≃ Fin n`); the
measurement partial-trace reindex `measTraceReindex` (`MeasurementDilation.lean`) permutes between
two arrangements of equal cardinality (`Fin (d·d·d·dB) ≃ Fin (d·dB·(d·d))`). Reindexing by a single
equivalence on rows and columns is unitary conjugation by a permutation, hence preserves the PSD
order and the trace.
-/

/-!
## The dilated state and the `X`-measured marginal

`measDilate R ρ_AB := (R.dilationIso ⊗ 1_B) ρ_AB (R.dilationIso ⊗ 1_B)ᴴ` on the dilated register
`R ⊗ R′ ⊗ A ⊗ B` (`tr.tex:292`, `ρ_{XX′AB} := U ρ_{ABC} Uᴴ` / `ρ_{ZZ′AB} := V ρ_{ABC} Vᴴ`,
specialized to the sub-normalized state on `A ⊗ B`). Sub-normalization is automatic via
`subDensityOpLeftIsometryEmbed`.
-/

/-- The **measurement dilation of a state** `R ρ_AB Rᴴ` on `R ⊗ R′ ⊗ A ⊗ B` for a rank-1 projective
basis `R` (`tr.tex:292`): the state after applying the Stinespring dilation isometry
`R.dilationIso ⊗ 1_B` (`R` on the measured register `A`, spectator `B` carried along). -/
noncomputable def measDilate {d dB : ℕ} (R : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : SubDensityOp (d * d * d * dB) :=
  subDensityOpLeftIsometryEmbed (kronLeftIsoId dB R.dilationIso)
    (kronLeftIsoId_left_iso R.dilationIso R.dilationIso_isometry) ρAB

@[simp]
lemma measDilate_toOp {d dB : ℕ} (R : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) :
    (measDilate R ρAB).toOp =
      kronLeftIsoId dB R.dilationIso * ρAB.toOp * (kronLeftIsoId dB R.dilationIso)ᴴ :=
  rfl

/-- The **`X`-measured marginal** `ρ_XB = Tr_{X′A}(U ρ_AB Uᴴ)` on `X ⊗ B` (`tr.tex:293`, the
post-measurement state that Theorem `thm:mother` conditions on): reorder the `X`-dilation
`measDilate P ρ_AB` to `X ⊗ B ⊗ (X′ ⊗ A)` (`measTraceReindex`) and trace out the trailing
`X′ ⊗ A` block. -/
noncomputable def xMeasuredMarginal {d dB : ℕ} (P : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : SubDensityOp (d * dB) :=
  SubDensityOp.partialTraceB
    (SubDensityOp.reindexHetero (measTraceReindex d dB) (measDilate P ρAB))

/-- The **Z-dilated state in the entropy layout** `ρ_ZZ′AB` on `Z ⊗ (Z′ ⊗ A ⊗ B)`: the Z-dilation
`measDilate Q ρ_AB`, reassociated from `d·d·d·dB` to `d·(d·d·dB)` so that the system register `Z`
(dimension `d`) is the leading factor and `Z′AB` (dimension `d·d·dB`) the conditioning factor, as
`bipartiteMinEntropyOptReal` expects. -/
noncomputable def zDilatedState {d dB : ℕ} (Q : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : SubDensityOp (d * (d * d * dB)) :=
  SubDensityOp.castDim (by ring) (measDilate Q ρAB)

/-!
## The three constructions are trace-preserving

The dilation conjugates by a left isometry, the entropy-layout cast is a relabelling, and the
`X`-measured marginal is a reindex followed by a partial trace. All three therefore carry the
trace of `ρ_AB` unchanged. This is what makes the nondegeneracy side-conditions of the entropy
transport (`MeasurementTransport.lean`) reducible to `ρ_AB ≠ 0`, rather than assumed.
-/

/-- The measurement dilation is trace-preserving: `Tr(R ρ_AB Rᴴ) = Tr ρ_AB`. -/
@[simp] lemma measDilate_trace {d dB : ℕ} (R : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : (measDilate R ρAB).trace = ρAB.trace :=
  subDensityOpLeftIsometryEmbed_trace _ _ ρAB

/-- The Z-dilated state in the entropy layout has the trace of `ρ_AB`. -/
@[simp] lemma zDilatedState_trace {d dB : ℕ} (Q : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : (zDilatedState Q ρAB).trace = ρAB.trace := by
  rw [zDilatedState, SubDensityOp.castDim_trace, measDilate_trace]

/-- The `X`-measured marginal has the trace of `ρ_AB`: `Tr ρ_XB = Tr(U ρ_AB Uᴴ) = Tr ρ_AB`. -/
@[simp] lemma xMeasuredMarginal_trace {d dB : ℕ} (P : RankOneProjectiveBasis d)
    (ρAB : SubDensityOp (d * dB)) : (xMeasuredMarginal P ρAB).trace = ρAB.trace := by
  rw [xMeasuredMarginal, SubDensityOp.trace_partialTraceB, SubDensityOp.reindexHetero_trace,
    measDilate_trace]

/-!
## The recovery identity `eqn:mo10`
-/

/-- **`eqn:mo10` — the recovery identity.** Applying the measurement
conjugation-trace map `Ξ = measConjTraceMap (U Vᴴ)` to the Z-dilated state recovers the `X`-measured
marginal:

`Tr_{X′A}( W (ρ_ZZ′AB) Wᴴ ) = ρ_XB` .

Both sides apply the same `partialTraceB ∘ reindex` wrapper, so the identity reduces to the inner
operator equality `(W ⊗ 1_B)(V ⊗ 1_B) = (U ⊗ 1_B)`, i.e. `W V = U`, i.e. `U Vᴴ V = U`, consuming the
`Z`-dilation isometry certificate `Vᴴ V = 1` (Q.dilationIso_isometry). No evaluation of the
non-adjacent partial trace is required (that is the `eqn:mo8/mo9` reference bound). -/
theorem measConjTraceMap_measDilate_eq_xMeasuredMarginal {d dB : ℕ}
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB)) :
    measConjTraceMap (P.partialIsometryW Q) (measDilate Q ρAB).toOp =
      (xMeasuredMarginal P ρAB).toOp := by
  -- The inner operator identity `(W ⊗ 1)(V ⊗ 1) ρ (V ⊗ 1)ᴴ (W ⊗ 1)ᴴ = (U ⊗ 1) ρ (U ⊗ 1)ᴴ`.
  have hWV : P.partialIsometryW Q * Q.dilationIso = P.dilationIso := by
    unfold RankOneProjectiveBasis.partialIsometryW
    rw [Matrix.mul_assoc, Q.dilationIso_isometry, Matrix.mul_one]
  have hWK : Op.tensor (P.partialIsometryW Q) (1 : Op dB) * kronLeftIsoId dB Q.dilationIso =
      kronLeftIsoId dB P.dilationIso := by
    rw [Op.tensor_one_eq_kronLeftIsoId, kronLeftIsoId_mul, hWV]
  have hWKd : (kronLeftIsoId dB Q.dilationIso)ᴴ *
      (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ = (kronLeftIsoId dB P.dilationIso)ᴴ := by
    rw [← Matrix.conjTranspose_mul, hWK]
  have hinner :
      Op.tensor (P.partialIsometryW Q) (1 : Op dB) * (measDilate Q ρAB).toOp *
          (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ =
        (measDilate P ρAB).toOp := by
    rw [measDilate_toOp, measDilate_toOp]
    calc Op.tensor (P.partialIsometryW Q) (1 : Op dB) *
            (kronLeftIsoId dB Q.dilationIso * ρAB.toOp * (kronLeftIsoId dB Q.dilationIso)ᴴ) *
            (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ
        = (Op.tensor (P.partialIsometryW Q) (1 : Op dB) * kronLeftIsoId dB Q.dilationIso) *
            ρAB.toOp *
            ((kronLeftIsoId dB Q.dilationIso)ᴴ *
              (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = kronLeftIsoId dB P.dilationIso * ρAB.toOp * (kronLeftIsoId dB P.dilationIso)ᴴ := by
          rw [hWK, hWKd]
  unfold measConjTraceMap xMeasuredMarginal
  rw [SubDensityOp.partialTraceB_toOp, SubDensityOp.reindexHetero_toOp, hinner]

/-!
## Reference-side helpers

The `B`-marginal `σ_B = Tr_{Z′A}(σ)` of a reference `σ` on `Z′ ⊗ A ⊗ B`, and the `Op.castDim`
invariance of `dmaxFeasibleLambda` needed to move between the raw dilated register `d·d·d·dB`
(used by `MeasurementDilation.lean`) and the entropy layout `d·(d·d·dB)`. The overlap constant's
nonnegativity
(`RankOneProjectiveBasis.overlapConst_nonneg`) and the derived preparation quality
`RankOneProjectiveBasis.preparationQuality` now live with `overlapConst` itself, in
`MeasurementDilation.lean`.
-/

/-- The `B`-marginal `Tr_{Z′A}(σ)` of a sub-normalized reference `σ` on `(Z′ ⊗ A) ⊗ B`, tracing out
the leading `Z′ ⊗ A` block. Sub-normalized (partial trace preserves PSD and trace). -/
noncomputable def SubDensityOp.partialTraceA {n m : ℕ} (ρ : SubDensityOp (n * m)) :
    SubDensityOp m where
  toOp := Quantum.TensorProducts.partialTraceA ρ.toOp
  isHermitian := Quantum.TensorProducts.partialTraceA_hermitian ρ.toOp ρ.isHermitian
  pos_semidef := Quantum.TensorProducts.partialTraceA_posSemidef ρ.toPosSemidefOp
  trace_le_one := by
    rw [Quantum.TensorProducts.trace_partialTraceA]
    exact ρ.trace_le_one

@[simp]
lemma SubDensityOp.partialTraceA_toOp {n m : ℕ} (ρ : SubDensityOp (n * m)) :
    ρ.partialTraceA.toOp = Quantum.TensorProducts.partialTraceA ρ.toOp :=
  rfl

/-- **The `D_max` SDP scalar is `Op.castDim`-invariant.** Transporting both arguments across a
dimension equality is a relabelling, so the feasible set — and hence its infimum — is unchanged.
The reindex analogue is `dmaxFeasibleLambda_reindexHetero` below. -/
lemma dmaxFeasibleLambda_op_castDim {n m : ℕ} (h : n = m) (A B : Op n) :
    dmaxFeasibleLambda (Op.castDim h A) (Op.castDim h B) = dmaxFeasibleLambda A B := by
  subst h; rfl

/-!
## The `n·|X| ↔ |X|·n` factor-swap bridge

The pure-core lift uses bipartite layouts and does not consume the factor swap.
The factor-swap bridge of `BipartiteMinMax.lean` relates the general-bipartite
`bipartiteMinEntropyReal` on the (system-first, `|X|·n`) reindexed joint density to the CQ
`conditionalMinEntropyReal` (quantum-first, `n·|X|`).
-/

/-- The tensor-factor swap equivalence `Fin (n · m) ≃ Fin (m · n)`, relabelling `A ⊗ B` as
`B ⊗ A`. -/
def swapTensorEquiv (n m : ℕ) : Fin (n * m) ≃ Fin (m * n) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin n) (Fin m)).trans finProdFinEquiv)

/-- `D_max`-feasibility is invariant under a simultaneous rectangular reindex of both arguments. -/
lemma dmaxIsFeasible_reindexHetero_iff {n m : ℕ} (e : Fin n ≃ Fin m) (A Q : Op n) (t : ℝ) :
    dmaxIsFeasible (Matrix.reindex e e A) (Matrix.reindex e e Q) t ↔ dmaxIsFeasible A Q t := by
  unfold dmaxIsFeasible
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hle
    rw [← Matrix.reindex_smul] at hle
    have h := opLe_reindex_rect e.symm hle
    rwa [Matrix.reindex_symm_reindex, Matrix.reindex_symm_reindex] at h
  · intro hle
    rw [← Matrix.reindex_smul]
    exact opLe_reindex_rect e hle

/-- **`D_max` SDP-scalar reindex invariance.** `dmaxFeasibleLambda` is unchanged by a simultaneous
rectangular reindex of both arguments (a unitary relabelling). -/
theorem dmaxFeasibleLambda_reindexHetero {n m : ℕ} (e : Fin n ≃ Fin m) (A Q : Op n) :
    dmaxFeasibleLambda (Matrix.reindex e e A) (Matrix.reindex e e Q) = dmaxFeasibleLambda A Q := by
  unfold dmaxFeasibleLambda
  congr 1
  ext t
  exact dmaxIsFeasible_reindexHetero_iff e A Q t

/-- `(finProdFinEquiv (a, b)).divNat = a` and `.modNat = b`. -/
private lemma finProdFinEquiv_divNat_modNat {a b : ℕ} (x : Fin a) (y : Fin b) :
    (finProdFinEquiv (x, y)).divNat = x ∧ (finProdFinEquiv (x, y)).modNat = y := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (x, y))
  rw [Equiv.symm_apply_apply] at h
  exact ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2.symm⟩

/-- The tensor-factor swap relabels `A ⊗ B` as `B ⊗ A`:
`reindex (swapTensorEquiv n m) (A ⊗ B) = B ⊗ A`. -/
lemma reindex_swapTensorEquiv_tensor {n m : ℕ} (A : Op n) (B : Op m) :
    Matrix.reindex (swapTensorEquiv n m) (swapTensorEquiv n m) (Op.tensor A B) = Op.tensor B A := by
  ext i j
  simp only [swapTensorEquiv, Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.kroneckerMap_apply,
    finProdFinEquiv_symm_apply]
  rw [(finProdFinEquiv_divNat_modNat i.modNat i.divNat).1,
    (finProdFinEquiv_divNat_modNat i.modNat i.divNat).2,
    (finProdFinEquiv_divNat_modNat j.modNat j.divNat).1,
    (finProdFinEquiv_divNat_modNat j.modNat j.divNat).2]
  ring

/-- **The factor-swap bridge.** The general-bipartite conditional min-entropy of the
(system-first, `|X|·n`) reindexed CQ joint density, referenced against `1_X ⊗ σ`, equals the CQ
conditional min-entropy `conditionalMinEntropyReal` (quantum-first, `n·|X|`, referenced against
`σ ⊗ 1_X`). The two differ only by the `n·|X| ↔ |X|·n` tensor-factor swap; `dmaxFeasibleLambda` is
invariant under it (`dmaxFeasibleLambda_reindexHetero`) once the reference tensor is transported
(`reindex_swapTensorEquiv_tensor`). -/
theorem bipartiteMinEntropyReal_reindexSwap_eq_cq
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    bipartiteMinEntropyReal
        (SubDensityOp.reindexHetero (swapTensorEquiv n (Fintype.card X)) ρ.toJointDensity) σ =
      conditionalMinEntropyReal ρ σ := by
  rw [conditionalMinEntropyReal_eq_dmax_toJointDensity_tensor_one]
  unfold bipartiteMinEntropyReal
  rw [SubDensityOp.reindexHetero_toOp,
    ← reindex_swapTensorEquiv_tensor σ.toOp (1 : Op (Fintype.card X)),
    dmaxFeasibleLambda_reindexHetero]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
