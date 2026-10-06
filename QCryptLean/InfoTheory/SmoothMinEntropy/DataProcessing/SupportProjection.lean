import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.IsometryConjugation
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.SupportCompression
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning

/-!
# Renner `rem:Hinfex` support-projection CPM

This file builds the **support-projection completely-positive map (CPM)** of
Renner 2005 (thesis arXiv:quant-ph/0512258v2, Remark `rem:Hinfex`): for an
orthogonal projector `P` (Hermitian idempotent), the map

    `E(ρ) = P · ρ · P`

applied blockwise to a classical-quantum state.  Renner's remark restricts the
supremum in the smooth conditional min-entropy to operators whose image lies in
`im(ρ_A) ⊗ im(σ_B)`; the support-projection CPM (sandwich by the support
projector of the reference) realizes that restriction.  Two analytic properties
are isolated here as named, proved lemmas:

* **`lem:distdecr`** — the CPM does not increase purified distance to a center it
  fixes (`supportProjectionCPM_purifiedDistance_le_of_fixed`).

* **`lem:Hinfclassop`** — the CPM does not decrease the conditional min-entropy
  when the entropy reference is contracted by `P`
  (`supportProjectionCPM_conditionalMinEntropyReal_le`).

## Main definitions
- `IsOrthogonalProjector`: a Hermitian idempotent matrix.
- `SubDensityOp.projectorSandwich`: `ρ ↦ P · ρ · P` on a sub-density operator.
- `CQState.supportProjectionCPM`: the blockwise support-projection CPM `E`.

## Main statements
- `supportProjectionCPM_minFeasibleLambda_le` (`lem:Hinfclassop`, λ-form).
- `supportProjectionCPM_conditionalMinEntropyReal_le` (`lem:Hinfclassop`).
- `supportProjectionCPM_purifiedDistance_le_of_fixed` (`lem:distdecr`).
- `supportProjectionCPM_fixes_of_supported`: `E` fixes states supported on `im(P)`.
- `supportProjector_isOrthogonalProjector`: the reference support projector is an
  orthogonal projector.
-/

open Quantum.Operators Matrix
open InfoTheory.RelativeEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Orthogonal projectors -/

/-- An orthogonal projector: a Hermitian idempotent matrix. -/
structure IsOrthogonalProjector {n : ℕ} (P : Op n) : Prop where
  /-- The projector is Hermitian. -/
  isHermitian : P.IsHermitian
  /-- The projector is idempotent. -/
  idempotent : P * P = P

/-- The reference support projector `supportProjector σ` is an orthogonal
projector. -/
lemma supportProjector_isOrthogonalProjector {N : ℕ} (σ : DensityOp N) :
    IsOrthogonalProjector (supportProjector σ) where
  isHermitian := supportProjector_isHermitian σ
  idempotent := by
    -- P = V Vᴴ with Vᴴ V = 1, so P P = V (Vᴴ V) Vᴴ = V Vᴴ = P.
    unfold supportProjector
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (supportIsometry σ).conjTranspose,
      supportIsometry_isometry σ, Matrix.one_mul]

/-! ## Blockwise projector sandwich -/

/-- The conjugate `P · A · P` of a PSD operator by an orthogonal projector is
PSD: `⟨v, P A P v⟩ = ⟨P v, A (P v)⟩ ≥ 0`. -/
lemma projectorSandwich_posSemidef {n : ℕ} {P : Op n}
    (hP : IsOrthogonalProjector P) {A : Op n}
    (hA : ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm A v).re) :
    ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (P * A * P) v).re := by
  intro v
  have := Quantum.Channels.quadraticForm_kraus_sandwich P A v
  rw [hP.isHermitian] at this
  rw [this]
  exact hA (P.mulVec v)

/-- An orthogonal projector is positive semidefinite: `P = Pᴴ · P`. -/
lemma IsOrthogonalProjector.posSemidef {n : ℕ} {P : Op n}
    (hP : IsOrthogonalProjector P) : P.PosSemidef := by
  have h : P = P.conjTranspose * P := by
    rw [hP.isHermitian, hP.idempotent]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self P

/-- The complement `1 - P` of an orthogonal projector is an orthogonal
projector, hence positive semidefinite. -/
lemma IsOrthogonalProjector.one_sub_posSemidef {n : ℕ} {P : Op n}
    (hP : IsOrthogonalProjector P) :
    ((1 : Op n) - P).PosSemidef := by
  have hHerm : ((1 : Op n) - P).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian]
  have hidem : ((1 : Op n) - P) * ((1 : Op n) - P) = (1 : Op n) - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hP.idempotent]
    abel
  have h : (1 : Op n) - P = ((1 : Op n) - P).conjTranspose * ((1 : Op n) - P) := by
    rw [hHerm, hidem]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- An orthogonal projector contracts the maximally-mixed reference:
`P · ((1/d)·I) · P = (1/d)·P ⪯ (1/d)·I`.

This supplies the `hσ_contract` hypothesis of `lem:Hinfclassop` for the
maximally-mixed calibration reference used in the BB84 conditional min-entropy
SDP.  General PSD references are *not* contracted by
arbitrary projectors; the maximally-mixed reference is contracted because it is a
scalar multiple of the identity and therefore commutes with `P`. -/
lemma supportProjector_contracts_maxMixed {n : ℕ} [NeZero n] {P : Op n}
    (hP : IsOrthogonalProjector P) :
    opLe (P * (DensityOp.maxMixed n).toOp * P) (DensityOp.maxMixed n).toOp := by
  have hd_nonneg : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  -- `P · ((1/n)•I) · P = (1/n) • P`.
  have hsandwich : P * (DensityOp.maxMixed n).toOp * P
      = (Complex.ofReal (1 / (n : ℝ))) • P := by
    change P * ((1 / (n : ℂ)) • (1 : Op n)) * P = (Complex.ofReal (1 / (n : ℝ))) • P
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP.idempotent]
    congr 1
    push_cast
    ring
  have hmm : (DensityOp.maxMixed n).toOp = (Complex.ofReal (1 / (n : ℝ))) • (1 : Op n) := by
    change (1 / (n : ℂ)) • (1 : Op n) = (Complex.ofReal (1 / (n : ℝ))) • (1 : Op n)
    congr 1
    push_cast; ring
  rw [hsandwich, hmm]
  -- `(1/n)•P ⪯ (1/n)•I` since `I - P ⪰ 0`.
  refine opLe_smul_nonneg hd_nonneg ?_
  exact Quantum.Operators.opLe_of_posSemidef_sub (by simpa using hP.one_sub_posSemidef)

/-- The trace deficit of a projector sandwich: `Re tr(P A P) ≤ Re tr A` for PSD
`A` and an orthogonal projector `P`.

This is `tr(P A P) = tr(P A)` (cyclicity + idempotence) and
`tr A - tr(P A) = tr((1 - P) A) ≥ 0` since `1 - P` and `A` are both PSD. -/
lemma projectorSandwich_trace_re_le {n : ℕ} {P : Op n}
    (hP : IsOrthogonalProjector P) {A : Op n}
    (hA : A.PosSemidef) :
    (P * A * P).trace.re ≤ A.trace.re := by
  have hcyc : (P * A * P).trace = (P * A).trace := by
    rw [Matrix.trace_mul_cycle, hP.idempotent]
  have hdiff : A.trace - (P * A).trace = (((1 : Op n) - P) * A).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  have hnn : 0 ≤ (((1 : Op n) - P) * A).trace.re :=
    Quantum.Operators.trace_mul_psd_nonneg _ _ hP.one_sub_posSemidef hA
  have : 0 ≤ A.trace.re - (P * A).trace.re := by
    have := congrArg Complex.re hdiff
    rw [Complex.sub_re] at this
    rw [this]; exact hnn
  rw [hcyc]; linarith

/-- The blockwise projector sandwich of a sub-density operator: `ρ ↦ P · ρ · P`.

For an orthogonal projector `P`, this is again a sub-density operator (PSD and
trace `≤ 1`), the single-block primitive of the support-projection CPM. -/
def SubDensityOp.projectorSandwich {n : ℕ} (P : Op n)
    (hP : IsOrthogonalProjector P) (ρ : SubDensityOp n) : SubDensityOp n where
  toOp := P * ρ.toOp * P
  isHermitian := Quantum.TensorProducts.projector_sandwich_isHermitian hP.isHermitian ρ.isHermitian
  pos_semidef := projectorSandwich_posSemidef hP ρ.pos_semidef
  trace_le_one :=
    le_trans (projectorSandwich_trace_re_le hP
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)) ρ.trace_le_one

@[simp]
lemma SubDensityOp.projectorSandwich_toOp {n : ℕ} (P : Op n)
    (hP : IsOrthogonalProjector P) (ρ : SubDensityOp n) :
    (ρ.projectorSandwich P hP).toOp = P * ρ.toOp * P :=
  rfl

/-! ## The support-projection CPM on CQ states -/

/-- **The support-projection CPM** `E(ρ) = P · ρ · P` (Renner `rem:Hinfex`).

Applied blockwise to a classical-quantum state: each conditional state
`ρ.stateMap x` is sandwiched by the orthogonal projector `P`.  The total weight
is preserved or decreased blockwise, so the result is again a CQ state. -/
def CQState.supportProjectionCPM {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P) (ρ : CQState X n) : CQState X n where
  stateMap x := (ρ.stateMap x).projectorSandwich P hP
  weight_le_one :=
    le_trans
      (Finset.sum_le_sum fun x _ =>
        projectorSandwich_trace_re_le hP
          (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp))
      ρ.weight_le_one

@[simp]
lemma CQState.supportProjectionCPM_stateMap_toOp {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P) (ρ : CQState X n) (x : X) :
    ((ρ.supportProjectionCPM P hP).stateMap x).toOp = P * (ρ.stateMap x).toOp * P :=
  rfl

/-! ## `lem:Hinfclassop` — conditional min-entropy does not decrease -/

/-- Feasibility is preserved under the support-projection CPM when the projector
contracts the reference (`P · σ · P ⪯ σ` in the Löwner order): any feasible scalar
for `(ρ, σ)` is feasible for `(E ρ, σ)`.

Proof: `tσ ⪰ ρ_x ⟹ P(tσ)P ⪰ Pρ_xP`, and `P(tσ)P = t·(PσP) ⪯ t·σ`, so
`t·σ ⪰ P(tσ)P ⪰ Pρ_xP = (Eρ)_x`.

The contraction hypothesis `hσ_contract` is genuinely required: a general
orthogonal projector does *not* satisfy `PσP ⪯ σ` for arbitrary PSD `σ`.  It does
hold for the maximally-mixed calibration reference `σ = (1/d)·I`
(`supportProjector_contracts_maxMixed`), where `PσP = (1/d)·P ⪯ (1/d)·I = σ`, and
for any reference fixed by `P` (`PσP = σ`), where it holds with equality. -/
lemma isFeasible_supportProjectionCPM_of_isFeasible
    {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P)
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_contract : opLe (P * σ.toOp * P) σ.toOp)
    {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible (ρ.supportProjectionCPM P hP) σ t := by
  refine ⟨ht.1, fun x => ?_⟩
  have hx := ht.2 x
  have hconj := Quantum.Channels.opLe_kraus_sandwich P hx
  rw [hP.isHermitian] at hconj
  have hσ_smul : P * ((Complex.ofReal t) • σ.toOp) * P =
      (Complex.ofReal t) • (P * σ.toOp * P) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hσ_smul] at hconj
  -- `t·(PσP) ⪯ t·σ`, so chain dominates `(Eρ)_x = Pρ_xP`.
  have hcontract_smul : opLe ((Complex.ofReal t) • (P * σ.toOp * P))
      ((Complex.ofReal t) • σ.toOp) := opLe_smul_nonneg ht.1 hσ_contract
  exact opLe_trans (by simpa [CQState.supportProjectionCPM_stateMap_toOp] using hconj)
    hcontract_smul

/-- **Renner `lem:Hinfclassop` (λ-form).** When the projector contracts the entropy
reference (`P · σ · P ⪯ σ`) and the SDP is feasible for `(ρ, σ)`, the
support-projection CPM does not increase `minFeasibleLambda`.

The feasibility hypothesis `hfeas` makes the original feasible set nonempty, which
is what bounds the infimum from above. -/
lemma supportProjectionCPM_minFeasibleLambda_le
    {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P)
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_contract : opLe (P * σ.toOp * P) σ.toOp)
    (hfeas : hasFeasibleLambda ρ σ) :
    minFeasibleLambda (ρ.supportProjectionCPM P hP) σ ≤ minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  obtain ⟨t, ht⟩ := hfeas
  exact csInf_le_csInf (minFeasibleLambda_bddBelow _ σ) ⟨t, ht⟩
    (fun s hs => isFeasible_supportProjectionCPM_of_isFeasible P hP ρ σ hσ_contract hs)

/-- **Renner `lem:Hinfclassop`.** When the entropy reference `σ` is contracted by the
projector (`P · σ · P ⪯ σ`) and the CPM image is feasible with a strictly positive
optimum, the support-projection CPM does not decrease the real-valued conditional
min-entropy.

The strict-positivity hypothesis `hpos` is required because
`conditionalMinEntropyReal` is defined via `Real.log (minFeasibleLambda …)`, whose
value at `0` is a junk sentinel; positivity of the optimum keeps the logarithm
monotone and honest at the boundary. -/
lemma supportProjectionCPM_conditionalMinEntropyReal_le
    {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P)
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_contract : opLe (P * σ.toOp * P) σ.toOp)
    (hfeas : hasFeasibleLambda ρ σ)
    (hpos : 0 < minFeasibleLambda (ρ.supportProjectionCPM P hP) σ) :
    conditionalMinEntropyReal ρ σ ≤
      conditionalMinEntropyReal (ρ.supportProjectionCPM P hP) σ := by
  have hle := supportProjectionCPM_minFeasibleLambda_le P hP ρ σ hσ_contract hfeas
  unfold conditionalMinEntropyReal
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_le :
      Real.log (minFeasibleLambda (ρ.supportProjectionCPM P hP) σ) ≤
        Real.log (minFeasibleLambda ρ σ) :=
    Real.log_le_log hpos hle
  apply div_le_div_of_nonneg_right (by linarith) (le_of_lt hlog2)

/-! ## `lem:distdecr` — purified distance does not increase -/

/-- The principal square root of a PSD operator supported on `im P` is annihilated
by the complementary projector on the right: `√A · (1 - P) = 0` when `P · A · P = A`.

The square root inherits the support of `A`: from `P A P = A` one has
`A (1 - P) = 0`, and `(√A (1 - P))ᴴ (√A (1 - P)) = (1 - P) A (1 - P) = 0`, so the
factor `√A (1 - P)` vanishes (`Matrix.conjTranspose_mul_self_eq_zero`). -/
lemma sqrtPosSemidefOp_mul_one_sub_projector_eq_zero {n : ℕ} {P : Op n}
    (hP : IsOrthogonalProjector P) (A : PosSemidefOp n)
    (hAfix : P * A.toOp * P = A.toOp) :
    Quantum.Metrics.sqrtPosSemidefOp A * ((1 : Op n) - P) = 0 := by
  set S := Quantum.Metrics.sqrtPosSemidefOp A
  have hSherm : Sᴴ = S := Quantum.Metrics.sqrtPosSemidefOp_isHermitian A
  have hSsq : S * S = A.toOp := Quantum.Metrics.sqrtPosSemidefOp_sq A
  have hAP : A.toOp * P = A.toOp := by
    conv_lhs => rw [← hAfix]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hP.idempotent, ← Matrix.mul_assoc, hAfix]
  have hAcompl : A.toOp * ((1 : Op n) - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hAP, sub_self]
  have hcompl_herm : ((1 : Op n) - P)ᴴ = (1 : Op n) - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian]
  have hzero : (S * ((1 : Op n) - P))ᴴ * (S * ((1 : Op n) - P)) = 0 := by
    rw [Matrix.conjTranspose_mul, hcompl_herm, hSherm]
    calc ((1 : Op n) - P) * S * (S * ((1 : Op n) - P))
        = ((1 : Op n) - P) * (S * S) * ((1 : Op n) - P) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ((1 : Op n) - P) * (A.toOp * ((1 : Op n) - P)) := by rw [hSsq, Matrix.mul_assoc]
      _ = 0 := by rw [hAcompl, Matrix.mul_zero]
  exact Matrix.conjTranspose_mul_self_eq_zero.mp hzero

/-- **Ordinary Uhlmann fidelity is unchanged by the projector sandwich on the
right argument, when the left argument is supported on `im P`.**

For an orthogonal projector `P`, a PSD operator `A` fixed by the sandwich
(`P A P = A`), and any PSD `B`, the fidelity to `B` equals the fidelity to
`P B P`: `F(A, B) = F(A, P B P)`.  Indeed `√A = √A · P = P · √A`, so the inner
product `√A · B · √A` is unchanged when `B` is replaced by `P B P`. -/
lemma fidelity_eq_of_projectorSandwich_of_fixed {n : ℕ} [NeZero n] {P : Op n}
    (hP : IsOrthogonalProjector P) (A B C : PosSemidefOp n)
    (hAfix : P * A.toOp * P = A.toOp)
    (hC : C.toOp = P * B.toOp * P) :
    Quantum.Metrics.fidelity A B = Quantum.Metrics.fidelity A C := by
  set S := Quantum.Metrics.sqrtPosSemidefOp A
  have hScompl : S * ((1 : Op n) - P) = 0 :=
    sqrtPosSemidefOp_mul_one_sub_projector_eq_zero hP A hAfix
  have hSherm : Sᴴ = S := Quantum.Metrics.sqrtPosSemidefOp_isHermitian A
  have hSP : S * P = S := by
    have h := hScompl
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have hPS : P * S = S := by
    have h2 : ((1 : Op n) - P) * S = 0 := by
      have h := congrArg Matrix.conjTranspose hScompl
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hP.isHermitian, hSherm, Matrix.conjTranspose_zero] at h
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h2
    exact h2.symm
  have hinner : S * B.toOp * S = S * C.toOp * S := by
    rw [hC]
    calc S * B.toOp * S = (S * P) * B.toOp * (P * S) := by rw [hSP, hPS]
      _ = S * (P * B.toOp * P) * S := by simp only [Matrix.mul_assoc]
  unfold Quantum.Metrics.fidelity
  rw [hinner]

/-- **Renner `lem:distdecr`.** The support-projection CPM does not increase the CQ
purified distance to a center `c` it fixes (`E c = c`).

The fixed-center hypothesis `hc_fixed` is essential: it forces each center block
to be supported on `im P`, so ordinary fidelity to `c` is unchanged by the
sandwich while the sub-normalization correction can only grow (`E` is
trace-non-increasing blockwise).

Reference: Tomamichel 2016, §3.4; Renner 2005, `lem:distdecr`. -/
lemma supportProjectionCPM_purifiedDistance_le_of_fixed
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (P : Op n) (hP : IsOrthogonalProjector P)
    (c ρ : CQState X n)
    (hc_fixed : c.supportProjectionCPM P hP = c) :
    CQState.purifiedDistance c (ρ.supportProjectionCPM P hP) ≤
      CQState.purifiedDistance c ρ := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  -- Each center block is fixed by the projector sandwich.
  have hc_block : ∀ x : X, P * (c.stateMap x).toOp * P = (c.stateMap x).toOp := by
    intro x
    have hx := congrArg (fun s => (s.stateMap x).toOp) hc_fixed
    simpa [CQState.supportProjectionCPM_stateMap_toOp] using hx
  -- It suffices to show the generalized fidelity to the fixed center does not decrease.
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_fidelityGen_ge
  -- Goal: F*(c, ρ) ≤ F*(c, E ρ).
  unfold fidelityGen
  -- Ordinary fidelity is unchanged blockwise, hence on the joint density.
  have hF :
      Quantum.Metrics.fidelity c.toJointDensity.toPosSemidefOp ρ.toJointDensity.toPosSemidefOp =
        Quantum.Metrics.fidelity c.toJointDensity.toPosSemidefOp
          (ρ.supportProjectionCPM P hP).toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
    apply Finset.sum_congr rfl
    intro x _
    exact fidelity_eq_of_projectorSandwich_of_fixed hP
      (c.stateMap x).toPosSemidefOp (ρ.stateMap x).toPosSemidefOp
      ((ρ.supportProjectionCPM P hP).stateMap x).toPosSemidefOp
      (hc_block x)
      (CQState.supportProjectionCPM_stateMap_toOp P hP ρ x)
  -- The trace of the CPM image does not exceed the trace of ρ.
  have htrace_le :
      (ρ.supportProjectionCPM P hP).toJointDensity.trace ≤ ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    apply Finset.sum_le_sum
    intro x _
    change ((ρ.supportProjectionCPM P hP).stateMap x).toOp.trace.re ≤ (ρ.stateMap x).toOp.trace.re
    rw [CQState.supportProjectionCPM_stateMap_toOp]
    exact projectorSandwich_trace_re_le hP
      (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  -- Correction term grows: √((1-tr c)(1-tr ρ)) ≤ √((1-tr c)(1-tr Eρ)).
  have hc_nonneg : 0 ≤ 1 - c.toJointDensity.trace := c.toJointDensity.one_sub_trace_nonneg
  have hcorr :
      Real.sqrt ((1 - c.toJointDensity.trace) * (1 - ρ.toJointDensity.trace)) ≤
        Real.sqrt ((1 - c.toJointDensity.trace) *
          (1 - (ρ.supportProjectionCPM P hP).toJointDensity.trace)) := by
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hc_nonneg
    linarith
  rw [hF]
  linarith

/-! ## Fixing supported states -/

/-- The support-projection CPM fixes any CQ state whose blocks are supported on
`im(P)` (`P · ρ_x · P = ρ_x` for every block). -/
lemma supportProjectionCPM_fixes_of_supported
    {X : Type*} [Fintype X] {n : ℕ}
    (P : Op n) (hP : IsOrthogonalProjector P) (ρ : CQState X n)
    (hsupp : ∀ x : X, P * (ρ.stateMap x).toOp * P = (ρ.stateMap x).toOp) :
    ρ.supportProjectionCPM P hP = ρ := by
  cases ρ with
  | mk ρMap ρWeight =>
    have hmap : (fun x : X => ((CQState.mk ρMap ρWeight).supportProjectionCPM P hP).stateMap x)
        = ρMap := by
      funext x
      apply SubDensityOp.ext
      simpa [CQState.supportProjectionCPM_stateMap_toOp] using hsupp x
    cases hmap_eq : (CQState.mk ρMap ρWeight).supportProjectionCPM P hP with
    | mk pMap pWeight =>
      have : pMap = ρMap := by
        rw [← hmap]
        rw [hmap_eq]
      subst this
      rfl

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
