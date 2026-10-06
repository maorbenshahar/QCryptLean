import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.MinEntropyGuess
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.IsometryConjugation

/-!
# OptReal invariance lemmas — Eve-unitary, classical relabeling, and uniform-classical Eve tensoring

Three structural invariance lemmas of the optimized real-valued conditional
min-entropy `conditionalMinEntropyOptReal` for CQ states. These are the OptReal
analogues of standard min-entropy identities (Tomamichel 2016, §6.1.1).

The auxiliary lower-level structural fact `SubDensityOp.unitaryConjugate`
(and its trace identity) lives in `InfoTheory/SmoothMinEntropy/SubNormalized.lean`.
The rectangular left-isometry conjugation backbone
(`minFeasibleLambda_left_isometry_embed_eq`) lives in
`InfoTheory/SmoothMinEntropy/IsometryConjugation.lean`.

## Main definitions
- `CQState.eveConjugate ρ V`: per-outcome unitary conjugation on Eve.
- `CQState.relabelClassical ρ b`: classical-outcome relabeling along `b`.
- `CQState.eveTensorUniformClassical ρ k`: tensor each block with the
  maximally-mixed state `I_k / k`.

## Main statements
- `conditionalMinEntropyOptReal_eveUnitary_invariant`: conjugating Eve by a
  unitary `V : UnitaryOp dE` leaves the optimized conditional min-entropy
  unchanged.
- `conditionalMinEntropyOptReal_relabelClassical_invariant`: reindexing the
  classical register along any bijection `b : X ≃ X'` leaves
  `conditionalMinEntropyOptReal` unchanged.
- `conditionalMinEntropyOptReal_eveTensorUniformClassical_invariant`: tensoring
  Eve with the maximally-mixed sub-density operator on `Fin k` (`k ≥ 1`)
  leaves `conditionalMinEntropyOptReal` unchanged.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## CQ-state operations -/

/-- Conjugate a CQ state by a unitary `V` on the Eve (quantum) register:
    `(ρ.eveConjugate V).stateMap x := V · (ρ.stateMap x) · V†`. -/
noncomputable def CQState.eveConjugate {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (V : UnitaryOp dE) : CQState X dE where
  stateMap x := (ρ.stateMap x).unitaryConjugate V
  weight_le_one := by
    simp_rw [SubDensityOp.unitaryConjugate_trace]
    exact ρ.weight_le_one

/-- Relabel the classical register of a CQ state along a bijection
    `b : X ≃ X'`: the new block at index `x' : X'` is
    `ρ.stateMap (b.symm x')`. -/
noncomputable def CQState.relabelClassical
    {X X' : Type*} [Fintype X] [Fintype X'] {n : ℕ}
    (ρ : CQState X n) (b : X ≃ X') : CQState X' n where
  stateMap x' := ρ.stateMap (b.symm x')
  weight_le_one := by
    rw [Equiv.sum_comp b.symm (fun x => (ρ.stateMap x).trace)]
    exact ρ.weight_le_one

/-- Tensor the Eve (quantum) register of a CQ state with the maximally-mixed
    sub-density operator on `Fin k`. The classical label register of size
    `k` is absorbed into Eve as a maximally-mixed quantum register, raising
    the Eve dimension from `dE` to `dE * k`. Requires `k ≥ 1` so the
    maximally-mixed state on `Fin k` is defined. -/
noncomputable def CQState.eveTensorUniformClassical
    {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (k : ℕ) [NeZero k] : CQState X (dE * k) where
  stateMap x :=
    (ρ.stateMap x).tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed k))
  weight_le_one := by
    have htr : ∀ x : X,
        ((ρ.stateMap x).tensor
            (DensityOp.toSubDensityOp (DensityOp.maxMixed k))).trace =
          (ρ.stateMap x).trace := by
      intro x
      rw [SubDensityOp.tensor_trace, toSubDensityOp_trace, mul_one]
    simp_rw [htr]
    exact ρ.weight_le_one

/-! ## Adjoint-conjugation identities for sub-density operators -/

/-- Defining identity: the underlying matrix of `σ.unitaryConjugate V`. -/
lemma SubDensityOp.unitaryConjugate_toOp {n : ℕ}
    (σ : SubDensityOp n) (V : UnitaryOp n) :
    (σ.unitaryConjugate V).toOp = V.toOp * σ.toOp * V.toOp.conjTranspose := rfl

/-- Conjugating by `V` after conjugating by `V.adj` is the identity on
sub-density operators. -/
lemma SubDensityOp.unitaryConjugate_adj_left {n : ℕ}
    (σ : SubDensityOp n) (V : UnitaryOp n) :
    (σ.unitaryConjugate V.adj).unitaryConjugate V = σ := by
  apply SubDensityOp.ext
  simp only [SubDensityOp.unitaryConjugate_toOp]
  change V.toOp * (V.toOp.conjTranspose * σ.toOp * V.toOp.conjTranspose.conjTranspose) *
      V.toOp.conjTranspose = σ.toOp
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    V.toOp * (V.toOp.conjTranspose * σ.toOp * V.toOp) * V.toOp.conjTranspose
        = (V.toOp * V.toOp.conjTranspose) * σ.toOp *
            (V.toOp * V.toOp.conjTranspose) := by
          simp [Matrix.mul_assoc]
    _ = (1 : Op n) * σ.toOp * (1 : Op n) := by rw [V.unitary_right]
    _ = σ.toOp := by rw [Matrix.one_mul, Matrix.mul_one]

/-! ## Unitary specialization of the `minFeasibleLambda` equality -/

/-- Unitary-invariance of `minFeasibleLambda`: conjugating Eve by a unitary
and the reference by the same unitary leaves `λ*` unchanged. -/
lemma minFeasibleLambda_eveUnitary_invariant
    {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (σ : SubDensityOp dE) (V : UnitaryOp dE) :
    minFeasibleLambda (ρ.eveConjugate V) (σ.unitaryConjugate V) =
      minFeasibleLambda ρ σ := by
  refine minFeasibleLambda_left_isometry_embed_eq
    X V.toOp V.unitary_left ρ σ
    (ρ.eveConjugate V) ?_ (σ.unitaryConjugate V) ?_
  · intro x
    rfl
  · rfl

/-! ## Invariance lemmas -/

/-- **OptReal Eve-unitary invariance.**

Conjugating the Eve (quantum) register of a CQ state by any unitary `V`
leaves the optimized conditional min-entropy `H^opt_min` unchanged.

For any feasible `(σ, t)` for `(ρ.eveConjugate V, σ)`, the pair
`(V† · σ · V, t)` is feasible for `(ρ, V† · σ · V)` with the same `t`; the
reverse direction is symmetric. Hence the feasible-`λ` sets are in
bijection and the supremum over references is unchanged
(Tomamichel 2016, §6.1.1). -/
theorem conditionalMinEntropyOptReal_eveUnitary_invariant
    {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (V : UnitaryOp dE) :
    conditionalMinEntropyOptReal (ρ.eveConjugate V) =
      conditionalMinEntropyOptReal ρ := by
  unfold conditionalMinEntropyOptReal
  congr 1
  ext h
  constructor
  · rintro ⟨σ', rfl⟩
    refine ⟨σ'.unitaryConjugate V.adj, ?_⟩
    unfold conditionalMinEntropyReal
    have hlam :
        minFeasibleLambda (ρ.eveConjugate V) σ' =
          minFeasibleLambda ρ (σ'.unitaryConjugate V.adj) := by
      have h0 := minFeasibleLambda_eveUnitary_invariant
        ρ (σ'.unitaryConjugate V.adj) V
      rw [SubDensityOp.unitaryConjugate_adj_left σ' V] at h0
      exact h0
    rw [hlam]
  · rintro ⟨σ, rfl⟩
    refine ⟨σ.unitaryConjugate V, ?_⟩
    unfold conditionalMinEntropyReal
    rw [minFeasibleLambda_eveUnitary_invariant ρ σ V]

/-- Feasibility is invariant under classical relabeling: the universal
quantifier `∀ x : X, …` is reindexed bijectively along `b : X ≃ X'`. -/
lemma isFeasible_relabelClassical_iff
    {X X' : Type*} [Fintype X] [Fintype X'] {n : ℕ}
    (ρ : CQState X n) (b : X ≃ X') (σ : SubDensityOp n) (t : ℝ) :
    isFeasible (ρ.relabelClassical b) σ t ↔ isFeasible ρ σ t := by
  unfold isFeasible
  refine and_congr_right (fun _ => ?_)
  exact (Equiv.forall_congr_left b
    (p := fun x => opLe (ρ.stateMap x).toOp (Complex.ofReal t • σ.toOp))).symm

/-- `minFeasibleLambda` is invariant under classical relabeling, per
reference. -/
lemma minFeasibleLambda_relabelClassical_eq
    {X X' : Type*} [Fintype X] [Fintype X'] {n : ℕ}
    (ρ : CQState X n) (b : X ≃ X') (σ : SubDensityOp n) :
    minFeasibleLambda (ρ.relabelClassical b) σ = minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_relabelClassical_iff ρ b σ t

/-- **OptReal classical-outcome relabeling invariance.**

Reindexing the classical register of a CQ state along any bijection
`b : X ≃ X'` leaves the optimized conditional min-entropy `H^opt_min`
unchanged.

The feasibility predicate
`isFeasible ρ σ t = ∀ x, opLe (ρ.stateMap x).toOp (t • σ.toOp)` is
preserved bijectively under the reindexing `x ↔ b x`, because the
quantifier ranges over all classical outcomes universally. -/
theorem conditionalMinEntropyOptReal_relabelClassical_invariant
    {X X' : Type*} [Fintype X] [Fintype X'] {n : ℕ}
    (ρ : CQState X n) (b : X ≃ X') :
    conditionalMinEntropyOptReal (ρ.relabelClassical b) =
      conditionalMinEntropyOptReal ρ := by
  unfold conditionalMinEntropyOptReal
  congr 1
  ext h
  refine ⟨?_, ?_⟩ <;>
  · rintro ⟨σ, rfl⟩
    refine ⟨σ, ?_⟩
    unfold conditionalMinEntropyReal
    rw [minFeasibleLambda_relabelClassical_eq ρ b σ]

/-! ### Helper lemmas for the uniform-classical-Eve tensoring invariance -/

/-- A positive semidefinite operator whose quadratic form vanishes on all
vectors is the zero operator. -/
private lemma op_eq_zero_of_posSemidef_quadraticForm_re_zero
    {n : ℕ} {A : Op n} (hA : A.PosSemidef)
    (h : ∀ v : Fin n → ℂ, (quadraticForm A v).re = 0) :
    A = 0 := by
  have h_im : ∀ v : Fin n → ℂ, (quadraticForm A v).im = 0 := fun v => by
    have h_nn := hA.dotProduct_mulVec_nonneg v
    rw [Complex.nonneg_iff] at h_nn
    exact h_nn.2.symm
  have h_qf_zero : ∀ v : Fin n → ℂ, quadraticForm A v = 0 := fun v =>
    Complex.ext (h v) (h_im v)
  have h_mulVec : ∀ v : Fin n → ℂ, A.mulVec v = 0 := fun v =>
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA v).mp (h_qf_zero v)
  ext i j
  have hcol := congr_fun (h_mulVec (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hcol

/-- A positive semidefinite operator dominated by zero in the `opLe` ordering
is itself zero. -/
private lemma posSemidef_eq_zero_of_opLe_zero
    {n : ℕ} {A : Op n} (hA : A.PosSemidef) (h : opLe A 0) : A = 0 := by
  refine op_eq_zero_of_posSemidef_quadraticForm_re_zero hA (fun v => ?_)
  have hqle := h v
  have hqle' : (quadraticForm A v).re ≤ 0 := by
    convert hqle using 1
    simp [quadraticForm, Matrix.zero_mulVec, dotProduct]
  have hqge : 0 ≤ (quadraticForm A v).re :=
    (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1
  linarith

/-- **Lift feasibility along the Eve uniform-classical tensoring.** If `t` is
feasible for `(ρ, σ)`, then `t` is also feasible for
`(ρ.eveTensorUniformClassical k, σ ⊗ (I_k / k))`. This is the "lift" direction
that shows the original sup-set embeds into the tensored sup-set. -/
lemma isFeasible_eveTensorUniformClassical_tensor_of_isFeasible
    {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (σ : SubDensityOp dE) (k : ℕ) [NeZero k]
    {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible (ρ.eveTensorUniformClassical k)
      (σ.tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed k))) t := by
  set τ_sub : SubDensityOp k :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed k)
  refine ⟨ht.1, fun x => ?_⟩
  have h_smul_herm : ((Complex.ofReal t) • σ.toOp).IsHermitian :=
    isHermitian_real_smul σ.isHermitian t
  have h_diff_psd :
      ((Complex.ofReal t • σ.toOp) - (ρ.stateMap x).toOp).PosSemidef :=
    Quantum.Operators.opLe.posSemidef_sub (ρ.stateMap x).isHermitian
      h_smul_herm (ht.2 x)
  have h_τ_psd : τ_sub.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib τ_sub.toPosSemidefOp
  have h_tensor_psd :
      (((Complex.ofReal t • σ.toOp) - (ρ.stateMap x).toOp) ⊗
          τ_sub.toOp).PosSemidef :=
    Quantum.TensorProducts.Op.tensor_posSemidef_mathlib h_diff_psd h_τ_psd
  rw [Quantum.TensorProducts.Op.tensor_sub_left,
      Quantum.TensorProducts.Op.tensor_smul_left] at h_tensor_psd
  -- Goal unfolds to opLe on `(ρ.stateMap x).toOp ⊗ τ_sub.toOp` vs.
  -- `Complex.ofReal t • (σ.toOp ⊗ τ_sub.toOp)`.
  exact Quantum.Operators.opLe_of_posSemidef_sub h_tensor_psd

/-- Partial trace preserves Mathlib-PSD on the right tensor factor. -/
private lemma partialTraceB_posSemidef_local {n m : ℕ}
    {A : Op (n * m)} (hA : A.PosSemidef) :
    (Quantum.TensorProducts.partialTraceB A).PosSemidef := by
  let Apsd : PosSemidefOp (n * m) :=
    { toOp := A
      isHermitian := hA.isHermitian
      pos_semidef := fun v =>
        (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1 }
  refine Quantum.Operators.posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
    ?_ ?_
  · exact Quantum.TensorProducts.partialTraceB_hermitian A hA.isHermitian
  · intro v
    have := Quantum.TensorProducts.partialTraceB_posSemidef Apsd v
    simpa [Apsd] using this

/-- The partial trace over the maximally-mixed factor is the identity on the
remaining factor: `(σ ⊗ τ_k).partialTraceB = σ`. -/
private lemma partialTraceB_tensor_maxMixed
    {dE k : ℕ} [NeZero k] (σ : SubDensityOp dE) :
    (σ.tensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed k))).partialTraceB = σ := by
  apply SubDensityOp.ext
  rw [SubDensityOp.partialTraceB_toOp]
  change Quantum.TensorProducts.partialTraceB
      (σ.toOp ⊗
        (DensityOp.toSubDensityOp (DensityOp.maxMixed k)).toOp) = σ.toOp
  rw [Quantum.TensorProducts.partialTraceB_tensor_op]
  rw [show (DensityOp.toSubDensityOp (DensityOp.maxMixed k)).toOp.trace = (1 : ℂ)
        from (DensityOp.maxMixed k).trace_one, one_smul]

/-- **Push feasibility down along the Eve uniform-classical tensoring.**
If `t` is feasible for `(ρ.eveTensorUniformClassical k, σ')`, then `t` is
feasible for `(ρ, σ'.partialTraceB)`. Uses partial trace over the new uniform
factor, with the trace-one identity `Tr (I_k / k) = 1` removing the scalar. -/
lemma isFeasible_partialTraceB_of_isFeasible_eveTensorUniformClassical
    {X : Type*} [Fintype X] {dE : ℕ} [NeZero dE]
    {k : ℕ} [NeZero k]
    (ρ : CQState X dE) (σ' : SubDensityOp (dE * k))
    {t : ℝ} (ht : isFeasible (ρ.eveTensorUniformClassical k) σ' t) :
    isFeasible ρ σ'.partialTraceB t := by
  set τ_sub : SubDensityOp k :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed k)
  refine ⟨ht.1, fun x => ?_⟩
  -- From `ht.2 x` we get the lifted opLe.
  have h_step1 :
      opLe ((ρ.stateMap x).toOp ⊗ τ_sub.toOp)
           (Complex.ofReal t • σ'.toOp) := ht.2 x
  have h_lhs_herm :
      ((ρ.stateMap x).toOp ⊗ τ_sub.toOp).IsHermitian := by
    change ((ρ.stateMap x).tensor τ_sub).toOp.IsHermitian
    exact ((ρ.stateMap x).tensor τ_sub).isHermitian
  have h_rhs_herm : ((Complex.ofReal t) • σ'.toOp).IsHermitian :=
    isHermitian_real_smul σ'.isHermitian t
  have h_diff_psd :
      ((Complex.ofReal t • σ'.toOp) -
          ((ρ.stateMap x).toOp ⊗ τ_sub.toOp)).PosSemidef :=
    Quantum.Operators.opLe.posSemidef_sub h_lhs_herm h_rhs_herm h_step1
  -- Push through the partial trace.
  have h_pt_psd :
      (Quantum.TensorProducts.partialTraceB
          ((Complex.ofReal t • σ'.toOp) -
            ((ρ.stateMap x).toOp ⊗ τ_sub.toOp))).PosSemidef :=
    partialTraceB_posSemidef_local h_diff_psd
  -- Rewrite the partial trace.
  rw [Quantum.TensorProducts.partialTraceB_sub,
      Quantum.TensorProducts.partialTraceB_smul,
      Quantum.TensorProducts.partialTraceB_tensor_op,
      show τ_sub.toOp.trace = (1 : ℂ) from (DensityOp.maxMixed k).trace_one,
      one_smul] at h_pt_psd
  change opLe (ρ.stateMap x).toOp
              (Complex.ofReal t • σ'.partialTraceB.toOp)
  rw [SubDensityOp.partialTraceB_toOp]
  exact Quantum.Operators.opLe_of_posSemidef_sub h_pt_psd

/-! ### Dim-zero edge case -/

/-- On a zero-dimensional Eve register, every reference and every CQ block is
the unique zero operator, so the optimized real conditional min-entropy is
`0`. -/
private lemma conditionalMinEntropyOptReal_eq_zero_of_dim_zero
    {X : Type*} [Fintype X] {n : ℕ} (hn : n = 0) (ρ : CQState X n) :
    conditionalMinEntropyOptReal ρ = 0 := by
  subst hn
  unfold conditionalMinEntropyOptReal
  have h_all_zero : ∀ σ : SubDensityOp 0, conditionalMinEntropyReal ρ σ = 0 := by
    intro σ
    have h_feas0 : isFeasible ρ σ 0 := by
      refine ⟨le_refl 0, fun x v => ?_⟩
      -- the quadratic form on `Fin 0 → ℂ` is identically zero.
      have h_lhs :
          (quadraticForm (ρ.stateMap x).toOp v).re = 0 := by
        simp [quadraticForm, Matrix.mulVec, dotProduct,
          Finset.univ_eq_empty]
      have h_rhs :
          (quadraticForm (Complex.ofReal 0 • σ.toOp) v).re = 0 := by
        simp [quadraticForm, Matrix.mulVec, dotProduct,
          Finset.univ_eq_empty]
      rw [h_lhs, h_rhs]
    have h_lam_zero : minFeasibleLambda ρ σ = 0 := by
      apply le_antisymm _ (minFeasibleLambda_nonneg ρ σ)
      exact csInf_le (minFeasibleLambda_bddBelow ρ σ) h_feas0
    unfold conditionalMinEntropyReal
    rw [h_lam_zero, Real.log_zero, neg_zero, zero_div]
  have h_set_eq :
      ({h | ∃ σ : SubDensityOp 0, h = conditionalMinEntropyReal ρ σ} : Set ℝ) =
        {0} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨σ, hσ⟩
      rw [hσ, h_all_zero σ]
    · intro h0
      exact ⟨0, by rw [h0, h_all_zero (0 : SubDensityOp 0)]⟩
  rw [h_set_eq]
  exact csSup_singleton 0

/-! ### Boundary handling for `conditionalMinEntropyReal` -/

/-- `conditionalMinEntropyReal ρ 0 = 0` for any CQ state `ρ`: feasibility with
`σ = 0` either forces all blocks to be zero (giving `λ* = 0`) or is empty
(giving the sentinel `sInf ∅ = 0`); either way `Real.log 0 = 0`. -/
private lemma conditionalMinEntropyReal_zero_eq_zero
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    conditionalMinEntropyReal ρ (0 : SubDensityOp n) = 0 := by
  unfold conditionalMinEntropyReal
  have h_lam_zero : minFeasibleLambda ρ (0 : SubDensityOp n) = 0 := by
    apply le_antisymm _ (minFeasibleLambda_nonneg ρ _)
    by_cases hempty :
        (setOf (isFeasible ρ (0 : SubDensityOp n))).Nonempty
    · obtain ⟨t, ht⟩ := hempty
      have h_blocks_zero : ∀ x : X, (ρ.stateMap x).toOp = 0 := fun x => by
        have hop : opLe (ρ.stateMap x).toOp (Complex.ofReal t • (0 : Op n)) :=
          ht.2 x
        rw [smul_zero] at hop
        exact posSemidef_eq_zero_of_opLe_zero
          (Quantum.Operators.posSemidefOp_implies_mathlib
            (ρ.stateMap x).toPosSemidefOp) hop
      have h0_feas : isFeasible ρ (0 : SubDensityOp n) 0 := by
        refine ⟨le_refl 0, fun x v => ?_⟩
        rw [h_blocks_zero x]
        simp [quadraticForm, Matrix.zero_mulVec, dotProduct]
      exact csInf_le (minFeasibleLambda_bddBelow ρ _) h0_feas
    · rw [Set.not_nonempty_iff_eq_empty] at hempty
      unfold minFeasibleLambda
      rw [hempty, Real.sInf_empty]
  rw [h_lam_zero, Real.log_zero, neg_zero, zero_div]

/-- The optimized real conditional min-entropy is nonneg: take `σ = 0` as a
witness, which always gives the value `0`. -/
private lemma conditionalMinEntropyOptReal_nonneg
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    0 ≤ conditionalMinEntropyOptReal ρ := by
  unfold conditionalMinEntropyOptReal
  refine le_csSup (conditionalMinEntropyOptReal_bddAbove ρ) ?_
  exact ⟨(0 : SubDensityOp n), (conditionalMinEntropyReal_zero_eq_zero ρ).symm⟩

/-- The blockwise tensor in `ρ.eveTensorUniformClassical k` makes the lifted
blocks zero exactly when the original blocks are. -/
private lemma eveTensorUniformClassical_stateMap_toOp_eq_zero_iff
    {X : Type*} [Fintype X] {dE : ℕ} [NeZero dE]
    {k : ℕ} [NeZero k]
    (ρ : CQState X dE) (x : X) :
    ((ρ.eveTensorUniformClassical k).stateMap x).toOp = 0 ↔
      (ρ.stateMap x).toOp = 0 := by
  set τ_sub : SubDensityOp k :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed k)
  have h_eq :
      ((ρ.eveTensorUniformClassical k).stateMap x).toOp =
        (ρ.stateMap x).toOp ⊗ τ_sub.toOp := rfl
  rw [h_eq]
  constructor
  · intro hz
    -- partial trace yields (ρx)
    have hpt :
        Quantum.TensorProducts.partialTraceB
          ((ρ.stateMap x).toOp ⊗ τ_sub.toOp) = 0 := by
      rw [hz]; ext i j; simp [Quantum.TensorProducts.partialTraceB]
    rw [Quantum.TensorProducts.partialTraceB_tensor_op,
        show τ_sub.toOp.trace = (1 : ℂ) from (DensityOp.maxMixed k).trace_one,
        one_smul] at hpt
    exact hpt
  · intro hz
    rw [hz]
    ext i j
    simp [Quantum.TensorProducts.Op.tensor]

/-- **The boundary inequality.** For any reference `σ'` on the enlarged Eve
register, the value `H(ρ.eveTensorUniformClassical k, σ')` is bounded above by
`conditionalMinEntropyOptReal ρ`. Either positivity holds for both sides
(giving the log-monotone inequality `H(ρ⊗τ, σ') ≤ H(ρ, σ'.partialTraceB)`),
or `H(ρ⊗τ, σ') = 0 ≤ conditionalMinEntropyOptReal ρ`. -/
private lemma conditionalMinEntropyReal_eveTensorUniformClassical_le_optReal
    {X : Type*} [Fintype X] {dE : ℕ} [NeZero dE]
    {k : ℕ} [NeZero k]
    (ρ : CQState X dE) (σ' : SubDensityOp (dE * k)) :
    conditionalMinEntropyReal (ρ.eveTensorUniformClassical k) σ' ≤
      conditionalMinEntropyOptReal ρ := by
  have hlA_nn :
      0 ≤ minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' :=
    minFeasibleLambda_nonneg _ _
  have hlB_nn :
      0 ≤ minFeasibleLambda ρ σ'.partialTraceB :=
    minFeasibleLambda_nonneg _ _
  have hbdd := conditionalMinEntropyOptReal_bddAbove ρ
  have h_opt_nn : 0 ≤ conditionalMinEntropyOptReal ρ :=
    conditionalMinEntropyOptReal_nonneg ρ
  by_cases hlA_pos :
      0 < minFeasibleLambda (ρ.eveTensorUniformClassical k) σ'
  · -- Positive branch: closed-set sInf attainment plus push-down feasibility
    -- give `0 < lB` and the log-monotone inequality.
    have hA_ne :
        (setOf (isFeasible (ρ.eveTensorUniformClassical k) σ')).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hzero :
          minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' = 0 := by
        unfold minFeasibleLambda
        rw [hempty, Real.sInf_empty]
      linarith
    -- The sInf is attained (closed set, bounded below, nonempty).
    have hA_closed :
        IsClosed
          (setOf (isFeasible (ρ.eveTensorUniformClassical k) σ')) :=
      isFeasible_isClosed _ _
    have hlA_mem :
        minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' ∈
          setOf (isFeasible (ρ.eveTensorUniformClassical k) σ') := by
      unfold minFeasibleLambda
      exact hA_closed.csInf_mem hA_ne (minFeasibleLambda_bddBelow _ _)
    -- Each feasible `t` for `(ρ⊗τ, σ')` is feasible for `(ρ, σ'.partialTraceB)`.
    have hsub :
        setOf (isFeasible (ρ.eveTensorUniformClassical k) σ') ⊆
          setOf (isFeasible ρ σ'.partialTraceB) := fun t ht =>
      isFeasible_partialTraceB_of_isFeasible_eveTensorUniformClassical
        (k := k) ρ σ' ht
    have hB_ne :
        (setOf (isFeasible ρ σ'.partialTraceB)).Nonempty :=
      ⟨_, hsub hlA_mem⟩
    have hB_closed :
        IsClosed (setOf (isFeasible ρ σ'.partialTraceB)) :=
      isFeasible_isClosed _ _
    have hlB_mem :
        minFeasibleLambda ρ σ'.partialTraceB ∈
          setOf (isFeasible ρ σ'.partialTraceB) := by
      unfold minFeasibleLambda
      exact hB_closed.csInf_mem hB_ne (minFeasibleLambda_bddBelow _ _)
    have hlB_le_lA :
        minFeasibleLambda ρ σ'.partialTraceB ≤
          minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' := by
      unfold minFeasibleLambda
      exact csInf_le_csInf (minFeasibleLambda_bddBelow _ _) hA_ne hsub
    -- Show 0 < lB.
    have hlB_pos : 0 < minFeasibleLambda ρ σ'.partialTraceB := by
      by_contra hnot
      push Not at hnot
      have hlB_zero : minFeasibleLambda ρ σ'.partialTraceB = 0 :=
        le_antisymm hnot hlB_nn
      have h_zero_feas_B : isFeasible ρ σ'.partialTraceB 0 := by
        rw [hlB_zero] at hlB_mem; exact hlB_mem
      have h_blocks_zero : ∀ x : X, (ρ.stateMap x).toOp = 0 := fun x => by
        have hop :
            opLe (ρ.stateMap x).toOp
                 (Complex.ofReal 0 • σ'.partialTraceB.toOp) :=
          h_zero_feas_B.2 x
        rw [Complex.ofReal_zero, zero_smul] at hop
        exact posSemidef_eq_zero_of_opLe_zero
          (Quantum.Operators.posSemidefOp_implies_mathlib
            (ρ.stateMap x).toPosSemidefOp) hop
      -- Lift to ρ.eveTensorUniformClassical k blocks all zero.
      have h_lifted_zero :
          ∀ x : X, ((ρ.eveTensorUniformClassical k).stateMap x).toOp = 0 := by
        intro x
        rw [eveTensorUniformClassical_stateMap_toOp_eq_zero_iff]
        exact h_blocks_zero x
      have h0_feas_A :
          isFeasible (ρ.eveTensorUniformClassical k) σ' 0 := by
        refine ⟨le_refl 0, fun x v => ?_⟩
        rw [h_lifted_zero x]
        simp [quadraticForm, Matrix.zero_mulVec, dotProduct,
          Complex.ofReal_zero, zero_smul]
      have hzero :
          minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' = 0 := by
        apply le_antisymm _ hlA_nn
        unfold minFeasibleLambda
        exact csInf_le (minFeasibleLambda_bddBelow _ _) h0_feas_A
      linarith
    -- Log monotonicity gives the inequality.
    have hlog_le :
        Real.log (minFeasibleLambda ρ σ'.partialTraceB) ≤
          Real.log (minFeasibleLambda (ρ.eveTensorUniformClassical k) σ') :=
      Real.log_le_log hlB_pos hlB_le_lA
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_step :
        conditionalMinEntropyReal (ρ.eveTensorUniformClassical k) σ' ≤
          conditionalMinEntropyReal ρ σ'.partialTraceB := by
      unfold conditionalMinEntropyReal
      exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le
    calc conditionalMinEntropyReal (ρ.eveTensorUniformClassical k) σ'
        ≤ conditionalMinEntropyReal ρ σ'.partialTraceB := h_step
      _ ≤ conditionalMinEntropyOptReal ρ :=
          le_csSup hbdd ⟨σ'.partialTraceB, rfl⟩
  · -- lA ≤ 0, so lA = 0, hence H_LHS = 0.
    push Not at hlA_pos
    have hlA_zero :
        minFeasibleLambda (ρ.eveTensorUniformClassical k) σ' = 0 :=
      le_antisymm hlA_pos hlA_nn
    have h_lhs_zero :
        conditionalMinEntropyReal (ρ.eveTensorUniformClassical k) σ' = 0 := by
      unfold conditionalMinEntropyReal
      rw [hlA_zero, Real.log_zero, neg_zero, zero_div]
    rw [h_lhs_zero]
    exact h_opt_nn

/-- **OptReal uniform-classical-Eve-tensoring invariance.**

Tensoring the Eve (quantum) register of a CQ state with the maximally-mixed
sub-density operator on `Fin k` (`k ≥ 1`, representing a uniform classical
label absorbed into Eve) leaves the optimized conditional min-entropy
`H^opt_min` unchanged.

Every feasible reference `σ_E` for `ρ` lifts to a feasible reference
`σ_E ⊗ (I_k / k)` for `ρ.eveTensorUniformClassical k` with the same `λ`;
conversely, partial-tracing any feasible reference `σ_{E ⊗ R}` on the
enlarged register yields a feasible `σ_E` with the same `λ`
(Tomamichel 2016, Lemma 6.5; Renner 2005, §4.2.2). -/
theorem conditionalMinEntropyOptReal_eveTensorUniformClassical_invariant
    {X : Type*} [Fintype X] {dE : ℕ}
    (ρ : CQState X dE) (k : ℕ) [NeZero k] :
    conditionalMinEntropyOptReal (ρ.eveTensorUniformClassical k) =
      conditionalMinEntropyOptReal ρ := by
  by_cases hdE : dE = 0
  · -- Both sides are zero on a zero-dimensional Eve register.
    have hdEk : dE * k = 0 := by rw [hdE]; ring
    rw [conditionalMinEntropyOptReal_eq_zero_of_dim_zero hdEk _,
        conditionalMinEntropyOptReal_eq_zero_of_dim_zero hdE _]
  · haveI hNZ : NeZero dE := ⟨hdE⟩
    apply le_antisymm
    · -- LHS ≤ RHS: every value of the tensored sup-set is bounded by the
      -- original optimized min-entropy via partial trace / boundary handling.
      apply csSup_le
      · exact ⟨_, (0 : SubDensityOp (dE * k)), rfl⟩
      · rintro h ⟨σ', rfl⟩
        exact conditionalMinEntropyReal_eveTensorUniformClassical_le_optReal
          ρ σ'
    · -- RHS ≤ LHS: for every σ on Eve, the lifted reference `σ ⊗ τ_k` realizes
      -- the same conditional min-entropy on the enlarged sup-set.
      refine csSup_le_csSup (conditionalMinEntropyOptReal_bddAbove _)
        ⟨conditionalMinEntropyReal ρ 0, (0 : SubDensityOp dE), rfl⟩ ?_
      rintro h ⟨σ, rfl⟩
      refine
        ⟨σ.tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed k)), ?_⟩
      -- Feasibility sets coincide: the lift direction tensorizes, and the
      -- push-down direction uses `(σ ⊗ τ_k).partialTraceB = σ`.
      have h_set_eq :
          setOf (isFeasible (ρ.eveTensorUniformClassical k)
              (σ.tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed k)))) =
            setOf (isFeasible ρ σ) := by
        ext t
        refine ⟨fun ht => ?_, fun ht => ?_⟩
        · have hpt :
              isFeasible ρ
                (σ.tensor
                    (DensityOp.toSubDensityOp
                      (DensityOp.maxMixed k))).partialTraceB t :=
            isFeasible_partialTraceB_of_isFeasible_eveTensorUniformClassical
              (k := k) ρ _ ht
          rw [partialTraceB_tensor_maxMixed] at hpt
          exact hpt
        · exact isFeasible_eveTensorUniformClassical_tensor_of_isFeasible
            ρ σ k ht
      have h_lam_eq :
          minFeasibleLambda ρ σ =
            minFeasibleLambda (ρ.eveTensorUniformClassical k)
              (σ.tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed k))) := by
        unfold minFeasibleLambda
        rw [h_set_eq]
      unfold conditionalMinEntropyReal
      rw [h_lam_eq]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
