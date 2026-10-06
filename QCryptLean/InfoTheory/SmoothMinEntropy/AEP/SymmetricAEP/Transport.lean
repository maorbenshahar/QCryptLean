import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.CorrectionAndWitness

/-!
# Transport for symmetric-state entropy bounds

Tensoring a classical tail and reindexing quantum or classical registers transport feasible
witnesses. These constructions give canonical smooth entropy comparisons and invariance
identities.
-/

open Real Math.ClassicalEntropy InfoTheory.VonNeumannEntropy
open Quantum.Operators Quantum.Symmetry
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy.SymmetricAEP

/-! ## Purified-distance and coefficient transport -/

/-! ## Purified-distance and coefficient transport -/

/-- Extensionality for CQ states: equal `stateMap`s give equal states (the weight
    bound is a proposition). -/
lemma CQState.ext {X : Type*} [Fintype X] {n : ℕ} {ρ σ : CQState X n}
    (h : ρ.stateMap = σ.stateMap) : ρ = σ := by
  cases ρ; cases σ; simp only [CQState.mk.injEq]; exact h

/-- **Quadratic form under a simultaneous index reindex.** Reindexing both row and
    column of an operator by `e` (unitary conjugation by the permutation matrix)
    transports the quadratic form by precomposing the test vector with `e`:
    `⟨x | reindex e e A | x⟩ = ⟨x∘e | A | x∘e⟩`. -/
lemma quadraticForm_reindex {n : ℕ} (e : Fin n ≃ Fin n) (A : Op n) (x : Fin n → ℂ) :
    quadraticForm (Matrix.reindex e e A) x = quadraticForm A (x ∘ e) := by
  unfold quadraticForm
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [dotProduct_comp_equiv_symm]
  rfl

/-- **`opLe` is invariant under a simultaneous index reindex.** Since
    `quadraticForm (reindex e e A) x = quadraticForm A (x∘e)` and `x ↦ x∘e` is a
    bijection on test vectors, the Löwner comparison `opLe A B` transports to
    `opLe (reindex e e A) (reindex e e B)` and back. -/
lemma opLe_reindex_iff {n : ℕ} (e : Fin n ≃ Fin n) (A B : Op n) :
    opLe (Matrix.reindex e e A) (Matrix.reindex e e B) ↔ opLe A B := by
  unfold opLe
  constructor
  · intro h y
    have := h (y ∘ e.symm)
    rwa [quadraticForm_reindex, quadraticForm_reindex,
      show (y ∘ e.symm) ∘ e = y from by funext i; simp] at this
  · intro h x
    rw [quadraticForm_reindex, quadraticForm_reindex]
    exact h (x ∘ e)

/-- **Quantum reindex of a CQ state.** Reindex the quantum register of every
    classical block by a permutation `e : Fin n ≃ Fin n` (the same `e` on all
    blocks). This is the CQ analogue of `SubDensityOp.reindex`, lifting it to each
    `stateMap x`. The classical register is untouched. -/
noncomputable def CQState.reindexQ {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) : CQState X n where
  stateMap x := InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e (ρ.stateMap x)
  weight_le_one := by
    have heq : ∀ x : X,
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e (ρ.stateMap x)).trace =
          (ρ.stateMap x).trace := fun x =>
      InfoTheory.SmoothMinEntropy.SubDensityOp.reindex_trace e (ρ.stateMap x)
    simp_rw [heq]
    exact ρ.weight_le_one

@[simp] lemma CQState.reindexQ_stateMap {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) (x : X) :
    (CQState.reindexQ e ρ).stateMap x =
      InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e (ρ.stateMap x) :=
  rfl

/-- **`isFeasible` transports under the simultaneous quantum reindex of state and
    reference.** Reindexing every block of `ρ` and the reference `σ` by the same
    `e` preserves feasibility of every scalar `t`. -/
lemma isFeasible_reindexQ {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) (σ : SubDensityOp n) (t : ℝ) :
    isFeasible (CQState.reindexQ e ρ) (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ) t ↔
      isFeasible ρ σ t := by
  unfold isFeasible
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h x
    have hx := h x
    rw [CQState.reindexQ_stateMap] at hx
    have hsmul :
        (Complex.ofReal t •
            (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ).toOp) =
          Matrix.reindex e e (Complex.ofReal t • σ.toOp) := by
      change Complex.ofReal t • Matrix.reindex e e σ.toOp =
        Matrix.reindex e e (Complex.ofReal t • σ.toOp)
      simp [Matrix.reindex_apply, Matrix.submatrix_smul]
    rw [hsmul] at hx
    have hreindexstate :
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e (ρ.stateMap x)).toOp =
          Matrix.reindex e e (ρ.stateMap x).toOp := rfl
    rw [hreindexstate] at hx
    exact (opLe_reindex_iff e _ _).mp hx
  · intro h x
    rw [CQState.reindexQ_stateMap]
    have hsmul :
        (Complex.ofReal t •
            (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ).toOp) =
          Matrix.reindex e e (Complex.ofReal t • σ.toOp) := by
      change Complex.ofReal t • Matrix.reindex e e σ.toOp =
        Matrix.reindex e e (Complex.ofReal t • σ.toOp)
      simp [Matrix.reindex_apply, Matrix.submatrix_smul]
    rw [hsmul]
    have hreindexstate :
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e (ρ.stateMap x)).toOp =
          Matrix.reindex e e (ρ.stateMap x).toOp := rfl
    rw [hreindexstate]
    exact (opLe_reindex_iff e _ _).mpr (h x)

/-- **`minFeasibleLambda` is invariant under the simultaneous quantum reindex.** -/
lemma minFeasibleLambda_reindexQ {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) (σ : SubDensityOp n) :
    minFeasibleLambda (CQState.reindexQ e ρ)
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ) =
      minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_reindexQ e ρ σ t

/-- **`conditionalMinEntropyReal` is invariant under the simultaneous quantum
    reindex of state and reference.** -/
lemma conditionalMinEntropyReal_reindexQ {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) (σ : SubDensityOp n) :
    conditionalMinEntropyReal (CQState.reindexQ e ρ)
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ) =
      conditionalMinEntropyReal ρ σ := by
  unfold conditionalMinEntropyReal
  rw [minFeasibleLambda_reindexQ e ρ σ]

/-- **`blockDiagonal` of blockwise-reindexed operators is a reindex of the
    `blockDiagonal`.** Conjugating every classical block by the quantum permutation
    `e` (`Matrix.reindex e e`) equals reindexing the whole block-diagonal operator by
    the product permutation `e × id` on `Fin n × X`. -/
lemma blockDiagonal_reindex_eq {X : Type*} [DecidableEq X] {n : ℕ}
    (e : Fin n ≃ Fin n) (blocks : X → Op n) :
    (Matrix.blockDiagonal fun x => Matrix.reindex e e (blocks x)) =
      Matrix.reindex (Equiv.prodCongr e (Equiv.refl X)) (Equiv.prodCongr e (Equiv.refl X))
        (Matrix.blockDiagonal blocks) := by
  ext ⟨q1, x1⟩ ⟨q2, x2⟩
  by_cases h : x1 = x2 <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
      Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl,
      Prod.map_apply, id_eq, h]

/-- The fixed joint-register permutation realizing the blockwise quantum reindex
    `CQState.reindexQ e` at the joint-density level: conjugate the quantum index by
    `e` through the joint reindex `Fin n × X ≃ Fin (n * card X)`. -/
noncomputable def jointReindexQEquiv {X : Type*} [Fintype X] (e : Fin n ≃ Fin n) :
    Fin (n * Fintype.card X) ≃ Fin (n * Fintype.card X) :=
  let eJ : Fin n × X ≃ Fin (n * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv
  eJ.symm.trans ((Equiv.prodCongr e (Equiv.refl X)).trans eJ)

/-- **The joint density of a blockwise quantum-reindexed CQ state is the reindex of
    the joint density.** Pushing the quantum permutation `e` through every classical
    block (`CQState.reindexQ e`) equals reindexing the whole joint density operator by
    the fixed joint permutation `jointReindexQEquiv e`. The permutation is independent
    of the state, which is what lets it be cancelled in a purified-distance comparison. -/
lemma CQState.reindexQ_toJointDensity {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) :
    (CQState.reindexQ e ρ).toJointDensity =
      InfoTheory.SmoothMinEntropy.SubDensityOp.reindex (jointReindexQEquiv (X := X) e)
        ρ.toJointDensity := by
  apply InfoTheory.SmoothMinEntropy.SubDensityOp.ext
  change (CQState.reindexQ e ρ).toJointDensity.toOp =
    Matrix.reindex (jointReindexQEquiv (X := X) e) (jointReindexQEquiv (X := X) e)
      ρ.toJointDensity.toOp
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
    CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  have hblocks :
      (fun x => ((CQState.reindexQ e ρ).stateMap x).toOp) =
        (fun x => Matrix.reindex e e (ρ.stateMap x).toOp) := by
    funext x; rfl
  rw [hblocks, blockDiagonal_reindex_eq e (fun x => (ρ.stateMap x).toOp)]
  -- Both sides are now reindexes of the same blockDiagonal; combine via
  -- `Matrix.reindex` composition (`submatrix_submatrix`) and match index functions.
  simp only [jointReindexQEquiv, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  congr 1 <;>
    · funext z
      simp [Equiv.symm_apply_apply]

/-- **CQ purified distance is invariant under a blockwise quantum reindex.** -/
lemma CQState.purifiedDistance_reindexQ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (e : Fin n ≃ Fin n) (ρ τ : CQState X n) :
    CQState.purifiedDistance (CQState.reindexQ e ρ) (CQState.reindexQ e τ) =
      CQState.purifiedDistance ρ τ := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  rw [CQState.reindexQ_toJointDensity e ρ, CQState.reindexQ_toJointDensity e τ]
  exact InfoTheory.SmoothMinEntropy.purifiedDistance_reindex (jointReindexQEquiv (X := X) e)
    ρ.toJointDensity τ.toJointDensity

/-- The blockwise quantum reindex round-trips: reindexing by `e` then by `e.symm`
    (or vice versa) recovers the original CQ state. -/
@[simp] lemma CQState.reindexQ_reindexQ_symm {X : Type*} [Fintype X] {n : ℕ}
    (e : Fin n ≃ Fin n) (ρ : CQState X n) :
    CQState.reindexQ e (CQState.reindexQ e.symm ρ) = ρ := by
  apply CQState.ext
  funext x
  apply InfoTheory.SmoothMinEntropy.SubDensityOp.ext
  change Matrix.reindex e e (Matrix.reindex e.symm e.symm (ρ.stateMap x).toOp) =
    (ρ.stateMap x).toOp
  simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]

/-- **CQ purified distance is invariant under a classical relabel.** A relabel of the
    classical register permutes the per-block fidelities and traces identically on both
    arguments; since the CQ joint fidelity is the sum over blocks of the per-block
    fidelities (`CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity`) and the joint
    trace is the sum of per-block traces, both are invariant under the relabel, hence so is
    the generalized fidelity and therefore the purified distance. -/
lemma CQState.purifiedDistance_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    {n : ℕ} [NeZero n] (e : X ≃ Y) (ρ τ : CQState Y n) :
    CQState.purifiedDistance (CQState.relabel e ρ) (CQState.relabel e τ) =
      CQState.purifiedDistance ρ τ := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have : NeZero (n * Fintype.card Y) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  -- The per-block fidelities and the traces both reindex by `e`, so the generalized
  -- fidelity (and hence the purified distance, a function of it) is unchanged.
  have hfid :
      Quantum.Metrics.fidelity (CQState.relabel e ρ).toJointDensity.toPosSemidefOp
          (CQState.relabel e τ).toJointDensity.toPosSemidefOp =
        Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
          τ.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity]
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  have htrace_ρ : (CQState.relabel e ρ).toJointDensity.trace = ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  have htrace_τ : (CQState.relabel e τ).toJointDensity.trace = τ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  have hfidGen :
      fidelityGen (CQState.relabel e ρ).toJointDensity (CQState.relabel e τ).toJointDensity =
        fidelityGen ρ.toJointDensity τ.toJointDensity := by
    unfold fidelityGen
    rw [hfid, htrace_ρ, htrace_τ]
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  rw [hfidGen]

/-- The classical relabel round-trips: relabelling by `e` then by `e.symm` recovers
    the original CQ state. -/
@[simp] lemma CQState.relabel_relabel_symm {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (e : X ≃ Y) (ρ : CQState X n) :
    CQState.relabel e (CQState.relabel e.symm ρ) = ρ := by
  apply CQState.ext
  funext y
  change ρ.stateMap (e.symm (e y)) = ρ.stateMap y
  rw [Equiv.symm_apply_apply]

/-- The per-component weight `|γ_s|²` of the symmetric decomposition. -/
noncomputable def superpositionWeight
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ) (s : ℕ) : ℝ :=
  InfoTheory.SmoothMinEntropy.componentWeight (symWit.coefficients s)

/-- **The dephased-mixture B-marginal pin for the superposition reference
    (Renner main.tex:6201, 6213, the reference `ρ̃_{B^n}`).**

    Renner conditions the n-round smooth min-entropy throughout (eqs `Hinfmins`
    6212, `Hinffb` 6292) on `ρ̃_{B^n} := Σ_{s∈S} |γ_s|² ρ̃^s_{B^n}`, the B-marginal
    of the **dephased mixture** `ρ̃_{X^n B^n S}`, NOT on `σ_B^{⊗n}` (which differs:
    `ρ̃^s_{B^n} = σ_B^{⊗(n−r)} ⊗ ρ̂^s_{B^r}` carries an s-dependent r-round tail).
    `SuperpositionReferencePin` records the equation `σ_ref = ρ̃_{B^n}` at the
    operator level (matching the operator-level image equations of
    `CQChannelImageWitness`):

      `σ_ref.toOp = Σ_{s∈S} |γ_s|² • (componentReference imgWit s).toOp`.

    This pins the reference `σ_ref`: a `σ_ref`-independent conclusion would be false as
    `σ_ref → 0`, by monotonicity of `Hmin(·|σ)` in `σ`.  Reducible so it unfolds to
    the operator equation `smoothHmin_classicalCond_reduction` expects as its
    classical-on-`S` reference pin. -/
@[reducible] def SuperpositionReferencePin
    {d dX dB n r : ℕ} [NeZero d] [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    [NeZero (d ^ n)] [NeZero (dX ^ n)] [NeZero (dB ^ n)]
    [NeZero (dX ^ r)] [NeZero (dB ^ r)] [NeZero (dX ^ n * dB ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    {symWit : RestrictedSymSpaceWitness d n r θ Ψ}
    {σ_XB : DensityOp (dX * dB)}
    {ρ_n : CQState (Fin (dX ^ n)) (dB ^ n)}
    {σ_ref : SubDensityOp (dB ^ n)}
    {ε : ℝ}
    (imgWit : CQChannelImageWitness θ Ψ symWit σ_XB ρ_n σ_ref ε) : Prop :=
  σ_ref.toOp =
    ∑ s ∈ symWit.S,
      (superpositionWeight symWit s : ℂ) • (componentReference imgWit s).toOp

/-- An independent classical tail referenced to its own marginal increases extended smooth
entropy. No normalization, radius, or reference regularity condition is needed. -/
lemma smoothMinEntropy_le_tensor_classical_tail
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X'] {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ε : ℝ) (block : CQState X n) (tail : CQState X' n') (σ : SubDensityOp n) :
    smoothMinEntropy ε block σ ≤
      smoothMinEntropy ε (CQState.tensor block tail)
        (SubDensityOp.tensor σ tail.quantumMarginal) := by
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨CQState.tensor τ tail, ?_, fun t ht => ?_⟩
  · have hdist := CQState.tensor_purifiedDistance_subadditive block τ tail tail
    rw [CQState.purifiedDistance_self_zero, add_zero] at hdist
    exact hdist.trans hd
  · have htail : isFeasible tail tail.quantumMarginal 1 :=
      isFeasible_of_quantumMarginalOp_dominated tail tail.quantumMarginal zero_le_one
        (by rw [Complex.ofReal_one, one_smul]; exact fun _ => le_rfl)
    simpa only [mul_one] using isFeasible_tensor ht htail

/-- Simultaneous quantum reindexing preserves extended smooth min-entropy. -/
lemma smoothMinEntropy_reindexQ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (e : Fin n ≃ Fin n) (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropy ε (CQState.reindexQ e ρ) (SubDensityOp.reindex e σ) =
      smoothMinEntropy ε ρ σ := by
  apply le_antisymm
  · apply smoothMinEntropy_le_of_transport
    intro τ hd
    refine ⟨CQState.reindexQ e.symm τ, ?_, fun t ht => ?_⟩
    · rwa [← CQState.purifiedDistance_reindexQ e ρ (CQState.reindexQ e.symm τ),
        CQState.reindexQ_reindexQ_symm]
    · apply (isFeasible_reindexQ e (CQState.reindexQ e.symm τ) σ t).mp
      simpa only [CQState.reindexQ_reindexQ_symm] using ht
  · apply smoothMinEntropy_le_of_transport
    intro τ hd
    refine ⟨CQState.reindexQ e τ, ?_, fun t ht => (isFeasible_reindexQ e τ σ t).mpr ht⟩
    simpa only [CQState.purifiedDistance_reindexQ] using hd

/-- Classical relabelling preserves extended smooth min-entropy. -/
lemma smoothMinEntropy_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    {n : ℕ} [NeZero n] (e : X ≃ Y) (ε : ℝ) (ρ : CQState Y n) (σ : SubDensityOp n) :
    smoothMinEntropy ε (CQState.relabel e ρ) σ = smoothMinEntropy ε ρ σ := by
  apply le_antisymm
  · apply smoothMinEntropy_le_of_transport
    intro τ hd
    refine ⟨CQState.relabel e.symm τ, ?_, fun t ht => ⟨ht.1, fun y => ht.2 (e.symm y)⟩⟩
    rwa [← CQState.purifiedDistance_relabel e ρ (CQState.relabel e.symm τ),
      CQState.relabel_relabel_symm]
  · apply smoothMinEntropy_le_of_transport
    intro τ hd
    refine ⟨CQState.relabel e τ, ?_, fun t ht => ⟨ht.1, fun x => ht.2 (e x)⟩⟩
    simpa only [CQState.purifiedDistance_relabel] using hd


/-- Quantum reindexing of both state and reference preserves signed smooth min-entropy. -/
lemma smoothMinEntropyReal_reindexQ {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (e : Fin n ≃ Fin n) (ε : ℝ) (ρ : CQState X n) (σ : SubDensityOp n) :
    smoothMinEntropyReal ε (CQState.reindexQ e ρ)
        (InfoTheory.SmoothMinEntropy.SubDensityOp.reindex e σ) =
      smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  congr 1
  ext h
  constructor
  · rintro ⟨rho2, hval, hd⟩
    -- A candidate `rho2` near `reindexQ e ρ` is `reindexQ e ρ2'` with `ρ2' = reindexQ e.symm rho2`.
    refine ⟨CQState.reindexQ e.symm rho2, ?_, ?_⟩
    · rw [hval, ← conditionalMinEntropyReal_reindexQ e (CQState.reindexQ e.symm rho2) σ,
        CQState.reindexQ_reindexQ_symm]
    · rw [← CQState.purifiedDistance_reindexQ e ρ (CQState.reindexQ e.symm rho2),
        CQState.reindexQ_reindexQ_symm]
      exact hd
  · rintro ⟨rho2, hval, hd⟩
    refine ⟨CQState.reindexQ e rho2, ?_, ?_⟩
    · rw [hval, conditionalMinEntropyReal_reindexQ e rho2 σ]
    · rw [CQState.purifiedDistance_reindexQ e ρ rho2]; exact hd

/-- Relabelling the classical register preserves signed smooth min-entropy. -/
lemma smoothMinEntropyReal_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    {n : ℕ} [NeZero n] (e : X ≃ Y) (ε : ℝ) (ρ : CQState Y n) (σ : SubDensityOp n) :
    smoothMinEntropyReal ε (CQState.relabel e ρ) σ = smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  congr 1
  ext h
  constructor
  · rintro ⟨rho2, hval, hd⟩
    -- A candidate `rho2 : CQState X n` near `relabel e ρ` is `relabel e ρ2'` with
    -- `ρ2' = relabel e.symm rho2 : CQState Y n`.
    refine ⟨CQState.relabel e.symm rho2, ?_, ?_⟩
    · rw [hval, ← conditionalMinEntropyReal_relabel e (CQState.relabel e.symm rho2) σ,
        CQState.relabel_relabel_symm]
    · rw [← CQState.purifiedDistance_relabel e ρ (CQState.relabel e.symm rho2),
        CQState.relabel_relabel_symm]
      exact hd
  · rintro ⟨rho2, hval, hd⟩
    refine ⟨CQState.relabel e rho2, ?_, ?_⟩
    · rw [hval, conditionalMinEntropyReal_relabel e rho2 σ]
    · rw [CQState.purifiedDistance_relabel e ρ rho2]; exact hd


/-- Tensoring with a normalized tail and its marginal reference does not decrease signed smooth
min-entropy at a positive-definite block reference. -/
lemma smoothMinEntropyReal_le_tensor_classical_tail
    {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    [Nonempty X] [Nonempty X']
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ε' : ℝ) (hε'_pos : 0 < ε') (hε'_lt_one : ε' < 1)
    (block : CQState X n) (tail : CQState X' n')
    (ref_block : SubDensityOp n)
    (hblock_norm : ∑ x : X, (block.stateMap x).trace = 1)
    (htail_norm : ∑ x' : X', (tail.stateMap x').trace = 1)
    (href_block_posdef : ref_block.toOp.PosDef) :
    smoothMinEntropyReal ε' block ref_block ≤
      smoothMinEntropyReal ε' (CQState.tensor block tail)
        (SubDensityOp.tensor ref_block tail.quantumMarginal) := by
  apply le_of_forall_pos_le_add
  intro ν hν
  have h_lt : smoothMinEntropyReal ε' block ref_block - ν <
      smoothMinEntropyReal ε' block ref_block := by
    linarith
  obtain ⟨bhat, hd1, hh1⟩ :=
    smoothMinEntropyReal_exists_approx ε' hε'_pos.le block ref_block
      (smoothMinEntropyReal ε' block ref_block - ν) h_lt
  have hd_tensor :
      CQState.purifiedDistance (CQState.tensor block tail) (CQState.tensor bhat tail) ≤ ε' := by
    have h_sub := InfoTheory.SmoothMinEntropy.CQState.tensor_purifiedDistance_subadditive
      (X := X) (X' := X') block bhat tail tail
    rw [CQState.purifiedDistance_self_zero] at h_sub
    linarith
  have hε'_sq_lt : ε' ^ 2 < 1 := by nlinarith [sq_nonneg ε']
  have hweight1 : 0 < ∑ x : X, (bhat.stateMap x).trace := by
    have h_ge : 1 - ε' ^ 2 ≤ ∑ x : X, (bhat.stateMap x).trace :=
      CQState.sum_stateMap_trace_ge_of_purifiedDistance hε'_pos.le hblock_norm hd1
    linarith
  have hfeas1 : hasFeasibleLambda bhat ref_block :=
    hasFeasibleLambda_of_posDef bhat ref_block href_block_posdef
  have hlam1 : 0 < minFeasibleLambda bhat ref_block :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos bhat ref_block hweight1 hfeas1
  have htail_feas1 : isFeasible tail tail.quantumMarginal 1 :=
    InfoTheory.SmoothMinEntropy.isFeasible_of_quantumMarginalOp_dominated
      tail tail.quantumMarginal zero_le_one
      (by rw [Complex.ofReal_one, one_smul]; intro v; exact le_refl _)
  have hfeas2 : hasFeasibleLambda tail tail.quantumMarginal := ⟨1, htail_feas1⟩
  have hweight2 : 0 < ∑ x' : X', (tail.stateMap x').trace := by rw [htail_norm]; norm_num
  have hlam2 : 0 < minFeasibleLambda tail tail.quantumMarginal :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos tail tail.quantumMarginal
      hweight2 hfeas2
  have hfeasT : hasFeasibleLambda (CQState.tensor bhat tail)
      (SubDensityOp.tensor ref_block tail.quantumMarginal) := by
    obtain ⟨t1, ht1⟩ := id hfeas1
    exact ⟨t1 * 1, InfoTheory.SmoothMinEntropy.isFeasible_tensor ht1 htail_feas1⟩
  have hweightT :
      0 < ∑ p : X × X', ((CQState.tensor bhat tail).stateMap p).trace := by
    rw [CQState.tensor_sum_trace]
    exact mul_pos hweight1 hweight2
  have hlamT : 0 < minFeasibleLambda (CQState.tensor bhat tail)
      (SubDensityOp.tensor ref_block tail.quantumMarginal) :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hweightT hfeasT
  have hAdd :=
    InfoTheory.SmoothMinEntropy.conditionalMinEntropyReal_tensor_additivity_le
      bhat tail ref_block tail.quantumMarginal hfeas1 hfeas2 hlam1 hlam2 hlamT
  have htail_nonneg : 0 ≤ conditionalMinEntropyReal tail tail.quantumMarginal :=
    conditionalMinEntropyReal_quantumMarginal_nonneg tail
  have hρρ'_norm :
      ∑ p : X × X', ((CQState.tensor block tail).stateMap p).trace = 1 := by
    rw [CQState.tensor_sum_trace, hblock_norm, htail_norm]; ring
  have hbdd_tensor :
      BddAbove (Set.ofPred (isInSmoothedSetReal ε' (CQState.tensor block tail)
        (SubDensityOp.tensor ref_block tail.quantumMarginal))) :=
    smoothMinEntropyReal_bddAbove ε' hε'_lt_one (CQState.tensor block tail) hρρ'_norm
      (SubDensityOp.tensor ref_block tail.quantumMarginal)
  have hsmooth_le :
      conditionalMinEntropyReal (CQState.tensor bhat tail)
          (SubDensityOp.tensor ref_block tail.quantumMarginal) ≤
        smoothMinEntropyReal ε' (CQState.tensor block tail)
          (SubDensityOp.tensor ref_block tail.quantumMarginal) :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε'
      (CQState.tensor block tail) (SubDensityOp.tensor ref_block tail.quantumMarginal)
      _ (CQState.tensor bhat tail) hbdd_tensor hd_tensor le_rfl
  linarith

end InfoTheory.SmoothMinEntropy.SymmetricAEP

end -- noncomputable section
