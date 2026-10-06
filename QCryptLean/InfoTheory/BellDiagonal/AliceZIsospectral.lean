import QCryptLean.InfoTheory.BellDiagonal.AliceZMonotone
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQConditionalEntropyMaxBound
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance
import QCryptLean.InfoTheory.VonNeumannEntropy.Additivity

/-!
# CQ measurement isospectrality for the Alice-`Z` dephasing

For a two-qubit `AB` density operator `σ : DensityOp 4` and any tripartite **pure** purifier
`Ψ : DensityOp (4·4)` with `Tr_E Ψ = σ`, the bit–Eve joint CQ state obtained by measuring Alice's
qubit in the `Z` basis is isospectral to the Alice-`Z` dephased state `Δ_A σ`:

`S(joint_σ) = S(Δ_A σ)`,

where `joint_σ` is the joint density operator of the bit-CQ state whose `z`-block is
`Tr_AB[(Π_z ⊗ I) Ψ (Π_z ⊗ I)]` (Eve's reduced state conditioned on Alice's bit `z`), and
`Δ_A σ = Π_0 σ Π_0 + Π_1 σ Π_1`.

The proof decomposes both sides
as `Σ_z entropyTerm(p_z) + Σ_z p_z · S(block_z)` via the CQ entropy split, identifying the
joint blocks (Eve) and the dephased blocks (Alice–Bob) as the two reduced states of the **pure**
`z`-component `(Π_z ⊗ I) Ψ (Π_z ⊗ I)`, hence Schmidt-isospectral.

References: Coles–Colbeck–Yu–Zwolak 2012 (PRL 108, 210405); Devetak–Winter 2005; Nahar, Tupkary,
Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851) App. B.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open InfoTheory.VonNeumannEntropy InfoTheory.SmoothMinEntropy
open scoped BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open Math.ClassicalEntropy

/-! ## The Alice-`Z` block as a sub-density operator -/

/-- The Alice-`Z` bit of computational index `a ∈ Fin 4`: `a / 2`. -/
def aliceZBit (a : Fin 4) : Fin 2 := ⟨a.val / 2, by omega⟩

/-- The `z`-block `Π_z σ Π_z` of the Alice-`Z` dephasing is positive semidefinite. -/
lemma aliceZBlock_posSemidef (σ : DensityOp 4) (z : Fin 2) :
    (aliceZProj z * σ.toOp * aliceZProj z).PosSemidef := by
  have hσ : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have h := InfoTheory.RelativeEntropy.posSemidef_conj_aux σ.toOp (aliceZProj z) hσ
  rwa [aliceZProj_conjTranspose] at h

/-- The two Alice-`Z` block traces sum to one. -/
lemma aliceZBlock_trace_sum (σ : DensityOp 4) :
    (aliceZProj 0 * σ.toOp * aliceZProj 0).trace
      + (aliceZProj 1 * σ.toOp * aliceZProj 1).trace = 1 := by
  have h := aliceZDephaseOp_trace σ
  unfold aliceZDephaseOp at h
  rwa [Matrix.trace_add] at h

/-- Each Alice-`Z` block has real trace at most one. -/
lemma aliceZBlock_trace_le_one (σ : DensityOp 4) (z : Fin 2) :
    (aliceZProj z * σ.toOp * aliceZProj z).trace.re ≤ 1 := by
  have hsum := congrArg Complex.re (aliceZBlock_trace_sum σ)
  rw [Complex.add_re, Complex.one_re] at hsum
  have h0 : 0 ≤ (aliceZProj 0 * σ.toOp * aliceZProj 0).trace.re :=
    (Complex.le_def.mp (aliceZBlock_posSemidef σ 0).trace_nonneg).1.trans_eq (by simp)
  have h1 : 0 ≤ (aliceZProj 1 * σ.toOp * aliceZProj 1).trace.re :=
    (Complex.le_def.mp (aliceZBlock_posSemidef σ 1).trace_nonneg).1.trans_eq (by simp)
  fin_cases z
  · simpa using by linarith
  · simpa using by linarith

/-- The Alice-`Z` `z`-block `Π_z σ Π_z`, packaged as a `SubDensityOp 4`. -/
def aliceZDephaseBlock (σ : DensityOp 4) (z : Fin 2) : SubDensityOp 4 where
  toOp := aliceZProj z * σ.toOp * aliceZProj z
  isHermitian := (aliceZBlock_posSemidef σ z).1
  pos_semidef := fun x => posSemidef_re_quadraticForm_nonneg (aliceZBlock_posSemidef σ z) x
  trace_le_one := aliceZBlock_trace_le_one σ z

@[simp] lemma aliceZDephaseBlock_toOp (σ : DensityOp 4) (z : Fin 2) :
    (aliceZDephaseBlock σ z).toOp = aliceZProj z * σ.toOp * aliceZProj z := rfl

/-- The Alice-`Z` dephased bit-CQ state on the Alice–Bob register: classical register the Alice bit
`z ∈ Fin 2`, block `z` the (sub-normalized) `Π_z σ Π_z`. Its quantum marginal is `Δ_A σ` and its
joint density is isospectral to `Δ_A σ`. -/
def aliceZDephaseCQState (σ : DensityOp 4) : CQState (Fin 2) 4 where
  stateMap := aliceZDephaseBlock σ
  weight_le_one := by
    have hsum := congrArg Complex.re (aliceZBlock_trace_sum σ)
    rw [Complex.add_re, Complex.one_re] at hsum
    simp only [SubDensityOp.trace, aliceZDephaseBlock_toOp, Fin.sum_univ_two]
    exact le_of_eq hsum

@[simp] lemma aliceZDephaseCQState_stateMap (σ : DensityOp 4) (z : Fin 2) :
    (aliceZDephaseCQState σ).stateMap z = aliceZDephaseBlock σ z := rfl

/-- The Alice-`Z` dephased bit-CQ state is normalized (total weight one). -/
lemma aliceZDephaseCQState_norm (σ : DensityOp 4) :
    ∑ z : Fin 2, ((aliceZDephaseCQState σ).stateMap z).trace = 1 := by
  have hsum := congrArg Complex.re (aliceZBlock_trace_sum σ)
  rw [Complex.add_re, Complex.one_re] at hsum
  simp only [aliceZDephaseCQState_stateMap, SubDensityOp.trace, aliceZDephaseBlock_toOp,
    Fin.sum_univ_two]
  exact hsum

/-! ## Matrix-entry formulas for the Alice-`Z` blocks -/

/-- The `(a, a')` entry of the Alice-`Z` block `Π_z σ Π_z`. -/
lemma aliceZBlock_apply (σ : DensityOp 4) (z : Fin 2) (a a' : Fin 4) :
    (aliceZProj z * σ.toOp * aliceZProj z) a a'
      = (if aliceZBit a = z then (1 : ℂ) else 0) * σ.toOp a a'
          * (if aliceZBit a' = z then (1 : ℂ) else 0) := by
  unfold aliceZProj
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcond : ∀ b : Fin 4, (if b.val / 2 = z.val then (1 : ℂ) else 0)
      = (if aliceZBit b = z then (1 : ℂ) else 0) := by
    intro b; simp only [aliceZBit, Fin.ext_iff]
  rw [hcond a, hcond a']

/-- The `(a, a')` entry of the Alice-`Z` dephasing `Δ_A σ`. -/
lemma aliceZDephaseOp_apply (σ : DensityOp 4) (a a' : Fin 4) :
    (aliceZDephaseOp σ) a a'
      = (if aliceZBit a = aliceZBit a' then σ.toOp a a' else 0) := by
  unfold aliceZDephaseOp
  rw [Matrix.add_apply, aliceZBlock_apply, aliceZBlock_apply]
  fin_cases a <;> fin_cases a' <;> simp [aliceZBit]

/-! ## The reconciliation isometry `Δ_A σ ↪ ν.toJointDensity` -/

/-- The coordinate inclusion `ℂ⁴ ↪ ℂ⁴ ⊗ ℂ²` sending Alice block `z`'s coordinates into the
`z`-th summand of the joint CQ register: column `c` is the standard basis vector indexed by
`(c, aliceZBit c)` under the joint reindexing `cqJointEquiv`. -/
def aliceZDephaseEmbed : Matrix (Fin (4 * Fintype.card (Fin 2))) (Fin 4) ℂ :=
  Matrix.of fun i c => if i = cqJointEquiv (Fin 2) 4 (c, aliceZBit c) then 1 else 0

/-- `aliceZDephaseEmbed` is an isometry: `V† V = 1`. -/
lemma aliceZDephaseEmbed_isometry :
    aliceZDephaseEmbed.conjTranspose * aliceZDephaseEmbed = 1 := by
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ i, aliceZDephaseEmbed.conjTranspose c i * aliceZDephaseEmbed i c'
      = (if i = cqJointEquiv (Fin 2) 4 (c, aliceZBit c) then (1 : ℂ) else 0)
          * (if i = cqJointEquiv (Fin 2) 4 (c', aliceZBit c') then (1 : ℂ) else 0) := by
    intro i
    simp only [aliceZDephaseEmbed, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star : ℂ → ℂ), star_one, star_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_eq_single (cqJointEquiv (Fin 2) 4 (c, aliceZBit c))]
  · rw [ite_eq_left rfl, one_mul]
    by_cases hcc : c = c'
    · subst hcc; simp
    · rw [ite_eq_right hcc, ite_eq_right]
      intro h
      exact hcc (Prod.ext_iff.mp ((cqJointEquiv (Fin 2) 4).injective h)).1
  · intro i _ hi; rw [ite_eq_right hi, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Row-collapse for the embedding: summing a function against the embedding indicator selects the
value at the first component of `q` when the second component of `q` is the Alice bit of the
first. -/
lemma aliceZEmbed_collapse (g : Fin 4 → ℂ) (q : Fin 4 × Fin 2) :
    ∑ c : Fin 4, (if cqJointEquiv (Fin 2) 4 q = cqJointEquiv (Fin 2) 4 (c, aliceZBit c)
        then (1 : ℂ) else 0) * g c
      = (if q.2 = aliceZBit q.1 then g q.1 else 0) := by
  rw [Finset.sum_eq_single q.1]
  · have hcond : (cqJointEquiv (Fin 2) 4 q = cqJointEquiv (Fin 2) 4 (q.1, aliceZBit q.1))
        ↔ (q.2 = aliceZBit q.1) := by
      rw [(cqJointEquiv (Fin 2) 4).apply_eq_iff_eq, Prod.ext_iff]
      simp
    by_cases h : q.2 = aliceZBit q.1
    · rw [ite_eq_left (hcond.mpr h), one_mul, ite_eq_left h]
    · rw [ite_eq_right (fun hh => h (hcond.mp hh)), zero_mul, ite_eq_right h]
  · intro c _ hc
    rw [ite_eq_right (fun heq =>
      hc ((Prod.ext_iff.mp ((cqJointEquiv (Fin 2) 4).injective heq)).1.symm)), zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- `(V M)` row entry at an embedded index selects the entry of `M` at the first component of
`p`. -/
lemma aliceZEmbed_mul_apply (M : Op 4) (p : Fin 4 × Fin 2) (c' : Fin 4) :
    (aliceZDephaseEmbed * M) (cqJointEquiv (Fin 2) 4 p) c'
      = (if p.2 = aliceZBit p.1 then M p.1 c' else 0) := by
  rw [Matrix.mul_apply]
  simp only [aliceZDephaseEmbed, Matrix.of_apply]
  exact aliceZEmbed_collapse (fun c => M c c') p

/-- The `(p, q)` entry of `V M V†` (both indices embedded) selects the `(p.1, q.1)` entry of `M`,
gated by both Alice-bit consistency conditions. -/
lemma aliceZEmbed_conj_apply (M : Op 4) (p q : Fin 4 × Fin 2) :
    (aliceZDephaseEmbed * M * aliceZDephaseEmbed.conjTranspose)
        (cqJointEquiv (Fin 2) 4 p) (cqJointEquiv (Fin 2) 4 q)
      = (if p.2 = aliceZBit p.1 then
            (if q.2 = aliceZBit q.1 then M p.1 q.1 else 0) else 0) := by
  rw [Matrix.mul_apply]
  have hVdag : ∀ c', aliceZDephaseEmbed.conjTranspose c' (cqJointEquiv (Fin 2) 4 q)
      = (if cqJointEquiv (Fin 2) 4 q = cqJointEquiv (Fin 2) 4 (c', aliceZBit c')
          then (1 : ℂ) else 0) := by
    intro c'
    simp only [aliceZDephaseEmbed, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star : ℂ → ℂ), star_one, star_zero]
  simp only [hVdag, aliceZEmbed_mul_apply]
  by_cases hp : p.2 = aliceZBit p.1
  · simp only [ite_eq_left hp]
    rw [show (∑ c' : Fin 4, M p.1 c'
            * (if cqJointEquiv (Fin 2) 4 q = cqJointEquiv (Fin 2) 4 (c', aliceZBit c')
                then (1 : ℂ) else 0))
          = ∑ c' : Fin 4, (if cqJointEquiv (Fin 2) 4 q = cqJointEquiv (Fin 2) 4 (c', aliceZBit c')
                then (1 : ℂ) else 0) * M p.1 c' from by
        apply Finset.sum_congr rfl; intro c' _; ring]
    exact aliceZEmbed_collapse (fun c' => M p.1 c') q
  · simp only [ite_eq_right hp, zero_mul, Finset.sum_const_zero]

/-- Scalar identity underlying the reconciliation: the doubly-bit-gated dephasing entry equals the
block-diagonal entry of the per-bit block. -/
lemma aliceZ_ind_scalar (P Q w w' : Fin 2) (s : ℂ) :
    (if w = P then (if w' = Q then (if P = Q then s else 0) else 0) else 0)
      = (if w = w' then (if P = w then (1 : ℂ) else 0) * s * (if Q = w then 1 else 0) else 0) := by
  fin_cases P <;> fin_cases Q <;> fin_cases w <;> fin_cases w' <;> simp

/-- The underlying operator of a CQ state's joint density, written with the joint reindexing
equivalence `cqJointEquiv`. -/
lemma aliceZ_toJointDensity_reindex (ρ : CQState (Fin 2) 4) :
    ρ.toJointDensity.toOp
      = Matrix.reindex (cqJointEquiv (Fin 2) 4) (cqJointEquiv (Fin 2) 4)
          (Matrix.blockDiagonal (fun z => (ρ.stateMap z).toOp)) :=
  CQState.toJointDensity_toOp_eq_reindex_blockDiagonal ρ

/-- The Alice-`Z` dephased state `Δ_A σ` is isospectral to the joint density
operator of its bit-CQ form `ν`, via the explicit reconciliation isometry. -/
lemma aliceZDephase_entropy_eq_jointDensity (σ : DensityOp 4) :
    vonNeumannEntropy (aliceZDephase σ)
      = vonNeumannEntropy
          ((aliceZDephaseCQState σ).toJointDensityOp (aliceZDephaseCQState_norm σ)) := by
  have : NeZero (4 * Fintype.card (Fin 2)) := ⟨by simp⟩
  rw [← InfoTheory.RelativeEntropy.vonNeumannEntropy_isometry_invariance aliceZDephaseEmbed
        aliceZDephaseEmbed_isometry (aliceZDephase σ)]
  congr 1
  apply DensityOp.ext
  change aliceZDephaseEmbed * (aliceZDephase σ).toOp * aliceZDephaseEmbed.conjTranspose
      = (aliceZDephaseCQState σ).toJointDensity.toOp
  rw [aliceZ_toJointDensity_reindex, aliceZDephase_toOp]
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  set e := cqJointEquiv (Fin 2) 4 with he
  set p := e.symm i with hp
  set q := e.symm j with hq
  have hi : i = e p := by rw [hp, e.apply_symm_apply]
  have hj : j = e q := by rw [hq, e.apply_symm_apply]
  rw [hi, hj, aliceZEmbed_conj_apply, Matrix.blockDiagonal_apply,
      aliceZDephaseCQState_stateMap, aliceZDephaseBlock_toOp,
      aliceZDephaseOp_apply, aliceZBlock_apply]
  exact aliceZ_ind_scalar (aliceZBit p.1) (aliceZBit q.1) p.2 q.2 (σ.toOp p.1 q.1)

/-! ## Per-block Schmidt and the assembled isospectrality -/

/-- The Alice-`Z` block projector tensored with the Eve identity is Hermitian. -/
lemma aliceZProjTensor_isHermitian (z : Fin 2) :
    (Op.tensor (aliceZProj z) (1 : Op 4)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Op.tensor_conjTranspose, aliceZProj_conjTranspose, conjTranspose_one]

/-- The weighted block entropy of a two-outcome CQ state, written as the classical-marginal-weighted
sum of conditional-state von Neumann entropies. -/
lemma weightedBlockEntropy_eq_sum_conditionalState (ξ : CQState (Fin 2) 4) :
    ξ.weightedBlockEntropy
      = ∑ z : Fin 2, ξ.classicalMarginal z * vonNeumannEntropy (ξ.conditionalState z) := by
  rw [CQState.weightedBlockEntropy]
  exact Finset.sum_congr rfl
    (fun z _ => (ξ.classicalMarginal_mul_vonNeumannEntropy_conditionalState z).symm)

/-- The bit–Eve joint CQ state of a pure Alice-`Z`-measured purifier is
isospectral to the Alice-`Z` dephased Alice–Bob state.

For any normalized two-outcome CQ state `ρ` whose `z`-block is Eve's reduced state after measuring
Alice's `Z` bit on a pure purifier `Ψ` of `σ` (`horigin`), the joint von Neumann entropy of `ρ`
equals that of `Δ_A σ`. -/
theorem aliceZ_measuredJoint_entropy_eq_dephase
    (σ : DensityOp 4)
    (ρ : CQState (Fin 2) 4) (hρ_norm : ∑ z : Fin 2, (ρ.stateMap z).trace = 1)
    (Ψ : DensityOp (4 * 4)) (hΨ : Ψ.IsPure)
    (hΨσ : partialTraceB Ψ.toOp = σ.toOp)
    (horigin : ∀ z : Fin 2, (ρ.stateMap z).toOp =
        partialTraceA (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
          * Op.tensor (aliceZProj z) (1 : Op 4))) :
    vonNeumannEntropy (ρ.toJointDensityOp hρ_norm) = vonNeumannEntropy (aliceZDephase σ) := by
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  rw [aliceZDephase_entropy_eq_jointDensity σ,
      CQState.vonNeumannEntropy_toJointDensityOp_eq_classicalShannon_add_weightedBlockEntropy
        ρ hρ_norm,
      CQState.vonNeumannEntropy_toJointDensityOp_eq_classicalShannon_add_weightedBlockEntropy
        (aliceZDephaseCQState σ) (aliceZDephaseCQState_norm σ),
      weightedBlockEntropy_eq_sum_conditionalState ρ,
      weightedBlockEntropy_eq_sum_conditionalState (aliceZDephaseCQState σ)]
  have hcm : ∀ z, ρ.classicalMarginal z = (aliceZDephaseCQState σ).classicalMarginal z := by
    intro z
    simp only [CQState.classicalMarginal, SubDensityOp.trace, aliceZDephaseCQState_stateMap,
      aliceZDephaseBlock_toOp]
    rw [horigin z]
    congr 1
    rw [trace_partialTraceA,
        ← trace_partialTraceB (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
          * Op.tensor (aliceZProj z) (1 : Op 4)),
        partialTraceB_sandwich_tensor_one, hΨσ]
  have hcond : ∀ z, 0 < ρ.classicalMarginal z →
      vonNeumannEntropy (ρ.conditionalState z)
        = vonNeumannEntropy ((aliceZDephaseCQState σ).conditionalState z) := by
    intro z hz
    have : NeZero (4 * 4) := ⟨by norm_num⟩
    have hMherm : (Op.tensor (aliceZProj z) (1 : Op 4)).IsHermitian :=
      aliceZProjTensor_isHermitian z
    have hΨpsd : Ψ.toOp.PosSemidef := posSemidefOp_implies_mathlib Ψ.toPosSemidefOp
    have hPTA : partialTraceA (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
        * Op.tensor (aliceZProj z) (1 : Op 4)) = (ρ.stateMap z).toOp := (horigin z).symm
    have hPTB : partialTraceB (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
        * Op.tensor (aliceZProj z) (1 : Op 4)) = aliceZProj z * σ.toOp * aliceZProj z := by
      rw [partialTraceB_sandwich_tensor_one, hΨσ]
    have hXpsd : (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
        * Op.tensor (aliceZProj z) (1 : Op 4)).PosSemidef := by
      have h := InfoTheory.RelativeEntropy.posSemidef_conj_aux Ψ.toOp
        (Op.tensor (aliceZProj z) (1 : Op 4)) hΨpsd
      rwa [show (Op.tensor (aliceZProj z) (1 : Op 4))ᴴ = Op.tensor (aliceZProj z) (1 : Op 4)
        from hMherm] at h
    set Xz := Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp * Op.tensor (aliceZProj z) (1 : Op 4)
      with hXzdef
    -- real, positive trace of the z-component
    have htr_eq : Xz.trace = (ρ.stateMap z).toOp.trace := by rw [← hPTA, trace_partialTraceA]
    set a : ℝ := Xz.trace.re with hadef
    have ha_eq : a = ρ.classicalMarginal z := by
      rw [hadef, htr_eq]; rfl
    have ha_pos : 0 < a := ha_eq ▸ hz
    have him : Xz.trace.im = 0 := by
      have h := (Complex.le_def.mp hXpsd.trace_nonneg).2; simpa using h.symm
    have hXtr : Xz.trace = (a : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im, him]
    -- rank-one structure via the purifying ket
    set k := Ψ.pureKetOf hΨ with hkdef
    have hkspec : Ψ.toOp = k * k.dag := Ψ.pureKetOf_spec hΨ
    set φ : Ket (4 * 4) := Op.tensor (aliceZProj z) (1 : Op 4) * k with hφdef
    have hφX : φ * φ.dag = Xz := by
      rw [hXzdef, hkspec, hφdef,
          Ket.dag_op_mul_of_isHermitian (Op.tensor (aliceZProj z) (1 : Op 4)) hMherm k,
          op_mul_ketbra, ketbra_mul_op]
    have hφnorm : φ.dag * φ = (a : ℂ) := by
      rw [← hXtr, ← hφX, ket_mul_dag_eq_vecMulVec, bra_mul_ket_eq]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Ket.dag_vec,
        Pi.star_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hXX : Xz * Xz = (a : ℂ) • Xz := by
      rw [← hφX, ketbra_mul_ketbra, hφnorm]
    -- the normalized pure z-component
    set Xop : PosSemidefOp (4 * 4) :=
      ⟨⟨Xz, hXpsd.1⟩, fun x => posSemidef_re_quadraticForm_nonneg hXpsd x⟩ with hXopdef
    have ha_pos' : 0 < (Matrix.trace Xop.toOp).re := ha_pos
    set τ : DensityOp (4 * 4) := normalizePosSemidefOp Xop ha_pos' with hτdef
    have hτtoOp : τ.toOp = ((a⁻¹ : ℝ) : ℂ) • Xz := by
      rw [hτdef, normalizePosSemidefOp_toOp]
    have hpure_tau : τ.IsPure := by
      change τ.toOp * τ.toOp = τ.toOp
      rw [hτtoOp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hXX, smul_smul]
      congr 1
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp
    -- the two reduced states are the conditional states
    have hτA : DensityOp.partialTraceA τ = ρ.conditionalState z := by
      apply DensityOp.ext
      change partialTraceA τ.toOp = (ρ.conditionalState z).toOp
      rw [hτtoOp, partialTraceA_smul, hPTA, CQState.conditionalState, dite_eq_left hz]
      change ((a⁻¹ : ℝ) : ℂ) • (ρ.stateMap z).toOp =
        ((((ρ.stateMap z).toOp.trace.re)⁻¹ : ℝ) : ℂ) • (ρ.stateMap z).toOp
      congr 2
      rw [hadef, htr_eq]
    have hτB : DensityOp.partialTraceB τ = (aliceZDephaseCQState σ).conditionalState z := by
      apply DensityOp.ext
      change partialTraceB τ.toOp = ((aliceZDephaseCQState σ).conditionalState z).toOp
      rw [hτtoOp, partialTraceB_smul, hPTB, CQState.conditionalState,
          dite_eq_left (hcm z ▸ hz)]
      change ((a⁻¹ : ℝ) : ℂ) • (aliceZProj z * σ.toOp * aliceZProj z) =
        (((((aliceZDephaseCQState σ).stateMap z).toOp.trace.re)⁻¹ : ℝ) : ℂ) •
          ((aliceZDephaseCQState σ).stateMap z).toOp
      congr 2
      rw [aliceZDephaseCQState_stateMap, aliceZDephaseBlock_toOp]
      have hblockre : (aliceZProj z * σ.toOp * aliceZProj z).trace.re = a := by
        rw [← hPTB, trace_partialTraceB]
      rw [hblockre]
    rw [← hτA, ← hτB]
    exact purification_entropy_equality τ hpure_tau
  congr 1
  · exact Finset.sum_congr rfl (fun z _ => by rw [hcm z])
  · apply Finset.sum_congr rfl
    intro z _
    rw [hcm z]
    rcases eq_or_lt_of_le (ρ.classicalMarginal_nonneg z) with h0 | hpos
    · rw [← hcm z, ← h0, zero_mul, zero_mul]
    · rw [hcond z hpos]

/-! ## A.3a: the Eve quantum marginal of the measured CQ state purifies `σ` -/

/-- The bit-summed Alice-`Z` measurement of a pure tripartite state has Eve marginal equal to the
unmeasured Eve marginal: `Σ_z Tr_AB[(Π_z⊗I) Ψ (Π_z⊗I)] = Tr_AB Ψ`. -/
lemma aliceZ_sum_partialTraceA_eq (Ψ : Op (4 * 4)) :
    partialTraceA (Op.tensor (aliceZProj 0) (1 : Op 4) * Ψ * Op.tensor (aliceZProj 0) (1 : Op 4))
      + partialTraceA (Op.tensor (aliceZProj 1) (1 : Op 4) * Ψ
          * Op.tensor (aliceZProj 1) (1 : Op 4))
      = partialTraceA Ψ := by
  ext a b
  simp only [Matrix.add_apply]
  unfold aliceZProj
  rw [partialTraceA_sandwich_tensor_diagonal_one, partialTraceA_sandwich_tensor_diagonal_one]
  simp only [Matrix.of_apply]
  show (∑ k : Fin 4, _) + (∑ k : Fin 4, _) = partialTraceA Ψ a b
  rw [← Finset.sum_add_distrib]
  simp only [partialTraceA, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k _
  fin_cases k <;> simp

/-- Eve's reduced state after the Alice-`Z` measurement of a pure purifier
of `σ` is isentropic to `σ`. -/
theorem aliceZ_quantumMarginal_entropy_eq_self
    (σ : DensityOp 4)
    (ρ : CQState (Fin 2) 4) (hρ_norm : ∑ z : Fin 2, (ρ.stateMap z).trace = 1)
    (Ψ : DensityOp (4 * 4)) (hΨ : Ψ.IsPure)
    (hΨσ : partialTraceB Ψ.toOp = σ.toOp)
    (horigin : ∀ z : Fin 2, (ρ.stateMap z).toOp =
        partialTraceA (Op.tensor (aliceZProj z) (1 : Op 4) * Ψ.toOp
          * Op.tensor (aliceZProj z) (1 : Op 4))) :
    vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm) = vonNeumannEntropy σ := by
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have : NeZero (4 * 4) := ⟨by norm_num⟩
  have hqm : (ρ.quantumMarginalDensityOp hρ_norm).toOp = (DensityOp.partialTraceA Ψ).toOp := by
    change ρ.quantumMarginalOp = partialTraceA Ψ.toOp
    rw [CQState.quantumMarginalOp, Fin.sum_univ_two, horigin 0, horigin 1,
        aliceZ_sum_partialTraceA_eq]
  rw [InfoTheory.RelativeEntropy.vonNeumannEntropy_toOp_eq _ (DensityOp.partialTraceA Ψ) hqm,
      purification_entropy_equality Ψ hΨ]
  exact InfoTheory.RelativeEntropy.vonNeumannEntropy_toOp_eq (DensityOp.partialTraceB Ψ) σ hΨσ

end QKD.BB84.Engine

end
