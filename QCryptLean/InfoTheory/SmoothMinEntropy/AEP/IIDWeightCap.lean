import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBlockDomination

/-!
# Renner's per-(x,z) weight-cap smoothed state (main.tex:4617–4665)

This module supplies the explicit object-level construction of Renner's faithful
smoothed state for `thm:Hmincondrep`. The unfaithful single cumulative-projector
sandwich `Π · ρ^{⊗n} · Π` cannot dominate `2^{-T} (id⊗σ)^{⊗n}` for non-commuting
`ρ, σ` (the cross terms `Π ρ Π⊥` do not vanish). Renner's construction instead
redistributes the spectral weight of each conditional block across the cumulative
projectors `B_z` via the soft per-(x,z) cap, giving a state that dominates by
construction.

## The construction (main.tex:4617–4642)

Fix a classical label `xs : Fin n_copies → X`. The conditional block operator
`q_xs := (ρ.stateMap xs).toOp^{⊗}` (an `Op (n^n_copies)`) has a spectral
decomposition

  `q_xs = Σ_x p_x(xs) · |x⟩⟨x|`,         (`blockEigenvalue` / `blockSpectralProjector`)

with eigenvalues `p_x(xs) ≥ 0` and rank-one eigenprojectors `|x⟩⟨x|`. The
reference `τ := (id_A ⊗ σ_B)^{⊗n}` carries the **sorted** cumulative resolution
already built in `IID.lean`:

  `τ = Σ_z β_z · B_z`,    `q_z := Σ_{z' ≤ z} β_{z'}`,    `B_z = Σ_{z ≤ z'} P_{z'}`,

where `q_z = W.referenceEigenvalue z` is nondecreasing, `β_z = W.betaCoefficient z`
are the nonnegative increments, and `B_z = W.cumulativeProjector z` are the
nested cumulative projectors (main.tex:4600–4615).

With `λ := 2^{-T}`, the **split coefficients** are the increments of the capped
cumulative mass along the sorted reference order (main.tex:4626–4633):

  `Σ_{z ≤ z'} p_{x,z}(xs) = min(p_x(xs), λ · q_{z'})`,

so per `(x, z)`

  `p_{x,z}(xs) = min(p_x(xs), λ q_z) − min(p_x(xs), λ q_{z⁻})`,    (`splitCoefficient`)

with the convention `λ q_{z⁻} = 0` at the minimal sorted index (`q_{z⁻}`
shifted by `lamShift`).

The **weight-cap block** is (main.tex:4636–4642)

  `ρ̄_xs := Σ_x Σ_z p_{x,z}(xs) · B_z |x⟩⟨x| B_z`,             (`weightCapBlockOp`)

and the **weight-cap smoothed state** `ρ̄` is the CQ state whose `xs`-block is
`ρ̄_xs` (`weightCapCQState`).

## What this file proves

* `splitCoefficient_nonneg` — `0 ≤ p_{x,z}(xs)` (the capped cumulative mass is
  nondecreasing along the sorted order).
* `splitCoefficient_le_lambda_betaCoefficient` — Renner's **weight cap**
  `p_{x,z}(xs) ≤ λ β_z` (main.tex:4644–4645), the algebraic heart of the
  domination.
* `sum_splitCoefficient_le_blockEigenvalue` — `Σ_z p_{x,z}(xs) ≤ p_x(xs)`, the
  capped total mass per eigenvalue (`= min(p_x, λ q_{max})`).

The operator domination `2^{-T} τ − ρ̄_xs ≽ 0` (main.tex:4646–4665) is proved as
`weightCapBlock_opLe_pow_neg_threshold_smul_reference` by the orthogonal-`B_z`
resolution of the scalar cap. The weight-cap block is packaged as a sub-density
operator (`weightCapBlockSubDensityOp`) and CQ state (`weightCapCQState`), then
installed as the witness's smoothed state together with Renner's retained
crossing cut (`iidAEPRennerCutWitness`), discharging the Leaf-A block
domination `iidAEPSpectralCutBlockDomination`.

All essential objects are explicit `def`s — no `Classical.choose`, no
existential-backed placeholders. -/

open Quantum.Operators Matrix
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.IIDAEPCumulative
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {X : Type*} [Fintype X] {n : ℕ} [NeZero n]

/-! ## Per-block spectral data of the conditional tensor-power state -/

/-- Eigenvalues `p_x(xs)` of the conditional block operator
`(ρ.stateMap xs)^{⊗}` on the `A`-register `Op (n^n_copies)`. These are Renner's
`p_x` for the fixed classical label `xs` (main.tex:4617–4620). They are
nonnegative because the block operator is positive semidefinite. -/
def blockEigenvalue
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) : Fin (n ^ n_copies) → ℝ :=
  ((iidAEPTensorState ρ n_copies).stateMap
    xs).toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues

/-- Rank-one spectral eigenprojectors `|x⟩⟨x|` of the conditional block operator
`(ρ.stateMap xs)^{⊗}`, formed from its Hermitian eigenvector basis. These are
Renner's `|x⟩⟨x|` for the fixed classical label `xs` (main.tex:4617–4620). -/
def blockSpectralProjector
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) : Op (n ^ n_copies) :=
  let hτ :=
    ((iidAEPTensorState ρ n_copies).stateMap xs).toPosSemidefOp.toHermitianOp.isHermitian
  Matrix.vecMulVec ((hτ.eigenvectorBasis x).ofLp) (star (hτ.eigenvectorBasis x).ofLp)

omit [NeZero n] in
lemma blockEigenvalue_nonneg
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    0 ≤ blockEigenvalue ρ n_copies xs x := by
  unfold blockEigenvalue
  exact
    (Quantum.Operators.posSemidefOp_implies_mathlib
      ((iidAEPTensorState ρ n_copies).stateMap xs).toPosSemidefOp).eigenvalues_nonneg x

omit [NeZero n] in
/-- Each block eigenprojector `|x⟩⟨x|` is positive semidefinite (a rank-one
projector onto a normalized eigenvector). -/
theorem blockSpectralProjector_posSemidef
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    (blockSpectralProjector ρ n_copies xs x).PosSemidef := by
  simpa [blockSpectralProjector] using
    Matrix.posSemidef_vecMulVec_self_star
      (((iidAEPTensorState ρ n_copies).stateMap
        xs).toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis x).ofLp

omit [NeZero n] in
/-- **Eigenprojector relation for the conditional block operator.** The
block operator `ρ^{⊗}_xs` acts on its own rank-one eigenprojector `|x⟩⟨x|` by the
eigenvalue: `ρ^{⊗}_xs · |x⟩⟨x| = p_x(xs) · |x⟩⟨x|`. This is the spectral identity
`T |x⟩ = p_x |x⟩` lifted to the projector. -/
lemma blockOp_mul_blockSpectralProjector
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    ((iidAEPTensorState ρ n_copies).stateMap xs).toOp *
        blockSpectralProjector ρ n_copies xs x =
      (blockEigenvalue ρ n_copies xs x : ℂ) • blockSpectralProjector ρ n_copies xs x := by
  unfold blockSpectralProjector blockEigenvalue
  rw [Matrix.mul_vecMulVec, Matrix.IsHermitian.mulVec_eigenvectorBasis]
  ext i j
  simp [Matrix.vecMulVec, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- **Tensor-power Löwner domination of the conditional block.** From the
single-copy support gate `hasFeasibleLambda` (`∃ t, ρ_x ≼ t·σ` for every classical
outcome `x`), the tensor-power conditional block `ρ^{⊗}_xs` is Löwner-dominated by
a scalar multiple of the tensor-power reference `τ = σ^{⊗N}`:
`ρ^{⊗}_xs ≼ tᴺ · τ`. This lifts the per-copy domination through the tensor
power via `SubDensityOp.tensorFinProd_opLe_pow_const`. It is the operator
content of `hfeas` that forces `ker τ ⊆ ker ρ^{⊗}_xs`. -/
lemma iidAEPBlockOp_opLe_smul_tensorReference
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (xs : Fin n_copies → X) :
    ∃ c : ℝ, opLe ((iidAEPTensorState ρ n_copies).stateMap xs).toOp
      ((c : ℂ) • (iidAEPTensorReference σ n_copies).toOp) := by
  obtain ⟨t, ht0, htdom⟩ := hfeas
  refine ⟨t ^ n_copies, ?_⟩
  have hkey := SubDensityOp.tensorFinProd_opLe_pow_const
    (DensityOp.toSubDensityOp σ) n_copies (fun j => ρ.stateMap (xs j)) ht0
    (fun j => htdom (xs j))
  unfold iidAEPTensorState iidAEPTensorReference
  rw [CQState.tensorPower_stateMap_toOp]
  unfold SubDensityOp.tensorPower
  exact hkey

/-! ## Split coefficients (Renner's `p_{x,z}`)

The capped cumulative mass `min(p_x, λ q_{z'})` is nondecreasing in `z'` along
the sorted reference order. Its increments along that order are Renner's
nonnegative `p_{x,z}`. We phrase the increment with `lamShift` so the convention
`λ q_{z⁻} = 0` at the minimal sorted index is automatic. -/

/-- Renner's separation scale `λ = 2^{-T}` at the witness threshold
(main.tex:4586). -/
def weightCapScale
    {n_copies : ℕ} (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  (2 : ℝ) ^ (-W.entropyThreshold)

omit [NeZero n] in
lemma weightCapScale_pos
    {n_copies : ℕ} (W : IIDAEPSpectralWitness X n n_copies) :
    0 < weightCapScale W := by
  unfold weightCapScale; positivity

/-- The capped cumulative mass `min(p_x(xs), λ q_{z})` read as a function of the
sorted reference index, shifted to `Fin (n^n_copies + 1)` by prepending `0`
(the `q_{z⁻} = 0` convention at the minimal index). Here `q_z` is the sorted
reference eigenvalue `W.referenceEigenvalue z`. -/
def cappedCumulativeMass
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    Fin (n ^ n_copies + 1) → ℝ :=
  lamShift
    (fun z => min (blockEigenvalue ρ n_copies xs x)
      (weightCapScale W * W.referenceEigenvalue z))

/-- Renner's split coefficient `p_{x,z}(xs)` (main.tex:4626–4633): the increment
of the capped cumulative mass `min(p_x(xs), λ q_z)` along the sorted reference
order, with `min(p_x, λ q_{z⁻}) = 0` at the minimal sorted index.

By construction `Σ_{z ≤ z'} p_{x,z}(xs) = min(p_x(xs), λ q_{z'})`. -/
def splitCoefficient
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) : ℝ :=
  cappedCumulativeMass ρ n_copies W xs x z.succ
    - cappedCumulativeMass ρ n_copies W xs x z.castSucc

/-! ## The weight-cap smoothed state -/

/-- Renner's weight-cap conditional block `ρ̄_xs` (main.tex:4636–4642):

  `ρ̄_xs = Σ_x Σ_z p_{x,z}(xs) · B_z |x⟩⟨x| B_z`,

where `B_z = W.cumulativeProjector z` are the cumulative reference projectors,
`|x⟩⟨x| = blockSpectralProjector` are the block eigenprojectors, and
`p_{x,z}(xs) = splitCoefficient` are the split coefficients. -/
def weightCapBlockOp
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) : Op (n ^ n_copies) :=
  ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
    (splitCoefficient ρ n_copies W xs x z : ℂ) •
      (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
        W.cumulativeProjector z)

/-! ## Split-coefficient arithmetic -/

omit [NeZero n] in
/-- The split coefficients are nonnegative: the capped cumulative mass
`min(p_x, λ q_z)` is nondecreasing in `z` because `q_z = W.referenceEigenvalue z`
is monotone (sorted) and `λ ≥ 0`. (main.tex: the `p_{x,z}` are nonnegative
coefficients, line 4624.) -/
theorem splitCoefficient_nonneg
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hmono : Monotone W.referenceEigenvalue)
    (hq_nonneg : ∀ z, 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) :
    0 ≤ splitCoefficient ρ n_copies W xs x z := by
  have hp : 0 ≤ blockEigenvalue ρ n_copies xs x :=
    blockEigenvalue_nonneg ρ n_copies xs x
  have hlam : 0 ≤ weightCapScale W := (weightCapScale_pos W).le
  unfold splitCoefficient cappedCumulativeMass
  rw [sub_nonneg, lamShift_succ]
  rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
  · rw [h, lamShift_zero]
    exact le_min hp (mul_nonneg hlam (hq_nonneg _))
  · rw [hw, lamShift_succ]
    refine min_le_min le_rfl ?_
    refine mul_le_mul_of_nonneg_left ?_ hlam
    apply hmono
    have hval := congrArg Fin.val hw
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    rw [Fin.le_def]; omega

/-- **Renner's weight cap** `p_{x,z}(xs) ≤ λ β_z` (main.tex:4644–4645).

The increment of the capped cumulative mass `min(p_x, λ q_z)` from `z⁻` to `z`
is at most the increment of `λ q_z = λ (q_{z⁻} + β_z)`, namely `λ β_z`, because
`min` is `1`-Lipschitz and the uncapped jump is exactly `λ β_z`. This is the
algebraic content that makes the operator domination hold. -/
theorem splitCoefficient_le_lambda_betaCoefficient
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceCumulativeResolution σ n_copies W)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) :
    splitCoefficient ρ n_copies W xs x z ≤
      weightCapScale W * W.betaCoefficient z := by
  obtain ⟨hbeta_nn, _, _, _, _, _, hq_eq⟩ := href
  have hlam : 0 ≤ weightCapScale W := (weightCapScale_pos W).le
  -- Increment relation `q_z − q_{z⁻} = β_z` from the cumulative coefficient law.
  have hincr :
      W.referenceEigenvalue z - lamShift W.referenceEigenvalue z.castSucc
        = W.betaCoefficient z := by
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero, sub_zero, hq_eq z]
      have hz0 : z = 0 := by
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_zero] at this
        exact Fin.ext this
      rw [hz0]
      have hset0 :
          Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z' ≤ (0 : Fin (n ^ n_copies)))
            = {(0 : Fin (n ^ n_copies))} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.le_def, Fin.ext_iff, Fin.val_zero]
        omega
      rw [hset0, Finset.sum_singleton]
    · rw [hw, lamShift_succ, hq_eq z, hq_eq w]
      have hwval : z.val = w.val + 1 := by
        have hval := congrArg Fin.val hw
        simpa only [Fin.val_castSucc, Fin.val_succ] using hval
      have hwz : w < z := by rw [Fin.lt_def]; omega
      have hwz_le : w ≤ z := le_of_lt hwz
      -- `{z' ≤ z} = insert z {z' ≤ w}` since `z = w + 1`.
      have hset :
          Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z' ≤ z) =
            insert z (Finset.univ.filter
              (fun z' : Fin (n ^ n_copies) => z' ≤ w)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro ha
          rcases eq_or_lt_of_le ha with rfl | hlt
          · exact Or.inl rfl
          · refine Or.inr ?_
            rw [Fin.le_def]; rw [Fin.lt_def] at hlt; omega
        · rintro (rfl | ha)
          · exact le_rfl
          · exact le_trans ha hwz_le
      rw [hset, Finset.sum_insert (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; exact hwz)]
      ring
  -- `min`-difference bound: for `c ≤ b`, `min(a,b) − min(a,c) ≤ b − c`.
  have hmin_diff : ∀ a b c : ℝ, c ≤ b → min a b - min a c ≤ b - c := by
    intro a b c hcb
    rcases le_total a c with hac | hca
    · rw [min_eq_left hac, min_eq_left (le_trans hac hcb)]; linarith
    · rw [min_eq_right hca]
      rcases le_total a b with hab | hba
      · rw [min_eq_left hab]; linarith
      · rw [min_eq_right hba]
  -- The shifted scaled reference equals `λ` times the shifted reference.
  have hshift_eq :
      lamShift (fun z => weightCapScale W * W.referenceEigenvalue z) z.castSucc
        = weightCapScale W * lamShift W.referenceEigenvalue z.castSucc := by
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero, lamShift_zero, mul_zero]
    · rw [hw, lamShift_succ, lamShift_succ]
  -- The uncapped jump `λ q_z − λ q_{z⁻} = λ β_z ≥ 0`, so the cap shrinks it.
  have hjump :
      weightCapScale W * lamShift W.referenceEigenvalue z.castSucc
        ≤ weightCapScale W * W.referenceEigenvalue z := by
    refine mul_le_mul_of_nonneg_left ?_ hlam
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero, hq_eq z]
      exact Finset.sum_nonneg (fun i _ => hbeta_nn i)
    · rw [hw, lamShift_succ, hq_eq z, hq_eq w]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        have hval := congrArg Fin.val hw
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        rw [Fin.le_def] at ha ⊢; omega
      · intro i _ _; exact hbeta_nn i
  -- The outer-`min` shift at `z⁻` equals `min(p, λ · q_{z⁻})` (using `p ≥ 0`).
  have hcastSucc_eq :
      lamShift (fun z => min (blockEigenvalue ρ n_copies xs x)
          (weightCapScale W * W.referenceEigenvalue z)) z.castSucc
        = min (blockEigenvalue ρ n_copies xs x)
          (weightCapScale W * lamShift W.referenceEigenvalue z.castSucc) := by
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero, lamShift_zero, mul_zero, min_eq_right
        (blockEigenvalue_nonneg ρ n_copies xs x)]
    · rw [hw, lamShift_succ, lamShift_succ]
  unfold splitCoefficient cappedCumulativeMass
  rw [lamShift_succ, hcastSucc_eq]
  calc
    min (blockEigenvalue ρ n_copies xs x)
          (weightCapScale W * W.referenceEigenvalue z)
        - min (blockEigenvalue ρ n_copies xs x)
          (weightCapScale W * lamShift W.referenceEigenvalue z.castSucc)
      ≤ weightCapScale W * W.referenceEigenvalue z
          - weightCapScale W * lamShift W.referenceEigenvalue z.castSucc :=
        hmin_diff _ _ _ hjump
    _ = weightCapScale W * W.betaCoefficient z := by rw [← mul_sub, hincr]

omit [NeZero n] in
/-- The capped total mass per eigenvalue: `Σ_z p_{x,z}(xs) ≤ p_x(xs)`.

Telescoping the increments gives `Σ_z p_{x,z}(xs) = min(p_x, λ q_{max}) ≤ p_x`.
This is the per-eigenvalue half of the discarded-mass accounting
(main.tex:4631–4633: the full sum over `z ∈ Z^n ∪ {∞}` equals `p_x`, and the
`∞` term carries the discarded part). -/
theorem sum_splitCoefficient_le_blockEigenvalue
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    ∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z ≤
      blockEigenvalue ρ n_copies xs x := by
  set f : Fin (n ^ n_copies) → ℝ :=
    fun z => min (blockEigenvalue ρ n_copies xs x)
      (weightCapScale W * W.referenceEigenvalue z) with hf
  have hstep : ∀ z : Fin (n ^ n_copies),
      splitCoefficient ρ n_copies W xs x z = lamNat f (z.val + 1) - lamNat f z.val := by
    intro z
    rw [lamNat_succ, lamNat_castSucc]
    rfl
  rw [Finset.sum_congr rfl (fun z _ => hstep z),
    Fin.sum_univ_eq_sum_range (fun j => lamNat f (j + 1) - lamNat f j),
    Finset.sum_range_sub (lamNat f), lamNat_zero, sub_zero]
  -- `lamNat f (n^n_copies) = lamShift f (Fin.last) = f (Fin.last).pred = min(p_x, λ q_·) ≤ p_x`.
  have hlast : lamNat f (n ^ n_copies) ≤ blockEigenvalue ρ n_copies xs x := by
    unfold lamNat
    rw [dif_pos (Nat.lt_succ_self _)]
    rcases Fin.eq_zero_or_eq_succ (⟨n ^ n_copies, Nat.lt_succ_self _⟩ : Fin (n ^ n_copies + 1))
      with h | ⟨w, hw⟩
    · rw [h, lamShift_zero]; exact blockEigenvalue_nonneg ρ n_copies xs x
    · rw [hw, lamShift_succ, hf]; exact min_le_left _ _
  exact hlast

/-- Renner's **discard coefficient** `p_{x,∞}(xs)` (main.tex:4631–4633): the
residual eigenvalue mass not absorbed by the finite capped cumulative split,

  `p_{x,∞}(xs) = p_x(xs) − Σ_z p_{x,z}(xs) = p_x(xs) − min(p_x(xs), λ q_max)`.

This is the coefficient of the `∞` label in Renner's extended split index set
`z ∈ Z^n ∪ {∞}`, carrying exactly the spectral mass that the weight cap discards.
It is the load-bearing extra label that makes the tensor-power purification exact:
the family `√(p_{x,z})·|x⟩` over the finite labels reproduces only
`Σ_x min(p_x, λ q_max)|x⟩⟨x|`, so the `∞` slot `√(p_{x,∞})·|x⟩` (paired with the
zero weight-cap vector) is needed to recover `R = Σ_x p_x|x⟩⟨x|` exactly. -/
def weightCapDiscardCoefficient
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) : ℝ :=
  blockEigenvalue ρ n_copies xs x
    - ∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z

omit [NeZero n] in
/-- The discard coefficient is nonnegative: the finite capped split mass never
exceeds the eigenvalue (`sum_splitCoefficient_le_blockEigenvalue`). -/
theorem weightCapDiscardCoefficient_nonneg
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    0 ≤ weightCapDiscardCoefficient ρ n_copies W xs x := by
  unfold weightCapDiscardCoefficient
  rw [sub_nonneg]
  exact sum_splitCoefficient_le_blockEigenvalue ρ n_copies W xs x

omit [NeZero n] in
/-- The extended split coefficients (finite labels plus the `∞` discard label)
sum to the full eigenvalue `p_x(xs)`, so the augmented family reproduces the
tensor-power block `Σ_x p_x|x⟩⟨x|` exactly. -/
theorem sum_splitCoefficient_add_discardCoefficient_eq_blockEigenvalue
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    (∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z)
        + weightCapDiscardCoefficient ρ n_copies W xs x
      = blockEigenvalue ρ n_copies xs x := by
  unfold weightCapDiscardCoefficient
  ring

/-! ## Operator domination (the TRUE Leaf-A content) -/

/-- The sorted reference spectrum is monotone: `q_z = Σ_{z' ≤ z} β_{z'}` with
nonnegative increments `β_z ≥ 0`, read off the cumulative resolution. -/
theorem referenceEigenvalue_monotone_of_cumulativeResolution
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hcum : iidAEPReferenceCumulativeResolution σ n_copies W) :
    Monotone W.referenceEigenvalue := by
  obtain ⟨hbeta_nn, _, _, _, _, _, hq_eq⟩ := hcum
  intro a b hab
  rw [hq_eq a, hq_eq b]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact le_trans hw hab
  · intro i _ _; exact hbeta_nn i

omit [NeZero n] in
/-- The conjugated eigenprojector `B_z |x⟩⟨x| B_z` is positive semidefinite, for a
Hermitian cumulative projector `B_z` (`B_z† = B_z`). -/
theorem blockSpectralProjector_conj_posSemidef
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies))
    (B : Op (n ^ n_copies)) (hB : B† = B) :
    (B * blockSpectralProjector ρ n_copies xs x * B).PosSemidef := by
  have hconj := (blockSpectralProjector_posSemidef ρ n_copies xs x).mul_mul_conjTranspose_same B
  rw [hB] at hconj
  simpa [mul_assoc] using hconj

/-- **Weight-cap operator domination** (main.tex:4646–4665):

  `ρ̄_xs ≼ 2^{-T} · (id_A ⊗ σ_B)^{⊗n}`.

Equivalently `2^{-T} τ − ρ̄_xs ≽ 0`. Renner's argument: with `p_{x,z} ≤ λ β_z`
(`splitCoefficient_le_lambda_betaCoefficient`) and the orthogonal cumulative
projectors `B_z`,

  `Σ_z λ β_z B_z − ρ̄_xs = Σ_z Σ_x (λ β_z − p_{x,z}) B_z |x⟩⟨x| B_z ≽ 0`

because each `B_z |x⟩⟨x| B_z` is PSD and `λ β_z − p_{x,z} ≥ 0`; and
`Σ_z λ β_z B_z B_z = Σ_z λ β_z B_z = λ τ` by the cumulative resolution
`τ = Σ_z β_z B_z` and idempotence of `B_z`. This is the faithful per-block
domination the CQ conditional min-entropy (`isFeasible`, Def 6.2) consumes; it
is **true** for non-commuting `ρ, σ`, unlike the single-projector sandwich. -/
theorem weightCapBlock_opLe_pow_neg_threshold_smul_reference
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) :
    opLe (weightCapBlockOp ρ n_copies W xs)
      (Complex.ofReal (weightCapScale W) •
        (iidAEPTensorReference σ n_copies).toOp) := by
  classical
  obtain ⟨hq_nn, _hincr, _haction, hcum⟩ := href
  have hmono : Monotone W.referenceEigenvalue :=
    referenceEigenvalue_monotone_of_cumulativeResolution σ n_copies W hcum
  -- Renner's weight cap and the per-block spectral resolution.
  have hcap : ∀ x z : Fin (n ^ n_copies),
      splitCoefficient ρ n_copies W xs x z ≤ weightCapScale W * W.betaCoefficient z :=
    fun x z => splitCoefficient_le_lambda_betaCoefficient ρ n_copies σ W hcum xs x z
  have hsplit_nn : ∀ x z : Fin (n ^ n_copies),
      0 ≤ splitCoefficient ρ n_copies W xs x z :=
    fun x z => splitCoefficient_nonneg ρ n_copies W hmono hq_nn xs x z
  have hres : ∑ x : Fin (n ^ n_copies), blockSpectralProjector ρ n_copies xs x = 1 := by
    simpa [blockSpectralProjector] using
      (isHermitian_eigenvectorBasis_rankOneProjectors_increments
        ((iidAEPTensorState ρ n_copies).stateMap
          xs).toPosSemidefOp.toHermitianOp.isHermitian).2.2.2.2
  obtain ⟨hbeta_nn, _hBdef, hBidem, hBherm, _hBnest, htau, _hq_eq⟩ := hcum
  -- The conjugated rank-one operators `B_z |x⟩⟨x| B_z` are PSD.
  set Q : Fin (n ^ n_copies) → Fin (n ^ n_copies) → Op (n ^ n_copies) :=
    fun x z => W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
      W.cumulativeProjector z with hQ
  have hQ_psd : ∀ x z, (Q x z).PosSemidef := by
    intro x z
    simpa [hQ] using
      blockSpectralProjector_conj_posSemidef ρ n_copies xs x (W.cumulativeProjector z) (hBherm z)
  refine opLe_of_posSemidef_sub ?_
  -- `λ τ = Σ_z Σ_x (λ β_z) • Q x z` and `ρ̄ = Σ_x Σ_z p_{x,z} • Q x z`.
  have hτ_expand :
      (Complex.ofReal (weightCapScale W) • (iidAEPTensorReference σ n_copies).toOp)
        = ∑ z : Fin (n ^ n_copies), ∑ x : Fin (n ^ n_copies),
            (Complex.ofReal (weightCapScale W * W.betaCoefficient z)) • Q x z := by
    rw [htau, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have hBz : W.cumulativeProjector z = ∑ x : Fin (n ^ n_copies), Q x z := by
      have : W.cumulativeProjector z * (1 : Op (n ^ n_copies)) * W.cumulativeProjector z
          = W.cumulativeProjector z := by rw [mul_one, hBidem z]
      rw [← hres] at this
      rw [Finset.mul_sum, Finset.sum_mul] at this
      simpa [hQ] using this.symm
    rw [smul_smul, hBz, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Complex.ofReal_mul]
  have hρbar_expand :
      weightCapBlockOp ρ n_copies W xs
        = ∑ z : Fin (n ^ n_copies), ∑ x : Fin (n ^ n_copies),
            (Complex.ofReal (splitCoefficient ρ n_copies W xs x z)) • Q x z := by
    unfold weightCapBlockOp
    rw [Finset.sum_comm]
  rw [hτ_expand, hρbar_expand, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro z _
  rw [← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro x _
  rw [← sub_smul, ← Complex.ofReal_sub]
  refine Matrix.PosSemidef.smul (hQ_psd x z) ?_
  rw [Complex.zero_le_real]
  have := hcap x z; linarith

/-! ## The weight-cap smoothed state as a CQ state

The weight-cap block `ρ̄_xs` is positive semidefinite (a nonnegative combination
of the PSD operators `B_z |x⟩⟨x| B_z`) and sub-normalized: its trace is at most
the trace of the original block `(ρ.stateMap xs)^{⊗}`, because each
`B_z |x⟩⟨x| B_z` has trace `≤ 1` and the split coefficients sum to at most the
block eigenvalue (`sum_splitCoefficient_le_blockEigenvalue`). Aggregating over
classical labels keeps the total weight `≤ 1`. This packages `ρ̄` as a genuine
`CQState` so it can serve as the witness's smoothed state. -/

/-- The weight-cap block is positive semidefinite: a nonnegative combination of
the PSD conjugated eigenprojectors `B_z |x⟩⟨x| B_z`. -/
theorem weightCapBlockOp_posSemidef
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) :
    (weightCapBlockOp ρ n_copies W xs).PosSemidef := by
  classical
  obtain ⟨hq_nn, _hincr, _haction, hcum⟩ := href
  have hmono : Monotone W.referenceEigenvalue :=
    referenceEigenvalue_monotone_of_cumulativeResolution σ n_copies W hcum
  obtain ⟨_, _, _, hBherm, _, _, _⟩ := hcum
  unfold weightCapBlockOp
  apply Matrix.posSemidef_sum
  intro x _
  apply Matrix.posSemidef_sum
  intro z _
  refine Matrix.PosSemidef.smul
    (blockSpectralProjector_conj_posSemidef ρ n_copies xs x (W.cumulativeProjector z)
      (hBherm z)) ?_
  rw [Complex.zero_le_real]
  exact splitCoefficient_nonneg ρ n_copies W hmono hq_nn xs x z

omit [NeZero n] in
/-- Each block eigenprojector `|x⟩⟨x|` has unit trace (a rank-one projector onto
a normalized eigenvector). -/
theorem blockSpectralProjector_trace
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    (blockSpectralProjector ρ n_copies xs x).trace = 1 := by
  set hM :=
    ((iidAEPTensorState ρ n_copies).stateMap
      xs).toPosSemidefOp.toHermitianOp.isHermitian with hMdef
  unfold blockSpectralProjector
  rw [Matrix.trace_vecMulVec]
  have hdot : star ((hM.eigenvectorBasis x).ofLp) ⬝ᵥ ((hM.eigenvectorBasis x).ofLp) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    have h := orthonormal_iff_ite.mp hM.eigenvectorBasis.orthonormal x x
    rwa [if_pos rfl] at h
  rw [dotProduct_comm]
  exact hdot

omit [NeZero n] in
/-- The conditional block operator's real trace is the sum of its eigenvalues
`Σ_x p_x(xs)` (`blockEigenvalue`). -/
theorem blockEigenvalue_sum_eq_block_trace
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) :
    ∑ x : Fin (n ^ n_copies), blockEigenvalue ρ n_copies xs x
      = ((iidAEPTensorState ρ n_copies).stateMap xs).trace := by
  have h :=
    ((iidAEPTensorState ρ n_copies).stateMap
      xs).toPosSemidefOp.toHermitianOp.isHermitian.trace_eq_sum_eigenvalues
  unfold SubDensityOp.trace blockEigenvalue
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact (Complex.ofReal_re _).symm

/-- **Weight-cap sub-normalization (per block).** The weight-cap block trace does
not exceed the original block trace:

  `tr(ρ̄_xs).re ≤ tr((ρ.stateMap xs)^{⊗}).re`.

Each `B_z |x⟩⟨x| B_z` has trace `≤ tr(|x⟩⟨x|) = 1` (Hermitian-projector sandwich)
and the split coefficients sum to at most the block eigenvalue
(`sum_splitCoefficient_le_blockEigenvalue`), whose total is the block trace. The
gap is exactly the discarded mass (main.tex:4665–4747). -/
theorem weightCapBlockOp_trace_re_le
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) :
    (weightCapBlockOp ρ n_copies W xs).trace.re ≤
      ((iidAEPTensorState ρ n_copies).stateMap xs).trace := by
  classical
  obtain ⟨hq_nn, _hincr, _haction, hcum⟩ := href
  have hmono : Monotone W.referenceEigenvalue :=
    referenceEigenvalue_monotone_of_cumulativeResolution σ n_copies W hcum
  obtain ⟨_, _, hBidem, hBherm, _, _, _⟩ := hcum
  have hsplit_nn : ∀ x z : Fin (n ^ n_copies), 0 ≤ splitCoefficient ρ n_copies W xs x z :=
    fun x z => splitCoefficient_nonneg ρ n_copies W hmono hq_nn xs x z
  -- Real trace of the weight-cap block as a double sum of nonnegative terms.
  have htrace_eq :
      (weightCapBlockOp ρ n_copies W xs).trace.re
        = ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
            splitCoefficient ρ n_copies W xs x z *
              (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
                W.cumulativeProjector z).trace.re := by
    unfold weightCapBlockOp
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [htrace_eq]
  -- `tr(B_z |x⟩⟨x| B_z).re ≤ tr(|x⟩⟨x|).re = 1`, so each inner sum `≤ Σ_z p_{x,z} ≤ p_x`.
  calc
    ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
        splitCoefficient ρ n_copies W xs x z *
          (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
            W.cumulativeProjector z).trace.re
      ≤ ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
          splitCoefficient ρ n_copies W xs x z * 1 := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ => ?_))
        refine mul_le_mul_of_nonneg_left ?_ (hsplit_nn x z)
        have hsand :=
          Quantum.TensorProducts.trace_re_projector_sandwich_le
            (P := W.cumulativeProjector z) (M := blockSpectralProjector ρ n_copies xs x)
            (hBidem z) (hBherm z) (blockSpectralProjector_posSemidef ρ n_copies xs x)
        have htr1 : (blockSpectralProjector ρ n_copies xs x).trace.re = 1 := by
          rw [blockSpectralProjector_trace]; simp
        rw [htr1] at hsand
        exact hsand
    _ ≤ ∑ x : Fin (n ^ n_copies), blockEigenvalue ρ n_copies xs x := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        simp only [mul_one]
        exact sum_splitCoefficient_le_blockEigenvalue ρ n_copies W xs x
    _ = ((iidAEPTensorState ρ n_copies).stateMap xs).trace :=
        blockEigenvalue_sum_eq_block_trace ρ n_copies xs

/-- The weight-cap conditional block `ρ̄_xs` packaged as a sub-density operator:
positive semidefinite (`weightCapBlockOp_posSemidef`) and sub-normalized
(`weightCapBlockOp_trace_re_le`, dominating trace at most the original block's,
which is itself `≤ 1`). -/
def weightCapBlockSubDensityOp
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) : SubDensityOp (n ^ n_copies) where
  toOp := weightCapBlockOp ρ n_copies W xs
  isHermitian := (weightCapBlockOp_posSemidef ρ n_copies σ W href xs).1
  pos_semidef := fun v =>
    Quantum.Operators.posSemidef_re_quadraticForm_nonneg
      (weightCapBlockOp_posSemidef ρ n_copies σ W href xs) v
  trace_le_one :=
    le_trans (weightCapBlockOp_trace_re_le ρ n_copies σ W href xs)
      ((iidAEPTensorState ρ n_copies).stateMap xs).trace_le_one

/-- **Renner's weight-cap smoothed state** as a CQ state (main.tex:4636–4642):
its `xs`-block is the weight-cap block `ρ̄_xs`. The total weight is at most the
total weight of the original tensor-power CQ state (`≤ 1`) because each block
trace is dominated by `weightCapBlockOp_trace_re_le`. This is the faithful
smoothed state — `ρ̄`, not the single-projector sandwich `Π ρ^{⊗} Π`. -/
def weightCapCQState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    CQState (Fin n_copies → X) (n ^ n_copies) where
  stateMap xs := weightCapBlockSubDensityOp ρ n_copies σ W href xs
  weight_le_one := by
    refine le_trans (Finset.sum_le_sum (fun xs _ => ?_))
      (iidAEPTensorState ρ n_copies).weight_le_one
    exact weightCapBlockOp_trace_re_le ρ n_copies σ W href xs

@[simp]
lemma weightCapCQState_stateMap_toOp
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) :
    ((weightCapCQState ρ n_copies σ W href).stateMap xs).toOp =
      weightCapBlockOp ρ n_copies W xs := rfl

/-! ## Installing the weight-cap state as the witness's smoothed state -/

/-- Overwrite a reference-stage witness's smoothed state with Renner's weight-cap
state `ρ̄` (`weightCapCQState`), preserving the truncation projector and every
reference, cumulative, cut, and `r_t` field. The reference data is unchanged, so
the reference spectral decomposition `href` of `W` is reused verbatim to build
the weight-cap state. -/
def iidAEPWitnessWithWeightCapState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    IIDAEPSpectralWitness X n n_copies where
  projectorData :=
    { truncationProjector := W.truncationProjector
      smoothedState := weightCapCQState ρ n_copies σ W href }
  referenceSpectrum := W.referenceSpectrum
  cumulativeResolution := W.cumulativeResolution
  spectralCut := W.spectralCut
  rtData := W.rtData

@[simp]
lemma iidAEPWitnessWithWeightCapState_smoothedState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    (iidAEPWitnessWithWeightCapState ρ n_copies σ W href).smoothedState
      = weightCapCQState ρ n_copies σ W href := rfl

@[simp]
lemma iidAEPWitnessWithWeightCapState_referenceEigenvalue
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    (iidAEPWitnessWithWeightCapState ρ n_copies σ W href).referenceEigenvalue
      = W.referenceEigenvalue := rfl

@[simp]
lemma iidAEPWitnessWithWeightCapState_entropyThreshold
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    (iidAEPWitnessWithWeightCapState ρ n_copies σ W href).entropyThreshold
      = W.entropyThreshold := rfl

/-- The witness whose smoothed state is the weight-cap state inherits `W`'s
reference spectral decomposition (all reference, cumulative, and increment fields
are preserved). -/
lemma iidAEPWitnessWithWeightCapState_reference
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    iidAEPReferenceSpectralDecomposition σ n_copies
      (iidAEPWitnessWithWeightCapState ρ n_copies σ W href) := href

/-- **The faithful Leaf-A block domination, proved.** With the weight-cap state
installed as the smoothed state, every conditional block satisfies Renner's
operator domination `ρ̄_xs ≼ 2^{-T} (id⊗σ)^{⊗n}`. This is exactly
`iidAEPSpectralCutBlockDomination`, discharged by the proved weight-cap
domination `weightCapBlock_opLe_pow_neg_threshold_smul_reference`. -/
theorem iidAEPWitnessWithWeightCapState_blockDomination
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    iidAEPSpectralCutBlockDomination σ n_copies
      (iidAEPWitnessWithWeightCapState ρ n_copies σ W href) := by
  intro xs
  have hdom := weightCapBlock_opLe_pow_neg_threshold_smul_reference ρ n_copies σ W href xs
  -- The smoothed block is the weight-cap block; the scale matches `2^{-T}`.
  have hscale :
      iidAEPSpectralCutDominationScale
          (iidAEPWitnessWithWeightCapState ρ n_copies σ W href)
        = weightCapScale W := by
    unfold iidAEPSpectralCutDominationScale weightCapScale
    rfl
  rw [hscale,
    iidAEPWitnessWithWeightCapState_smoothedState,
    weightCapCQState_stateMap_toOp]
  exact hdom

/-! ## Selecting Renner's spectral cut

Before the weight-cap state can be installed at scale `2^{-T}`, the witness must
carry Renner's retained crossing cut: the entropy threshold `T`, the crossing
index `z* = iidAEPCrossingCutIndex` (the least sorted index reaching the
scale, main.tex:4600–4604), and the truncation projector `B_{z*}`. -/

/-- Install Renner's retained crossing cut at threshold `T`: set the entropy
threshold to `T`, the cut index to the crossing index `z*` of the (sorted)
reference spectrum at scale `2^{-T}`, and the truncation projector to the
cumulative crossing projector `B_{z*}`. Reference, cumulative, and `r_t` fields
and the smoothed-state field are preserved. -/
def iidAEPWitnessWithCrossingCut
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    IIDAEPSpectralWitness X n n_copies where
  projectorData :=
    { truncationProjector :=
        W.cumulativeProjector (iidAEPCrossingCutIndex W.referenceEigenvalue T)
      smoothedState := W.smoothedState }
  referenceSpectrum := W.referenceSpectrum
  cumulativeResolution := W.cumulativeResolution
  spectralCut :=
    { cutIndex := iidAEPCrossingCutIndex W.referenceEigenvalue T
      entropyThreshold := T }
  rtData := W.rtData

omit [NeZero n] in
@[simp]
lemma iidAEPWitnessWithCrossingCut_referenceEigenvalue
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    (iidAEPWitnessWithCrossingCut n_copies W T).referenceEigenvalue
      = W.referenceEigenvalue := rfl

omit [NeZero n] in
@[simp]
lemma iidAEPWitnessWithCrossingCut_entropyThreshold
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    (iidAEPWitnessWithCrossingCut n_copies W T).entropyThreshold = T := rfl

omit [NeZero n] in
@[simp]
lemma iidAEPWitnessWithCrossingCut_cutIndex
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    (iidAEPWitnessWithCrossingCut n_copies W T).cutIndex
      = iidAEPCrossingCutIndex W.referenceEigenvalue T := rfl

omit [NeZero n] in
@[simp]
lemma iidAEPWitnessWithCrossingCut_truncationProjector
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    (iidAEPWitnessWithCrossingCut n_copies W T).truncationProjector
      = W.cumulativeProjector (iidAEPCrossingCutIndex W.referenceEigenvalue T) := rfl

omit [NeZero n] in
@[simp]
lemma iidAEPWitnessWithCrossingCut_cumulativeProjector
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    (iidAEPWitnessWithCrossingCut n_copies W T).cumulativeProjector
      = W.cumulativeProjector := rfl

/-- The crossing-cut witness preserves the reference spectral decomposition
(reference, increment, action, and cumulative fields are unchanged). -/
lemma iidAEPWitnessWithCrossingCut_reference
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    iidAEPReferenceSpectralDecomposition σ n_copies
      (iidAEPWitnessWithCrossingCut n_copies W T) := href

omit [NeZero n] in
/-- **Renner's retained crossing cut holds** (main.tex:4600–4604): the truncation
projector is `B_{z*}` and every strictly-below eigen-block lies below the
separation scale `2^{-T}`. This is `iidAEPNonnegativeThresholdCrossing` for
the crossing-cut witness, proved from `iidAEPCrossingCutIndex_below_lt`. -/
theorem iidAEPWitnessWithCrossingCut_crossing
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (T : ℝ) :
    iidAEPNonnegativeThresholdCrossing
      (iidAEPWitnessWithCrossingCut n_copies W T) := by
  refine ⟨rfl, ?_⟩
  intro z hz
  rw [iidAEPWitnessWithCrossingCut_referenceEigenvalue,
    iidAEPWitnessWithCrossingCut_entropyThreshold]
  rw [iidAEPWitnessWithCrossingCut_cutIndex] at hz
  exact iidAEPCrossingCutIndex_below_lt W.referenceEigenvalue T z hz

/-! ## Renner's full smoothed cut witness

Compose the crossing cut and the weight-cap state into a single witness that
carries, simultaneously, Renner's retained crossing cut at threshold `T` and the
weight-cap smoothed state `ρ̄` at scale `2^{-T}`. -/

/-- Renner's full smoothed witness at threshold `T`: first install the retained
crossing cut (threshold `T`, index `z*`, projector `B_{z*}`), then install the
weight-cap state `ρ̄` at the resulting scale `2^{-T}`. -/
def iidAEPRennerCutWitness
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    IIDAEPSpectralWitness X n n_copies :=
  iidAEPWitnessWithWeightCapState ρ n_copies σ
    (iidAEPWitnessWithCrossingCut n_copies W T)
    (iidAEPWitnessWithCrossingCut_reference n_copies σ W T href)

/-- The Renner cut witness preserves the reference spectral decomposition. -/
lemma iidAEPRennerCutWitness_reference
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    iidAEPReferenceSpectralDecomposition σ n_copies
      (iidAEPRennerCutWitness ρ n_copies σ W href T) :=
  iidAEPWitnessWithCrossingCut_reference n_copies σ W T href

@[simp]
lemma iidAEPRennerCutWitness_entropyThreshold
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    (iidAEPRennerCutWitness ρ n_copies σ W href T).entropyThreshold = T := rfl

/-- **Renner's retained crossing cut holds for the full cut witness.** The
weight-cap update preserves the spectral cut and truncation projector, so the
crossing condition of the crossing-cut witness transfers verbatim. -/
theorem iidAEPRennerCutWitness_crossing
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    iidAEPNonnegativeThresholdCrossing
      (iidAEPRennerCutWitness ρ n_copies σ W href T) :=
  iidAEPWitnessWithCrossingCut_crossing n_copies W T

/-- **The faithful Leaf-A block domination for the full cut witness.** Every
conditional block of `ρ̄` is dominated by `2^{-T} (id⊗σ)^{⊗n}`
(`iidAEPSpectralCutBlockDomination`). -/
theorem iidAEPRennerCutWitness_blockDomination
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    iidAEPSpectralCutBlockDomination σ n_copies
      (iidAEPRennerCutWitness ρ n_copies σ W href T) :=
  iidAEPWitnessWithWeightCapState_blockDomination ρ n_copies σ
    (iidAEPWitnessWithCrossingCut n_copies W T)
    (iidAEPWitnessWithCrossingCut_reference n_copies σ W T href)

/-! ## Pinning the witness smoothed state to the weight-cap state

The `smoothedState` field of `IIDAEPSpectralWitness` is free witness data.
The block-domination predicate `iidAEPSpectralCutBlockDomination` is an
*upper* operator bound `ρ̄_xs ≼ 2^{-T}τ`, which `smoothedState = 0` satisfies
vacuously. To keep the downstream trace-defect and purified-distance bounds true
as standalone statements, the smoothed state must be *identified* with Renner's
weight-cap blocks `ρ̄_xs = weightCapBlockOp`, not merely dominated by the
reference. The following predicate is that identification. -/

/-- **The smoothed state is Renner's weight-cap state.** Every conditional block
operator of W.smoothedState equals the explicit weight-cap block
`ρ̄_xs = Σ_{x,z} p_{x,z}(xs) · B_z|x⟩⟨x|B_z` (`weightCapBlockOp`,
main.tex:4636–4642). This is the load-bearing pin: with it,
`iidAEPTraceDefect ρ n_copies W` is the genuine discarded mass
`Σ_xs[tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]`, so the discarded-mass Chernoff bound and the
trace-distance purified-distance route are real Renner obligations. Without it,
adversarial values of the free `smoothedState` field (e.g. `0`, or a pure state
orthogonal to `ρ^{⊗n}`) falsify both bounds. -/
def iidAEPIsWeightCapSmoothedState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  ∀ xs : Fin n_copies → X,
    (W.smoothedState.stateMap xs).toOp = weightCapBlockOp ρ n_copies W xs

/-- The witness whose smoothed state is the weight-cap state satisfies the
weight-cap pin: each smoothed block is the corresponding weight-cap block by
construction. -/
theorem iidAEPWitnessWithWeightCapState_isWeightCapSmoothedState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    iidAEPIsWeightCapSmoothedState ρ n_copies
      (iidAEPWitnessWithWeightCapState ρ n_copies σ W href) :=
  fun _ => rfl

/-- **The weight-cap pin holds for the full Renner cut witness.** The smoothed
state installed by `iidAEPRennerCutWitness` is the weight-cap state, so each
of its conditional blocks equals the weight-cap block `weightCapBlockOp`. This
discharges `iidAEPIsWeightCapSmoothedState` by construction (`rfl`). -/
theorem iidAEPRennerCutWitness_isWeightCapSmoothedState
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (σ : DensityOp n)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPReferenceSpectralDecomposition σ n_copies W) (T : ℝ) :
    iidAEPIsWeightCapSmoothedState ρ n_copies
      (iidAEPRennerCutWitness ρ n_copies σ W href T) :=
  fun _ => rfl

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
