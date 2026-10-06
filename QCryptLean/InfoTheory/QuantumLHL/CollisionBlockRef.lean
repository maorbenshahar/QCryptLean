import QCryptLean.InfoTheory.QuantumLHL.CollisionAnnounceCharge
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.BlockRefRegularization
import QCryptLean.InfoTheory.QuantumLHL.CollisionRegExt

/-!
# The collision-route announce charge at a reference classical on the announced register

`InfoTheory/SmoothMinEntropy/ClassicalAnnounceKernelBlockRef.lean` shows that a classical
announcement is **free** on the smooth-min-entropy route when the reference is classical on the
announced register, `Σ_p |p⟩⟨p| ⊗ ν_p` — Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:2917`,
`\label{lem:Hminclasscondr}`.  This file is the **collision-route** counterpart: the same
zero-charge identity for `collisionQuantity`, plus the γ-regularisation the collision consumer
needs because that reference is singular.

## The two facts

* **The charge is exactly `0`** — `collisionQuantity_tensorLeftKernel_blockDiagRef_eq`, an
  equality.  Contrast the flat reference `(1/d_C)·1 ⊗ σ`, where a *deterministic* announcement pays
  the full `d_C` and the bound `collisionQuantity_tensorLeftKernel_le` is tight.  For an
  announced PE register of dimension `4^m` that
  is `2m` bits, which no key rate funds; the block-diagonal reference is what makes the collision
  route viable at all.

  The proof rests on `blockDiagRefOp_rpow`: real powers of a block-diagonal reference act
  blockwise, **including negative powers at singular blocks**, with Lean's `Real.rpow`
  pseudo-power convention `0 ^ y = 0`.

* **The regularisation costs exactly `(1−γ)⁻¹`** — `weightedFrobeniusSq_mix_smul_one_le`.  The
  reference has to be positive definite for the collision Hölder step
  `traceNorm_le_sqrt_trace_mul_weightedFrobenius`, and a block-diagonal announced reference whose
  weights saturate the sub-normalisation is dominated by no positive definite sub-density operator
  at all.  The
  strict rescale `blockDiagRefRegularized`, `ν^γ_p = (1−γ)·ν_p + (γ/d_C)·maxMixed`, is positive
  definite (`blockDiagRefRegularized_posDef`) and — being a **mixture, not an inflation** —
  weight-exact (`sum_blockFamilyRegularized_trace_eq`), so `Tr σ_γ = 1` when `Tr σ = 1`.  Its whole
  cost on this route is the factor `(1−γ)⁻¹` inside the collision square root, i.e.
  `log₂(1/(1−γ))` bits of key length.

## The load-bearing hypothesis

`weightedFrobeniusSq_mix_smul_one_le` needs `A = σ^{1/4} B σ^{1/4}` — the checkable form of "the
state lies in the support of the reference".  **It is not decoration:** without it the statement is
false, and badly so — over 400 random strictly-singular instances the maximum of `lhs − rhs` is
`−3.2e−03` with the factorisation and `+7.4e+03` with a generic `A`.
Every consumer must supply a genuine factorisation, and only the *paired-announce* block family
does: a plain compression `E_p τ E_p` puts the state **outside** the block's support, where the
weighted square is a pseudo-inverse under-estimate and the Hölder step simply fails.

## Method

Everything is proved on the **indicator spectral resolution** `{Q_l}` of the reference
(`CfcSpectral.specProj`), extended over any `Finset ℝ` containing the spectrum.  On that resolution
the operators involved commute and the continuous functional calculus is coefficientwise, so the
sandwiched-norm inequality `‖X M Y‖ ≤ ‖X‖_op ‖M‖ ‖Y‖_op` (Bhatia, *Matrix Analysis*, Springer GTM
169, §IV.2) reduces to two applications of the trace-pairing positivity `Tr[Zᴴ M Z] ≥ 0` for
`M ⪰ 0` (Renner 2005, `main.tex:10368`, `\label{lem:trprod}`) and needs no
unitarily-invariant-norm theory.

## Main statements

* `blockDiagRefOp_rpow` — real powers act blockwise.
* `weightedFrobeniusSq_blockDiagRefOp_stdProj_tensor` — the per-block identity (charge `0`).
* `collisionQuantity_tensorLeftKernel_blockDiagRef_eq` — the announce charge, an equality.
* `weightedFrobeniusSq_mix_smul_one_le` — the γ-comparison, at a possibly singular reference.
* `weightedFrobeniusSq_blockFamilyRegularized_le`,
  `collisionQuantity_tensorLeftKernel_blockDiagRefRegularized_le`,
  `blockDiagRefRegularized_trace_eq_one` — the same at the assembled regularised reference.
* `seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized` — the consumer-shaped packaging.

## A note on the import

`seedKeyExtractor_traceDistanceGen_le_collisionRoot` is register-generic and lives in the
InfoTheory.QuantumLHL namespace, but its module is filed under the BB84 tree
(`…/BellInnerBudgetCore/CollisionRegExt.lean`).  It imports nothing from `Protocols`, so the
dependency below is acyclic; the file is simply misplaced.

References: Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:2917` `\label{lem:Hminclasscondr}`,
`:6889` `\label{rem:Htworewr}` (the collision quantity), `:7080` `\label{thm:pa}` (the
privacy-amplification theorem that consumes it), `:10368` `\label{lem:trprod}`; Nahar, Tupkary,
Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) `main.tex:452` (announced registers inside the
conditioning register from the start); Bhatia, *Matrix Analysis*, Springer GTM 169, §IV.2.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy CfcSpectral

/-! ## Spectral resolutions over a finset containing the spectrum -/

/-- The indicator spectral projector at a value **off** the spectrum is `0`: the indicator of
`{l}` vanishes identically on `spectrum ℝ c`, and `cfc` only sees the spectrum. -/
private lemma specProj_eq_zero_of_notMem {d : ℕ} (c : Op d) {l : ℝ}
    (hl : l ∉ spectrum ℝ c) : specProj c l = 0 := by
  have h : cfc (Set.indicator ({l} : Set ℝ) (fun _ => (1:ℝ))) c = cfc (fun _ : ℝ => (0:ℝ)) c := by
    refine cfc_congr ?_
    intro x hx
    have hxl : x ≠ l := by rintro rfl; exact hl hx
    simp [Set.indicator, hxl]
  rw [specProj, h, cfc_const_zero]

/-- Completeness of the indicator spectral projectors over **any** finset containing the
spectrum: the extra labels carry zero projectors. -/
private lemma sum_specProj_superset {d : ℕ} (c : Op d) (hc : IsSelfAdjoint c)
    {T : Finset ℝ} (hT : specFinset c ⊆ T) :
    ∑ l ∈ T, specProj c l = (1 : Op d) := by
  rw [← sum_specProj c hc]
  exact (Finset.sum_subset hT fun l _ hl =>
    specProj_eq_zero_of_notMem c fun h => hl (mem_specFinset.mpr h)).symm

/-- Spectral decomposition over any finset containing the spectrum. -/
private lemma eq_sum_specProj_superset {d : ℕ} (c : Op d) (hc : IsSelfAdjoint c)
    {T : Finset ℝ} (hT : specFinset c ⊆ T) :
    c = ∑ l ∈ T, (l : ℂ) • specProj c l := by
  conv_lhs => rw [eq_sum_specProj c hc]
  refine Finset.sum_subset hT fun l _ hl => ?_
  have hz : specProj c l = 0 := specProj_eq_zero_of_notMem c fun h => hl (mem_specFinset.mpr h)
  rw [hz, smul_zero]

/-- The continuous-functional-calculus real power over any finset containing the spectrum:
`c ^ y = Σ_{l ∈ T} l^y • Q_l`. -/
private lemma rpow_eq_sum_specProj_superset {d : ℕ} (c : Op d) (hc : (0 : Op d) ≤ c)
    {T : Finset ℝ} (hT : specFinset c ⊆ T) (y : ℝ) :
    c ^ y = ∑ l ∈ T, ((l ^ y : ℝ) : ℂ) • specProj c l := by
  have hsa : IsSelfAdjoint c := (Matrix.nonneg_iff_posSemidef.mp hc).isHermitian
  have h := rpow_of_orthogonalResolution (n := Fin d) (ι := {x : ℝ // x ∈ T}) c
    (fun z => (z : ℝ)) (fun z => specProj c (z : ℝ)) hc
    (fun z => specProj_isHermitian c _)
    (fun z => specProj_idem c _)
    (fun z w hzw => specProj_orthogonal c (fun h => hzw (Subtype.ext h)))
    (by rw [Finset.sum_coe_sort T (fun l => specProj c l)]; exact sum_specProj_superset c hsa hT)
    (by rw [Finset.sum_coe_sort T (fun l => (l : ℂ) • specProj c l)]
        exact eq_sum_specProj_superset c hsa hT) y
  rw [h, Finset.sum_coe_sort T (fun l => ((l ^ y : ℝ) : ℂ) • specProj c l)]

/-- The real power over an arbitrary orthogonal resolution carried by a `Finset ℝ` of labels. -/
private lemma rpow_of_finsetResolution {d : ℕ} (a : Op d) (ha0 : (0 : Op d) ≤ a)
    (T : Finset ℝ) (Q : ℝ → Op d)
    (hHerm : ∀ l, (Q l).IsHermitian) (hidem : ∀ l, Q l * Q l = Q l)
    (horth : ∀ l l', l ≠ l' → Q l * Q l' = 0) (hsum : ∑ l ∈ T, Q l = (1 : Op d))
    (lam : ℝ → ℝ) (ha : a = ∑ l ∈ T, ((lam l : ℝ) : ℂ) • Q l) (y : ℝ) :
    a ^ y = ∑ l ∈ T, ((lam l ^ y : ℝ) : ℂ) • Q l := by
  have h := rpow_of_orthogonalResolution (n := Fin d) (ι := {x : ℝ // x ∈ T}) a
    (fun z => lam (z : ℝ)) (fun z => Q (z : ℝ)) ha0
    (fun z => hHerm _) (fun z => hidem _)
    (fun z w hzw => horth _ _ (fun h => hzw (Subtype.ext h)))
    (by rw [Finset.sum_coe_sort T (fun l => Q l)]; exact hsum)
    (by rw [Finset.sum_coe_sort T (fun l => ((lam l : ℝ) : ℂ) • Q l)]; exact ha) y
  rw [h, Finset.sum_coe_sort T (fun l => ((lam l ^ y : ℝ) : ℂ) • Q l)]

/-! ## The block-diagonal reference: real powers act blockwise -/

/-- The computational-basis projectors are idempotent. -/
private lemma stdKetProj_idem {dC : ℕ} (q : Fin dC) :
    (stdKet dC q * (stdKet dC q).dag) * (stdKet dC q * (stdKet dC q).dag)
      = stdKet dC q * (stdKet dC q).dag := by
  ext i j
  simp [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, Finset.sum_ite_eq]

/-- The computational-basis projectors at distinct labels are orthogonal. -/
private lemma stdKetProj_orthogonal {dC : ℕ} {q q' : Fin dC} (h : q ≠ q') :
    (stdKet dC q * (stdKet dC q).dag) * (stdKet dC q' * (stdKet dC q').dag) = 0 := by
  ext i j
  simp [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, h]

/-- **The real power of a block-diagonal announced reference acts blockwise.**

`(Σ_p |p⟩⟨p| ⊗ ν_p) ^ y = Σ_p |p⟩⟨p| ⊗ (ν_p ^ y)` for every real exponent `y`, including the
negative exponents the σ-weighted Hilbert–Schmidt square uses (with Lean's `Real.rpow`
pseudo-power convention `0 ^ y = 0` for `y ≠ 0`, so singular blocks are handled).

The projectors `|p⟩⟨p| ⊗ 1_E` are mutually orthogonal and resolve the identity
(`sum_stdKetProj_tensor_one_eq_one`), so refining each of them by the indicator spectral
projectors of its own block gives a joint orthogonal resolution of the assembled reference on
which the continuous functional calculus acts coefficientwise
(`CfcSpectral.rpow_of_orthogonalResolution`). -/
theorem blockDiagRefOp_rpow {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) (y : ℝ) :
    (blockDiagRefOp ν) ^ y
      = ∑ q : Fin dC, Op.tensor (stdKet dC q * (stdKet dC q).dag) ((ν q).toOp ^ y) := by
  classical
  set T : Finset ℝ := Finset.univ.biUnion fun q : Fin dC => specFinset (ν q).toOp with hT
  have hsub : ∀ q : Fin dC, specFinset (ν q).toOp ⊆ T := fun q =>
    Finset.subset_biUnion_of_mem (fun q : Fin dC => specFinset (ν q).toOp) (Finset.mem_univ q)
  have hνnn : ∀ q : Fin dC, (0 : Op dE) ≤ (ν q).toOp := fun q =>
    Matrix.nonneg_iff_posSemidef.mpr (posSemidefOp_implies_mathlib (ν q).toPosSemidefOp)
  have hνsa : ∀ q : Fin dC, IsSelfAdjoint (ν q).toOp := fun q =>
    (Matrix.nonneg_iff_posSemidef.mp (hνnn q)).isHermitian
  set P : Fin dC × {x : ℝ // x ∈ T} → Op (dC * dE) := fun z =>
    Op.tensor (stdKet dC z.1 * (stdKet dC z.1).dag) (specProj (ν z.1).toOp (z.2 : ℝ)) with hP
  -- the refined family is an orthogonal resolution of the identity on `C ⊗ E`
  have hHerm : ∀ z, (P z).IsHermitian := by
    intro z
    change (Op.tensor _ _)ᴴ = _
    rw [Op.tensor_conjTranspose, ketbra_hermitian, (specProj_isHermitian (ν z.1).toOp _).eq]
  have hidem : ∀ z, P z * P z = P z := by
    intro z
    rw [hP]
    simp only
    rw [Op.tensor_mul, stdKetProj_idem, specProj_idem]
  have horth : ∀ z w, z ≠ w → P z * P w = 0 := by
    intro z w hzw
    rw [hP]
    simp only
    rw [Op.tensor_mul]
    by_cases hq : z.1 = w.1
    · have hl : (z.2 : ℝ) ≠ (w.2 : ℝ) := by
        intro h
        exact hzw (Prod.ext hq (Subtype.ext h))
      rw [hq, specProj_orthogonal _ hl]
      simp [Op.tensor]
    · rw [stdKetProj_orthogonal hq]
      simp [Op.tensor]
  have hsum : ∑ z, P z = (1 : Op (dC * dE)) := by
    rw [hP, Fintype.sum_prod_type]
    simp only
    rw [← sum_stdKetProj_tensor_one_eq_one (dC := dC) (dE := dE)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_coe_sort T (fun l => Op.tensor (stdKet dC q * (stdKet dC q).dag)
      (specProj (ν q).toOp l)),
      (Quantum.TensorProducts.Op.tensor_finsetSum_right
        (stdKet dC q * (stdKet dC q).dag) T (fun l => specProj (ν q).toOp l)).symm,
      sum_specProj_superset _ (hνsa q) (hsub q)]
  -- the coefficientwise identities, at exponent `1` and at exponent `y`
  have hA : blockDiagRefOp ν = ∑ z, ((z.2 : ℝ) : ℂ) • P z := by
    rw [hP, Fintype.sum_prod_type, blockDiagRefOp]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only
    rw [Finset.sum_coe_sort T (fun l => ((l : ℝ) : ℂ) •
      Op.tensor (stdKet dC q * (stdKet dC q).dag) (specProj (ν q).toOp l))]
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ T) =>
      (Op.tensor_smul_right ((l : ℝ) : ℂ) (stdKet dC q * (stdKet dC q).dag)
        (specProj (ν q).toOp l)).symm)]
    rw [(Quantum.TensorProducts.Op.tensor_finsetSum_right
      (stdKet dC q * (stdKet dC q).dag) T
      (fun l => ((l : ℝ) : ℂ) • specProj (ν q).toOp l)).symm,
      ← eq_sum_specProj_superset _ (hνsa q) (hsub q)]
  have hnn : (0 : Op (dC * dE)) ≤ blockDiagRefOp ν :=
    Matrix.nonneg_iff_posSemidef.mpr (blockDiagRefOp_posSemidef ν)
  rw [rpow_of_orthogonalResolution (blockDiagRefOp ν) (fun z => ((z.2 : ℝ))) P hnn hHerm hidem
    horth hsum hA y, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP]
  simp only
  rw [Finset.sum_coe_sort T (fun l => (((l : ℝ) ^ y : ℝ) : ℂ) •
    Op.tensor (stdKet dC q * (stdKet dC q).dag) (specProj (ν q).toOp l))]
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ T) =>
    (Op.tensor_smul_right (((l : ℝ) ^ y : ℝ) : ℂ) (stdKet dC q * (stdKet dC q).dag)
      (specProj (ν q).toOp l)).symm)]
  rw [(Quantum.TensorProducts.Op.tensor_finsetSum_right
    (stdKet dC q * (stdKet dC q).dag) T
    (fun l => (((l : ℝ) ^ y : ℝ) : ℂ) • specProj (ν q).toOp l)).symm,
    ← rpow_eq_sum_specProj_superset _ (hνnn q) (hsub q) y]

/-! ## The announcement is charge-free relative to the per-block problem -/

/-- Sandwiching a single-announcement-block operator between blockwise powers of the
block-diagonal reference stays inside that block. -/
private lemma blockDiagRefOp_sandwich {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE)
    (p : Fin dC) (M : Op dE) (y : ℝ) :
    (blockDiagRefOp ν) ^ y * Op.tensor (stdKet dC p * (stdKet dC p).dag) M
        * (blockDiagRefOp ν) ^ y
      = Op.tensor (stdKet dC p * (stdKet dC p).dag)
          ((ν p).toOp ^ y * M * (ν p).toOp ^ y) := by
  classical
  have hleft : (blockDiagRefOp ν) ^ y * Op.tensor (stdKet dC p * (stdKet dC p).dag) M
      = Op.tensor (stdKet dC p * (stdKet dC p).dag) ((ν p).toOp ^ y * M) := by
    rw [blockDiagRefOp_rpow, Finset.sum_mul, Finset.sum_eq_single p]
    · rw [Op.tensor_mul, stdKetProj_idem]
    · intro q _ hq
      rw [Op.tensor_mul, stdKetProj_orthogonal hq]
      simp [Op.tensor]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hleft, blockDiagRefOp_rpow, Finset.mul_sum, Finset.sum_eq_single p]
  · rw [Op.tensor_mul, stdKetProj_idem]
  · intro q _ hq
    rw [Op.tensor_mul, stdKetProj_orthogonal (Ne.symm hq)]
    simp [Op.tensor]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- **The classical announcement costs exactly nothing on the collision route.**

At a reference that is classical on the announced register, `Σ_p |p⟩⟨p| ⊗ ν_p`, the σ-weighted
Hilbert–Schmidt square of an operator living in a single announcement block is *literally* the
weighted square of its `E`-part against that block's own reference:

`weightedFrobeniusSq (Σ_q |q⟩⟨q| ⊗ ν_q) (|p⟩⟨p| ⊗ M) = weightedFrobeniusSq ν_p M`.

This is the collision-route analogue of the min-entropy identity
`InfoTheory.SmoothMinEntropy.isFeasible_tensorLeftKernel_blockDiagRef_iff`: the charge is `0`, not
merely bounded.  Contrast `collisionQuantity_tensorLeftKernel_le`, where the reference has been
flattened to `(1/d_C)·1 ⊗ σ` and a deterministic announcement pays the full `d_C`
(`weightedFrobeniusSq_maxMixed_le_of_opLe`, tight).

No hypothesis on `ν` beyond what the `SubDensityOp` carrier supplies: the blocks may be singular,
which is the case this exists for. -/
theorem weightedFrobeniusSq_blockDiagRefOp_stdProj_tensor {dE dC : ℕ}
    (ν : Fin dC → SubDensityOp dE) (p : Fin dC) (M : Op dE) :
    weightedFrobeniusSq (blockDiagRefOp ν)
        (Op.tensor (stdKet dC p * (stdKet dC p).dag) M)
      = weightedFrobeniusSq (ν p).toOp M := by
  set N : Op dE := (ν p).toOp ^ (-1/4 : ℝ) * M * (ν p).toOp ^ (-1/4 : ℝ) with hN
  rw [weightedFrobeniusSq, weightedFrobeniusSq, blockDiagRefOp_sandwich ν p M (-1/4 : ℝ), ← hN,
    Op.tensor_conjTranspose, ketbra_hermitian, Op.tensor_mul, stdKetProj_idem,
    Quantum.TensorProducts.Op.trace_tensor,
    trace_ketbra_normalized _ (stdKet_braket_self p), one_mul]

/-! ## at the level of the collision quantity -/

/-- **The announce charge at a reference classical on the announced register is exactly `0`.**

Tensoring a deterministic classical announcement `K x = |ann x⟩⟨ann x|` onto the left of every
conditional operator and referencing the announced register to `Σ_p |p⟩⟨p| ⊗ ν_p` collapses the
collision quantity to the per-label sum `Σ_x weightedFrobeniusSq ν_{ann x} ρ_x` — an **equality**.

This is the collision-route analogue of
`InfoTheory.SmoothMinEntropy.minFeasibleLambda_tensorLeftKernel_blockDiagRef_eq`.  The reference
`blockDiagRef ν hν` may be (and in the intended application is) singular; nothing here needs it
positive definite. -/
theorem collisionQuantity_tensorLeftKernel_blockDiagRef_eq
    {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    collisionQuantity (blockDiagRef ν hν).toOp
        (fun x => ((ρ.tensorLeftKernel K).stateMap x).toOp)
      = ∑ x : X, weightedFrobeniusSq (ν (ann x)).toOp ((ρ.stateMap x).toOp) := by
  rw [collisionQuantity]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hstate : ((ρ.tensorLeftKernel K).stateMap x).toOp
      = Op.tensor (K x).toOp (ρ.stateMap x).toOp := rfl
  rw [hstate, hK x, blockDiagRef_toOp,
    weightedFrobeniusSq_blockDiagRefOp_stdProj_tensor ν (ann x) ((ρ.stateMap x).toOp)]

/-! ## The γ-regularisation comparison

The one genuinely new generic inequality.  All operators occurring below are real functions of the
same reference `σ`, evaluated on the **indicator spectral resolution** `{Q_l}` of `σ`; the
`resFun`-lemmas are that commutative calculus. -/

section Resolution

variable {d : ℕ} {T : Finset ℝ} {Q : ℝ → Op d}

/-- The resolution-diagonal operator `Σ_{l ∈ T} f(l)·Q_l`. -/
private def resFun (T : Finset ℝ) (Q : ℝ → Op d) (f : ℝ → ℝ) : Op d :=
  ∑ l ∈ T, ((f l : ℝ) : ℂ) • Q l

private lemma resFun_mul (hidem : ∀ l, Q l * Q l = Q l)
    (horth : ∀ l l', l ≠ l' → Q l * Q l' = 0) (f g : ℝ → ℝ) :
    resFun T Q f * resFun T Q g = resFun T Q (fun l => f l * g l) := by
  classical
  rw [resFun, resFun, resFun, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  refine Finset.sum_eq_single_of_mem l hl ?_ |>.trans ?_
  · intro l' _ hl'
    rw [Matrix.smul_mul, Matrix.mul_smul, horth l l' (Ne.symm hl'), smul_zero, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hidem l, smul_smul, ← Complex.ofReal_mul]

private lemma resFun_conjTranspose (hHerm : ∀ l, (Q l).IsHermitian) (f : ℝ → ℝ) :
    (resFun T Q f)ᴴ = resFun T Q f := by
  rw [resFun, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_smul, (hHerm l).eq, Complex.star_def, Complex.conj_ofReal]

private lemma resFun_sub (f g : ℝ → ℝ) :
    resFun T Q f - resFun T Q g = resFun T Q (fun l => f l - g l) := by
  rw [resFun, resFun, resFun, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul, ← Complex.ofReal_sub]

private lemma resFun_one (hsum : ∑ l ∈ T, Q l = (1 : Op d)) :
    resFun T Q (fun _ => (1 : ℝ)) = (1 : Op d) := by
  rw [resFun, ← hsum]
  exact Finset.sum_congr rfl fun l _ => by rw [Complex.ofReal_one, one_smul]

private lemma resFun_smul_one (hsum : ∑ l ∈ T, Q l = (1 : Op d)) (t : ℝ) :
    ((t : ℝ) : ℂ) • (1 : Op d) = resFun T Q (fun _ => t) := by
  rw [← resFun_one hsum, resFun, resFun, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [smul_smul, Complex.ofReal_one, mul_one]

private lemma resFun_posSemidef (hHerm : ∀ l, (Q l).IsHermitian)
    (hidem : ∀ l, Q l * Q l = Q l) {f : ℝ → ℝ} (hf : ∀ l ∈ T, 0 ≤ f l) :
    (resFun T Q f).PosSemidef := by
  rw [resFun]
  refine Matrix.posSemidef_sum _ fun l hl => ?_
  have hQ : (Q l).PosSemidef := by
    have h : (Q l)ᴴ * Q l = Q l := by rw [(hHerm l).eq, hidem l]
    rw [← h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  exact hQ.smul (Complex.zero_le_real.mpr (hf l hl))

end Resolution

/-- **Trace monotonicity in a bounded positive-semidefinite middle factor.**
If `t·1 − M ⪰ 0` then `Tr[Zᴴ M Z] ≤ t·Tr[Zᴴ Z]` for every `Z`, because
`Zᴴ (t·1 − M) Z ⪰ 0` (Renner 2005 `main.tex:10368`, `\label{lem:trprod}`, in its
congruence form). -/
private lemma trace_conj_le_of_opBound {d : ℕ} (M : Op d) (t : ℝ) (Z : Op d)
    (h : (((t : ℝ) : ℂ) • (1 : Op d) - M).PosSemidef) :
    (Zᴴ * M * Z).trace.re ≤ t * (Zᴴ * Z).trace.re := by
  have hp := h.conjTranspose_mul_mul_same Z
  have hnn : (0 : ℂ) ≤ (Zᴴ * (((t : ℝ) : ℂ) • (1 : Op d) - M) * Z).trace := hp.trace_nonneg
  have heq : Zᴴ * (((t : ℝ) : ℂ) • (1 : Op d) - M) * Z
      = ((t : ℝ) : ℂ) • (Zᴴ * Z) - Zᴴ * M * Z := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [heq] at hnn
  have hre : 0 ≤ t * (Zᴴ * Z).trace.re - (Zᴴ * M * Z).trace.re := by
    have := (Complex.nonneg_iff.mp hnn).1
    rwa [Matrix.trace_sub, Complex.sub_re, trace_real_smul_re] at this
  linarith

/-- **The sandwiched Hilbert–Schmidt bound in the commuting case.**
For Hermitian `C` with `C² ⪯ t·1`, `‖C X C‖_F² ≤ t²·‖X‖_F²`.  Two applications of
`trace_conj_le_of_opBound`; no unitarily-invariant-norm theory is needed because the outer
factors are the same Hermitian `C`. -/
private lemma sandwich_frobenius_le {d : ℕ} (C X : Op d) (t : ℝ) (ht : 0 ≤ t)
    (hCherm : Cᴴ = C)
    (hD : (((t : ℝ) : ℂ) • (1 : Op d) - C * C).PosSemidef) :
    ((C * X * C)ᴴ * (C * X * C)).trace.re ≤ t * t * (Xᴴ * X).trace.re := by
  have hEq1 : (C * X * C)ᴴ * (C * X * C) = (X * C)ᴴ * (C * C) * (X * C) := by
    simp only [Matrix.conjTranspose_mul, hCherm, Matrix.mul_assoc]
  have hEq2 : ((X * C)ᴴ * (X * C)).trace = (C * C * (Xᴴ * X)).trace := by
    rw [Matrix.conjTranspose_mul, hCherm,
      show C * Xᴴ * (X * C) = (C * Xᴴ * X) * C from by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm (C * Xᴴ * X) C,
      show C * (C * Xᴴ * X) = C * C * (Xᴴ * X) from by simp only [Matrix.mul_assoc]]
  have hEq2' : ((Xᴴ)ᴴ * (C * C) * Xᴴ).trace = (C * C * (Xᴴ * X)).trace := by
    rw [Matrix.conjTranspose_conjTranspose,
      show X * (C * C) * Xᴴ = X * (C * C * Xᴴ) from by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm X (C * C * Xᴴ),
      show C * C * Xᴴ * X = C * C * (Xᴴ * X) from by simp only [Matrix.mul_assoc]]
  have hEq3 : ((Xᴴ)ᴴ * Xᴴ).trace = (Xᴴ * X).trace := by
    rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  calc ((C * X * C)ᴴ * (C * X * C)).trace.re
      = ((X * C)ᴴ * (C * C) * (X * C)).trace.re := by rw [hEq1]
    _ ≤ t * ((X * C)ᴴ * (X * C)).trace.re := trace_conj_le_of_opBound (C * C) t (X * C) hD
    _ = t * ((Xᴴ)ᴴ * (C * C) * Xᴴ).trace.re := by rw [hEq2, hEq2']
    _ ≤ t * (t * ((Xᴴ)ᴴ * Xᴴ).trace.re) :=
        mul_le_mul_of_nonneg_left (trace_conj_le_of_opBound (C * C) t Xᴴ hD) ht
    _ = t * t * (Xᴴ * X).trace.re := by rw [hEq3, mul_assoc]

/-- **The γ-regularisation costs at most `(1−γ)⁻¹` in the collision quantity.**

For a positive **semi**definite reference `σ` (possibly singular), any `γ < 1` and any
`c ≥ 0`,

`weightedFrobeniusSq ((1−γ)·σ + c·1) A ≤ (1−γ)⁻¹ · weightedFrobeniusSq σ A`

**provided `A = σ^{1/4} B σ^{1/4}` for some `B`** — the checkable form of "`A` lies in the support
of `σ`".

**`hfac` is load-bearing, not decoration.** Dropping it makes the statement false: at a singular
`σ`, `weightedFrobeniusSq σ A` is a pseudo-power sandwich that ignores the part of `A` outside the
support, while the regularised reference sees all of it, so the right-hand side can be arbitrarily
smaller than the left.
*Proof.*  Everything in sight is a real function of `σ` on its indicator spectral resolution
`{Q_l}`.  Writing `σ_γ = (1−γ)σ + c·1 = Σ_l ((1−γ)l+c)·Q_l`, the sandwich
`σ_γ^{−1/4} A σ_γ^{−1/4}` equals `C X C` with `C = Σ_l k(l)·Q_l`,
`k(l) = ((1−γ)l+c)^{−1/4} l^{1/4}`, and `X = σ^{−1/4} A σ^{−1/4}`.  Since
`(1−γ)l ≤ (1−γ)l + c`, one has `k(l) ≤ (1−γ)^{−1/4} =: u` pointwise, hence `C² ⪯ u²·1`, and two
applications of `Tr[Zᴴ M Z] ≤ u²·Tr[Zᴴ Z]` (`trace_conj_le_of_opBound`) give the factor
`u⁴ = (1−γ)⁻¹`.  This is the sandwiched-norm inequality `‖XMY‖ ≤ ‖X‖_op‖M‖‖Y‖_op` of Bhatia,
*Matrix Analysis* (Springer GTM 169) §IV.2, specialised to the commuting case, where it needs no
unitarily-invariant-norm theory.  The argument uses only `γ < 1`; no lower bound on `γ` is
needed (the consumer `blockFamilyRegularized` has `0 ≤ γ`). -/
theorem weightedFrobeniusSq_mix_smul_one_le {d : ℕ}
    (σ : Op d) (hσ : (0 : Op d) ≤ σ) (A B : Op d)
    (hfac : A = σ ^ (1 / 4 : ℝ) * B * σ ^ (1 / 4 : ℝ))
    (γ c : ℝ) (hγ1 : γ < 1) (hc : 0 ≤ c) :
    weightedFrobeniusSq (((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)) A
      ≤ (1 - γ)⁻¹ * weightedFrobeniusSq σ A := by
  classical
  have hg : (0 : ℝ) < 1 - γ := sub_pos.mpr hγ1
  set T : Finset ℝ := specFinset σ with hTdef
  set Q : ℝ → Op d := specProj σ with hQdef
  have hHerm : ∀ l, (Q l).IsHermitian := fun l => specProj_isHermitian σ l
  have hidem : ∀ l, Q l * Q l = Q l := fun l => specProj_idem σ l
  have horth : ∀ l l', l ≠ l' → Q l * Q l' = 0 := fun l l' h => specProj_orthogonal σ h
  have hsa : IsSelfAdjoint σ := (Matrix.nonneg_iff_posSemidef.mp hσ).isHermitian
  have hsum : ∑ l ∈ T, Q l = (1 : Op d) := sum_specProj σ hsa
  have hlnn : ∀ l ∈ T, 0 ≤ l := fun l hl => spectrum_nonneg_of_nonneg hσ (mem_specFinset.mp hl)
  have hσres : σ = resFun T Q (fun l => l) := eq_sum_specProj σ hsa
  have hcongr : ∀ f g : ℝ → ℝ, (∀ l ∈ T, f l = g l) → resFun T Q f = resFun T Q g := by
    intro f g h
    exact Finset.sum_congr rfl fun l hl => by rw [h l hl]
  -- the regularised reference, on the same resolution
  have hσγres : ((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)
      = resFun T Q (fun l => (1 - γ) * l + c) := by
    conv_lhs => rw [hσres, resFun_smul_one (T := T) (Q := Q) hsum c]
    rw [resFun, resFun, resFun, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, ← add_smul, ← Complex.ofReal_add]
  have hσγnn : (0 : Op d) ≤ ((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d) := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact ((Matrix.nonneg_iff_posSemidef.mp hσ).smul (Complex.zero_le_real.mpr hg.le)).add
      (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc))
  -- the three real powers, coefficientwise
  have hσ14 : σ ^ (1/4 : ℝ) = resFun T Q (fun l => l ^ (1/4 : ℝ)) :=
    rpow_of_finsetResolution σ hσ T Q hHerm hidem horth hsum (fun l => l) hσres (1/4 : ℝ)
  have hσm14 : σ ^ (-1/4 : ℝ) = resFun T Q (fun l => l ^ (-1/4 : ℝ)) :=
    rpow_of_finsetResolution σ hσ T Q hHerm hidem horth hsum (fun l => l) hσres (-1/4 : ℝ)
  have hσγm14 : (((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)) ^ (-1/4 : ℝ)
      = resFun T Q (fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ)) :=
    rpow_of_finsetResolution _ hσγnn T Q hHerm hidem horth hsum
      (fun l => (1 - γ) * l + c) hσγres (-1/4 : ℝ)
  -- the two sandwiched operators
  set pf : ℝ → ℝ := fun l => l ^ (-1/4 : ℝ) * l ^ (1/4 : ℝ) with hpfdef
  set kf : ℝ → ℝ := fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ) * l ^ (1/4 : ℝ) with hkfdef
  set P0 : Op d := resFun T Q pf with hP0def
  set C : Op d := resFun T Q kf with hCdef
  set X : Op d := P0 * B * P0 with hXdef
  have hXeq : σ ^ (-1/4 : ℝ) * A * σ ^ (-1/4 : ℝ) = X := by
    rw [hfac, hσm14, hσ14, hXdef, hP0def,
      show resFun T Q (fun l => l ^ (-1/4 : ℝ))
            * (resFun T Q (fun l => l ^ (1/4 : ℝ)) * B * resFun T Q (fun l => l ^ (1/4 : ℝ)))
            * resFun T Q (fun l => l ^ (-1/4 : ℝ))
          = (resFun T Q (fun l => l ^ (-1/4 : ℝ)) * resFun T Q (fun l => l ^ (1/4 : ℝ))) * B
            * (resFun T Q (fun l => l ^ (1/4 : ℝ)) * resFun T Q (fun l => l ^ (-1/4 : ℝ)))
        from by simp only [Matrix.mul_assoc],
      resFun_mul hidem horth, resFun_mul hidem horth,
      hcongr (fun l => l ^ (1/4 : ℝ) * l ^ (-1/4 : ℝ)) pf (fun l _ => mul_comm _ _)]
  have hCeq : (((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)) ^ (-1/4 : ℝ) * A
        * (((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)) ^ (-1/4 : ℝ)
      = C * B * C := by
    rw [hfac, hσγm14, hσ14, hCdef,
      show resFun T Q (fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ))
            * (resFun T Q (fun l => l ^ (1/4 : ℝ)) * B * resFun T Q (fun l => l ^ (1/4 : ℝ)))
            * resFun T Q (fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ))
          = (resFun T Q (fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ))
              * resFun T Q (fun l => l ^ (1/4 : ℝ))) * B
            * (resFun T Q (fun l => l ^ (1/4 : ℝ))
              * resFun T Q (fun l => ((1 - γ) * l + c) ^ (-1/4 : ℝ)))
        from by simp only [Matrix.mul_assoc],
      resFun_mul hidem horth, resFun_mul hidem horth,
      hcongr (fun l => l ^ (1/4 : ℝ) * ((1 - γ) * l + c) ^ (-1/4 : ℝ)) kf
        (fun l _ => mul_comm _ _)]
  -- the support projector absorbs into `C`
  have hkfpf : ∀ l ∈ T, kf l * pf l = kf l ∧ pf l * kf l = kf l := by
    intro l hl
    rcases eq_or_lt_of_le (hlnn l hl) with h0 | h0
    · have hz : kf l = 0 := by
        rw [hkfdef, ← h0]
        simp
      rw [hz]; simp
    · have hp1 : pf l = 1 := by
        rw [hpfdef]
        simp only
        rw [← Real.rpow_add h0]
        norm_num
      rw [hp1, mul_one, one_mul]
      exact ⟨rfl, rfl⟩
  have hCP : C * P0 = C := by
    rw [hCdef, hP0def, resFun_mul hidem horth,
      hcongr (fun l => kf l * pf l) kf (fun l hl => (hkfpf l hl).1)]
  have hPC : P0 * C = C := by
    rw [hCdef, hP0def, resFun_mul hidem horth,
      hcongr (fun l => pf l * kf l) kf (fun l hl => (hkfpf l hl).2)]
  have hCXC : C * B * C = C * X * C := by
    rw [hXdef,
      show C * (P0 * B * P0) * C = (C * P0) * B * (P0 * C) from by simp only [Matrix.mul_assoc],
      hCP, hPC]
  -- the pointwise bound on the resolution coefficients
  set u : ℝ := (1 - γ) ^ (-1/4 : ℝ) with hudef
  have hu : 0 < u := Real.rpow_pos_of_pos hg _
  have hkfnn : ∀ l ∈ T, 0 ≤ kf l := by
    intro l hl
    rw [hkfdef]
    -- both factors are real powers of the nonnegative bases `(1-γ)l + c` and `l`
    exact mul_nonneg (Real.rpow_nonneg (add_nonneg (mul_nonneg hg.le (hlnn l hl)) hc) _)
      (Real.rpow_nonneg (hlnn l hl) _)
  have hkfle : ∀ l ∈ T, kf l ≤ u := by
    intro l hl
    have hl0 : 0 ≤ l := hlnn l hl
    rcases eq_or_lt_of_le hl0 with h0 | h0
    · have hz : kf l = 0 := by
        rw [hkfdef, ← h0]
        simp
      rw [hz]; exact hu.le
    · have hw : 0 < (1 - γ) * l + c := add_pos_of_pos_of_nonneg (mul_pos hg h0) hc
      have hw4 : 0 < ((1 - γ) * l + c) ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hw _
      have hg4 : 0 < (1 - γ) ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hg _
      have hstep : l ^ (1/4 : ℝ) * (1 - γ) ^ (1/4 : ℝ) ≤ ((1 - γ) * l + c) ^ (1/4 : ℝ) := by
        -- `l·(1−γ) ≤ (1−γ)·l + c`, and `t ↦ t^{1/4}` is monotone on `[0, ∞)`.
        rw [← Real.mul_rpow hl0 hg.le]
        exact Real.rpow_le_rpow (mul_nonneg hl0 hg.le)
          (by rw [mul_comm]; exact le_add_of_nonneg_right hc) (by norm_num)
      have hkfrw : kf l = (((1 - γ) * l + c) ^ (1/4 : ℝ))⁻¹ * l ^ (1/4 : ℝ) := by
        rw [hkfdef]
        simp only
        rw [show (-1/4 : ℝ) = -(1/4 : ℝ) by norm_num, Real.rpow_neg hw.le]
      have hurw : u = ((1 - γ) ^ (1/4 : ℝ))⁻¹ := by
        rw [hudef, show (-1/4 : ℝ) = -(1/4 : ℝ) by norm_num, Real.rpow_neg hg.le]
      rw [hkfrw, hurw, inv_mul_eq_div, ← one_div, div_le_div_iff₀ hw4 hg4, one_mul]
      exact hstep
  -- `C² ⪯ u²·1`
  have hD : ((((u ^ 2 : ℝ)) : ℂ) • (1 : Op d) - C * C).PosSemidef := by
    rw [hCdef, resFun_mul hidem horth, resFun_smul_one (T := T) (Q := Q) hsum (u ^ 2),
      resFun_sub]
    -- coefficientwise `kf l ^ 2 ≤ u ^ 2`, from `0 ≤ kf l ≤ u`
    exact resFun_posSemidef hHerm hidem fun l hl =>
      sub_nonneg.mpr ((mul_self_le_mul_self (hkfnn l hl) (hkfle l hl)).trans_eq (sq u).symm)
  have hCherm : Cᴴ = C := by rw [hCdef]; exact resFun_conjTranspose hHerm kf
  have hu4 : u ^ 2 * u ^ 2 = (1 - γ)⁻¹ := by
    have h4 : u ^ (4 : ℕ) = (1 - γ)⁻¹ := by
      rw [hudef, ← Real.rpow_natCast ((1 - γ) ^ (-1/4 : ℝ)) 4, ← Real.rpow_mul hg.le,
        show (-1/4 : ℝ) * ((4 : ℕ) : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hg.le,
        Real.rpow_one]
    calc u ^ 2 * u ^ 2 = u ^ (4 : ℕ) := by ring
      _ = (1 - γ)⁻¹ := h4
  have husq : (0 : ℝ) ≤ u ^ 2 := by positivity
  calc weightedFrobeniusSq (((1 - γ : ℝ) : ℂ) • σ + ((c : ℝ) : ℂ) • (1 : Op d)) A
      = ((C * X * C)ᴴ * (C * X * C)).trace.re := by rw [weightedFrobeniusSq, hCeq, hCXC]
    _ ≤ u ^ 2 * u ^ 2 * (Xᴴ * X).trace.re :=
        sandwich_frobenius_le C X (u ^ 2) husq hCherm hD
    _ = (1 - γ)⁻¹ * weightedFrobeniusSq σ A := by rw [weightedFrobeniusSq, hXeq, hu4]

/-! ## The γ-regularised announced reference, in the shape the extractor consumes -/

/-- The regularised block, written as the identity-shifted mixture `(1−γ)·ν_p + c·1` that
`weightedFrobeniusSq_mix_smul_one_le` consumes, with `c = γ/(d_C·d_E)`. -/
private lemma blockFamilyRegularized_toOp_eq {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (p : Fin dC) :
    (blockFamilyRegularized ν γ hγ0 hγ1 p).toOp
      = ((1 - γ : ℝ) : ℂ) • (ν p).toOp
        + ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ) • (1 : Op dE) := by
  have hdC : ((dC : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne dC)))
  have hdE : ((dE : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne dE)))
  have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp
      = (1 / (dE : ℂ)) • (1 : Op dE) := rfl
  rw [blockFamilyRegularized_toOp, hmm, smul_smul]
  congr 2
  push_cast
  field_simp

/-- **at a single regularised block.**  The γ-regularisation of one block of an announced
block-diagonal reference costs at most the factor `(1−γ)⁻¹`, provided the block's conditional
operator lies in the block's own support in the checkable form `M = ν_p^{1/4} N ν_p^{1/4}`. -/
theorem weightedFrobeniusSq_blockFamilyRegularized_le {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p : Fin dC)
    (M N : Op dE) (hfac : M = (ν p).toOp ^ (1 / 4 : ℝ) * N * (ν p).toOp ^ (1 / 4 : ℝ)) :
    weightedFrobeniusSq (blockFamilyRegularized ν γ hγ0 hγ1.le p).toOp M
      ≤ (1 - γ)⁻¹ * weightedFrobeniusSq (ν p).toOp M := by
  have hdC : (0 : ℝ) < (dC : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hdE : (0 : ℝ) < (dE : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dE)
  rw [blockFamilyRegularized_toOp_eq]
  exact weightedFrobeniusSq_mix_smul_one_le (ν p).toOp
    (Matrix.nonneg_iff_posSemidef.mpr (posSemidefOp_implies_mathlib (ν p).toPosSemidefOp))
    M N hfac γ (γ / ((dC : ℝ) * (dE : ℝ))) hγ1 (by positivity)

/-- **(A5, analytic half) The announce charge at the γ-regularised block-diagonal reference.**

Combining the exact block collapse `collisionQuantity_tensorLeftKernel_blockDiagRef_eq` with the
blockwise γ-comparison: at the **positive definite** reference
`blockDiagRefRegularized ν γ` the announced collision quantity is at most `(1−γ)⁻¹` times the
per-label sum against the (singular) blocks themselves.  The announcement itself is still free;
the only charge is the regularisation's `(1−γ)⁻¹`, i.e. `log₂(1/(1−γ))` bits of key length.

`hfac` is the support hypothesis, per label: it is exactly what the paired-announce block family
supplies by construction (`ν_p = Σ_{ω ∈ p} |u_ω⟩⟨u_ω|` is a sub-sum of the same rank-one terms the
state is built from) and what a plain compression `E_p τ E_p` does **not** supply. -/
theorem collisionQuantity_tensorLeftKernel_blockDiagRefRegularized_le
    {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (Bfac : X → Op dE)
    (hfac : ∀ x, (ρ.stateMap x).toOp
      = (ν (ann x)).toOp ^ (1 / 4 : ℝ) * Bfac x * (ν (ann x)).toOp ^ (1 / 4 : ℝ)) :
    collisionQuantity (blockDiagRefRegularized ν hν γ hγ0 hγ1.le).toOp
        (fun x => ((ρ.tensorLeftKernel K).stateMap x).toOp)
      ≤ (1 - γ)⁻¹ * ∑ x : X, weightedFrobeniusSq (ν (ann x)).toOp ((ρ.stateMap x).toOp) := by
  rw [blockDiagRefRegularized,
    collisionQuantity_tensorLeftKernel_blockDiagRef_eq ρ ann K hK
      (blockFamilyRegularized ν γ hγ0 hγ1.le)
      (sum_blockFamilyRegularized_trace_le_one ν hν γ hγ0 hγ1.le),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ =>
    weightedFrobeniusSq_blockFamilyRegularized_le ν γ hγ0 hγ1 (ann x) _ (Bfac x) (hfac x)

/-- The γ-regularised assembled reference of a **normalised** block family is normalised:
`tr σ_γ = (1−γ)·1 + γ = 1` exactly (`sum_blockFamilyRegularized_trace_eq`).  The regularisation is
a mixture, not an inflation, so no trace is lost. -/
theorem blockDiagRefRegularized_trace_eq_one {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (hν1 : ∑ p : Fin dC, (ν p).trace = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (blockDiagRefRegularized ν hν γ hγ0 hγ1).toOp.trace.re = 1 := by
  have h : (blockDiagRefRegularized ν hν γ hγ0 hγ1).trace
      = ∑ p : Fin dC, (blockFamilyRegularized ν γ hγ0 hγ1 p).trace :=
    blockDiagRef_trace _ _
  have h2 := sum_blockFamilyRegularized_trace_eq ν γ hγ0 hγ1
  change (blockDiagRefRegularized ν hν γ hγ0 hγ1).trace = 1
  rw [h, h2, hν1]
  ring

/-- **(A5) The consumer-shaped bound: seed-key extraction against the γ-regularised announced
reference.**

`seedKeyExtractor_traceDistanceGen_le_collisionRoot` at `σ = blockDiagRefRegularized ν γ`, whose
two side conditions are supplied by
`InfoTheory.SmoothMinEntropy.blockDiagRefRegularized_posDef` (positive definiteness — the reason
the regularisation exists) and `blockDiagRefRegularized_trace_eq_one` (`Tr σ_γ = 1`, exactly),
with the collision quantity replaced by
`collisionQuantity_tensorLeftKernel_blockDiagRefRegularized_le`.

The announced classical register therefore costs **nothing** beyond the regularisation factor
`(1−γ)⁻¹` under the square root, i.e. `½·log₂(1/(1−γ))` in the trace-distance exponent — against
the `d_C` that a flat reference `(1/d_C)·1 ⊗ σ` charges
(`collisionQuantity_tensorLeftKernel_le`, tight). -/
theorem seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized
    {S X Z : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    [Fintype X] [Fintype Z] [Nonempty Z] [DecidableEq Z]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star)
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (hν1 : ∑ p : Fin dC, (ν p).trace = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (Bfac : X → Op dE)
    (hfac : ∀ x, (ρ.stateMap x).toOp
      = (ν (ann x)).toOp ^ (1 / 4 : ℝ) * Bfac x * (ν (ann x)).toOp ^ (1 / 4 : ℝ)) :
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H (ρ.tensorLeftKernel K)).toJointDensity.toOp
        (seedUniformOutputState (S := S)
          (ρ.tensorLeftKernel K).quantumMarginal).toJointDensity.toOp
      ≤ (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * ((1 - γ)⁻¹
            * ∑ x : X, weightedFrobeniusSq (ν (ann x)).toOp ((ρ.stateMap x).toOp))) := by
  classical
  have hZ : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Z)
  have hZinv : 0 ≤ 1 - 1 / (Fintype.card Z : ℝ) := by
    have : 1 / (Fintype.card Z : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hZ
    linarith
  have htr : (blockDiagRefRegularized ν hν γ hγ0.le hγ1.le).toOp.trace.re = 1 :=
    blockDiagRefRegularized_trace_eq_one ν hν hν1 γ hγ0.le hγ1.le
  have hmain := seedKeyExtractor_traceDistanceGen_le_collisionRoot h2 (ρ.tensorLeftKernel K)
    (blockDiagRefRegularized ν hν γ hγ0.le hγ1.le).toOp
    (blockDiagRefRegularized_posDef ν hν γ hγ0 hγ1.le)
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  rw [htr, one_mul]
  refine mul_le_mul_of_nonneg_left
    (collisionQuantity_tensorLeftKernel_blockDiagRefRegularized_le ρ ann K hK ν hν γ hγ0.le hγ1
      Bfac hfac) ?_
  positivity

end InfoTheory.QuantumLHL

end
