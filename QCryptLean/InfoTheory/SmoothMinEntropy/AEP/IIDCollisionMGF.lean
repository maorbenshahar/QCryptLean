import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBitsBlockDomination
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDCollisionMGFSupport
import QCryptLean.Quantum.TensorProducts.Rpow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Operator-collision MGF layer for Renner's `thm:Hmincondrep` tail (bit track)

This module provides the operator-collision moment-generating-function layer of
Renner's smooth-min-entropy AEP (main.tex:4865-4979), expressed with the
continuous-functional-calculus real powers `· ^ (· : ℝ)` (`CFC.rpow`) of the
positive-semidefinite conditional blocks and reference.

Objects:
* `iidAEPSingleCopyMGF` — the single-copy tilted MGF
  `m(s) = Σ_x tr[ρ_x^{1+s} σ^{−s}]`.
* `iidAEPCollisionTrace` — the `N`-copy operator collision trace
  `Σ_{xs} tr[R_xs^{1+s} τ^{−s}]` over the conditional tensor-power block
  `R_xs = ρ_{x₁}⊗···⊗ρ_{x_N}` and the tensor-power reference `τ = σ^{⊗N}`.

Main results:
* `iidAEPCollisionTrace_eq_singleCopyMGF_pow` — the factorization
  `M(s) = m(s)^N`, assembled copy-by-copy (the CFC powers split factorwise via
  `Op.tensor_rpow`, since Mathlib provides no `(σ^{⊗N})^{−s} = (σ^{−s})^{⊗N}`
  identity).
* reality of the single-copy trace and nonnegativity of `m(s)`
  (`iidAEPSingleCopyMGF_nonneg`), with strict positivity `m(s) > 0` under the
  support-feasibility gate (`iidAEPSingleCopyMGF_pos`).
* `two_le_iidAEPSpectralRadius` — the reference spectral radius
  `μ = classicalRank + Σ_x tr[ρ_x² σ⁻¹] + 2` satisfies `μ ≥ 2`.
* `one_sub_log_two_div_log_two_pow_three_le_inv_log_two_sub_half` — the numerical inequality `(1 −
ln2)/(ln2)³ ≤ 1/ln2 − 1/2`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Object layer — single-copy MGF and operator collision trace -/

/-- **Single-copy tilted MGF** `m(s) = Σ_{x∈X} tr[ρ_x^{1+s} · σ^{−s}]`
(main.tex:4865–4920, per-copy form). The operator powers `(ρ.stateMap x).toOp ^ (1+s)`
and `σ.toOp ^ (−s)` are the Mathlib continuous-functional-calculus real powers
(`CFC.rpow`) of the positive-semidefinite single-copy block `ρ_x` and the reference
`σ`. Each summand `tr[ρ_x^{1+s} σ^{−s}]` is the trace of a product of two Hermitian
operators, hence real; `.re` records that. At `s = 1` it is the `s = 1` collision
moment that, with `classicalRank` and the `+2`, assembles Renner's spectral radius
`μ = iidAEPSpectralRadius ρ σ = γ + 2`. -/
def iidAEPSingleCopyMGF
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (s : ℝ) : ℝ :=
  (∑ x : X, ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace).re

/-- **`N`-copy operator collision trace**
`Σ_{xs} tr[R_xs^{1+s} · τ^{−s}]` (main.tex:4920–4979), where
`R_xs = (ρ^{⊗N})_xs = ρ_{x_1}⊗···⊗ρ_{x_N}` is the conditional tensor-power block
(`iidAEPTensorState`) and `τ = σ^{⊗N}` is the tensor-power reference
(`iidAEPTensorReference`). Powers are the CFC real powers. This is the operator
form of Renner's tilted MGF sum: the eigenbasis spectral sum
`iidAEPTiltedMGFSum` equals this under the reference spectral resolution (the
bridge `iidAEPTiltedMGFSum_eq_collisionTrace` lives in the main file). -/
def iidAEPCollisionTrace
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (s : ℝ) : ℝ :=
  ∑ xs : Fin n_copies → X,
    (((iidAEPTensorState ρ n_copies).stateMap xs).toOp ^ (1 + s)
      * (iidAEPTensorReference σ n_copies).toOp ^ (-s)).trace.re

/-! ## Tensor-power factorization `M(s) = m(s)^N` -/

/-- **Reality of a single-copy collision summand.** `tr[ρ_x^{1+s} σ^{−s}]` is the
trace of a product of two positive-semidefinite operators (CFC real powers are
PSD by `CFC.rpow_nonneg`), hence nonnegative, so its imaginary part vanishes. -/
lemma iidAEPSingleCopyTrace_im_zero
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (s : ℝ) (x : X) :
    ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.im = 0 := by
  have h1 : Matrix.PosSemidef ((ρ.stateMap x).toOp ^ (1 + s)) :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have h2 : Matrix.PosSemidef (σ.toOp ^ (-s)) :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  rw [← Complex.conj_eq_iff_im, starRingEnd_apply, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, h1.isHermitian.eq, h2.isHermitian.eq,
    Matrix.trace_mul_comm]

/-- **Reality of the single-copy collision sum.** The full sum
`Σ_x tr[ρ_x^{1+s} σ^{−s}]` has vanishing imaginary part, since each summand does
(`iidAEPSingleCopyTrace_im_zero`). This is the sum-level form backing the real
single-copy MGF `m(s)`. -/
lemma iidAEPSingleCopyTrace_sum_im_zero
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (s : ℝ) :
    (∑ x : X, ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace).im = 0 := by
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero fun x _ => iidAEPSingleCopyTrace_im_zero ρ σ s x

/-- **Dimension-cast invariance of the collision-trace expression.** The
`SubDensityOp.castDim` dimension transport `h ▸ ·` leaves the tilted collision
trace `tr[ρ^{a} τ^{b}]` unchanged: it is just a relabelling of basis indices, and
trace is invariant under it. Used to peel the `castDim` from each `tensorFinProd`
recursion step. -/
private lemma castDim_collisionTrace {d e : ℕ} (h : d = e)
    (ρ τ : SubDensityOp d) (a b : ℝ) :
    ((SubDensityOp.castDim h ρ).toOp ^ a * (SubDensityOp.castDim h τ).toOp ^ b).trace
      = (ρ.toOp ^ a * τ.toOp ^ b).trace := by
  subst h
  rfl

/-- **Copy-by-copy factorization of the finite-tensor-product collision trace.**
For two families `f, g : Fin N → SubDensityOp d`,

  `tr[(⊗_i f_i)^{1+s} · (⊗_i g_i)^{−s}] = Π_i tr[f_i^{1+s} · g_i^{−s}]`.

Inducting on `N` along the `SubDensityOp.tensorFinProd` recursion: the cast is
peeled by `castDim_collisionTrace`, the leading binary tensor factor has its CFC
real powers split off by `Op.tensor_rpow` (`(A ⊗ B)^t = A^t ⊗ B^t`), the product
recombines through `Op.tensor_mul`, and the trace factors via `Op.trace_tensor`.
The PSD side conditions on each factor come from `SubDensityOp.toPosSemidefOp`. -/
private lemma tensorFinProd_collisionTrace {d : ℕ} [NeZero d]
    (N : ℕ) (f g : Fin N → SubDensityOp d) (s : ℝ) :
    ((SubDensityOp.tensorFinProd N f).toOp ^ (1 + s)
        * (SubDensityOp.tensorFinProd N g).toOp ^ (-s)).trace
      = ∏ i : Fin N, ((f i).toOp ^ (1 + s) * (g i).toOp ^ (-s)).trace := by
  induction N with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      simp only [SubDensityOp.tensorFinProd, castDim_collisionTrace]
      have htriv : SubDensityOp.trivialOne.toOp = (1 : Op 1) := by
        simp only [SubDensityOp.trivialOne, DensityOp.toSubDensityOp, DensityOp.trivial]
        exact Matrix.ext fun i j => by fin_cases i; fin_cases j; rfl
      rw [htriv, CFC.one_rpow, CFC.one_rpow, mul_one, Matrix.trace_one]
      simp
  | succ k ih =>
      have hstep :
          ((SubDensityOp.tensorFinProd (k + 1) f).toOp ^ (1 + s)
              * (SubDensityOp.tensorFinProd (k + 1) g).toOp ^ (-s)).trace
            = ((Op.tensor (f 0).toOp (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toOp)
                  ^ (1 + s)
                * (Op.tensor (g 0).toOp (SubDensityOp.tensorFinProd k (g ∘ Fin.succ)).toOp)
                    ^ (-s)).trace := by
        simp only [SubDensityOp.tensorFinProd]
        rw [castDim_collisionTrace]
        rfl
      rw [hstep]
      have hf0 : (0 : Op d) ≤ (f 0).toOp :=
        Matrix.nonneg_iff_posSemidef.mpr
          (Quantum.Operators.posSemidefOp_implies_mathlib (f 0).toPosSemidefOp)
      have hg0 : (0 : Op d) ≤ (g 0).toOp :=
        Matrix.nonneg_iff_posSemidef.mpr
          (Quantum.Operators.posSemidefOp_implies_mathlib (g 0).toPosSemidefOp)
      have hfk : (0 : Op (d ^ k)) ≤ (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toOp :=
        Matrix.nonneg_iff_posSemidef.mpr
          (Quantum.Operators.posSemidefOp_implies_mathlib
            (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)).toPosSemidefOp)
      have hgk : (0 : Op (d ^ k)) ≤ (SubDensityOp.tensorFinProd k (g ∘ Fin.succ)).toOp :=
        Matrix.nonneg_iff_posSemidef.mpr
          (Quantum.Operators.posSemidefOp_implies_mathlib
            (SubDensityOp.tensorFinProd k (g ∘ Fin.succ)).toPosSemidefOp)
      rw [Op.tensor_rpow _ _ hf0 hfk, Op.tensor_rpow _ _ hg0 hgk, Op.tensor_mul,
        Op.trace_tensor, ih (f ∘ Fin.succ) (g ∘ Fin.succ), Fin.prod_univ_succ]
      rfl

/-- **Copy-by-copy factorization of the collision summand.** For a fixed classical
label `xs`, the trace of the tilted product over the conditional tensor-power
block `R_xs = ρ_{x₁}⊗···⊗ρ_{x_N}` and the tensor-power reference `τ = σ^{⊗N}`
factors per copy:

  `tr[R_xs^{1+s} · τ^{−s}] = Π_i tr[ρ_{x_i}^{1+s} · σ^{−s}]`.

The block and reference are tensor products (`CQState.tensorPower_stateMap_toOp`,
`iidAEPTensorReference`), so the CFC real powers split factorwise via
`Op.tensor_rpow` (`(A⊗B)^t = A^t⊗B^t` on PSD factors) and the trace factors
through `tensorFinProd_collisionTrace`. The factorwise route is used because
Mathlib has no `(σ^{⊗N})^{−s} = (σ^{−s})^{⊗N}` identity. -/
lemma iidAEPCollisionSummand_factor
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (s : ℝ) (xs : Fin n_copies → X) :
    (((iidAEPTensorState ρ n_copies).stateMap xs).toOp ^ (1 + s)
        * (iidAEPTensorReference σ n_copies).toOp ^ (-s)).trace
      = ∏ i : Fin n_copies,
          ((ρ.stateMap (xs i)).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace := by
  rw [show ((iidAEPTensorState ρ n_copies).stateMap xs).toOp
        = (SubDensityOp.tensorFinProd n_copies (fun j => ρ.stateMap (xs j))).toOp from
      CQState.tensorPower_stateMap_toOp ρ n_copies xs,
    show (iidAEPTensorReference σ n_copies).toOp
        = (SubDensityOp.tensorFinProd n_copies
            (fun _ => DensityOp.toSubDensityOp σ)).toOp from rfl,
    tensorFinProd_collisionTrace]
  rfl

/-- **Tensor-power factorization of the collision trace.** The `N`-copy operator
collision trace equals the `N`-th power of the single-copy MGF:

  `iidAEPCollisionTrace ρ σ N s = (iidAEPSingleCopyMGF ρ σ s) ^ N`.

For each label `xs` the summand factors copy-by-copy
(`iidAEPCollisionSummand_factor`:
`tr[R_xs^{1+s} τ^{−s}] = Π_i tr[ρ_{x_i}^{1+s} σ^{−s}]`); summing the product over
`xs ∈ X^N` gives the `N`-th power of `Σ_x tr[ρ_x^{1+s} σ^{−s}] = m(s)`. This is
operator bookkeeping and functional calculus only (no inequality). The CFC powers
split factorwise via `Op.tensor_rpow`, since Mathlib has no
`(σ^{⊗N})^{−s} = (σ^{−s})^{⊗N}` bridge. -/
theorem iidAEPCollisionTrace_eq_singleCopyMGF_pow
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (s : ℝ) :
    iidAEPCollisionTrace ρ σ n_copies s
      = iidAEPSingleCopyMGF ρ σ s ^ n_copies := by
  classical
  unfold iidAEPCollisionTrace iidAEPSingleCopyMGF
  set g : X → ℂ := fun x => ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace
    with hg
  -- The single-copy MGF is real: the imaginary part of the whole sum vanishes.
  have him : (∑ x, g x).im = 0 := iidAEPSingleCopyTrace_sum_im_zero ρ σ s
  have hz : (∑ x, g x) = ((∑ x, g x).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · rw [Complex.ofReal_im, him]
  calc
    ∑ xs : Fin n_copies → X,
        (((iidAEPTensorState ρ n_copies).stateMap xs).toOp ^ (1 + s)
            * (iidAEPTensorReference σ n_copies).toOp ^ (-s)).trace.re
        = ∑ xs : Fin n_copies → X, (∏ i, g (xs i)).re := by
          refine Finset.sum_congr rfl fun xs _ => ?_
          rw [iidAEPCollisionSummand_factor]
      _ = (∑ xs : Fin n_copies → X, ∏ i, g (xs i)).re := (Complex.re_sum _ _).symm
      _ = ((∑ x, g x) ^ n_copies).re := by rw [Fintype.sum_pow]
      _ = (((∑ x, g x).re : ℂ) ^ n_copies).re := by rw [← hz]
      _ = (∑ x, g x).re ^ n_copies := by
          rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-! ## Single-copy quadratic-CGF bound -/

/-- **Numerical cubic gate.** `(1 − ln2)/(ln2)³ ≤ 1/ln2 − 1/2`.

    Clearing the positive denominator `(ln2)³` this is
    `1 − ln2 ≤ (ln2)² − (ln2)³/2`, i.e. `(ln2)³/2 + 1 − ln2 − (ln2)² ≤ 0`. With
    `ln2 ≈ 0.6931` the left side is `≈ −0.007 < 0`. Proved with the rational
    enclosures `Real.log_two_gt_d9`, `Real.log_two_lt_d9` and `nlinarith`. -/
lemma one_sub_log_two_div_log_two_pow_three_le_inv_log_two_sub_half :
    (1 - Real.log 2) / (Real.log 2) ^ 3 ≤ 1 / Real.log 2 - 1 / 2 := by
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hne : Real.log 2 ≠ 0 := ne_of_gt hpos
  have hcube_pos : (0 : ℝ) < (Real.log 2) ^ 3 := pow_pos hpos 3
  have hlt := Real.log_two_lt_d9
  have hgt := Real.log_two_gt_d9
  rw [div_le_iff₀ hcube_pos]
  have hrw : (1 / Real.log 2 - 1 / 2) * (Real.log 2) ^ 3
      = (Real.log 2) ^ 2 - (Real.log 2) ^ 3 / 2 := by
    field_simp
  rw [hrw]
  nlinarith [hlt, hgt, sq_nonneg (Real.log 2),
    mul_nonneg (by linarith : (0:ℝ) ≤ Real.log 2 - 0.6931471803)
      (by linarith : (0:ℝ) ≤ 0.6931471808 - Real.log 2)]

/-- **Strict positivity of the single-copy tilted MGF** `0 < m(s)` for `s ≥ 0`. Each
summand `tr[ρ_x^{1+s} σ^{−s}]` is the trace of a product of PSD CFC powers, hence
nonnegative; normalization `hρ_norm` forces some block `ρ_{x₀} ≠ 0`, and the
support-feasibility gate `hfeas` (`ρ_{x₀} ≼ t·σ`) keeps `σ^{−s}` from annihilating
`range(ρ_{x₀})`, making that summand strictly positive.

`hfeas` is load-bearing: without the support condition the statement fails — e.g.
`n = 2`, `σ = |0⟩⟨0|`, `ρ_pt = |1⟩⟨1|`, where for `s > 0` the power `σ^{−s}`
annihilates `|1⟩` and `m(s) = 0`. Strict positivity (rather than just `0 ≤ m`) is
what lets the downstream cumulant bound take `Real.logb 2 m`. -/
lemma iidAEPSingleCopyMGF_pos
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s) :
    0 < iidAEPSingleCopyMGF ρ σ s := by
  classical
  unfold iidAEPSingleCopyMGF
  rw [Complex.re_sum]
  -- each summand `tr[ρ_x^{1+s} σ^{−s}].re` is nonnegative (product of two PSD ops)
  have hnn : ∀ x ∈ (Finset.univ : Finset X),
      0 ≤ ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re := by
    intro x _
    have h1 : Matrix.PosSemidef ((ρ.stateMap x).toOp ^ (1 + s)) :=
      Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    have h2 : Matrix.PosSemidef (σ.toOp ^ (-s)) :=
      Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    exact Quantum.Operators.trace_mul_psd_nonneg _ _ h1 h2
  -- `hρ_norm` (total mass `= 1`) forces some block `ρ_{x₀}` to be nonzero
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, (ρ.stateMap x₀).toOp ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∑ x : X, (ρ.stateMap x).trace = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      change (ρ.stateMap x).toOp.trace.re = 0
      rw [hcon x, Matrix.trace_zero, Complex.zero_re]
    rw [hρ_norm] at hzero
    exact one_ne_zero hzero
  -- feasibility supplies the Löwner domination `ρ_{x₀} ≼ t·σ`
  obtain ⟨t, _ht0, htle⟩ := hfeas
  -- a finite sum of nonnegative reals with one strictly positive term is positive
  refine Finset.sum_pos' hnn ⟨x₀, Finset.mem_univ x₀, ?_⟩
  exact trace_rpow_mul_rpow_pos_of_opLe
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x₀).toPosSemidefOp)
    (Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp)
    hx₀ (htle x₀) hs

/-- **Nonnegativity of the collision factor** `Σ_x tr[ρ_x² σ^{-1}]`. Each summand
is the real trace of a product of two positive-semidefinite operators
(`ρ_x² = ρ_xᴴ ρ_x` is PSD, and the CFC pseudo-inverse `σ^{-1} = σ.toOp ^ (-1 : ℝ)`
is PSD by `CFC.rpow_nonneg`), hence nonnegative. -/
lemma tracedSquareTimesInvFactor_nonneg
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) :
    0 ≤ ρ.tracedSquareTimesInvFactor σ := by
  unfold InfoTheory.SmoothMinEntropy.CQState.tracedSquareTimesInvFactor
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  have hA_psd : Matrix.PosSemidef (ρ.stateMap x).toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have hInv_psd : Matrix.PosSemidef (σ.toOp ^ (-1 : ℝ)) :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hAA_psd : Matrix.PosSemidef ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp) := by
    have hself := Matrix.posSemidef_conjTranspose_mul_self (ρ.stateMap x).toOp
    rwa [hA_psd.isHermitian.eq] at hself
  exact Quantum.Operators.trace_mul_psd_nonneg _ _ hAA_psd hInv_psd

/-- **The reference spectral radius is at least `2`.** It equals
`classicalRank + Σ_x tr[ρ_x² σ⁻¹] + 2` with both leading terms nonnegative. -/
lemma two_le_iidAEPSpectralRadius
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) :
    (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ := by
  unfold iidAEPSpectralRadius
  have h1 : (0 : ℝ) ≤ (ρ.classicalRank : ℝ) := Nat.cast_nonneg _
  have h2 := tracedSquareTimesInvFactor_nonneg ρ σ
  linarith

/-- **Nonnegativity of the single-copy tilted MGF.** Each summand
`tr[ρ_x^{1+s} σ^{−s}].re` is the real trace of a product of two
positive-semidefinite operators (CFC real powers are PSD by `CFC.rpow_nonneg`),
hence nonnegative; the sum is therefore `≥ 0`. -/
lemma iidAEPSingleCopyMGF_nonneg
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (s : ℝ) :
    0 ≤ iidAEPSingleCopyMGF ρ σ s := by
  classical
  unfold iidAEPSingleCopyMGF
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  have h1 : Matrix.PosSemidef ((ρ.stateMap x).toOp ^ (1 + s)) :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg)
  have h2 : Matrix.PosSemidef (σ.toOp ^ (-s)) :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg)
  exact trace_mul_psd_nonneg _ _ h1 h2

end InfoTheory.SmoothMinEntropy

end
