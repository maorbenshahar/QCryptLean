import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ProdPos
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ClassicalExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.Quantum.TensorProducts.Rpow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# IIDAEP class-reduction helpers — support positivity, pseudo-inverse trace bound, logb squeeze

Elementary and algebraic facts feeding the IIDAEP class-reduction step, together with the
relative-entropy self-vanishing identity `relativeEntropyReal_self`. (The general
iidAEPClassical/iidAEP unification was never assembled under those bare names in
this package; the completed corollaries are the suffixed forms, e.g.
`InfoTheory.SmoothMinEntropy.iidAEPClassical_bit_normalized` and its rank-bound variants.)

These lemmas are stated using only `CQState` / `SubDensityOp` / `DensityOp`-level
data, with no reference to the definitions in `IID.lean`
(`classicalRank`, `tracedSquareTimesInvFactor`, `quantumMarginalDensityOp`, …),
so that this file can be imported BY `IID.lean` without an import cycle.

## Main statements

* `CQState.classicalRank_filter_pos` — a normalized CQ state has at least one
  classical outcome of positive weight.
* `CQState.trace_sq_mul_inv_le_trace_of_opLe_posDef` — for `0 ≤ A ≤ σ` with `σ`
  positive definite, `Tr(A² σ⁻¹) ≤ Tr A` (via `prodpos`).
* `CQState.trace_sq_mul_rpowNegOne_le_trace_of_opLe` — the CFC pseudo-inverse
  generalization to merely PSD `σ`, with `σ⁻¹ = σ ^ (-1 : ℝ)`.
* `CQState.sum_trace_sq_mul_rpowNegOne_re_le_one` /
  `CQState.sum_trace_sq_mul_rpowNegOne_re_nonneg` — when `σ.toOp` is the quantum
  marginal of `ρ`, the sum `(∑_x Tr(ρ_x² σ⁻¹)).re` lies in `[0, 1]`.
* `InfoTheory.SmoothMinEntropy.logb_rank_plus_two_le_two_mul_logb_rank_plus_four` — the squeeze
  `2·logb₂(r + t + 2) ≤ 2·logb₂ r + 4` for `1 ≤ r`, `0 ≤ t ≤ 1`.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

namespace InfoTheory.SmoothMinEntropy

namespace CQState

/-- For a normalized CQ state, at least one classical outcome carries
positive weight: the support filter has cardinality `≥ 1`.

If the filter were empty, every classical weight would be `0`
(by `trace_nonneg`), forcing `∑ x, (ρ.stateMap x).trace = 0`,
contradicting the normalization `= 1`. -/
lemma classicalRank_filter_pos
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    1 ≤ (Finset.univ.filter (fun x : X => 0 < (ρ.stateMap x).trace)).card := by
  classical
  by_contra h
  push Not at h
  have hcard :
      (Finset.univ.filter (fun x : X => 0 < (ρ.stateMap x).trace)).card = 0 := by
    omega
  have hempty :
      (Finset.univ.filter (fun x : X => 0 < (ρ.stateMap x).trace)) = ∅ := by
    rw [← Finset.card_eq_zero]; exact hcard
  have hzero : ∀ x : X, (ρ.stateMap x).trace = 0 := by
    intro x
    have hx :
        x ∉ (Finset.univ.filter (fun y : X => 0 < (ρ.stateMap y).trace)) := by
      rw [hempty]; exact Finset.notMem_empty x
    have hxn : ¬ (0 < (ρ.stateMap x).trace) := by
      intro hpos; exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpos⟩)
    have hle : (ρ.stateMap x).trace ≤ 0 := not_lt.mp hxn
    exact le_antisymm hle (ρ.stateMap x).trace_nonneg
  have hsum_zero : ∑ x : X, (ρ.stateMap x).trace = 0 := by
    apply Finset.sum_eq_zero; intro x _; exact hzero x
  rw [hρ_norm] at hsum_zero
  exact one_ne_zero hsum_zero

/-- If `0 ≤ A ≤ σ` and `σ` is positive definite, then
`Tr(A² σ⁻¹) ≤ Tr(A)`.

The proof applies Renner `prodpos` with `λ = 1` to get
`sqrt(A) σ⁻¹ sqrt(A) ≤ I`, then tests that operator inequality against the
PSD weight `A` and cycles the trace back to `Tr(A² σ⁻¹)`. -/
lemma trace_sq_mul_inv_le_trace_of_opLe_posDef
    {n : ℕ} {A σ : Op n}
    (hA : A.PosSemidef) (hσ : σ.PosDef) (hA_le : opLe A σ) :
    (A * A * σ⁻¹).trace.re ≤ A.trace.re := by
  let APSD : PosSemidefOp n :=
    { toOp := A
      isHermitian := hA.isHermitian
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hA v }
  let R : Op n := sqrtPosSemidefOp APSD
  have hR_sq : R * R = A := by
    simpa [R, APSD] using sqrtPosSemidefOp_sq APSD
  have hR_herm : R.IsHermitian := by
    simpa [R, APSD] using sqrtPosSemidefOp_isHermitian APSD
  have hdom : (((1 : ℝ) : ℂ) • σ - A).PosSemidef := by
    have hsub : (σ - A).PosSemidef :=
      opLe.posSemidef_sub hA.isHermitian hσ.isHermitian hA_le
    simpa using hsub
  have hprod :
      (((1 : ℝ) : ℂ) • (1 : Op n) - R * σ⁻¹ * R).PosSemidef := by
    simpa [R, APSD] using
      InfoTheory.SmoothMinEntropy.prodpos APSD σ 1 hσ (by norm_num) hdom
  have hB_le_one : opLe (R * σ⁻¹ * R) (1 : Op n) := by
    exact opLe_of_posSemidef_sub (by simpa using hprod)
  have hB_psd : (R * σ⁻¹ * R).PosSemidef := by
    have hσinv_psd : (σ⁻¹).PosSemidef := hσ.posSemidef.inv
    have hconj : (Rᴴ * σ⁻¹ * R).PosSemidef :=
      hσinv_psd.conjTranspose_mul_mul_same R
    simpa [hR_herm.eq] using hconj
  have htrace_le :
      (A * (R * σ⁻¹ * R)).trace.re ≤ (A * (1 : Op n)).trace.re :=
    trace_mul_le_of_opLe hA hB_psd.isHermitian Matrix.isHermitian_one hB_le_one
  have hAA_eq : R * A * R = A * A := by
    calc
      R * A * R = R * (R * R) * R := by rw [hR_sq]
      _ = (R * R) * (R * R) := by simp [Matrix.mul_assoc]
      _ = A * A := by rw [hR_sq]
  have htarget :
      (A * A * σ⁻¹).trace = (A * (R * σ⁻¹ * R)).trace := by
    calc
      (A * A * σ⁻¹).trace = ((R * A * R) * σ⁻¹).trace := by rw [hAA_eq]
      _ = (R * A * (R * σ⁻¹)).trace := by simp [Matrix.mul_assoc]
      _ = ((R * σ⁻¹ * R) * A).trace := by
        simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle R A (R * σ⁻¹)
      _ = (A * (R * σ⁻¹ * R)).trace := Matrix.trace_mul_comm (R * σ⁻¹ * R) A
  calc
    (A * A * σ⁻¹).trace.re = (A * (R * σ⁻¹ * R)).trace.re := congrArg Complex.re htarget
    _ ≤ (A * (1 : Op n)).trace.re := htrace_le
    _ = A.trace.re := by rw [Matrix.mul_one]

open CfcSpectral in
/-- The CFC real power acts by the eigenvalue on an indicator spectral projector:
for `0 ≤ B`, `B ^ r * specProj B l = (l ^ r) • specProj B l`. -/
private lemma rpow_mul_specProj_aux {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : 0 ≤ B) (r l : ℝ) :
    B ^ r * specProj B l = (l ^ r : ℝ) • specProj B l := by
  simp only [specProj]
  rw [CFC.rpow_eq_cfc_real hB,
    ← cfc_mul _ _ B (continuousOn_spectrum B _) (continuousOn_spectrum B _),
    ← cfc_const_mul (l ^ r : ℝ) _ B (continuousOn_spectrum B _)]
  apply cfc_congr
  intro x _
  by_cases hxl : x = l <;> simp [Set.indicator, hxl]

/-- The PSD operator annihilates its own kernel projector: `σ · specProj σ 0 = 0`. -/
private lemma mul_specProj_zero {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    σ * CfcSpectral.specProj σ 0 = 0 := by
  have h := rpow_mul_specProj_aux σ hσ.nonneg 1 0
  rw [CFC.rpow_one σ hσ.nonneg] at h
  simpa using h

/-- An indicator spectral projector is positive semidefinite. -/
private lemma specProj_psd {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Matrix n n ℂ) (l : ℝ) : (CfcSpectral.specProj σ l).PosSemidef := by
  have hH := CfcSpectral.specProj_isHermitian σ l
  have hidem := CfcSpectral.specProj_idem σ l
  have hself : (CfcSpectral.specProj σ l)ᴴ * CfcSpectral.specProj σ l
      = CfcSpectral.specProj σ l := by rw [hH.eq, hidem]
  rw [← hself]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Inverse identity (algebraic).** With `Q₀ = specProj σ 0` the kernel projector and
`σ₊ = σ + Q₀`, the product `σ₊ · (σ^{-1} + Q₀) = 1`, so `σ₊⁻¹ = σ^{-1} + Q₀`. -/
private lemma sigma_add_kernelProj_mul_rpowNegOne_add_kernelProj_eq_one {n : Type*} [Fintype n]
    [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (σ + CfcSpectral.specProj σ 0) * (σ ^ (-1 : ℝ) + CfcSpectral.specProj σ 0) = 1 := by
  have e1 : σ + CfcSpectral.specProj σ 0
      = cfc (fun x => id x + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x) σ := by
    rw [cfc_add σ id (Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)))
        (CfcSpectral.continuousOn_spectrum σ _) (CfcSpectral.continuousOn_spectrum σ _),
        cfc_id ℝ σ]
    rfl
  have e2 : σ ^ (-1 : ℝ) + CfcSpectral.specProj σ 0
      = cfc (fun x => x ^ (-1 : ℝ) + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x) σ := by
    rw [cfc_add σ (fun x => x ^ (-1 : ℝ)) (Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)))
        (CfcSpectral.continuousOn_spectrum σ _) (CfcSpectral.continuousOn_spectrum σ _),
        ← CFC.rpow_eq_cfc_real hσ.nonneg]
    rfl
  rw [e1, e2, ← cfc_mul _ _ σ
      (CfcSpectral.continuousOn_spectrum σ _) (CfcSpectral.continuousOn_spectrum σ _)]
  have hgoal : cfc (fun x => (id x + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x)
        * (x ^ (-1 : ℝ) + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x)) σ
      = cfc (fun _ : ℝ => (1 : ℝ)) σ := by
    apply cfc_congr
    intro x hx
    have hxnn : 0 ≤ x := spectrum_nonneg_of_nonneg hσ.nonneg hx
    by_cases hx0 : x = 0
    · subst hx0
      change (id (0 : ℝ) + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) 0)
          * ((0 : ℝ) ^ (-1 : ℝ) + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) 0) = 1
      rw [Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0),
          Set.indicator_of_mem (show (0 : ℝ) ∈ ({0} : Set ℝ) by simp)]
      norm_num
    · have hxne : x ≠ 0 := hx0
      have hind : Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem (by simpa using hxne) _
      change (id x + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x)
          * (x ^ (-1 : ℝ) + Set.indicator ({0} : Set ℝ) (fun _ => (1 : ℝ)) x) = 1
      rw [hind, Real.rpow_neg_one, id_eq, add_zero, add_zero]
      exact mul_inv_cancel₀ hxne
  rw [hgoal]
  exact cfc_one ℝ σ

/-- If `0 ≤ A ≤ σ` (with `σ` only positive **semi**definite), then
`Tr(A² σ^{-1}) ≤ Tr(A)`, where `σ^{-1} = σ ^ (-1 : ℝ)` is the CFC pseudo-inverse
(inverts the nonzero eigenvalues of `σ`, `0` on `ker σ`).

This is the pseudo-inverse generalization of
`trace_sq_mul_inv_le_trace_of_opLe_posDef`. The Löwner domination `A ≤ σ` forces
`supp A ⊆ supp σ`, so the operator `A` lives inside the support of `σ`; on `supp σ`
the pseudo-inverse `σ^{-1}` agrees with the genuine inverse of the restriction
`σ|_{supp σ}`, and the positive-definite-subspace argument of
`trace_sq_mul_inv_le_trace_of_opLe_posDef` (via `prodpos` with `λ = 1`) applies to
the restricted operators, giving `Tr(A² σ^{-1}) ≤ Tr(A)`. The kernel contributes
nothing on either side. -/
lemma trace_sq_mul_rpowNegOne_le_trace_of_opLe
    {n : ℕ} {A σ : Op n}
    (hA : A.PosSemidef) (hσ : σ.PosSemidef) (hA_le : opLe A σ) :
    (A * A * σ ^ (-1 : ℝ)).trace.re ≤ A.trace.re := by
  classical
  set Q₀ : Op n := CfcSpectral.specProj σ 0 with hQ0def
  have hQ0_herm : Q₀.IsHermitian := CfcSpectral.specProj_isHermitian σ 0
  have hQ0_psd : Q₀.PosSemidef := specProj_psd σ 0
  -- Step 1: kernel inclusion `σ · Q₀ = 0`, then transfer to `A · Q₀ = 0`.
  have hσQ : σ * Q₀ = 0 := mul_specProj_zero hσ
  have hAQ : A * Q₀ = 0 := by
    refine mul_eq_zero_of_opLe_smul (c := 1) hA hσ.isHermitian hQ0_herm ?_ hσQ
    rw [Complex.ofReal_one, one_smul]; exact hA_le
  -- Step 2: `σ₊ = σ + Q₀` is positive definite (PSD + invertible).
  have hprod : (σ + Q₀) * (σ ^ (-1 : ℝ) + Q₀) = 1 :=
      sigma_add_kernelProj_mul_rpowNegOne_add_kernelProj_eq_one hσ
  have hsigP_psd : (σ + Q₀).PosSemidef := hσ.add hQ0_psd
  have hunit : IsUnit (σ + Q₀) := by
    have hdet : (σ + Q₀).det * (σ ^ (-1 : ℝ) + Q₀).det = 1 := by
      rw [← Matrix.det_mul, hprod, Matrix.det_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one _ hdet)
  have hsigP_pd : (σ + Q₀).PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hsigP_psd).mpr hunit
  -- `A ≤ σ₊`: `σ₊ - A = (σ - A) + Q₀` is a sum of PSD operators.
  have hsub : (σ - A).PosSemidef := opLe.posSemidef_sub hA.isHermitian hσ.isHermitian hA_le
  have hsubP : ((σ + Q₀) - A).PosSemidef := by
    have heq : (σ + Q₀) - A = (σ - A) + Q₀ := by abel
    rw [heq]; exact hsub.add hQ0_psd
  have hA_leP : opLe A (σ + Q₀) := opLe_of_posSemidef_sub hsubP
  -- Step 3: apply the PosDef base case.
  have hmain := trace_sq_mul_inv_le_trace_of_opLe_posDef hA hsigP_pd hA_leP
  -- Step 4: `σ₊⁻¹ = σ^{-1} + Q₀`; the kernel term `A·A·Q₀` vanishes.
  have hinv : (σ + Q₀)⁻¹ = σ ^ (-1 : ℝ) + Q₀ := Matrix.inv_eq_right_inv hprod
  rw [hinv] at hmain
  have hAAQ : A * A * Q₀ = 0 := by rw [Matrix.mul_assoc, hAQ, Matrix.mul_zero]
  have hrw : A * A * (σ ^ (-1 : ℝ) + Q₀) = A * A * σ ^ (-1 : ℝ) := by
    rw [Matrix.mul_add, hAAQ, add_zero]
  rw [hrw] at hmain
  exact hmain

/-- For a CQ state `ρ` and `σ : DensityOp n` whose `toOp` matches the quantum
marginal of `ρ`, the real part of the "squared-times-pseudo-inverse" sum is at
most `1`: `(∑_x Tr(ρ_x² · σ^{-1})).re ≤ 1`, where `σ^{-1} = σ.toOp ^ (-1 : ℝ)`
is the CFC pseudo-inverse (consistent with `iidAEPSingleCopyMGF` at `s = 1`).

Per summand, the block domination `ρ_x ≤ σ` (`stateMap_opLe_quantumMarginalOp`)
gives `Tr(ρ_x² σ^{-1}) ≤ Tr ρ_x` via `trace_sq_mul_rpowNegOne_le_trace_of_opLe`,
and the single-copy traces sum to `1` by normalization. -/
lemma sum_trace_sq_mul_rpowNegOne_re_le_one
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (hσ_eq : σ.toOp = ρ.quantumMarginalOp) :
    (∑ x : X,
        ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp * σ.toOp ^ (-1 : ℝ)).trace).re
      ≤ 1 := by
  classical
  have hσ_psd : σ.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σ.toPosSemidefOp
  rw [Complex.re_sum]
  calc
    ∑ x : X, ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp * σ.toOp ^ (-1 : ℝ)).trace.re
        ≤ ∑ x : X, (ρ.stateMap x).trace := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hx_psd : (ρ.stateMap x).toOp.PosSemidef :=
        posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
      have hx_le : opLe (ρ.stateMap x).toOp σ.toOp := by
        rw [hσ_eq]
        exact InfoTheory.SmoothMinEntropy.stateMap_opLe_quantumMarginalOp ρ x
      simpa [SubDensityOp.trace] using
        trace_sq_mul_rpowNegOne_le_trace_of_opLe
          (A := (ρ.stateMap x).toOp) (σ := σ.toOp) hx_psd hσ_psd hx_le
    _ = 1 := hρ_norm

/-- The same expression is non-negative. Each summand is the real trace of
`(ρ_x · ρ_x) · σ^{-1}`, a product of two positive-semidefinite operators:
`ρ_x · ρ_x = ρ_xᴴ · ρ_x` is PSD because `ρ_x` is Hermitian PSD, and the CFC
pseudo-inverse `σ^{-1} = σ.toOp ^ (-1 : ℝ)` is PSD because `σ` is PSD (CFC real
powers of a PSD operator are PSD, `CFC.rpow_nonneg`). Hence every summand is
nonneg by `trace_mul_psd_nonneg`, and so is the sum. -/
lemma sum_trace_sq_mul_rpowNegOne_re_nonneg
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (_hσ : σ.toOp = ρ.quantumMarginalOp) :
    0 ≤ (∑ x : X,
        ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp * σ.toOp ^ (-1 : ℝ)).trace).re := by
  classical
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  -- `ρ_x` is Hermitian and positive semidefinite.
  have hA_psd : Matrix.PosSemidef (ρ.stateMap x).toOp :=
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  -- `σ^{-1} = σ.toOp ^ (-1 : ℝ)` is positive semidefinite (`0` on `ker σ`).
  have hInv_psd : Matrix.PosSemidef (σ.toOp ^ (-1 : ℝ)) :=
    Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  -- `ρ_x · ρ_x = ρ_xᴴ · ρ_x` is positive semidefinite.
  have hAA_psd : Matrix.PosSemidef ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp) := by
    have hself : (ρ.stateMap x).toOpᴴ * (ρ.stateMap x).toOp
        = (ρ.stateMap x).toOp * (ρ.stateMap x).toOp := by
      rw [hA_psd.isHermitian.eq]
    rw [← hself]
    exact Matrix.posSemidef_conjTranspose_mul_self (ρ.stateMap x).toOp
  exact Quantum.Operators.trace_mul_psd_nonneg
    ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp) (σ.toOp ^ (-1 : ℝ)) hAA_psd hInv_psd

end CQState

end InfoTheory.SmoothMinEntropy

namespace InfoTheory.SmoothMinEntropy

/-- Algebraic squeeze used to reduce `δ_general` to `δ_class`:
for `1 ≤ r`, `0 ≤ t`, `t ≤ 1`,
`2 · logb₂(r + t + 2) ≤ 2 · logb₂ r + 4`.

Proof sketch: from the hypotheses, `r + t + 2 ≤ 4r`, so
`logb₂(r + t + 2) ≤ logb₂(4r) = logb₂ 4 + logb₂ r = 2 + logb₂ r`. -/
lemma logb_rank_plus_two_le_two_mul_logb_rank_plus_four
    {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht_nn : 0 ≤ t) (ht : t ≤ 1) :
    2 * Real.logb 2 ((r : ℝ) + t + 2) ≤ 2 * Real.logb 2 (r : ℝ) + 4 := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hb1 : (1 : ℝ) < 2 := by norm_num
  have h_logr_nonneg : 0 ≤ Real.logb 2 (r : ℝ) :=
    Real.logb_nonneg hb1 hr_ge_one
  -- `r + t + 2 ≥ 1 + 0 + 2 = 3 > 0`.
  have hpos : 0 < (r : ℝ) + t + 2 := by linarith
  -- `r + t + 2 ≤ 4r`.
  have hineq : (r : ℝ) + t + 2 ≤ 4 * (r : ℝ) := by nlinarith
  have h_log_le :
      Real.logb 2 ((r : ℝ) + t + 2) ≤ Real.logb 2 (4 * (r : ℝ)) :=
    Real.logb_le_logb_of_le hb1 hpos hineq
  have h4_ne : (4 : ℝ) ≠ 0 := by norm_num
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have h_split :
      Real.logb 2 (4 * (r : ℝ)) =
        Real.logb 2 4 + Real.logb 2 (r : ℝ) :=
    Real.logb_mul h4_ne hr_ne
  have h_logb_4 : Real.logb 2 (4 : ℝ) = 2 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.logb_self_pow (by norm_num) (by norm_num)]
    norm_num
  rw [h_logb_4] at h_split
  linarith

end InfoTheory.SmoothMinEntropy
