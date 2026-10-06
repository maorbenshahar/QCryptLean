import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.SmoothSuperadditivity
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TraceBound
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ProdPos
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ClassicalExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.HmaxClassical
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDClassReduction
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDCumulative
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.VonNeumannEntropy.Defs
import QCryptLean.InfoTheory.RelativeEntropy.Basic
import Mathlib.Analysis.Convex.Birkhoff

/-! # `IIDAEP`, part 1 of 3: foundations, reference spectrum, spectral cut scale

This file is one component of the Renner `thm:Hmincondrep` development, whose full module
docstring lives in the re-export hub `IID.lean`. This part carries the CQ-state tensor power and its
`SubDensityOp` counterpart, the penalty-constant helpers and definitions, the
entropy bridges, the main statement definitions and witness data structures
(`IIDAEPSpectralWitness` and friends), the reference-spectrum construction,
the sorted reference spectrum with Renner's cumulative resolution, the
nonnegative threshold-crossing predicate, and the spectral-cut domination
scale. -/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

/-! ### CQ-state tensor power and the SubDensityOp counterpart -/

/-- Base-case obligation for `CQState.tensorPower`: when `n_copies = 0` the
sum over the singleton type `Fin 0 → X` of the trace of the cast `trivialOne`
is exactly `1`, hence `≤ 1`. -/
lemma InfoTheory.SmoothMinEntropy.CQState.tensorPower_weight_le_one_zero
    {X : Type*} [Fintype X] {n : ℕ} (h : (1 : ℕ) = n ^ 0) :
    ∑ _ : Fin 0 → X,
        (SubDensityOp.castDim h SubDensityOp.trivialOne).trace ≤ 1 := by
  rw [Fintype.sum_unique]
  rw [SubDensityOp.castDim_trace, SubDensityOp.trivialOne_trace]

/-- Inductive-step obligation for `CQState.tensorPower`: given the binary
combined CQ state `combined : CQState (X × (Fin k → X)) (n * n^k)`, the
sum over `Fin (k+1) → X` of its (cast) traces — reindexed via
`Fin.consEquiv` — coincides with `combined`'s own `weight_le_one`. -/
lemma InfoTheory.SmoothMinEntropy.CQState.tensorPower_weight_le_one_succ
    {X : Type*} [Fintype X] {n k : ℕ}
    (combined : CQState (X × (Fin k → X)) (n * n ^ k))
    (h : n * n ^ k = n ^ (k + 1)) :
    ∑ f : Fin (k + 1) → X,
        (SubDensityOp.castDim h
            (combined.stateMap ⟨f 0, fun i => f i.succ⟩)).trace ≤ 1 := by
  -- 1. Drop the `castDim` from each summand.
  have hsumm : ∀ f : Fin (k + 1) → X,
      (SubDensityOp.castDim h
          (combined.stateMap ⟨f 0, fun i => f i.succ⟩)).trace =
        (combined.stateMap ⟨f 0, fun i => f i.succ⟩).trace := fun _ =>
    SubDensityOp.castDim_trace _ _
  simp_rw [hsumm]
  -- 2. Reindex via `Fin.consEquiv` to a sum over `X × (Fin k → X)`.
  refine
    (Finset.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => X)).symm
      (fun _ => by simp) (fun f _ => ?_)).trans_le combined.weight_le_one
  -- Show: the summand at `f` matches the one at `(Fin.consEquiv _).symm f`.
  have hsymm :
      (Fin.consEquiv (fun _ : Fin (k + 1) => X)).symm f = (f 0, Fin.tail f) :=
    Fin.consEquiv_symm_apply _ f
  rw [hsymm]
  rfl

/-- **n-fold tensor of a CQ state.** Built inductively from the binary
`CQState.tensor`. The classical register is
`Fin n_copies → X`; the quantum dimension is `n ^ n_copies`. -/
noncomputable def InfoTheory.SmoothMinEntropy.CQState.tensorPower
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (n_copies : ℕ) :
    CQState (Fin n_copies → X) (n ^ n_copies) :=
  match n_copies with
  | 0 =>
      { stateMap := fun _ =>
          SubDensityOp.castDim (by simp) SubDensityOp.trivialOne
        weight_le_one := by
          exact InfoTheory.SmoothMinEntropy.CQState.tensorPower_weight_le_one_zero
            (by simp) }
  | k + 1 =>
      let prev := InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ k
      let combined :
          CQState (X × (Fin k → X)) (n * n ^ k) :=
        InfoTheory.SmoothMinEntropy.CQState.tensor ρ prev
      { stateMap := fun f =>
          SubDensityOp.castDim (by ring)
            (combined.stateMap ⟨f 0, fun i => f i.succ⟩)
        weight_le_one := by
          exact InfoTheory.SmoothMinEntropy.CQState.tensorPower_weight_le_one_succ
            combined (by ring) }

/-- **Normalization of the n-fold CQ tensor power.** If the single-copy CQ state
`ρ` is normalized (its total trace is `1`), then so is every tensor power: the
sum over `Fin m → X` of the traces of `(CQState.tensorPower ρ m).stateMap`
equals `1`. -/
lemma InfoTheory.SmoothMinEntropy.CQState.tensorPower_sum_trace
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n)
    (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) (m : ℕ) :
    ∑ xs : Fin m → X, ((CQState.tensorPower ρ m).stateMap xs).trace = 1 := by
  induction m with
  | zero =>
      rw [Fintype.sum_unique]
      change (SubDensityOp.castDim (by simp) SubDensityOp.trivialOne).trace = 1
      rw [SubDensityOp.castDim_trace, SubDensityOp.trivialOne_trace]
  | succ k ih =>
      -- Drop the `castDim` from each summand (definitionally the `stateMap`
      -- of `tensorPower ρ (k+1)` is a cast of the binary `tensor`).
      have hstate : ∀ f : Fin (k + 1) → X,
          ((CQState.tensorPower ρ (k + 1)).stateMap f).trace =
            ((CQState.tensor ρ (CQState.tensorPower ρ k)).stateMap
              ⟨f 0, fun i => f i.succ⟩).trace := fun _ =>
        SubDensityOp.castDim_trace _ _
      simp_rw [hstate]
      -- Reindex via `Fin.consEquiv` to a sum over `X × (Fin k → X)`, then
      -- factor the trace and use the induction hypothesis.
      have hreindex :
          ∑ f : Fin (k + 1) → X,
              ((CQState.tensor ρ (CQState.tensorPower ρ k)).stateMap
                ⟨f 0, fun i => f i.succ⟩).trace =
            ∑ p : X × (Fin k → X),
              ((CQState.tensor ρ (CQState.tensorPower ρ k)).stateMap p).trace := by
        refine Finset.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => X)).symm
          (fun _ => by simp) (fun f _ => ?_)
        have hsymm :
            (Fin.consEquiv (fun _ : Fin (k + 1) => X)).symm f = (f 0, Fin.tail f) :=
          Fin.consEquiv_symm_apply _ f
        rw [hsymm]
        rfl
      rw [hreindex, CQState.tensor_sum_trace, hρ_norm, ih]
      ring

/-- **n-fold tensor power of a sub-density operator.** Specialization of
`SubDensityOp.tensorFinProd` to a constant family. -/
noncomputable def InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
    {n : ℕ} [NeZero n] (σ : SubDensityOp n) (n_copies : ℕ) :
    SubDensityOp (n ^ n_copies) :=
  SubDensityOp.tensorFinProd n_copies (fun _ => σ)

/-- **Block factorization of the CQ tensor-power into a `tensorFinProd`.**
The underlying operator of `(CQState.tensorPower ρ m).stateMap xs` is the finite
tensor product of the single-copy blocks `ρ.stateMap (xs j)`. This mirrors
`CQState.tensorPower_sum_trace`, but factors `toOp` rather than `trace`. -/
lemma InfoTheory.SmoothMinEntropy.CQState.tensorPower_stateMap_toOp
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n] (ρ : CQState X n) (m : ℕ) :
    ∀ xs : Fin m → X,
      ((CQState.tensorPower ρ m).stateMap xs).toOp =
        (SubDensityOp.tensorFinProd m (fun j => ρ.stateMap (xs j))).toOp := by
  induction m with
  | zero => intro xs; rfl
  | succ k ih =>
      intro xs
      apply SubDensityOp.castDim_toOp_congr
      change (ρ.stateMap (xs 0)).toOp ⊗
          ((CQState.tensorPower ρ k).stateMap (fun i => xs i.succ)).toOp =
        (ρ.stateMap (xs 0)).toOp ⊗
          (SubDensityOp.tensorFinProd k
            (fun j => ρ.stateMap (xs (Fin.succ j)))).toOp
      rw [ih (fun i => xs i.succ)]

/-! ### Helpers used by the penalty constants -/

/-- The number of classical outcomes with positive probability weight. In the
CQ encoding this plays the role of `rank(ρ_A)`: the size of the support of
the classical marginal. (For a CQ state the classical register is a copy of
the quantum support of `ρ_A`, so `|supp p_X|` and `rank ρ_A` agree.) -/
noncomputable def InfoTheory.SmoothMinEntropy.CQState.classicalRank
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) : ℕ :=
  (Finset.univ.filter (fun x => 0 < (ρ.stateMap x).trace)).card

/-- The real part of `tr(ρ_{XB}² · (id_X ⊗ σ_B^{-1}))` in the CQ encoding:
`∑_x tr((ρ.stateMap x)² · σ.toOp ^ (-1 : ℝ)).re`. Here `σ_B^{-1}` is the CFC real
power `σ.toOp ^ (-1 : ℝ)` (Moore–Penrose pseudo-inverse): it inverts the nonzero
eigenvalues of `σ` and is `0` on `ker σ = (supp σ)ᗮ`. The classical register is
diagonal, so the `id_X ⊗ ·` factor splits the trace into a sum over `x`, each
block contributing `tr(ρ_x · ρ_x · σ_B^{-1})`. -/
noncomputable def InfoTheory.SmoothMinEntropy.CQState.tracedSquareTimesInvFactor
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) : ℝ :=
  (∑ x : X,
      ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp * σ.toOp ^ (-1 : ℝ)).trace).re

/-- Hartley (Rényi-0) entropy `H_max(ρ_X) := log₂ (classicalRank ρ)` on nonempty support.
This matches Renner's `H_max` on the classical marginal: it equals the
logarithm of the size of the support of the classical distribution. -/
noncomputable def InfoTheory.SmoothMinEntropy.CQState.classicalHmax
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (_hρ : 1 ≤ ρ.classicalRank) : ℝ :=
  Real.logb 2 (ρ.classicalRank : ℝ)

/-- The library's shared noise factor for the Renner AEP correction:
`√((log₂(1/ε) + 1) / n_copies)` (Renner 2005, arXiv:quant-ph/0512258v2,
`main.tex:6288`–`:6289`). The printed theorem `thm:Hmincondrep` at `:4572`
instead places `+1` outside the fraction. The rate interpretation requires `n_copies > 0`
and `0 < ε < 1`; the scalar formula is total, using Mathlib's conventions for `Real.logb`,
inversion and square roots. -/
noncomputable def InfoTheory.SmoothMinEntropy.noiseFactor
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt ((Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ))

namespace InfoTheory.SmoothMinEntropy

/-- Renner's large-block regime predicate: `noiseFactor n_copies ε ≤ (2 − log 2)/2`,
the band in which the clamped optimal tilt still meets Renner's discarded-mass
budget `(ε/2)²` (main.tex:4575–4665, eq:tracelowbound). Its negation is the
small-block regime, where the classical correction `δ_iidAEP_class` exceeds
`H_max`, the entropy floor is already negative, and the bound holds trivially
because the smooth-min-entropy rate is nonnegative. -/
def iidAEPLargeBlockRegime (n_copies : ℕ) (ε : ℝ) : Prop :=
  noiseFactor n_copies ε ≤ (2 - Real.log 2) / 2

/-! ### Penalty constants

Renner's printed δ for `thm:Hmincondrep` is
`2 log(rank(ρ_A) + tr(ρ_{AB}²·(id⊗σ_B⁻¹)) + 2) · √(log(1/ε)/n + 1)`.
The printed corollary uses `(2 H_max(ρ_X) + 3) · √(log(1/ε)/n + 1)`.

In this CQ encoding the role of `rank(ρ_A)` is played by
`CQState.classicalRank`, and the trace term is given by
`CQState.tracedSquareTimesInvFactor`. The library uses the `√((log₂(1/ε)+1)/n)`
grouping from Renner's application at lines 6288–6289, defined as `noiseFactor`. -/

/-- Library correction associated with `thm:Hmincondrep` (Renner thesis line 4561):
`2 · log₂(rank(ρ_A) + tr(ρ_{AB}² · (id_A ⊗ σ_B⁻¹)) + 2) · √((log₂(1/ε)+1)/n)`.

In the CQ encoding `rank(ρ_A)` is `CQState.classicalRank ρ` and the trace
term is `CQState.tracedSquareTimesInvFactor ρ σ`. The right factor is
`noiseFactor n_copies ε`, with `+1` inside the fraction as in lines 6288–6289;
the printed theorem places it outside. The definition is total in `ε` and `σ`
(using Mathlib's conventions for `Real.logb` and for CFC real powers, where the exponent `−1`
gives the Moore–Penrose inverse). -/
noncomputable def δ_iidAEP_general
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  2 * Real.logb 2
        ((ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2)
      * noiseFactor n_copies ε

/-- Library correction associated with `cor:Hmincondrepclass` (Renner thesis line 4986):
`(2 · H_max(ρ_X) + 4) · √((log₂(1/ε)+1)/n)`.

For positive classical rank, `H_max(ρ_X)` is `CQState.classicalHmax ρ hρ`.
The scalar coefficient uses `log₂(classicalRank ρ)` directly and is total at rank zero;
its entropy interpretation requires positive rank. The right factor is `noiseFactor n_copies ε`,
using the grouping at lines 6288–6289; the printed corollary places `+1` outside the fraction.

Note: Renner's literal constant is `3`, but a clean elementary bound here
needs `4` (since `2·log₂(rank + tr + 2) ≤ 2·log₂(rank) + 4` already saturates
at `rank = 1`, `tr = 1`, where `2·log₂ 4 = 4`). This is harmless: the form
`(2·H_max + O(1))·noiseFactor` is what is used downstream. -/
noncomputable def δ_iidAEP_class
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n)
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (2 * Real.logb 2 (ρ.classicalRank : ℝ) + 4) * noiseFactor n_copies ε

/-! ### Entropy bridges

Bridges from `CQState` to `DensityOp` so that `vonNeumannEntropy` can be
invoked in the theorem statements. These live at the global
`InfoTheory.SmoothMinEntropy.CQState` namespace (via `_root_`) and are
defined before the penalty-constant block below so that
`δ_iidAEP_general` can reference `ρ.quantumMarginalDensityOp`. -/

/-- Quantum marginal of a normalized CQ state, viewed as a `DensityOp`. -/
noncomputable def _root_.InfoTheory.SmoothMinEntropy.CQState.quantumMarginalDensityOp
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    DensityOp n where
  toPosSemidefOp := ρ.quantumMarginal.toPosSemidefOp
  trace_one := by
    change ρ.quantumMarginalOp.trace = 1
    unfold InfoTheory.SmoothMinEntropy.CQState.quantumMarginalOp
    rw [Matrix.trace_sum]
    simp_rw [SubDensityOp.trace_complex_eq]
    rw [← Complex.ofReal_sum, hρ_norm, Complex.ofReal_one]

/-- Joint density of a normalized CQ state on `H_X ⊗ H_n`, viewed as a
`DensityOp` on dimension `n * card X`.

The underlying PSD/Hermitian data is reused from `ρ.toJointDensity` (a
`SubDensityOp`). The trace-one upgrade combines:
* the real-part identity `CQState.toJointDensity_trace_eq_sum` with the
  normalization hypothesis `hρ_norm`,
* the fact that the complex trace of any `SubDensityOp` equals its real-valued
  trace coerced to `ℂ` (`SubDensityOp.trace_complex_eq`). -/
noncomputable def _root_.InfoTheory.SmoothMinEntropy.CQState.toJointDensityOp
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    DensityOp (n * Fintype.card X) where
  toPosSemidefOp := ρ.toJointDensity.toPosSemidefOp
  trace_one := by
    have h_re : ρ.toJointDensity.trace = 1 :=
      (CQState.toJointDensity_trace_eq_sum ρ).trans hρ_norm
    rw [ρ.toJointDensity.trace_complex_eq, h_re, Complex.ofReal_one]

/-! ### Main statements -/

/-- The extended smooth-min-entropy rate of a positive tensor block length. -/
noncomputable def iidAEPSmoothRate
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] (ε : ℝ) : ENNReal :=
  smoothMinEntropy ε (CQState.tensorPower ρ n_copies)
    (SubDensityOp.tensorPower (DensityOp.toSubDensityOp σ) n_copies) / n_copies

/-- A signed per-copy floor is equivalent to its completed block floor in extended entropy. -/
theorem ofReal_le_iidAEPSmoothRate_iff
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] (ε k : ℝ) :
    ENNReal.ofReal k ≤ iidAEPSmoothRate ρ σ n_copies ε ↔
      ENNReal.ofReal ((n_copies : ℝ) * k) ≤
        smoothMinEntropy ε (CQState.tensorPower ρ n_copies)
          (SubDensityOp.tensorPower (DensityOp.toSubDensityOp σ) n_copies) := by
  have hn : (n_copies : ENNReal) ≠ 0 := by
    exact_mod_cast NeZero.ne n_copies
  rw [iidAEPSmoothRate,
    ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (by simp)),
    ENNReal.ofReal_mul (Nat.cast_nonneg n_copies), ENNReal.ofReal_natCast, mul_comm]

/-- Library single-copy von-Neumann/relative-entropy floor associated with Renner
`thm:Hmincondrep`, using the correction `δ_iidAEP_general`. -/
noncomputable def iidAEPEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
    - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)
    - δ_iidAEP_general ρ σ n_copies ε
    - InfoTheory.RelativeEntropy.relativeEntropyReal
        (ρ.quantumMarginalDensityOp hρ_norm) σ

/-- Tensor-power CQ state on the left side of Renner `thm:Hmincondrep`. -/
noncomputable def iidAEPTensorState
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ) :
    CQState (Fin n_copies → X) (n ^ n_copies) :=
  InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ n_copies

/-- Tensor-power reference operator on the conditioning register. -/
noncomputable def iidAEPTensorReference
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    SubDensityOp (n ^ n_copies) :=
  InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
    (DensityOp.toSubDensityOp σ) n_copies

/-- A signed block floor certified by a nearby CQ state bounds the extended per-copy rate. -/
theorem iidAEPSmoothRate_ge_of_blockFloor_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n] (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] (ε F : ℝ)
    (τ : CQState (Fin n_copies → X) (n ^ n_copies))
    (h_smooth : CQState.purifiedDistance (iidAEPTensorState ρ n_copies) τ ≤ ε)
    (h_entropy : ENNReal.ofReal ((n_copies : ℝ) * F) ≤
      conditionalMinEntropy τ (iidAEPTensorReference σ n_copies)) :
    ENNReal.ofReal F ≤ iidAEPSmoothRate ρ σ n_copies ε := by
  apply (ofReal_le_iidAEPSmoothRate_iff ρ σ n_copies ε F).mpr
  exact smoothMinEntropy_ge_of_hmin_approx (iidAEPTensorState ρ n_copies)
    τ (iidAEPTensorReference σ n_copies) ((n_copies : ℝ) * F) h_smooth h_entropy

/-- The block-length-scaled entropy floor that a smoothed witness must attain
before the final division by `n_copies`. -/
noncomputable def iidAEPBlockEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (n_copies : ℝ) * iidAEPEntropyFloor ρ hρ_norm σ n_copies ε

/-- Projector and smoothed-state data produced by the positive-smoothing
spectral truncation. -/
structure IIDAEPProjectorWitnessData (X : Type*) [Fintype X]
    (n n_copies : ℕ) where
  /-- The typical-subspace projector used to truncate each tensor-power block. -/
  truncationProjector : Op (n ^ n_copies)
  /-- The truncated/smoothed tensor-power CQ state. -/
  smoothedState : CQState (Fin n_copies → X) (n ^ n_copies)

/-- Orthogonal spectral increments and eigenvalue labels for the tensor-power
reference. The ordering convention is imposed by the predicates below, not by
this data record. -/
structure IIDAEPReferenceSpectrumData (n n_copies : ℕ) where
  /-- Eigenvalue labels for the tensor-power reference spectrum. -/
  referenceEigenvalue : Fin (n ^ n_copies) → ℝ
  /-- Orthogonal spectral increments resolving the tensor-power reference. -/
  spectralProjector : Fin (n ^ n_copies) → Op (n ^ n_copies)

/-- Renner cumulative spectral-resolution data for the tensor-power reference. -/
structure IIDAEPCumulativeResolutionData (n n_copies : ℕ) where
  /-- Renner's `β_z` coefficients for the cumulative spectral projectors. -/
  betaCoefficient : Fin (n ^ n_copies) → ℝ
  /-- Cumulative spectral projectors `B_z` of the tensor-power reference. -/
  cumulativeProjector : Fin (n ^ n_copies) → Op (n ^ n_copies)

/-- Spectral-cut data selecting the retained cumulative projector. -/
structure IIDAEPSpectralCutData (n n_copies : ℕ) where
  /-- Index of the cumulative projector retained by the spectral cut. -/
  cutIndex : Fin (n ^ n_copies)
  /-- Entropy threshold defining the spectral cut. -/
  entropyThreshold : ℝ

/-- Scalar data used by Renner's `r_t` estimate. -/
structure IIDAEPRtData where
  /-- Chernoff/MGF tilt used in the `r_t` estimate. -/
  tilt : ℝ

/-- Explicit data carried by the spectral-projector construction in Renner's
proof of `thm:Hmincondrep`.

The essential objects are separated into projector, reference-spectrum,
cumulative-resolution, spectral-cut, and `r_t` records. The mathematical
properties they satisfy are kept as named predicates and theorem leaves below. -/
structure IIDAEPSpectralWitness (X : Type*) [Fintype X]
    (n n_copies : ℕ) where
  /-- Projector sandwich and smoothed CQ state. -/
  projectorData : IIDAEPProjectorWitnessData X n n_copies
  /-- Eigenvalue labels and orthogonal increments for the reference. -/
  referenceSpectrum : IIDAEPReferenceSpectrumData n n_copies
  /-- Cumulative projectors and Renner `β_z` coefficients. -/
  cumulativeResolution : IIDAEPCumulativeResolutionData n n_copies
  /-- Spectral cut selecting the retained subspace. -/
  spectralCut : IIDAEPSpectralCutData n n_copies
  /-- Scalar `r_t` parameter data. -/
  rtData : IIDAEPRtData

namespace IIDAEPSpectralWitness

/-- The witness's truncation projector, projected out of W.projectorData. -/
abbrev truncationProjector
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : Op (n ^ n_copies) :=
  W.projectorData.truncationProjector

/-- The witness's smoothed CQ state, projected out of W.projectorData. -/
abbrev smoothedState
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    CQState (Fin n_copies → X) (n ^ n_copies) :=
  W.projectorData.smoothedState

/-- The witness's reference eigenvalue labels, projected out of
W.referenceSpectrum. -/
abbrev referenceEigenvalue
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    Fin (n ^ n_copies) → ℝ :=
  W.referenceSpectrum.referenceEigenvalue

/-- The witness's reference spectral projectors, projected out of
W.referenceSpectrum. -/
abbrev spectralProjector
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    Fin (n ^ n_copies) → Op (n ^ n_copies) :=
  W.referenceSpectrum.spectralProjector

/-- The witness's Renner `β_z` coefficients, projected out of
W.cumulativeResolution. -/
abbrev betaCoefficient
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    Fin (n ^ n_copies) → ℝ :=
  W.cumulativeResolution.betaCoefficient

/-- The witness's cumulative resolution projectors, projected out of
W.cumulativeResolution. -/
abbrev cumulativeProjector
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    Fin (n ^ n_copies) → Op (n ^ n_copies) :=
  W.cumulativeResolution.cumulativeProjector

/-- The witness's spectral-cut index, projected out of W.spectralCut. -/
abbrev cutIndex
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    Fin (n ^ n_copies) :=
  W.spectralCut.cutIndex

/-- The witness's entropy threshold, projected out of W.spectralCut. -/
abbrev entropyThreshold
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  W.spectralCut.entropyThreshold

/-- The witness's `r_t` tilt parameter, projected out of W.rtData. -/
abbrev rtTilt
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  W.rtData.tilt

end IIDAEPSpectralWitness

/-- Projector-sandwich part of the spectral construction: the truncation
operator is a Hermitian projector and every CQ block of the witness is obtained
by sandwiching the corresponding tensor-power block. -/
def iidAEPProjectorSandwich
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  W.truncationProjector * W.truncationProjector = W.truncationProjector ∧
    W.truncationProjector† = W.truncationProjector ∧
    ∀ xs : Fin n_copies → X,
      (W.smoothedState.stateMap xs).toOp =
        W.truncationProjector *
          ((iidAEPTensorState ρ n_copies).stateMap xs).toOp *
        W.truncationProjector

/-- The smoothed witness is a blockwise substate of the original tensor-power
CQ state. This is the order-theoretic input used by the purified-distance
trace-gap estimate. -/
def iidAEPSmoothedStateDominated
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  ∀ xs : Fin n_copies → X,
    opLe (W.smoothedState.stateMap xs).toOp
      ((iidAEPTensorState ρ n_copies).stateMap xs).toOp

/-- Canonical eigenvalue labels for the tensor-power reference, extracted from
the positive semidefinite spectral theorem. These labels are independent of the
projector-sandwich witness until the later spectral-increment and action
construction layers tie them to explicit projectors. -/
noncomputable def iidAEPReferenceEigenvalueLabels
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    Fin (n ^ n_copies) → ℝ :=
  let τ := iidAEPTensorReference σ n_copies
  τ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues

lemma iidAEPReferenceEigenvalueLabels_nonneg
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    ∀ z : Fin (n ^ n_copies),
      0 ≤ iidAEPReferenceEigenvalueLabels σ n_copies z := by
  intro z
  unfold iidAEPReferenceEigenvalueLabels
  exact
    (Quantum.Operators.posSemidefOp_implies_mathlib
      (iidAEPTensorReference σ n_copies).toPosSemidefOp).eigenvalues_nonneg z

/-- Replace only the reference eigenvalue labels of a spectral witness by the
canonical tensor-reference labels. The core projector/smoothed-state data are
preserved exactly; projector increments, cumulative projectors, cuts, and
`r_t` data are constructed by later layers. -/
noncomputable def iidAEPWitnessWithReferenceEigenvalues
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    IIDAEPSpectralWitness X n n_copies where
  projectorData := W.projectorData
  referenceSpectrum :=
    { referenceEigenvalue := iidAEPReferenceEigenvalueLabels σ n_copies
      spectralProjector := W.spectralProjector }
  cumulativeResolution := W.cumulativeResolution
  spectralCut := W.spectralCut
  rtData := W.rtData

/-- Reference eigenvalue setup for a witness: its labels are exactly the
canonical tensor-reference eigenvalues and hence are nonnegative. Orthogonal
increments and reference action are intentionally not part of this layer. -/
def iidAEPReferenceEigenvalueSetup
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  W.referenceEigenvalue = iidAEPReferenceEigenvalueLabels σ n_copies ∧
    ∀ z : Fin (n ^ n_copies), 0 ≤ W.referenceEigenvalue z

lemma iidAEPWitnessWithReferenceEigenvalues_referenceEigenvalueSetup
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceEigenvalueSetup σ
      (iidAEPWitnessWithReferenceEigenvalues σ W) := by
  refine ⟨rfl, ?_⟩
  intro z
  exact iidAEPReferenceEigenvalueLabels_nonneg σ n_copies z

/-- The rank-one projectors formed from a Hermitian eigenvector basis are
nonzero orthogonal Hermitian idempotents and resolve the identity. -/
lemma isHermitian_eigenvectorBasis_rankOneProjectors_increments
    {d : ℕ} [NeZero d] {M : Op d} (hM : M.IsHermitian) :
    (∀ z : Fin d,
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp) *
          Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp) =
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp)) ∧
      (∀ z : Fin d,
        (Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp))ᴴ =
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp)) ∧
      (∀ z : Fin d,
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp) ≠ 0) ∧
      (∀ z z' : Fin d, z ≠ z' →
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp) *
          Matrix.vecMulVec ((hM.eigenvectorBasis z').ofLp)
            (star (hM.eigenvectorBasis z').ofLp) = 0) ∧
      (∑ z : Fin d,
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp)) = 1 := by
  classical
  have hdot : ∀ i j : Fin d,
      star ((hM.eigenvectorBasis i).ofLp) ⬝ᵥ
          ((hM.eigenvectorBasis j).ofLp) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [dotProduct_comm]
    have h := orthonormal_iff_ite.mp hM.eigenvectorBasis.orthonormal i j
    rw [← EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot z z]
    simp
  · intro z
    rw [Matrix.conjTranspose_vecMulVec]
    simp
  · intro z
    have hvec : ((hM.eigenvectorBasis z).ofLp) ≠ 0 := by
      intro hzero
      exact hM.eigenvectorBasis.orthonormal.ne_zero z
        (by ext j; exact congr_fun hzero j)
    exact Matrix.vecMulVec_ne_zero hvec (star_ne_zero.mpr hvec)
  · intro z z' hzz'
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot z z']
    simp [hzz']
  · set U : Matrix (Fin d) (Fin d) ℂ :=
      (↑hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU_def
    have hUstar : Uᴴ * U = 1 := by
      simpa [hU_def, star_eq_conjTranspose] using
        UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    have hUU : U * Uᴴ = 1 := by
      exact
        ((Matrix.mul_eq_one_comm_of_card_eq
            (m := Fin d) (n := Fin d) (R := ℂ)
            (A := Uᴴ) (B := U) (by rfl)).mp hUstar)
    ext a b
    calc
      (∑ z : Fin d,
          Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp)) a b
          = ∑ z : Fin d,
              ((hM.eigenvectorBasis z).ofLp a) *
                star ((hM.eigenvectorBasis z).ofLp b) := by
            simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
      _ = (U * Uᴴ) a b := by
            simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_def]
      _ = (1 : Matrix (Fin d) (Fin d) ℂ) a b := by
            rw [hUU]

/-- The Hermitian operator `M` acts diagonally on its rank-one eigenvector
projectors `P_z = |e_z⟩⟨e_z|`: it is reconstructed as the eigenvalue-weighted
sum of these projectors, and both `M * P_z` and `P_z * M` equal `λ_z • P_z`.
This is the action/diagonalization companion of
`isHermitian_eigenvectorBasis_rankOneProjectors_increments`. -/
lemma isHermitian_eigenvectorBasis_rankOneProjectors_action
    {d : ℕ} [NeZero d] {M : Op d} (hM : M.IsHermitian) :
    (M = ∑ z : Fin d,
        (hM.eigenvalues z : ℂ) •
          Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp)) ∧
      ∀ z : Fin d,
        (M *
            Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
              (star (hM.eigenvectorBasis z).ofLp) =
          (hM.eigenvalues z : ℂ) •
            Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
              (star (hM.eigenvectorBasis z).ofLp)) ∧
        (Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
              (star (hM.eigenvectorBasis z).ofLp) * M =
          (hM.eigenvalues z : ℂ) •
            Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
              (star (hM.eigenvectorBasis z).ofLp)) := by
  classical
  -- Rank-one projectors are Hermitian.
  have hPherm : ∀ z : Fin d,
      (Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp))ᴴ =
        Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star (hM.eigenvectorBasis z).ofLp) := by
    intro z
    rw [Matrix.conjTranspose_vecMulVec]
    simp
  -- Left action: `M * P_z = λ_z • P_z` from the eigenvector equation.
  have hleft : ∀ z : Fin d,
      M *
          Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp) =
        (hM.eigenvalues z : ℂ) •
          Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
            (star (hM.eigenvectorBasis z).ofLp) := by
    intro z
    rw [Matrix.mul_vecMulVec, hM.mulVec_eigenvectorBasis]
    ext a b
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul]
    ring
  refine ⟨DistTraceBoundSpectral.isHermitian_eq_sum_smul_vecMulVec hM, ?_⟩
  intro z
  refine ⟨hleft z, ?_⟩
  -- Right action by conjugate-transposing the left action.
  have h := congrArg Matrix.conjTranspose (hleft z)
  rw [Matrix.conjTranspose_mul, hM, hPherm z, Matrix.conjTranspose_smul,
    hPherm z] at h
  simpa [Complex.conj_ofReal] using h

/-- Canonical rank-one spectral increment of the tensor-power reference,
formed from the Hermitian eigenvector basis of the reference operator. -/
noncomputable def iidAEPReferenceSpectralIncrementProjector
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ)
    (z : Fin (n ^ n_copies)) : Op (n ^ n_copies) :=
  let τ := iidAEPTensorReference σ n_copies
  let hτ := τ.toPosSemidefOp.toHermitianOp.isHermitian
  Matrix.vecMulVec ((hτ.eigenvectorBasis z).ofLp)
    (star (hτ.eigenvectorBasis z).ofLp)

/-- The explicit tensor-reference increment projectors are nonzero
orthogonal Hermitian idempotents and resolve the identity. -/
lemma iidAEPReferenceSpectralIncrementProjector_increments
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ)
    [NeZero (n ^ n_copies)] :
    (∀ z : Fin (n ^ n_copies),
        iidAEPReferenceSpectralIncrementProjector σ n_copies z *
          iidAEPReferenceSpectralIncrementProjector σ n_copies z =
        iidAEPReferenceSpectralIncrementProjector σ n_copies z) ∧
      (∀ z : Fin (n ^ n_copies),
        (iidAEPReferenceSpectralIncrementProjector σ n_copies z)ᴴ =
        iidAEPReferenceSpectralIncrementProjector σ n_copies z) ∧
      (∀ z : Fin (n ^ n_copies),
        iidAEPReferenceSpectralIncrementProjector σ n_copies z ≠ 0) ∧
      (∀ z z' : Fin (n ^ n_copies), z ≠ z' →
        iidAEPReferenceSpectralIncrementProjector σ n_copies z *
          iidAEPReferenceSpectralIncrementProjector σ n_copies z' = 0) ∧
      (∑ z : Fin (n ^ n_copies),
        iidAEPReferenceSpectralIncrementProjector σ n_copies z) = 1 := by
  -- the increments are by definition the rank-one eigenprojectors of the Hermitian reference
  exact isHermitian_eigenvectorBasis_rankOneProjectors_increments
    (iidAEPTensorReference σ n_copies).toPosSemidefOp.toHermitianOp.isHermitian

/-- The tensor-power reference acts diagonally on its canonical rank-one
spectral increments, and is reconstructed from the eigenvalue-weighted
increments. This is the raw matrix spectral-action fact phrased directly in
terms of the canonical eigenvalue labels and increment projectors. -/
lemma iidAEPReferenceSpectralIncrementProjector_action
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    (iidAEPTensorReference σ n_copies).toOp =
        ∑ z : Fin (n ^ n_copies),
          (iidAEPReferenceEigenvalueLabels σ n_copies z : ℂ)
            • iidAEPReferenceSpectralIncrementProjector σ n_copies z
      ∧ ∀ z : Fin (n ^ n_copies),
          (iidAEPTensorReference σ n_copies).toOp
              * iidAEPReferenceSpectralIncrementProjector σ n_copies z =
            (iidAEPReferenceEigenvalueLabels σ n_copies z : ℂ)
              • iidAEPReferenceSpectralIncrementProjector σ n_copies z
        ∧ iidAEPReferenceSpectralIncrementProjector σ n_copies z
              * (iidAEPTensorReference σ n_copies).toOp =
            (iidAEPReferenceEigenvalueLabels σ n_copies z : ℂ)
              • iidAEPReferenceSpectralIncrementProjector σ n_copies z := by
  -- the labels and increments are by definition the eigenvalues and eigenprojectors
  exact isHermitian_eigenvectorBasis_rankOneProjectors_action
    (iidAEPTensorReference σ n_copies).toPosSemidefOp.toHermitianOp.isHermitian

/-- Canonical reference-spectrum data for the tensor-power reference: the
Hermitian spectral eigenvalue labels together with the corresponding
rank-one eigenvector projectors. -/
noncomputable def iidAEPReferenceSpectrumData
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    IIDAEPReferenceSpectrumData n n_copies where
  referenceEigenvalue := iidAEPReferenceEigenvalueLabels σ n_copies
  spectralProjector :=
    iidAEPReferenceSpectralIncrementProjector σ n_copies

/-- Replace the full reference-spectrum layer of a witness by the canonical
tensor-reference eigenvalue labels and rank-one spectral increments. The
projector sandwich, cumulative resolution, spectral cut, and `r_t` data are
unchanged. -/
noncomputable def iidAEPWitnessWithReferenceSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    IIDAEPSpectralWitness X n n_copies where
  projectorData := W.projectorData
  referenceSpectrum := iidAEPReferenceSpectrumData σ n_copies
  cumulativeResolution := W.cumulativeResolution
  spectralCut := W.spectralCut
  rtData := W.rtData

lemma iidAEPWitnessWithReferenceSpectrum_referenceEigenvalueSetup
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceEigenvalueSetup σ
      (iidAEPWitnessWithReferenceSpectrum σ W) := by
  refine ⟨rfl, ?_⟩
  intro z
  exact iidAEPReferenceEigenvalueLabels_nonneg σ n_copies z

/-- The spectral radius parameter entering Renner's `r_t` bound. -/
noncomputable def iidAEPSpectralRadius
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) : ℝ :=
  (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2

/-- Renner's optimal Chernoff tilt for the discarded-mass exponent
(main.tex:4965), **clamped into the `lem:rtbound` range** (main.tex:10487):
`τ* = −min(δ · log 2 / (log μ)², log 2 / log μ)`, where
`δ = δ_iidAEP_general ρ σ n_copies ε` is the per-block bit penalty and
`μ = iidAEPSpectralRadius ρ σ ≥ 2` is Renner's `γ + 2` base.

The unclamped Chernoff optimum `−δ·log 2/(log μ)²` minimizes the
entropy-cancelled exponent `rt(t, μ) + t·δ·log 2` over `t ≤ 0`, but at that tilt
`|s·log μ| = 2·noiseFactor` (where `s = −τ*`), which leaves Renner's `r_t` gate
`|s·log μ| ≤ log 2` (`lem:rtbound`, the single-copy MGF leaf hypothesis) only in
the regime `noiseFactor ≤ log 2 / 2`.  Clamping the magnitude at `log 2 / log μ`
(so `s·log μ ≤ log 2` **always**) keeps the tilt in range for every `n` and `ε`,
at the cost of using the boundary tilt outside the optimal regime.  Since
`μ ≥ 2 > 1`, `log μ > 0`, so both arguments of `min` are positive and the tilt is
still `≤ 0`. -/
noncomputable def iidAEPOptimalTilt
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  -(min (δ_iidAEP_general ρ σ n_copies ε * Real.log 2
            / (Real.log (iidAEPSpectralRadius ρ σ)) ^ 2)
        (Real.log 2 / Real.log (iidAEPSpectralRadius ρ σ)))

/-- Trace-defect budget sufficient for an `ε` purified-distance bound via
`P(ρ, ρ̄) ≤ sqrt (2 · traceDefect)`. -/
def iidAEPSmoothingTraceBudget (ε : ℝ) : ℝ :=
  ε ^ 2 / 2

lemma iidAEPSmoothingTraceBudget_nonneg {ε : ℝ} (_hε : 0 ≤ ε) :
    0 ≤ iidAEPSmoothingTraceBudget ε := by
  unfold iidAEPSmoothingTraceBudget
  nlinarith [sq_nonneg ε]

lemma iidAEP_sqrt_two_mul_smoothingTraceBudget {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (2 * iidAEPSmoothingTraceBudget ε) = ε := by
  unfold iidAEPSmoothingTraceBudget
  have hcalc : 2 * (ε ^ 2 / 2) = ε ^ 2 := by ring
  rw [hcalc, Real.sqrt_sq_eq_abs, abs_of_nonneg hε]

/-- Trace mass lost by replacing the tensor-power state by the spectral
projector sandwich. -/
noncomputable def iidAEPTraceDefect
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  (∑ xs : Fin n_copies → X,
      ((iidAEPTensorState ρ n_copies).stateMap xs).trace)
    - ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace

/-- The entropy-cancelled tilted discarded-mass exponent at tilt `t = W.rtTilt`,
before Renner's quadratic relaxation (main.tex:4865–4960):
`n_copies · (rt(t,μ) + t·δ·log 2)`, with `μ = iidAEPSpectralRadius ρ σ` and
`δ = δ_iidAEP_general ρ σ n_copies ε`. -/
noncomputable def iidAEPRtExponent
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  (n_copies : ℝ) *
    (rt W.rtTilt (iidAEPSpectralRadius ρ σ)
      + W.rtTilt * δ_iidAEP_general ρ σ n_copies ε * Real.log 2)

/-- Renner's proven discarded-mass tail bound (main.tex:4962):
`2 ^ (−n_copies · δ² / (2 · (log₂ μ)²))`, where
`δ = δ_iidAEP_general ρ σ n_copies ε` and `μ = iidAEPSpectralRadius ρ σ`
is Renner's `γ + 2` base. This is the right-hand side after the quadratic
relaxation `rt(t,μ) ≤ ½ t²(log μ)²` at the optimal tilt. -/
noncomputable def iidAEPRtErrorBound
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (_W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  (2 : ℝ) ^ (-(n_copies : ℝ) * δ_iidAEP_general ρ σ n_copies ε ^ 2
    / (2 * Real.logb 2 (iidAEPSpectralRadius ρ σ) ^ 2))

/-- Orthogonal spectral increments for the tensor-power reference. The
nonzero-increment condition prevents arbitrary eigenvalue labels from being
attached to zero projectors. -/
def iidAEPReferenceSpectralIncrements
    {X : Type*} [Fintype X] {n : ℕ}
    {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  (∀ z : Fin (n ^ n_copies),
      W.spectralProjector z * W.spectralProjector z =
        W.spectralProjector z) ∧
    (∀ z : Fin (n ^ n_copies),
      (W.spectralProjector z)† = W.spectralProjector z) ∧
    (∀ z : Fin (n ^ n_copies), W.spectralProjector z ≠ 0) ∧
    (∀ z z' : Fin (n ^ n_copies), z ≠ z' →
      W.spectralProjector z * W.spectralProjector z' = 0) ∧
    (∑ z : Fin (n ^ n_copies), W.spectralProjector z) = 1

/-- The tensor-power reference acts diagonally on the explicit spectral
increments, and is reconstructed from the eigenvalue-weighted increments. -/
def iidAEPReferenceSpectralAction
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  (iidAEPTensorReference σ n_copies).toOp =
      ∑ z : Fin (n ^ n_copies),
        (W.referenceEigenvalue z : ℂ) • W.spectralProjector z ∧
    ∀ z : Fin (n ^ n_copies),
      (iidAEPTensorReference σ n_copies).toOp *
          W.spectralProjector z =
        (W.referenceEigenvalue z : ℂ) • W.spectralProjector z ∧
      W.spectralProjector z *
          (iidAEPTensorReference σ n_copies).toOp =
        (W.referenceEigenvalue z : ℂ) • W.spectralProjector z

/-- Renner's cumulative projectors `B_z`, linked to the orthogonal spectral
increments and the `β_z` coefficients by `q_z = ∑_{z' ≤ z} β_z'`. -/
def iidAEPReferenceCumulativeResolution
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
    (∀ z : Fin (n ^ n_copies), 0 ≤ W.betaCoefficient z) ∧
    (∀ z : Fin (n ^ n_copies),
      W.cumulativeProjector z =
        (Finset.univ.filter
          (fun z' : Fin (n ^ n_copies) => z ≤ z')).sum
          (fun z' => W.spectralProjector z')) ∧
    (∀ z : Fin (n ^ n_copies),
      W.cumulativeProjector z * W.cumulativeProjector z =
        W.cumulativeProjector z) ∧
    (∀ z : Fin (n ^ n_copies),
      (W.cumulativeProjector z)† = W.cumulativeProjector z) ∧
    (∀ z z' : Fin (n ^ n_copies), z ≤ z' →
      W.cumulativeProjector z' * W.cumulativeProjector z =
        W.cumulativeProjector z') ∧
    (iidAEPTensorReference σ n_copies).toOp =
      ∑ z : Fin (n ^ n_copies),
        (W.betaCoefficient z : ℂ) • W.cumulativeProjector z ∧
    ∀ z : Fin (n ^ n_copies),
      W.referenceEigenvalue z =
        (Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z' ≤ z)).sum
          (fun z' => W.betaCoefficient z')

/-- Spectral decomposition data for the tensor-power reference. This contains
both the orthogonal increment resolution and Renner's cumulative projector
expansion, so eigenvalue labels are tied to nonzero spectral increments and to
the operator action of the reference. -/
def iidAEPReferenceSpectralDecomposition
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  (∀ z : Fin (n ^ n_copies), 0 ≤ W.referenceEigenvalue z) ∧
    iidAEPReferenceSpectralIncrements W ∧
    iidAEPReferenceSpectralAction σ n_copies W ∧
    iidAEPReferenceCumulativeResolution σ n_copies W

/-! ### Sorted reference spectrum and Renner cumulative resolution

The canonical eigenvalue labels carry no ordering, so the discrete increments
`β_z = λ_z - λ_{z-1}` need not be nonnegative. We reindex the reference spectrum
into nondecreasing order via `Tuple.sort`; the reindexed increment family is
still an orthogonal family of nonzero Hermitian idempotents resolving the
identity with the same diagonal action, and now the increments are nonnegative
differences. The algebraic content of the cumulative resolution is
isolated in the InfoTheory.SmoothMinEntropy.IIDAEPCumulative namespace below. -/

open InfoTheory.SmoothMinEntropy.IIDAEPCumulative

/-- Permutation sorting the canonical reference eigenvalues into nondecreasing
order. -/
noncomputable def iidAEPReferenceSortPerm
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    Equiv.Perm (Fin (n ^ n_copies)) :=
  Tuple.sort (iidAEPReferenceEigenvalueLabels σ n_copies)

/-- Sorted reference eigenvalue labels (nondecreasing). -/
noncomputable def iidAEPSortedReferenceEigenvalue
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    Fin (n ^ n_copies) → ℝ :=
  fun z =>
    iidAEPReferenceEigenvalueLabels σ n_copies
      (iidAEPReferenceSortPerm σ n_copies z)

/-- Sorted rank-one spectral increment projectors. -/
noncomputable def iidAEPSortedReferenceProjector
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    Fin (n ^ n_copies) → Op (n ^ n_copies) :=
  fun z =>
    iidAEPReferenceSpectralIncrementProjector σ n_copies
      (iidAEPReferenceSortPerm σ n_copies z)

/-- Reference-spectrum data carrying the sorted (nondecreasing) labels and the
correspondingly reindexed orthogonal increments. -/
noncomputable def iidAEPSortedReferenceSpectrumData
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    IIDAEPReferenceSpectrumData n n_copies where
  referenceEigenvalue := iidAEPSortedReferenceEigenvalue σ n_copies
  spectralProjector := iidAEPSortedReferenceProjector σ n_copies

/-- Renner cumulative-resolution data built from the sorted spectrum: the `β_z`
increments and cumulative projectors `B_z = ∑_{z ≤ z'} P_{z'}`. -/
noncomputable def iidAEPSortedCumulativeResolutionData
    {n : ℕ} [NeZero n] (σ : DensityOp n) (n_copies : ℕ) :
    IIDAEPCumulativeResolutionData n n_copies where
  betaCoefficient := betaIncr (iidAEPSortedReferenceEigenvalue σ n_copies)
  cumulativeProjector := cumProj (iidAEPSortedReferenceProjector σ n_copies)

/-- Replace the reference-spectrum and cumulative-resolution layers of a witness
by the sorted spectrum and its Renner cumulative resolution. The projector
sandwich, spectral cut, and `r_t` data are unchanged. -/
noncomputable def iidAEPWitnessWithSortedSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    IIDAEPSpectralWitness X n n_copies where
  projectorData := W.projectorData
  referenceSpectrum := iidAEPSortedReferenceSpectrumData σ n_copies
  cumulativeResolution := iidAEPSortedCumulativeResolutionData σ n_copies
  spectralCut := W.spectralCut
  rtData := W.rtData

/-- The sorted eigenvalue labels are nonnegative. -/
lemma iidAEPWitnessWithSortedSpectrum_eigenvalue_nonneg
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) :
    ∀ z : Fin (n ^ n_copies),
      0 ≤ (iidAEPWitnessWithSortedSpectrum σ W).referenceEigenvalue z := by
  intro z
  simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedReferenceSpectrumData,
    IIDAEPSpectralWitness.referenceEigenvalue, iidAEPSortedReferenceEigenvalue]
  exact iidAEPReferenceEigenvalueLabels_nonneg σ n_copies _

/-- The reindexed increments are still nonzero orthogonal Hermitian idempotents
resolving the identity. -/
lemma iidAEPWitnessWithSortedSpectrum_increments
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ} [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceSpectralIncrements (iidAEPWitnessWithSortedSpectrum σ W) := by
  obtain ⟨idem, herm, nz, orth, hsum⟩ :=
    iidAEPReferenceSpectralIncrementProjector_increments σ n_copies
  simp only [iidAEPReferenceSpectralIncrements, iidAEPWitnessWithSortedSpectrum,
    iidAEPSortedReferenceSpectrumData, IIDAEPSpectralWitness.spectralProjector,
    iidAEPSortedReferenceProjector]
  refine ⟨fun z => idem _, fun z => herm _, fun z => nz _, ?_, ?_⟩
  · intro z z' hzz
    exact orth _ _ (fun he => hzz ((iidAEPReferenceSortPerm σ n_copies).injective he))
  · rw [Equiv.sum_comp (iidAEPReferenceSortPerm σ n_copies)
        (iidAEPReferenceSpectralIncrementProjector σ n_copies)]
    exact hsum

/-- The tensor-power reference acts diagonally on the reindexed increments and is
reconstructed from the eigenvalue-weighted increments. -/
lemma iidAEPWitnessWithSortedSpectrum_action
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ} [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceSpectralAction σ n_copies
      (iidAEPWitnessWithSortedSpectrum σ W) := by
  obtain ⟨hdecomp, haction⟩ := iidAEPReferenceSpectralIncrementProjector_action σ n_copies
  simp only [iidAEPReferenceSpectralAction, iidAEPWitnessWithSortedSpectrum,
    iidAEPSortedReferenceSpectrumData, IIDAEPSpectralWitness.spectralProjector,
    IIDAEPSpectralWitness.referenceEigenvalue, iidAEPSortedReferenceProjector,
    iidAEPSortedReferenceEigenvalue]
  refine ⟨?_, ?_⟩
  · rw [Equiv.sum_comp (iidAEPReferenceSortPerm σ n_copies)
      (fun w => (iidAEPReferenceEigenvalueLabels σ n_copies w : ℂ)
        • iidAEPReferenceSpectralIncrementProjector σ n_copies w)]
    exact hdecomp
  · intro z
    exact ⟨(haction _).1, (haction _).2⟩

/-- The Renner cumulative resolution holds for the sorted spectrum: this is where
the sorting pays off, making the increments `β_z` nonnegative. -/
lemma iidAEPWitnessWithSortedSpectrum_cumulative
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ} [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceCumulativeResolution σ n_copies
      (iidAEPWitnessWithSortedSpectrum σ W) := by
  obtain ⟨idem, herm, _nz, orth, _hsum⟩ :=
    iidAEPReferenceSpectralIncrementProjector_increments σ n_copies
  obtain ⟨hdecomp, _⟩ := iidAEPReferenceSpectralIncrementProjector_action σ n_copies
  have hmono : Monotone (iidAEPSortedReferenceEigenvalue σ n_copies) := by
    unfold iidAEPSortedReferenceEigenvalue iidAEPReferenceSortPerm
    exact Tuple.monotone_sort _
  have hnonneg : ∀ z, 0 ≤ iidAEPSortedReferenceEigenvalue σ n_copies z := by
    intro z
    simp only [iidAEPSortedReferenceEigenvalue]
    exact iidAEPReferenceEigenvalueLabels_nonneg σ n_copies _
  have idemP : ∀ z, iidAEPSortedReferenceProjector σ n_copies z
        * iidAEPSortedReferenceProjector σ n_copies z
      = iidAEPSortedReferenceProjector σ n_copies z := by
    intro z; simp only [iidAEPSortedReferenceProjector]; exact idem _
  have hermP : ∀ z, (iidAEPSortedReferenceProjector σ n_copies z)ᴴ
      = iidAEPSortedReferenceProjector σ n_copies z := by
    intro z; simp only [iidAEPSortedReferenceProjector]; exact herm _
  have orthP : ∀ z z', z ≠ z' →
      iidAEPSortedReferenceProjector σ n_copies z
        * iidAEPSortedReferenceProjector σ n_copies z' = 0 := by
    intro z z' h
    simp only [iidAEPSortedReferenceProjector]
    exact orth _ _ (fun he => h ((iidAEPReferenceSortPerm σ n_copies).injective he))
  have hM : (iidAEPTensorReference σ n_copies).toOp
      = ∑ z, (iidAEPSortedReferenceEigenvalue σ n_copies z : ℂ)
          • iidAEPSortedReferenceProjector σ n_copies z := by
    simp only [iidAEPSortedReferenceEigenvalue, iidAEPSortedReferenceProjector]
    rw [Equiv.sum_comp (iidAEPReferenceSortPerm σ n_copies)
      (fun w => (iidAEPReferenceEigenvalueLabels σ n_copies w : ℂ)
        • iidAEPReferenceSpectralIncrementProjector σ n_copies w)]
    exact hdecomp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedCumulativeResolutionData,
      IIDAEPSpectralWitness.betaCoefficient]
    exact betaIncr_nonneg _ hmono hnonneg z
  · intro z
    rfl
  · intro z
    simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedCumulativeResolutionData,
      IIDAEPSpectralWitness.cumulativeProjector]
    exact cumProj_idem _ idemP orthP z
  · intro z
    simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedCumulativeResolutionData,
      IIDAEPSpectralWitness.cumulativeProjector]
    exact cumProj_conjTranspose _ hermP z
  · intro z z' hzz
    simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedCumulativeResolutionData,
      IIDAEPSpectralWitness.cumulativeProjector]
    exact cumProj_nesting _ idemP orthP hzz
  · simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedCumulativeResolutionData,
      IIDAEPSpectralWitness.betaCoefficient, IIDAEPSpectralWitness.cumulativeProjector]
    exact sum_beta_cumProj _ _ _ hM
  · intro z
    simp only [iidAEPWitnessWithSortedSpectrum, iidAEPSortedReferenceSpectrumData,
      iidAEPSortedCumulativeResolutionData, IIDAEPSpectralWitness.referenceEigenvalue,
      IIDAEPSpectralWitness.betaCoefficient]
    exact (sum_filter_le_betaIncr _ z).symm

/-- Always-smooth spectral cut (Renner, main.tex:4575–4665). Renner's
construction handles **every** threshold sign with the same smoothed cut: the
retained truncation is the cumulative crossing projector `B_{z*}` at the
separation scale `2 ^ (-T)`, where `z* = W.cutIndex` is the least sorted index
whose reference eigenvalue reaches the scale (main.tex:4600–4604). The carried
bookkeeping is the projector identity together with the below-crossing
inequality `λ_z < 2^(-T)` for the strictly-discarded eigen-blocks `z < z*`, which
is exactly the sub-threshold support the Chernoff tail step exploits. There is **no**
`sign(T)` split and **no** unconditional above-crossing claim: the operator
domination that retains mass is carried separately by
`iidAEPSpectralCutBlockDomination`, which is the faithful Renner
weight-cap `p_{x,z} ≤ λ β_z` (main.tex:4644–4665), not a single-projector
truncation identity. -/
def iidAEPNonnegativeThresholdCrossing
    {X : Type*} [Fintype X] {n : ℕ}
    {n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  W.truncationProjector = W.cumulativeProjector W.cutIndex ∧
    ∀ z : Fin (n ^ n_copies), z < W.cutIndex →
      W.referenceEigenvalue z < (2 : ℝ) ^ (-W.entropyThreshold)

/-- The always-smooth spectral cut selecting the truncation projector. There is
no `sign(T)` branch: the single retained-crossing cut applies for every
threshold (main.tex:4575–4665). -/
def iidAEPSpectralCutCondition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  W.entropyThreshold =
      iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε ∧
    iidAEPNonnegativeThresholdCrossing W

/-- Feasible scalar induced by the retained spectral cut. This is the scalar
used both in the block-domination condition and in the conditional
min-entropy feasibility package. -/
noncomputable def iidAEPSpectralCutDominationScale
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  (2 : ℝ) ^ (-W.entropyThreshold)


/-- The signed smooth min-entropy of a tensor power, divided by the number of copies. -/
noncomputable def iidAEPSmoothRateReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) : ℝ :=
  (1 / (n_copies : ℝ)) *
    @smoothMinEntropyReal (Fin n_copies → X) _ _ _ (n ^ n_copies) _ ε
      (InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ n_copies)
      (InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
        (DensityOp.toSubDensityOp σ) n_copies)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
