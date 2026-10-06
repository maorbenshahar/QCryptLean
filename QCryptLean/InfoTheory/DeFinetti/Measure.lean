import QCryptLean.Quantum.Operators.MatrixIntegral
import QCryptLean.Math.Probability.HaarMeasure
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.TensorProducts.CastDim
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Star
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.Order

/-!
# Measure-Theoretic Infrastructure for de Finetti — tensor-power integrals and Haar pushforwards

This module provides the measure-theoretic tools used in the de Finetti
construction: measurable-space instances for density operators, tensor-power
partial-trace lemmas, Bochner integration of density-operator-valued tensor
powers, and the Haar-pushforward measure on pure states.

## Main definitions
- `DensityMeasure`: probability measure on `DensityOp d`
- `partialTraceToFirst`: partial trace onto the first tensor factor
- `partialTraceToFirstK`: partial trace onto the first `k` tensor factors
- `integralSingleCopy`: Bochner integral of single-copy density operators
- `integralTensorPower`: Bochner integral of tensor powers
- `pureStateMap`: map from unitaries to pure-state density operators
- `deFinetti_haarMeasure`: Haar-pushforward density measure on pure states

## Main statements
- `partialTraceToFirst_tensorPowGen`: tracing out `n - 1` tensor factors of `ρ^⊗n`
  recovers `ρ`
- `partialTraceToFirstK_tensorPowGen`: tracing out `n - k` tensor factors of `ρ^⊗n`
  yields `ρ^⊗k`
- `partialTraceB_measurable`: the density-operator partial trace is measurable
- `pushforward_partialTraceB_exists`: a density measure pushes forward along partial trace
- `integral_deFinetti_haarMeasure_eq_integral_haar`: integrals against the Haar-pushforward
  measure reduce to Haar integrals over the unitary group
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Symmetry MeasureTheory
open Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-!
## Measurable Space Infrastructure for Density Operators

We equip `Matrix (Fin n) (Fin n) ℂ` with the Borel σ-algebra from its
product topology, then pull this back to `DensityOp n` via its embedding
into matrices.
-/

noncomputable instance instMeasurableSpaceMatrixComplex {n : ℕ} :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
instance instBorelSpaceMatrixComplex {n : ℕ} :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- Borel σ-algebra on `DensityOp n` from the induced topology. -/
noncomputable instance instMeasurableSpaceDensityOp {n : ℕ} :
    MeasurableSpace (DensityOp n) := borel _
instance instBorelSpaceDensityOp {n : ℕ} :
    BorelSpace (DensityOp n) := ⟨rfl⟩

/-!
## Probability Measures over Density Operators

For the de Finetti theorem, we need to integrate over the space of
density operators with respect to a probability measure.
-/

/-- Probability measure over single-system density operators.

    This represents a classical mixture of quantum states, where `μ`
    specifies the probability distribution over possible states.
    The underlying measure lives on `DensityOp d` equipped with the
    Borel σ-algebra from the induced matrix topology. -/
structure DensityMeasure (d : ℕ) where
  /-- The underlying probability measure on the space of density
      operators. -/
  measure : Measure (DensityOp d)
  /-- The measure is a probability measure (total mass 1). -/
  isProbability : IsProbabilityMeasure measure

/-- `DensityMeasure` is inhabited: the Dirac measure at the maximally
    mixed state is a valid probability measure over density operators. -/
noncomputable instance DensityMeasure.nonempty (d : ℕ) [NeZero d] :
    Nonempty (DensityMeasure d) :=
  ⟨⟨Measure.dirac (DensityOp.maxMixed d), inferInstance⟩⟩

/-- A `DensityMeasure` is a *product-state* (equivalently, pure-state) measure
    when its underlying probability measure is concentrated on rank-1 projectors:
    almost every sample `σ` satisfies `σ.IsPure` (i.e. `σ² = σ`).

    This is the support condition required by the
    Christandl–König–Mitchison–Renner finite quantum de Finetti theorem
    (CKMR, Corollary II.3): the approximating mixture
    `ρ_k ≈ ∫ σ^{⊗k} dμ(σ)` from the symmetric extension of an `n`-copy state
    is supported on pure product states `|ψ⟩⟨ψ|^{⊗k}`. The current
    `DensityMeasure` type does not track this condition, so downstream
    theorems that need it (e.g. consumers of CKMR Cor II.3 phrased over
    pure-state mixtures, or arguments invoking concavity/convexity
    specifically of pure-state functionals) should take
    `IsProductStateMeasure` as an additional hypothesis on the witness
    `μ` returned by `pure_state_deFinetti_symmetric` /
    `deFinetti_paired` rather than weakening to an arbitrary
    measure on `DensityOp d`.

    The "product-state" name refers to the *tensor-power* image
    `σ^{⊗k} = (|ψ⟩⟨ψ|)^{⊗k}` that appears in the de Finetti integral; the
    underlying single-copy property is rank-1 / pure, so the predicate
    is stated in terms of `DensityOp.IsPure`. -/
def DensityMeasure.IsProductStateMeasure {d : ℕ} (μ : DensityMeasure d) : Prop :=
  ∀ᵐ σ ∂μ.measure, σ.IsPure

/-- Equivalent reformulation: the set of non-pure states has outer measure zero.
    `IsProductStateMeasure` is unfolded via `MeasureTheory.ae_iff`. -/
lemma DensityMeasure.isProductStateMeasure_iff_measure_compl_zero
    {d : ℕ} (μ : DensityMeasure d) :
    μ.IsProductStateMeasure ↔
      μ.measure (setOf (fun σ : DensityOp d => ¬ σ.IsPure)) = 0 :=
  MeasureTheory.ae_iff

/-!
## Partial Trace to First System

For the de Finetti theorem, we need to trace out the last n-1 systems
from a state on (ℂᵈ)^⊗n to get a state on ℂᵈ.
-/

/-- Partial trace to the first system of an n-system state.

    For ρ on (ℂᵈ)^⊗n, this returns Tr_{2,...,n}[ρ] on ℂᵈ.

    Factors d^n = d * d^(n-1) via `pow_succ`, casts, then traces out
    the d^(n-1) subsystem using `partialTraceB`. -/
noncomputable def partialTraceToFirst {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) : DensityOp d :=
  have hdim : d ^ n = d * d ^ (n - 1) := by
    cases n with
    | zero => exact absurd rfl (NeZero.ne 0)
    | succ m => simp [pow_succ, mul_comm]
  DensityOp.partialTraceB (DensityOp.castDim hdim ρ)

/-- Partial trace of a tensor power returns the original state:
    `Tr_{2,...,n}[ρ^⊗n] = ρ` for any density operator `ρ` and `n ≥ 1`. -/
theorem partialTraceToFirst_tensorPowGen {d : ℕ} [NeZero d] (ρ : DensityOp d)
    (n : ℕ) [NeZero n] [NeZero (d ^ n)] :
    partialTraceToFirst (ρ.tensorPowGen n) = ρ := by
  cases n with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ k =>
    apply DensityOp.ext
    simp only [partialTraceToFirst, DensityOp.tensorPowGen]
    change (DensityOp.castDim (pow_succ' d k)
      (DensityOp.castDim (pow_succ' d k).symm (ρ.tensor (ρ.tensorPowGen k)))).partialTraceB.toOp = _
    rw [DensityOp.castDim_cancel]
    exact partialTraceB_tensor ρ (ρ.tensorPowGen k)

/-- Partial trace to k copies of an n-system state.

    For ρ on (ℂᵈ)^⊗n, this returns Tr_{n-k copies}[ρ] on (ℂᵈ)^⊗k.

    Factors d^n = d^k * d^(n-k), casts, then traces out the d^(n-k)
    subsystem using `partialTraceB`. Generalizes `partialTraceToFirst` (k=1).

    **Convention note**: Under `finProdFinEquiv`, the first factor (d^k) corresponds
    to the high-order digits of the mixed-radix encoding. For permutation-invariant
    states (the only use case in de Finetti), the choice of which k copies to keep
    is irrelevant. See `partialTraceToFirstK_tensorPowGen` for the correctness
    theorem on tensor powers. -/
noncomputable def partialTraceToFirstK {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (k : ℕ) [NeZero k] [NeZero (d ^ k)]
    (hk : k ≤ n) (ρ : DensityOp (d ^ n)) : DensityOp (d ^ k) :=
  DensityOp.partialTraceB (DensityOp.castDim (pow_eq_mul_pow_sub hk) ρ)

/-- Index decomposition: `finProdFinEquiv` composed with `finFunctionFinEquiv` on each factor
    corresponds to `finFunctionFinEquiv` of the concatenated function, up to dimension casts.

    Specifically, for `f : Fin k → Fin d` and `g : Fin p → Fin d`, the element
    `finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g)` in `Fin (d^k * d^p)`
    corresponds (via cast) to `finFunctionFinEquiv (Fin.append f g ∘ cast)` in `Fin (d^(k+p))`.

    This is the key combinatorial fact: the mixed-radix encoding of a pair of digit
    sequences equals the encoding of their concatenation (with appropriate endianness). -/
lemma finFunctionFinEquiv_prod_eq_append {d k p : ℕ}
    (f : Fin k → Fin d) (g : Fin p → Fin d) :
    (finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g) : ℕ) =
    (finFunctionFinEquiv (fun i : Fin (p + k) =>
      if h : (i : ℕ) < p then g ⟨i, h⟩ else f ⟨i - p, by omega⟩) : ℕ) := by
  -- `finProdFinEquiv` encodes the low-order digits from `g`
  -- and the high-order digits from `f`.
  rw [finProdFinEquiv_apply_val, finFunctionFinEquiv_apply, finFunctionFinEquiv_apply,
      finFunctionFinEquiv_apply]
  -- Split RHS sum over Fin (p + k) into two halves
  rw [Fin.sum_univ_add]
  congr 1
  · -- First half: i < p, the "if" picks g
    apply Finset.sum_congr rfl; intro i _
    have hi : (Fin.castAdd k i : ℕ) < p := i.isLt
    simp [Fin.castAdd]
  · -- Second half: i ≥ p, the "if" picks f, and shift index
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [Fin.natAdd, Fin.val_mk]
    have hi : ¬ (p + (i : ℕ)) < p := by omega
    rw [dif_neg hi]
    have hsub : (p + (i : ℕ)) - p = (i : ℕ) := by omega
    simp only [hsub]
    have hval : (⟨(i : ℕ), by omega⟩ : Fin k) = i := by ext; rfl
    rw [hval, pow_add]
    ring

/-- Trace of a density operator expressed as sum of diagonal entries. -/
lemma DensityOp.trace_eq_sum_diag {d : ℕ} (ρ : DensityOp d) :
    ∑ i : Fin d, ρ.toOp i i = 1 := by
  have h := ρ.trace_one
  simp only [Matrix.trace, Matrix.diag] at h
  exact_mod_cast h

/-- Sum over all functions `Fin p → Fin d` of a product of diagonal entries equals 1
    for a density operator. This is the Fubini + trace = 1 argument:
    ∑_{g : Fin p → Fin d} ∏_{m} ρ_{g(m),g(m)} = (Tr ρ)^p = 1^p = 1. -/
lemma sum_prod_diag_eq_one {d p : ℕ} [NeZero d] (ρ : DensityOp d) :
    ∑ g : Fin p → Fin d, ∏ m : Fin p, ρ.toOp (g m) (g m) = 1 := by
  conv_lhs => rw [← Fintype.prod_sum (fun i a => ρ.toOp a a)]
  simp [DensityOp.trace_eq_sum_diag ρ]

/-- A tensor-power entry indexed by `Fin (d ^ n)` is the product of the
corresponding single-copy entries obtained by decoding the indices into digits. -/
lemma tensorPowGen_toOp_eq_prod_of_fin {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (ρ : DensityOp d) (a b : Fin (d ^ n)) :
    (ρ.tensorPowGen n).toOp a b =
      ∏ m : Fin n, ρ.toOp ((finFunctionFinEquiv.symm a) m) ((finFunctionFinEquiv.symm b) m) := by
  simpa only [Equiv.apply_symm_apply]
    using tensorPowGen_toOp_eq_prod ρ (finFunctionFinEquiv.symm a) (finFunctionFinEquiv.symm b)

/-- Key index lemma: the Fin.cast of finProdFinEquiv applied to encoded digit functions
    equals the encoding of the concatenated digit function (as Fin values, not just ℕ). -/
lemma cast_finProdFinEquiv_finFunctionFinEquiv {d k p : ℕ}
    (h : d ^ k * d ^ p = d ^ (p + k))
    (f : Fin k → Fin d) (g : Fin p → Fin d) :
    Fin.cast h (finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g)) =
    finFunctionFinEquiv (fun i : Fin (p + k) =>
      if hi : (i : ℕ) < p then g ⟨i, hi⟩ else f ⟨i - p, by omega⟩) := by
  ext
  simp only [Fin.val_cast]
  exact finFunctionFinEquiv_prod_eq_append f g

/-- Digit extraction from the product encoding: the `finFunctionFinEquiv.symm` of
    `Fin.cast h (finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g))`
    extracts `g` for low-order digits and `f` for high-order digits.

    This is the key combinatorial fact connecting `partialTraceB`'s index structure
    with `tensorPowGen`'s digit-product representation. -/
lemma digit_of_cast_finProdFinEquiv {d k n : ℕ}
    (hk : k ≤ n)
    (f : Fin k → Fin d) (g : Fin (n - k) → Fin d)
    (m : Fin n) :
    (finFunctionFinEquiv.symm (Fin.cast (pow_eq_mul_pow_sub hk).symm
      (finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g)))) m =
    if hm : (m : ℕ) < n - k then g ⟨m, hm⟩
    else f ⟨m - (n - k), by omega⟩ := by
  -- Strategy: both sides extract the same digit from the same ℕ value.
  -- The LHS is finFunctionFinEquiv.symm applied to a Fin whose val equals
  -- (finFunctionFinEquiv concat).val by finFunctionFinEquiv_prod_eq_append.
  -- Key ℕ-value equality
  have hpkn : (n - k) + k = n := Nat.sub_add_cancel hk
  set concat : Fin ((n - k) + k) → Fin d :=
    fun i => if hi : (i : ℕ) < (n - k) then g ⟨i, hi⟩ else f ⟨i - (n - k), by omega⟩
  -- The two Fin (d^n) values are equal (same ℕ value)
  have heq : Fin.cast (pow_eq_mul_pow_sub hk).symm
      (finProdFinEquiv (finFunctionFinEquiv f, finFunctionFinEquiv g)) =
    Fin.cast (show d ^ ((n - k) + k) = d ^ n by rw [hpkn])
      (finFunctionFinEquiv concat) := by
    ext; simp only [Fin.val_cast]; exact finFunctionFinEquiv_prod_eq_append f g
  rw [heq]
  -- The Fin.cast + finFunctionFinEquiv.symm ∘ finFunctionFinEquiv = id (up to cast)
  -- Use: for any v : Fin (d^N) and cast h : Fin (d^N) → Fin (d^M),
  --   finFunctionFinEquiv.symm (Fin.cast h v) m has the same ℕ val as
  --   finFunctionFinEquiv.symm v (Fin.cast _ m)
  -- because both equal v.val / d^m.val % d
  -- Then: finFunctionFinEquiv.symm (finFunctionFinEquiv concat) = concat (Equiv.symm_apply_apply)
  have key : finFunctionFinEquiv.symm
      (Fin.cast (show d ^ ((n - k) + k) = d ^ n by rw [hpkn])
        (finFunctionFinEquiv concat))
      m = concat (Fin.cast hpkn.symm m) := by
    -- Both sides equal (finFunctionFinEquiv concat).val / d^m.val % d as ℕ
    apply Fin.ext
    change (Fin.cast _ (finFunctionFinEquiv concat)).val / d ^ m.val % d =
      (concat (Fin.cast hpkn.symm m)).val
    rw [Fin.val_cast]
    -- RHS: concat (cast m) = (finFunctionFinEquiv.symm (finFunctionFinEquiv concat)) (cast m)
    rw [← show (finFunctionFinEquiv.symm (finFunctionFinEquiv concat)
        (Fin.cast hpkn.symm m) : ℕ) =
        (concat (Fin.cast hpkn.symm m) : ℕ) from by
      simp [Equiv.symm_apply_apply]]
    -- Both sides: (finFunctionFinEquiv concat).val / d^m.val % d
    rfl
  rw [key]
  simp only [concat, Fin.val_cast]

/-- Tracing out the last `n - k` tensor factors of `ρ^⊗n` leaves `ρ^⊗k`. -/
theorem partialTraceToFirstK_tensorPowGen {d : ℕ} [NeZero d] (ρ : DensityOp d)
    (n k : ℕ) [NeZero n] [NeZero k] [NeZero (d ^ n)] [NeZero (d ^ k)]
    (hk : k ≤ n) :
    partialTraceToFirstK k hk (ρ.tensorPowGen n) = ρ.tensorPowGen k := by
  apply DensityOp.ext; ext i j
  unfold partialTraceToFirstK
  simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
             Quantum.TensorProducts.partialTraceB, Matrix.of_apply, castDim_toOp_cast]
  set p := n - k with hp_def
  set fi := finFunctionFinEquiv.symm i
  set fj := finFunctionFinEquiv.symm j
  rw [show i = finFunctionFinEquiv fi from by simp [fi],
      show j = finFunctionFinEquiv fj from by simp [fj]]
  change (∑ x, (ρ.tensorPowGen n).toOp
    (Fin.cast _ (finProdFinEquiv (finFunctionFinEquiv fi, x)))
    (Fin.cast _ (finProdFinEquiv (finFunctionFinEquiv fj, x)))) =
    (ρ.tensorPowGen k).toOp
      (@finFunctionFinEquiv d k fi)
      (@finFunctionFinEquiv d k fj)
  rw [tensorPowGen_toOp_eq_prod]
  have hpkn : p + k = n := Nat.sub_add_cancel hk
  simp_rw [tensorPowGen_toOp_eq_prod_of_fin]
  conv_lhs =>
    arg 2; ext x; arg 2; ext m
    rw [show x = finFunctionFinEquiv (finFunctionFinEquiv.symm x) from
        (Equiv.apply_symm_apply _ x).symm]
    rw [digit_of_cast_finProdFinEquiv hk fi (finFunctionFinEquiv.symm x) m,
        digit_of_cast_finProdFinEquiv hk fj (finFunctionFinEquiv.symm x) m]
  have prod_split : ∀ (x : Fin (d ^ p)),
    (∏ m : Fin n,
      ρ.toOp
        (if hm : (m : ℕ) < n - k then
          finFunctionFinEquiv.symm x ⟨m, hm⟩
        else fi ⟨m - (n - k), by omega⟩)
        (if hm : (m : ℕ) < n - k then
          finFunctionFinEquiv.symm x ⟨m, hm⟩
        else fj ⟨m - (n - k), by omega⟩)) =
    (∏ m : Fin p, ρ.toOp (finFunctionFinEquiv.symm x m) (finFunctionFinEquiv.symm x m)) *
    (∏ m : Fin k, ρ.toOp (fi m) (fj m)) := by
    intro x
    set gx := finFunctionFinEquiv.symm x
    -- Reindex: Fin n → Fin (p + k) using finCongr (preserves ℕ value)
    have prod_reindex : ∀ (F : Fin n → ℂ),
        ∏ m : Fin n, F m = ∏ m : Fin (p + k), F (finCongr hpkn m) := by
      intro F; exact (Fintype.prod_equiv (finCongr hpkn) _ _ (fun m => rfl)).symm
    rw [prod_reindex]
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl; intro m _
      have hm : ((finCongr hpkn (Fin.castAdd k m) : Fin n) : ℕ) < n - k := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]; exact m.isLt
      rw [dif_pos hm, dif_pos hm]
      simp [finCongr_apply, Fin.val_castAdd]
    · apply Finset.prod_congr rfl; intro m _
      have hm : ¬ ((finCongr hpkn (Fin.natAdd p m) : Fin n) : ℕ) < n - k := by
        simp [finCongr, Fin.natAdd]; omega
      rw [dif_neg hm, dif_neg hm]
      have hidx : (⟨p + (m : ℕ) - (n - k), by omega⟩ : Fin k) = m := by
        subst p
        apply Fin.ext
        simp
      simp [hidx]
  conv_lhs => arg 2; ext x; rw [prod_split x]
  rw [← Finset.sum_mul]
  rw [show (∑ x : Fin (d ^ p),
      ∏ m : Fin p,
        ρ.toOp (finFunctionFinEquiv.symm x m) (finFunctionFinEquiv.symm x m)) =
    (∑ gx : Fin p → Fin d, ∏ m : Fin p, ρ.toOp (gx m) (gx m)) from by
    rw [← Equiv.sum_comp (finFunctionFinEquiv (n := p) (m := d))]
    simp [Equiv.symm_apply_apply]]
  rw [sum_prod_diag_eq_one ρ, one_mul]

/-!
## Integration of Tensor Powers

The de Finetti representation involves integrals of the form ∫ σ^⊗n dμ(σ).
-/

-- Integral of single-copy states: ∫ σ dμ(σ) as a DensityOp d.
-- Uses entrywise ℂ-valued Bochner integral to avoid Matrix norm choice.

-- === Measurability/integrability infrastructure ===
-- These are needed by all six integration lemmas below.

/-- Coordinate extraction `σ ↦ σ_{ij}` is measurable. -/
lemma measurable_toOp_entry {d : ℕ} [NeZero d] (i j : Fin d) :
    Measurable (fun (σ : DensityOp d) => σ.toOp i j) := by
  apply Continuous.measurable
  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_induced_dom))

/-- Casting a density operator along an equality of dimensions is continuous. -/
lemma densityOp_castDim_continuous {n m : ℕ} (h : n = m) :
    Continuous (DensityOp.castDim h : DensityOp n → DensityOp m) := by
  cases h
  exact (continuous_id : Continuous (fun ρ : DensityOp n => ρ))

/-- Casting a density operator along an equality of dimensions is measurable. -/
lemma densityOp_castDim_measurable {n m : ℕ} (h : n = m) :
    Measurable (DensityOp.castDim h : DensityOp n → DensityOp m) :=
  (densityOp_castDim_continuous h).measurable

/-- The tensor-power map is continuous after embedding density operators as matrices. -/
lemma continuous_tensorPowGen_toOp {d n : ℕ} [NeZero d] [NeZero (d ^ n)] :
    Continuous (fun σ : DensityOp d => (σ.tensorPowGen n).toOp) := by
  apply continuous_matrix
  intro i j
  set fi : Fin n → Fin d := finFunctionFinEquiv.symm i
  set fj : Fin n → Fin d := finFunctionFinEquiv.symm j
  have h_eq :
      (fun σ : DensityOp d => (σ.tensorPowGen n).toOp i j) =
        fun σ : DensityOp d => ∏ m : Fin n, σ.toOp (fi m) (fj m) := by
    ext σ
    simpa [fi, fj] using tensorPowGen_toOp_eq_prod_of_fin (d := d) (n := n) σ i j
  rw [h_eq]
  exact continuous_finsetProd Finset.univ (fun m _ =>
    ((continuous_apply (fj m)).comp ((continuous_apply (fi m)).comp continuous_induced_dom)))

/-- The tensor-power map on density operators is continuous. -/
lemma tensorPowGen_continuous {d n : ℕ} [NeZero d] [NeZero (d ^ n)] :
    Continuous (fun σ : DensityOp d => σ.tensorPowGen n) := by
  rw [continuous_induced_rng]
  exact continuous_tensorPowGen_toOp

/-- The tensor-power map on density operators is measurable. -/
lemma tensorPowGen_measurable {d n : ℕ} [NeZero d] [NeZero (d ^ n)] :
    Measurable (fun σ : DensityOp d => σ.tensorPowGen n) :=
  (tensorPowGen_continuous (d := d) (n := n)).measurable

/-- `DensityOp.partialTraceB` is continuous for arbitrary finite tensor factors.

    Each output entry is a finite sum of coordinate projections on the ambient
    matrix space, so continuity on the induced topology is immediate. -/
lemma partialTraceB_continuous_general {n m : ℕ} :
    Continuous (DensityOp.partialTraceB : DensityOp (n * m) → DensityOp n) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h_eq : (fun ρ : DensityOp (n * m) =>
    ((fun σ : DensityOp n => σ.toOp) ∘ DensityOp.partialTraceB) ρ i j) =
    (fun ρ : DensityOp (n * m) =>
      ∑ k : Fin m, ρ.toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))) := by
    ext ρ
    simp only [Function.comp]
    unfold DensityOp.partialTraceB PosSemidefOp.partialTraceB partialTraceB
    simp only [Matrix.of_apply]
  rw [h_eq]
  apply continuous_finsetSum
  intro k _
  exact ((continuous_apply (finProdFinEquiv (j, k))).comp
    ((continuous_apply (finProdFinEquiv (i, k))).comp continuous_induced_dom))

/-- `DensityOp.partialTraceB` is measurable for arbitrary finite tensor factors. -/
lemma partialTraceB_measurable_general {n m : ℕ} :
    Measurable (DensityOp.partialTraceB : DensityOp (n * m) → DensityOp n) :=
  partialTraceB_continuous_general.measurable

/-- `DensityOp.partialTraceB` is measurable.

    This equal-factor form is kept for existing de Finetti callers. -/
lemma partialTraceB_measurable {d : ℕ} [NeZero d] :
    Measurable (DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d) :=
  partialTraceB_measurable_general

/-- Tracing all but the first tensor factor is continuous. -/
lemma partialTraceToFirst_continuous {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    Continuous (partialTraceToFirst : DensityOp (d ^ n) → DensityOp d) := by
  unfold partialTraceToFirst
  let hdim : d ^ n = d * d ^ (n - 1) := by
    cases n with
    | zero => exact absurd rfl (NeZero.ne 0)
    | succ m => simp [pow_succ, mul_comm]
  exact partialTraceB_continuous_general.comp (densityOp_castDim_continuous hdim)

/-- Tracing all but the first tensor factor is measurable. -/
lemma partialTraceToFirst_measurable {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    Measurable (partialTraceToFirst : DensityOp (d ^ n) → DensityOp d) :=
  (partialTraceToFirst_continuous (d := d) (n := n)).measurable

/-- Coordinate extraction `σ ↦ σ_{ij}` is integrable with respect to any probability measure on
states: it is continuous on the compact state space. -/
lemma integrable_toOp_entry {d : ℕ} (i j : Fin d) (μ : DensityMeasure d) :
    MeasureTheory.Integrable (fun σ : DensityOp d => σ.toOp i j) μ.measure := by
  haveI := μ.isProbability
  exact ((continuous_apply j).comp
    ((continuous_apply i).comp DensityOp.continuous_toOp)).integrable_of_compactSpace

/-- The entrywise integral ∫ σ_{ij} dμ(σ) is Hermitian.
    Proof: M†_{ij} = conj(M_{ji}) = conj(∫ σ_{ji} dμ) = ∫ conj(σ_{ji}) dμ
    = ∫ σ_{ij} dμ = M_{ij}, using integral_conj and σ.IsHermitian. -/
private lemma integralSingleCopy_hermitian {d : ℕ} [NeZero d] (μ : DensityMeasure d) :
    Matrix.IsHermitian
      (Matrix.of fun i j : Fin d => ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  change starRingEnd ℂ (∫ (σ : DensityOp d), σ.toOp j i ∂μ.measure) =
    ∫ (σ : DensityOp d), σ.toOp i j ∂μ.measure
  rw [← integral_conj]
  congr 1
  ext σ
  exact σ.toPosSemidefOp.toHermitianOp.isHermitian.apply i j

/-- The entrywise integral ∫ σ_{ij} dμ(σ) is positive semidefinite.
    Proof: ⟨x|M|x⟩ = ∑_{ij} x̄ᵢ (∫ σ_{ij} dμ) xⱼ = ∫ ∑_{ij} x̄ᵢ σ_{ij} xⱼ dμ
    = ∫ ⟨x|σ|x⟩ dμ ≥ 0 since each ⟨x|σ|x⟩ ≥ 0. -/
private lemma integralSingleCopy_posSemidef {d : ℕ} [NeZero d] (μ : DensityMeasure d) :
    ∀ x : Fin d → ℂ,
      0 ≤ (quadraticForm
        (Matrix.of fun i j : Fin d =>
          ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure) x).re := by
  intro x
  suffices h : (quadraticForm
      (Matrix.of fun i j : Fin d => ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure) x).re =
    ∫ σ : DensityOp d, (quadraticForm σ.toOp x).re ∂μ.measure by
    rw [h]
    exact integral_nonneg (fun σ => σ.toPosSemidefOp.pos_semidef x)
  have hmv : ∀ i : Fin d,
      (Matrix.of fun i j : Fin d => ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure).mulVec x i =
      ∫ σ : DensityOp d, (σ.toOp.mulVec x) i ∂μ.measure := by
    intro i
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
    simp_rw [← integral_mul_const]
    exact (integral_finsetSum _ (fun j _ => (integrable_toOp_entry i j μ).mul_const _)).symm
  simp only [quadraticForm]
  have hmv_eq : (Matrix.of fun i j : Fin d => ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure).mulVec x =
      fun i => ∫ σ : DensityOp d, (σ.toOp.mulVec x) i ∂μ.measure := funext hmv
  rw [hmv_eq]
  simp only [dotProduct]
  simp_rw [← integral_const_mul]
  have hint : ∀ i : Fin d, Integrable
      (fun σ : DensityOp d => star x i * (σ.toOp.mulVec x) i) μ.measure := by
    intro i
    apply Integrable.const_mul
    simp only [Matrix.mulVec, dotProduct]
    apply integrable_finsetSum
    intro j _
    exact (integrable_toOp_entry i j μ).mul_const _
  rw [← (integral_finsetSum _ (fun i _ => hint i))]
  have hre : ∀ z : ℂ, z.re = Complex.reCLM z := fun z => (Complex.reCLM_apply z).symm
  simp_rw [hre]
  rw [ContinuousLinearMap.integral_comp_comm]
  exact integrable_finsetSum _ (fun i _ => hint i)

/-- The entrywise integral ∫ σ_{ij} dμ(σ) has trace 1.
    Proof: Tr(M) = ∑ᵢ ∫ σ_{ii} dμ = ∫ ∑ᵢ σ_{ii} dμ = ∫ Tr(σ) dμ = ∫ 1 dμ = 1. -/
private lemma integralSingleCopy_trace {d : ℕ} [NeZero d] (μ : DensityMeasure d) :
    Matrix.trace
      (Matrix.of fun i j : Fin d => ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure) = 1 := by
  -- Unfold trace to ∑ i, M i i and Matrix.of to get ∑ i, ∫ σ, σ.toOp i i ∂μ = 1
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  -- Swap ∑ and ∫ via integral_finsetSum
  rw [← MeasureTheory.integral_finsetSum]
  · -- Recognise ∑ i, σ.toOp i i = Tr(σ) = 1, so integrand is constant 1
    have : (fun a : DensityOp d => ∑ i, a.toOp i i) = fun _ => (1 : ℂ) := by
      ext a
      change a.toOp.trace = 1
      exact a.trace_one
    rw [this]
    have := μ.isProbability
    simp [MeasureTheory.integral_const, MeasureTheory.Measure.real,
      MeasureTheory.IsProbabilityMeasure.measure_univ]
  · intro i _
    exact integrable_toOp_entry i i μ

/-- Integral of single-copy states: ∫ σ dμ(σ).

    This is the k=1 case: a convex combination of single-system states,
    defined entrywise via Bochner integration of ℂ-valued functions. -/
noncomputable def integralSingleCopy {d : ℕ} [NeZero d]
    (μ : DensityMeasure d) : DensityOp d :=
  let M : Op d := Matrix.of fun i j =>
    ∫ σ : DensityOp d, σ.toOp i j ∂μ.measure
  ⟨⟨⟨M, integralSingleCopy_hermitian μ⟩,
    integralSingleCopy_posSemidef μ⟩,
   integralSingleCopy_trace μ⟩

/-- Push forward a `DensityMeasure` along the second-factor partial trace. -/
lemma pushforward_partialTraceB_exists {d : ℕ} [NeZero d]
    (ν : DensityMeasure (d * d)) :
    ∃ μ : DensityMeasure d,
      integralSingleCopy μ =
        DensityOp.partialTraceB (integralSingleCopy ν) := by
  let f := (DensityOp.partialTraceB : DensityOp (d * d) → DensityOp d)
  have hf : Measurable f := partialTraceB_measurable
  haveI := ν.isProbability
  let μ : DensityMeasure d :=
    { measure := Measure.map f ν.measure
      isProbability := by
        constructor
        rw [Measure.map_apply hf MeasurableSet.univ]
        simp only [Set.preimage_univ]
        exact IsProbabilityMeasure.measure_univ }
  refine ⟨μ, ?_⟩
  apply DensityOp.ext
  ext i j
  simp only [integralSingleCopy, Matrix.of_apply]
  have h_entry_cont : ∀ (a : Fin d) (b : Fin d), Continuous
      (fun σ : DensityOp d => σ.toOp a b) := by
    intro a b
    change Continuous ((fun M : Matrix (Fin d) (Fin d) ℂ => M a b) ∘
      (fun σ : DensityOp d => σ.toOp))
    exact ((continuous_apply b).comp (continuous_apply a)).comp continuous_induced_dom
  have h_asm : AEStronglyMeasurable (fun σ : DensityOp d => σ.toOp i j)
      (Measure.map f ν.measure) :=
    (h_entry_cont i j).measurable.aestronglyMeasurable
  rw [integral_map hf.aemeasurable h_asm]
  unfold DensityOp.partialTraceB PosSemidefOp.partialTraceB partialTraceB
  simp only [Matrix.of_apply]
  change ∫ ρ : DensityOp (d * d),
    (∑ k : Fin d, ρ.toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))) ∂ν.measure =
    ∑ k : Fin d, ∫ σ : DensityOp (d * d),
      σ.toOp (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) ∂ν.measure
  rw [integral_finsetSum]
  exact fun k _ => integrable_toOp_entry (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) ν

-- Integral of tensor powers: ∫ σ^⊗n dμ(σ).
-- Same entrywise approach as integralSingleCopy but integrand is σ.tensorPowGen n.

/-- Coordinate extraction `σ ↦ (σ^⊗n)_{ij}` is integrable with respect to any probability measure
on states: it is continuous on the compact state space. The tensor-power analogue of
`integrable_toOp_entry`. -/
lemma integrable_tensorPow_entry {d : ℕ} [NeZero d]
    (n : ℕ) [NeZero n] [NeZero (d ^ n)] (i j : Fin (d ^ n)) (μ : DensityMeasure d) :
    MeasureTheory.Integrable
      (fun σ : DensityOp d => (σ.tensorPowGen n).toOp i j) μ.measure := by
  haveI := μ.isProbability
  exact ((continuous_apply j).comp
    ((continuous_apply i).comp continuous_tensorPowGen_toOp)).integrable_of_compactSpace

/-- The entrywise integral ∫ (σ^⊗n)_{ij} dμ(σ) is Hermitian.
    Same proof pattern as integralSingleCopy_hermitian via integral_conj. -/
private lemma integralTensorPower_hermitian {d : ℕ} [NeZero d]
    (n : ℕ) [NeZero n] [NeZero (d ^ n)] (μ : DensityMeasure d) :
    Matrix.IsHermitian
      (Matrix.of fun i j : Fin (d ^ n) =>
        ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  change (starRingEnd ℂ) _ = _
  rw [← integral_conj (𝕜 := ℂ)]
  congr 1; ext σ
  exact congrFun (congrFun (σ.tensorPowGen n).isHermitian i) j

/-- The entrywise integral ∫ (σ^⊗n)_{ij} dμ(σ) is positive semidefinite.
    Same proof pattern as integralSingleCopy_posSemidef. -/
private lemma integralTensorPower_posSemidef {d : ℕ} [NeZero d]
    (n : ℕ) [NeZero n] [NeZero (d ^ n)] (μ : DensityMeasure d) :
    ∀ x : Fin (d ^ n) → ℂ,
      0 ≤ (quadraticForm
        (Matrix.of fun i j : Fin (d ^ n) =>
          ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure)
        x).re := by
  intro x
  have hint : ∀ i j, MeasureTheory.Integrable
      (fun σ : DensityOp d => (σ.tensorPowGen n).toOp i j) μ.measure :=
    fun i j => integrable_tensorPow_entry n i j μ
  have h_int_mv : ∀ k, MeasureTheory.Integrable
      (fun σ : DensityOp d => ((σ.tensorPowGen n).toOp.mulVec x) k) μ.measure := by
    intro k
    -- `(A *ᵥ x) k = ∑ⱼ A k j * x j` by definition
    change MeasureTheory.Integrable
      (fun σ : DensityOp d => ∑ j, (σ.tensorPowGen n).toOp k j * x j) μ.measure
    exact MeasureTheory.integrable_finsetSum _ (fun j _ => (hint k j).mul_const (x j))
  have h_int : MeasureTheory.Integrable
      (fun σ : DensityOp d => quadraticForm (σ.tensorPowGen n).toOp x) μ.measure := by
    change MeasureTheory.Integrable
      (fun σ : DensityOp d => ∑ k, star x k * ((σ.tensorPowGen n).toOp.mulVec x) k) μ.measure
    exact MeasureTheory.integrable_finsetSum _ (fun k _ =>
      (h_int_mv k).const_mul (star x k))
  suffices key : quadraticForm
      (Matrix.of fun i j : Fin (d ^ n) =>
        ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure) x =
      ∫ σ : DensityOp d, quadraticForm (σ.tensorPowGen n).toOp x ∂μ.measure by
    rw [key]
    change 0 ≤ RCLike.re
      (∫ σ : DensityOp d, quadraticForm (σ.tensorPowGen n).toOp x ∂μ.measure)
    rw [← integral_re h_int]
    exact MeasureTheory.integral_nonneg
      (fun σ => (σ.tensorPowGen n).toPosSemidefOp.pos_semidef x)
  unfold quadraticForm
  have h_mv : (Matrix.of fun i j : Fin (d ^ n) =>
      ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure).mulVec x =
      fun k => ∫ σ, ((σ.tensorPowGen n).toOp.mulVec x) k ∂μ.measure := by
    ext k
    change ∑ j, (∫ σ, (σ.tensorPowGen n).toOp k j ∂μ.measure) * x j =
        ∫ σ, ∑ j, (σ.tensorPowGen n).toOp k j * x j ∂μ.measure
    simp_rw [← integral_mul_const]
    exact (MeasureTheory.integral_finsetSum _
      (fun j _ => (hint k j).mul_const (x j))).symm
  rw [h_mv]
  change ∑ k, star x k * ∫ σ, ((σ.tensorPowGen n).toOp.mulVec x) k ∂μ.measure =
      ∫ σ, ∑ k, star x k * ((σ.tensorPowGen n).toOp.mulVec x) k ∂μ.measure
  simp_rw [← integral_const_mul]
  exact (MeasureTheory.integral_finsetSum _
    (fun k _ => (h_int_mv k).const_mul (star x k))).symm

/-- The entrywise integral ∫ (σ^⊗n)_{ij} dμ(σ) has trace 1.
    Same proof pattern as integralSingleCopy_trace. -/
private lemma integralTensorPower_trace {d : ℕ} [NeZero d]
    (n : ℕ) [NeZero n] [NeZero (d ^ n)] (μ : DensityMeasure d) :
    Matrix.trace
      (Matrix.of fun i j : Fin (d ^ n) =>
        ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure) = 1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [← MeasureTheory.integral_finsetSum _
    (fun i _ => integrable_tensorPow_entry n i i μ)]
  have h : ∀ σ : DensityOp d, ∑ i : Fin (d ^ n), (σ.tensorPowGen n).toOp i i = 1 :=
    fun σ => by change (σ.tensorPowGen n).toOp.trace = 1; exact (σ.tensorPowGen n).trace_one
  simp_rw [h]
  haveI := μ.isProbability
  rw [MeasureTheory.integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- Integral of tensor powers: ∫ σ^⊗n dμ(σ).

    This represents a convex combination of i.i.d. states, where the
    single-copy states are distributed according to μ. Defined entrywise
    via Bochner integration of ℂ-valued functions. -/
noncomputable def integralTensorPower {d : ℕ} [NeZero d] (n : ℕ)
    [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d) : DensityOp (d ^ n) :=
  let M : Op (d ^ n) := Matrix.of fun i j =>
    ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure
  ⟨⟨⟨M, integralTensorPower_hermitian n μ⟩,
    integralTensorPower_posSemidef n μ⟩,
   integralTensorPower_trace n μ⟩

section IntegralMap

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The entrywise-defined de Finetti mixture `integralTensorPower` is the Bochner integral of
    the tensor powers (integrability: the tensor-power map is continuous on the compact state
    space). -/
lemma integralTensorPower_toOp_eq_integral {d : ℕ} [NeZero d] (n : ℕ) [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d) :
    (integralTensorPower n μ).toOp
      = ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp ∂μ.measure := by
  haveI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  ext i j
  exact (matrix_integral_entry _ continuous_tensorPowGen_toOp.integrable_of_compactSpace i j).symm

/-- A complex-linear operator map commutes with the tensor-power mixture. -/
lemma integralTensorPower_map {d m : ℕ} [NeZero d] (n : ℕ) [NeZero n]
    (μ : DensityMeasure d) (Ψ : Op (d ^ n) →ₗ[ℂ] Op m) :
    Ψ (integralTensorPower n μ).toOp =
      ∫ σ : DensityOp d, Ψ (σ.tensorPowGen n).toOp ∂μ.measure := by
  haveI := μ.isProbability
  rw [integralTensorPower_toOp_eq_integral]
  exact (Ψ.toContinuousLinearMap.integral_comp_comm
    continuous_tensorPowGen_toOp.integrable_of_compactSpace).symm

end IntegralMap

/-!
## Haar Pushforward Measure

The de Finetti measure used later in the library is obtained by pushing
normalized Haar measure on `U(d)` forward along `U ↦ |U0⟩⟨U0|`.
-/

/-- Map from unitary U to the pure-state density operator |Uψ₀⟩⟨Uψ₀|,
    where ψ₀ = |0⟩ is a fixed reference state.
    Constructs the ket U|0⟩ (first column of U) and forms |Uψ₀⟩⟨Uψ₀|. -/
noncomputable def pureStateMap {d : ℕ} [NeZero d]
    (U : unitaryGroup (Fin d) ℂ) : DensityOp d :=
  -- U|0⟩ is the first column of U, viewed as a Ket
  let ψ : Ket d := ⟨fun i => (U : Matrix (Fin d) (Fin d) ℂ) i 0⟩
  DensityOp.fromPure ψ (by
    -- ψ†ψ = ∑ᵢ conj(U_{i,0}) * U_{i,0} = (U†U)_{0,0} = I_{0,0} = 1
    simp only [bra_mul_ket_eq, Ket.dag]
    -- Extract (U†U)_{0,0} = 1 from U being unitary
    have hU := UnitaryGroup.star_mul_self U
    -- hU : star U.val * U.val = 1 (as matrices)
    have h00 := congr_fun (congr_fun hU 0) 0
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h00
    exact h00)

/-- The pure-state map U ↦ |Uψ₀⟩⟨Uψ₀| is continuous. -/
lemma pureStateMap_continuous {d : ℕ} [NeZero d] :
    Continuous (@pureStateMap d _) := by
  -- DensityOp topology is induced from toOp, so reduce to continuity of entries
  rw [continuous_induced_rng]
  apply continuous_pi; intro i; apply continuous_pi; intro j
  -- Each entry (pureStateMap U).toOp i j = U i 0 * star (U j 0)
  -- which is a product of continuous functions on unitaryGroup
  have h_entry : ∀ U : unitaryGroup (Fin d) ℂ,
      ((fun ρ : DensityOp d => ρ.toOp) ∘ pureStateMap) U i j =
      (U : Matrix (Fin d) (Fin d) ℂ) i 0 *
        star ((U : Matrix (Fin d) (Fin d) ℂ) j 0) := by
    intro U
    simp only [Function.comp, pureStateMap, DensityOp.fromPure,
      ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply]
  simp_rw [show (fun U => ((fun ρ : DensityOp d => ρ.toOp) ∘
    pureStateMap) U i j) = (fun U : unitaryGroup (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) i 0 *
      star ((U : Matrix (Fin d) (Fin d) ℂ) j 0)) from
    funext h_entry]
  have h1 : Continuous (fun U : unitaryGroup (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)
  have h2 : Continuous (fun U : unitaryGroup (Fin d) ℂ =>
      (U : Matrix (Fin d) (Fin d) ℂ) j 0) :=
    (continuous_apply 0).comp ((continuous_apply j).comp continuous_subtype_val)
  exact h1.mul (continuous_star.comp h2)

/-- The pure-state map U ↦ |Uψ₀⟩⟨Uψ₀| is measurable. -/
lemma pureStateMap_measurable {d : ℕ} [NeZero d] :
    Measurable (@pureStateMap d _) :=
  pureStateMap_continuous.measurable

/-- `pureStateMap U = |U|0⟩⟩⟨U|0⟩|` is a pure density operator. -/
lemma pureStateMap_isPure {d : ℕ} [NeZero d]
    (U : unitaryGroup (Fin d) ℂ) : (pureStateMap U).IsPure := by
  unfold pureStateMap
  exact DensityOp.fromPure_isPure _ _

/-- The de Finetti measure: pushforward of normalized Haar measure on U(d)
    through the pure-state map U ↦ |Uψ₀⟩⟨Uψ₀|.

    This gives a probability measure over density operators that is
    the uniform distribution over all pure states (since Haar measure
    on U(d) pushed forward through U ↦ U|0⟩ gives the uniform measure
    on the unit sphere, and then ψ ↦ |ψ⟩⟨ψ| maps to pure states). -/
noncomputable def deFinetti_haarMeasure
    (d : ℕ) [NeZero d] : DensityMeasure d :=
  { measure := Measure.map pureStateMap (haarProbUnitary d)
    isProbability := by
      constructor
      rw [Measure.map_apply pureStateMap_measurable MeasurableSet.univ]
      simp only [Set.preimage_univ]
      exact (haarProbUnitary_isProbability d).measure_univ }

/-- The underlying measure of `deFinetti_haarMeasure d` is the pushforward
    of the normalized Haar measure on `U(d)` through `pureStateMap`. -/
lemma deFinetti_haarMeasure_measure_eq_map (d : ℕ) [NeZero d] :
    (deFinetti_haarMeasure d).measure =
      MeasureTheory.Measure.map pureStateMap (haarProbUnitary d) := rfl

/-- For any real-valued continuous function `g : DensityOp d → ℝ`,
    the integral against `deFinetti_haarMeasure` reduces to an integral
    over the unitary group via `pureStateMap`. -/
lemma integral_deFinetti_haarMeasure_eq_integral_haar
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : DensityOp d → E) (hg : AEStronglyMeasurable g
      (deFinetti_haarMeasure d).measure) :
    (∫ σ : DensityOp d, g σ ∂(deFinetti_haarMeasure d).measure)
      = ∫ U : unitaryGroup (Fin d) ℂ, g (pureStateMap U) ∂(haarProbUnitary d) := by
  rw [deFinetti_haarMeasure_measure_eq_map,
    MeasureTheory.integral_map pureStateMap_measurable.aemeasurable]
  exact hg

/-- The Haar-pushforward de Finetti measure is supported on pure states.

    Every state in the image of `pureStateMap` is rank-1 by
    `pureStateMap_isPure`, so the pushforward of any measure on
    `unitaryGroup (Fin d) ℂ` along `pureStateMap` satisfies the
    `IsProductStateMeasure` predicate. This is the canonical witness
    that `deFinetti_haarMeasure` (the uniform pure-state measure used
    in CKMR Cor II.3 and related constructions) tracks the support
    condition the predicate encodes. -/
lemma deFinetti_haarMeasure_isProductStateMeasure (d : ℕ) [NeZero d] :
    (deFinetti_haarMeasure d).IsProductStateMeasure := by
  -- Reduce to: ∀ᵐ U ∂haar, (pureStateMap U).IsPure, which holds *everywhere*.
  change ∀ᵐ σ ∂(deFinetti_haarMeasure d).measure, σ.IsPure
  rw [deFinetti_haarMeasure_measure_eq_map]
  -- Measurability of the predicate set: `{σ | σ.IsPure}` equals `{σ | σ² = σ}`,
  -- and the latter is closed (hence Borel-measurable) since `σ ↦ σ.toOp` is
  -- continuous. With this we can apply `ae_map_iff`.
  have h_toOp : Continuous (fun σ : DensityOp d => σ.toOp) := continuous_induced_dom
  have h_closed : IsClosed
      (setOf (fun σ : DensityOp d => σ.toOp * σ.toOp = σ.toOp)) :=
    isClosed_eq (h_toOp.mul h_toOp) h_toOp
  have h_meas : MeasurableSet
      (setOf (fun σ : DensityOp d => σ.IsPure)) := by
    have hset : setOf (fun σ : DensityOp d => σ.IsPure)
        = setOf (fun σ : DensityOp d => σ.toOp * σ.toOp = σ.toOp) := rfl
    rw [hset]; exact h_closed.measurableSet
  refine (MeasureTheory.ae_map_iff pureStateMap_measurable.aemeasurable h_meas).mpr ?_
  -- Pure-ness holds pointwise for every `U` in `unitaryGroup (Fin d) ℂ`.
  exact MeasureTheory.ae_of_all _ (fun U => pureStateMap_isPure U)

end InfoTheory.DeFinetti

end
