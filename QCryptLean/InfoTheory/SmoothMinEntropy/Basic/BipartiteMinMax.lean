import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropyFidelity
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.TraceNorm.FidelityPositivity
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct

/-!
# General bipartite conditional min- and max-entropy — SDP D_max, fidelity form, CQ agreement

This module builds the minimal *general-bipartite* conditional min- and max-entropy layer for a
sub-normalized state `ρ_AB` on a bipartite register `A ⊗ B`, following Tomamichel (2016) /
Tomamichel–Colbeck–Renner (arXiv:1504.00233, `df:min-entropy` calculus §, `df:max-entropy` §).
It is the object layer underneath the finite-key entropic-uncertainty duality arc
(TLGR, arXiv:1103.4130): the intermediate min-entropy `H_min(A|B)` appearing in that proof is
genuinely non-CQ, so it cannot be phrased through the existing CQ-only interface
(`conditionalMinEntropyReal` / `conditionalMaxEntropyFidelityReal`).

These are standard textbook definitions; only the Lean *encoding* here is ours.

## Register-order convention (standard, system-first)

For `H(A|B)` of a bipartite state on `A ⊗ B` we take the **system register `A` first** and the
**conditioning register `B` second**, so the operator lives on `SubDensityOp (dA * dB)` and the
reference operator is `1_A ⊗ σ_B` (identity on the kept system `A`, `σ` on the conditioning
system `B`). This is the standard mathematical convention and is the layout in which the
tripartite duality statements read cleanly.

The library's CQ interface uses the *opposite* (quantum-first) convention: `CQState.toJointDensity`
places the quantum conditioning register first and the classical kept register second
(`SubDensityOp (n * card X)`, see `CQState.toJointDensity` docstring). The CQ agreement lemmas
below therefore reconcile the two layouts by an explicit tensor-factor swap; this reconciliation
is the mathematical content of the seam and is stated using the quantum-first realization
`σ ⊗ 1` of the reference (matching how `MaxEntropyFidelity.lean` builds its own reference operator
`cqBlockPosSemidefOp (fun _ => σ) = σ ⊗ 1`).

## Main definitions

- `dmaxFeasibleLambda ρ Q`: `inf {t ≥ 0 : ρ ≼ t · Q}`, the SDP scalar behind `D_max`/`H_min`.
- `bipartiteMinEntropyReal`, `bipartiteMinEntropyOptReal`: `H_min(A|B)_{ρ|σ}` and its
  reference-optimized form, in the real-valued (`Real.log`) formulation. The optimized form takes
  the supremum over `D_max`-*feasible* references only, so the `Real.log 0 = 0` sentinel at
  infeasible `σ` (e.g. `σ = 0`) does not enter the supremum (the ℝ-encoding of the book's `-∞`
  convention; see the def docstring). The CQ reference optimizations use the
  nonnegativity of optimized CQ entropy. Canonical `smoothMinEntropyOpt` takes an `ENNReal`
  supremum, with infinite entropy when the smoothing ball contains zero.
- `bipartiteMaxEntropyReal`, `bipartiteMaxEntropyOptReal`: `H_max(A|B)_{ρ|σ}` via the Uhlmann
  fidelity `log₂ F(ρ, 1_A ⊗ σ)²` on positive fidelity. The optimized
  form has nonzero-state domain and takes the supremum over normalized references
  with `0 < F(ρ, 1_A ⊗ σ)` (support overlap).
- `bipartiteMaxReferenceOp`: the reference operator `1_A ⊗ σ` as a `PosSemidefOp`.
- `PureTripartite`: a normalized tripartite ket with its induced pure density and the three
  pairwise marginals, packaging the data a tripartite duality statement needs.

## Main statements

- `dmaxFeasibleLambda_mono_of_orderPreserving`: `D_max` monotonicity — the SDP scalar decreases
  under any order-preserving, real-homogeneous map applied to both arguments (the abstract form
  of the two data-processing steps used downstream).
- `bipartiteMinEntropy_zeroReference_infeasible` / `hasDmaxFeasibleLambda_of_posDef_reference`:
  soundness of the min-side feasibility guard — the `σ = 0` sentinel reference is excluded from
  the optimized supremum, while every positive-definite reference remains feasible.
- CQ agreement lemmas relating the bipartite definitions on `CQState.toJointDensity` to the CQ
  `conditionalMinEntropyReal` / `conditionalMaxEntropyFidelityReal`.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## The unconditioned `D_max` SDP scalar

For general operators `ρ, Q : Op d`, `dmaxFeasibleLambda ρ Q = inf {t ≥ 0 : ρ ≼ t · Q}` is the
scalar whose base-2 logarithm is the relative-max-entropy `D_max(ρ‖Q) = log₂ λ`. Its negation
`−log₂ λ = −D_max` is the conditional min-entropy, so setting `Q = 1_A ⊗ σ_B` recovers
`H_min(A|B)_{ρ|σ}`.

The definition mirrors `minFeasibleLambda`: same nonnegativity sentinel, same `sInf ∅ = 0`
behaviour on the infeasible boundary.
-/

/-- Predicate: `t` is `D_max`-feasible for `(ρ, Q)`, i.e. `t ≥ 0` and `t · Q` dominates `ρ`
in the operator-semidefinite order. -/
def dmaxIsFeasible {d : ℕ} (ρ Q : Op d) (t : ℝ) : Prop :=
  0 ≤ t ∧ opLe ρ (Complex.ofReal t • Q)

/-- The smallest `D_max`-feasible scalar for `(ρ, Q)`:
`inf {t ≥ 0 : ρ ≼ t · Q}`. Equals `2 ^ (D_max(ρ‖Q))`.

As with `minFeasibleLambda`, the infimum of an empty feasible set is Lean's `sInf ∅ = 0`
sentinel (interpreted as `D_max = +∞`). -/
noncomputable def dmaxFeasibleLambda {d : ℕ} (ρ Q : Op d) : ℝ :=
  sInf (setOf (dmaxIsFeasible ρ Q))

/-- Predicate: the `D_max`-feasible set for `(ρ, Q)` is nonempty. -/
def hasDmaxFeasibleLambda {d : ℕ} (ρ Q : Op d) : Prop :=
  ∃ t : ℝ, dmaxIsFeasible ρ Q t

/-- The `D_max`-feasible set is bounded below by `0`. -/
lemma dmaxFeasibleLambda_bddBelow {d : ℕ} (ρ Q : Op d) :
    BddBelow (setOf (dmaxIsFeasible ρ Q)) :=
  ⟨0, fun _ ht => ht.1⟩

/-- Every `D_max`-feasible scalar bounds the optimum from above. -/
lemma dmaxFeasibleLambda_le_of_feasible {d : ℕ} (ρ Q : Op d) {t : ℝ}
    (ht : dmaxIsFeasible ρ Q t) : dmaxFeasibleLambda ρ Q ≤ t :=
  csInf_le (dmaxFeasibleLambda_bddBelow ρ Q) ht

/-- The `D_max` optimum is nonnegative. -/
lemma dmaxFeasibleLambda_nonneg {d : ℕ} (ρ Q : Op d) :
    0 ≤ dmaxFeasibleLambda ρ Q := by
  unfold dmaxFeasibleLambda
  by_cases h : (setOf (dmaxIsFeasible ρ Q)).Nonempty
  · exact le_csInf h (fun _ ht => ht.1)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty]

/-- Upward-closure of `D_max`-feasibility when the reference `Q` is positive semidefinite:
if `t` is feasible and `t ≤ s`, then `s` is feasible. -/
lemma dmaxIsFeasible_mono_t {d : ℕ} {ρ Q : Op d} (hQ : Q.PosSemidef)
    {t s : ℝ} (ht : dmaxIsFeasible ρ Q t) (hts : t ≤ s) :
    dmaxIsFeasible ρ Q s := by
  refine ⟨ht.1.trans hts, fun v => ?_⟩
  have hstep : opLe (Complex.ofReal t • Q) (Complex.ofReal s • Q) := by
    intro w
    simp only [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_right hts (posSemidef_re_quadraticForm_nonneg hQ w)
  exact opLe_trans ht.2 hstep v

/-!
## Bipartite conditional min-entropy (real-valued)
-/

/-- Real-valued conditional min-entropy `H_min(A|B)_{ρ|σ}` of a sub-normalized bipartite state
`ρ_AB` relative to a reference `σ_B`:

`H_min(A|B)_{ρ|σ} = -log₂ dmaxFeasibleLambda ρ (1_A ⊗ σ)`.

Tomamichel (2016), Def. 6.2 (Tomamichel–Colbeck–Renner, `df:min-entropy`). Real-valued variant
for arithmetic; boundary cases use Lean's `Real.log 0 = 0` sentinel. -/
noncomputable def bipartiteMinEntropyReal {dA dB : ℕ}
    (ρ : SubDensityOp (dA * dB)) (σ : SubDensityOp dB) : ℝ :=
  -Real.log (dmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp)) / Real.log 2

/-- The reference-optimized bipartite conditional min-entropy
`H_min(A|B)_ρ = sup_{σ_B} H_min(A|B)_{ρ|σ}`, the supremum over references `σ` that are
`D_max`-*feasible* for `ρ` against `1_A ⊗ σ`.

Tomamichel (2016), Def. 6.3 (`df:min-entropy`, `cond.tex:149`, `eq:min2`): the supremum ranges
over the pairs `(λ, σ)` with `ρ_AB ≤ 2^{-λ} · 1_A ⊗ σ`, i.e. over *feasible* references only.

The `hasDmaxFeasibleLambda` guard is essential and is not an optimization artifact. An infeasible
`σ` — in particular `σ = 0`, and every rank-deficient `σ` whose support misses `ρ` — has an empty
`D_max`-feasible set, so `dmaxFeasibleLambda ρ (1_A ⊗ σ) = sInf ∅ = 0` (the nonnegativity
sentinel) and `bipartiteMinEntropyReal ρ σ = -Real.log 0 / Real.log 2 = 0`. Without the guard the
value `0` would be a member of the supremum set for *every* `ρ` (via `σ = 0`), forcing
`bipartiteMinEntropyOptReal ρ ≥ 0` by construction and contradicting the true `H_min(A|B) < 0` in
the entangled regime that the duality targets: at the maximally-entangled marginal the unguarded
sup returns `0` instead of `-log₂ d`. In the book this
is automatic: an infeasible reference gives `D_max = +∞`, i.e. `H_min = -∞`, which drops out of the
supremum. The guard is the ℝ-valued encoding of that `-∞` convention. See
`bipartiteMinEntropy_zeroReference_infeasible` (the `σ = 0` sentinel is excluded) and
`hasDmaxFeasibleLambda_of_posDef_reference` (any positive-definite reference `1_A ⊗ σ` remains
feasible, so the guarded family is nonempty). -/
noncomputable def bipartiteMinEntropyOptReal {dA dB : ℕ}
    (ρ : SubDensityOp (dA * dB)) : ℝ :=
  sSup {h | ∃ σ : SubDensityOp dB,
    hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) σ.toOp) ∧
    h = bipartiteMinEntropyReal ρ σ}

/-!
## Guard soundness: the sentinel is excluded and a genuine feasible family remains

Two facts pin down that the `hasDmaxFeasibleLambda` guard in `bipartiteMinEntropyOptReal`
removes exactly the `Real.log 0 = 0` sentinel and nothing legitimate. The zero reference `σ = 0`
is infeasible (so its sentinel value `0` is no longer forced into the supremum), while every
positive-definite reference `1_A ⊗ σ` remains feasible (so the guarded supremum is over a
genuine, nonempty family).
-/

/-- **Guard acceptance — the `σ = 0` sentinel is excluded.** For a state `ρ` of positive trace
(any normalized `ρ`, `tr ρ = 1`), the zero reference `σ = 0` — whose tensor `1_A ⊗ 0` vanishes —
is *not* `D_max`-feasible. Hence the value `bipartiteMinEntropyReal ρ 0 = -Real.log 0 / Real.log 2
= 0` is no longer a member of the guarded supremum set: the guard removes precisely the sentinel
that forced `bipartiteMinEntropyOptReal ρ ≥ 0` in the unguarded definition. -/
theorem bipartiteMinEntropy_zeroReference_infeasible {dA dB : ℕ}
    (ρ : SubDensityOp (dA * dB)) (hρ : 0 < ρ.trace) :
    ¬ hasDmaxFeasibleLambda ρ.toOp (Op.tensor (1 : Op dA) (0 : SubDensityOp dB).toOp) := by
  rintro ⟨t, _, hle⟩
  have htz : Op.tensor (1 : Op dA) ((0 : SubDensityOp dB).toOp) = (0 : Op (dA * dB)) := by
    change Op.tensor (1 : Op dA) (0 : Op dB) = 0
    rw [(zero_smul ℂ (1 : Op dB)).symm, Op.tensor_smul_right, Op.tensor_one, zero_smul]
  rw [htz, smul_zero] at hle
  have htr := trace_mul_le_of_opLe (M := (1 : Op (dA * dB))) Matrix.PosSemidef.one
    ρ.isHermitian Matrix.isHermitian_zero hle
  rw [Matrix.one_mul, Matrix.one_mul, Matrix.trace_zero, Complex.zero_re] at htr
  exact absurd htr (not_le.mpr hρ)

/-- **Guard acceptance — the feasible family is nonempty.** Any positive-definite reference `Q`
is `D_max`-feasible for every positive-semidefinite `ρ` (a real scalar `t` with `ρ ≤ t · Q` exists
by sandwiching with `Q^{-1/2}`). Instantiated at `Q = 1_A ⊗ σ` with `σ` positive definite (in
particular the maximally-mixed reference), this shows the guarded supremum in
`bipartiteMinEntropyOptReal` still ranges over a genuine, nonempty family of feasible references —
the guard removes only the `σ = 0` sentinel, not the legitimate optimization. -/
theorem hasDmaxFeasibleLambda_of_posDef_reference {d : ℕ} {ρ Q : Op d}
    (hρ : ρ.PosSemidef) (hQ : Q.PosDef) : hasDmaxFeasibleLambda ρ Q :=
  Matrix.PosDef.exists_smul_opLe_of_posSemidef hQ hρ

/-!
## Bipartite conditional max-entropy (fidelity form)
-/

/-- The reference operator `1_A ⊗ σ_B` as a positive semidefinite operator on `A ⊗ B`.
This is the fidelity target for `H_max(A|B)`, in the system-first (`A ⊗ B`) layout. -/
noncomputable def bipartiteMaxReferenceOp {dB : ℕ} (dA : ℕ) (σ : DensityOp dB) :
    PosSemidefOp (dA * dB) where
  toOp := Op.tensor (1 : Op dA) σ.toOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Op.tensor_conjTranspose, conjTranspose_one, σ.isHermitian]
  pos_semidef :=
    Op.tensor_posSemidef (1 : Op dA) σ.toOp
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_one])
      σ.isHermitian
      (fun x => posSemidef_re_quadraticForm_nonneg Matrix.PosSemidef.one x)
      σ.pos_semidef

@[simp]
lemma bipartiteMaxReferenceOp_toOp {dB : ℕ} (dA : ℕ) (σ : DensityOp dB) :
    (bipartiteMaxReferenceOp dA σ).toOp = Op.tensor (1 : Op dA) σ.toOp :=
  rfl

/-- Real conditional max-entropy relative to a normalized reference with positive fidelity:
`H_max(A|B)_{ρ|σ} = log₂ F(ρ_AB, 1_A ⊗ σ_B)²`.

The zero-fidelity value is `−∞` and is excluded from this real domain.
Reference: Tomamichel (2016), Definition 6.3. -/
noncomputable def bipartiteMaxEntropyReal {dA dB : ℕ} [NeZero (dA * dB)]
    (ρ : SubDensityOp (dA * dB)) (σ : DensityOp dB)
    (_hF : 0 < fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp dA σ)) : ℝ :=
  Real.log ((fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp dA σ)) ^ 2) / Real.log 2

/-- Conditional max-entropy of a nonzero bipartite state, optimized over normalized
references with positive fidelity:
`H_max(A|B)_ρ = sup_{σ_B ∈ S_=(B), F(ρ, 1_A ⊗ σ_B) > 0} log₂ F(ρ, 1_A ⊗ σ_B)²`.

Zero-fidelity references have extended entropy `−∞` and do not affect the supremum.
The nonzero-state domain excludes the empty optimization with value `−∞`.
Reference: Tomamichel (2016), Definition 6.3. -/
noncomputable def bipartiteMaxEntropyOptReal {dA dB : ℕ} [NeZero (dA * dB)]
    (ρ : SubDensityOp (dA * dB)) (_hρ : ρ.toOp ≠ 0) : ℝ :=
  sSup {h | ∃ (σ : DensityOp dB)
    (hF : 0 < fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp dA σ)),
    h = bipartiteMaxEntropyReal ρ σ hF}

/-- **Max-side guard nonemptiness (B-fidpos corollary).** Every positive-definite
reference `σ` (in particular the maximally-mixed reference) satisfies the
`0 < fidelity` overlap guard of `bipartiteMaxEntropyOptReal`, for any nonzero state
`ρ`: the reference `1_A ⊗ σ` is then positive definite, so `fidelity` against it is
strictly positive by `fidelity_pos_of_posDef`.

This is the fidelity twin of the min-side feasibility lemma
`hasDmaxFeasibleLambda_of_posDef_reference`: it shows the guarded supremum in
`bipartiteMaxEntropyOptReal` still ranges over a genuine, nonempty family of
references, discharging the max-side nonemptiness obligation that the `≤` direction
of the pure-state duality (`duality_le`) depends on. -/
theorem bipartiteMaxReference_fidelity_pos_of_posDef {dA dB : ℕ} [NeZero (dA * dB)]
    (ρ : SubDensityOp (dA * dB)) (hρ : ρ.toOp ≠ 0)
    (σ : DensityOp dB) (hσ : σ.toOp.PosDef) :
    0 < fidelity ρ.toPosSemidefOp (bipartiteMaxReferenceOp dA σ) := by
  refine fidelity_pos_of_posDef ρ.toPosSemidefOp (bipartiteMaxReferenceOp dA σ) hρ ?_
  rw [bipartiteMaxReferenceOp_toOp]
  unfold Quantum.TensorProducts.Op.tensor
  rw [Matrix.reindex_apply]
  exact (Matrix.PosDef.kronecker Matrix.PosDef.one hσ).submatrix finProdFinEquiv.symm.injective

/-!
## `D_max` monotonicity under order-preserving maps

The core data-processing ingredient: `dmaxFeasibleLambda` cannot increase when an
order-preserving, real-homogeneous map `Φ` is applied to *both* arguments. These two properties
(`opLe`-monotonicity and commuting with real scalar multiplication) are exactly the defining
properties of a positive linear map, so this covers the pinching and measurement channels used
by the downstream entropic-uncertainty data-processing steps. Stated at this abstract generality
rather than through `IsCPTP` so that no complete-positivity-to-order-preservation bridge is
assumed. -/
theorem dmaxFeasibleLambda_mono_of_orderPreserving {d d' : ℕ} (Φ : Op d → Op d')
    (hmono : ∀ A B : Op d, opLe A B → opLe (Φ A) (Φ B))
    (hsmul : ∀ (t : ℝ) (Q : Op d), Φ (Complex.ofReal t • Q) = Complex.ofReal t • Φ Q)
    (ρ Q : Op d) (hfeas : hasDmaxFeasibleLambda ρ Q) :
    dmaxFeasibleLambda (Φ ρ) (Φ Q) ≤ dmaxFeasibleLambda ρ Q := by
  have hsub : setOf (dmaxIsFeasible ρ Q) ⊆ setOf (dmaxIsFeasible (Φ ρ) (Φ Q)) := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have himg : opLe (Φ ρ) (Φ (Complex.ofReal t • Q)) := hmono _ _ ht.2
    rwa [hsmul t Q] at himg
  obtain ⟨t, ht⟩ := hfeas
  exact csInf_le_csInf (dmaxFeasibleLambda_bddBelow (Φ ρ) (Φ Q)) ⟨t, ht⟩ hsub

/-!
## Pure tripartite states

Packaging for the tripartite entropic-uncertainty duality: a normalized ket on `A ⊗ B ⊗ C`,
its induced pure density, and the three pairwise reduced states, so that a duality statement
`H_max(A|B)_ρ = -H_min(A|C)_ρ` can be written over explicit witness data without inline
reindexing/casts. The reduced states other than `A ⊗ B` are obtained by relabelling the ket's
tensor factors (a norm-preserving basis permutation) and tracing out the trailing factor.
-/

/-- Relabel a ket along a basis-index equivalence `e : Fin n ≃ Fin m`. -/
def Ket.reindexEquiv {n m : ℕ} (e : Fin n ≃ Fin m) (ψ : Ket n) : Ket m :=
  ⟨fun i => ψ.vec (e.symm i)⟩

/-- Basis relabelling preserves the squared norm `⟨ψ|ψ⟩`, hence normalization. -/
lemma Ket.reindexEquiv_dag_mul_self {n m : ℕ} (e : Fin n ≃ Fin m) (ψ : Ket n) :
    (Ket.reindexEquiv e ψ).dag * (Ket.reindexEquiv e ψ) = ψ.dag * ψ := by
  rw [bra_mul_ket_eq, bra_mul_ket_eq]
  simp only [Ket.dag_vec, Ket.reindexEquiv]
  exact Equiv.sum_comp e.symm (fun j => (starRingEnd ℂ) (ψ.vec j) * ψ.vec j)

/-- The reindex equivalence realizing the tensor-factor permutation `A⊗B⊗C ≃ A⊗C⊗B`
(swapping the last two factors), used to expose the `A⊗C` marginal. -/
def reorderTripartiteACB (dA dB dC : ℕ) :
    Fin (dA * dB * dC) ≃ Fin (dA * dC * dB) :=
  (finProdFinEquiv (m := dA * dB) (n := dC)).symm.trans
    (((finProdFinEquiv (m := dA) (n := dB)).symm.prodCongr (Equiv.refl (Fin dC))).trans
      (((Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).trans
          (((Equiv.refl (Fin dA)).prodCongr (Equiv.prodComm (Fin dB) (Fin dC))).trans
            (Equiv.prodAssoc (Fin dA) (Fin dC) (Fin dB)).symm)).trans
        (((finProdFinEquiv (m := dA) (n := dC)).prodCongr (Equiv.refl (Fin dB))).trans
          finProdFinEquiv)))

/-- The reindex equivalence realizing the tensor-factor permutation `A⊗B⊗C ≃ B⊗C⊗A`
(cycling `A` to the back), used to expose the `B⊗C` marginal. -/
def reorderTripartiteBCA (dA dB dC : ℕ) :
    Fin (dA * dB * dC) ≃ Fin (dB * dC * dA) :=
  (finProdFinEquiv (m := dA * dB) (n := dC)).symm.trans
    (((finProdFinEquiv (m := dA) (n := dB)).symm.prodCongr (Equiv.refl (Fin dC))).trans
      (((Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)).trans
          (Equiv.prodComm (Fin dA) (Fin dB × Fin dC))).trans
        (((finProdFinEquiv (m := dB) (n := dC)).prodCongr (Equiv.refl (Fin dA))).trans
          finProdFinEquiv)))

/-- A pure tripartite state on registers `A ⊗ B ⊗ C`: a normalized ket, from which the pure
density and pairwise marginals are derived. -/
structure PureTripartite (dA dB dC : ℕ) where
  /-- The tripartite state vector on `A ⊗ B ⊗ C`. -/
  ket : Ket (dA * dB * dC)
  /-- The state vector is a unit vector: `⟨ψ|ψ⟩ = 1`. -/
  normalized : ket.dag * ket = 1

namespace PureTripartite

variable {dA dB dC : ℕ}

/-- The induced pure density operator `|ψ⟩⟨ψ|` on `A ⊗ B ⊗ C`. -/
noncomputable def density (T : PureTripartite dA dB dC) : DensityOp (dA * dB * dC) :=
  DensityOp.fromPure T.ket T.normalized

/-- The induced density is pure: `ρ² = ρ`. -/
lemma density_isPure (T : PureTripartite dA dB dC) : T.density.IsPure :=
  DensityOp.fromPure_isPure T.ket T.normalized

/-- The `A ⊗ B` marginal `ρ_AB = Tr_C |ψ⟩⟨ψ|`. -/
noncomputable def marginalAB (T : PureTripartite dA dB dC) : DensityOp (dA * dB) :=
  T.density.partialTraceB

/-- The `A ⊗ C` marginal `ρ_AC = Tr_B |ψ⟩⟨ψ|`, obtained by relabelling `A⊗B⊗C → A⊗C⊗B`
and tracing out the trailing (`B`) factor. -/
noncomputable def marginalAC (T : PureTripartite dA dB dC) : DensityOp (dA * dC) :=
  (DensityOp.fromPure (Ket.reindexEquiv (reorderTripartiteACB dA dB dC) T.ket)
    (by rw [Ket.reindexEquiv_dag_mul_self]; exact T.normalized)).partialTraceB

/-- The `B ⊗ C` marginal `ρ_BC = Tr_A |ψ⟩⟨ψ|`, obtained by relabelling `A⊗B⊗C → B⊗C⊗A`
and tracing out the trailing (`A`) factor. -/
noncomputable def marginalBC (T : PureTripartite dA dB dC) : DensityOp (dB * dC) :=
  (DensityOp.fromPure (Ket.reindexEquiv (reorderTripartiteBCA dA dB dC) T.ket)
    (by rw [Ket.reindexEquiv_dag_mul_self]; exact T.normalized)).partialTraceB

/-- The `A ⊗ B` marginal is a normalized state: `Tr ρ_AB = 1`. -/
lemma marginalAB_trace_one (T : PureTripartite dA dB dC) : T.marginalAB.toOp.trace = 1 :=
  T.marginalAB.trace_one

/-- The `A ⊗ C` marginal is a normalized state: `Tr ρ_AC = 1`. -/
lemma marginalAC_trace_one (T : PureTripartite dA dB dC) : T.marginalAC.toOp.trace = 1 :=
  T.marginalAC.trace_one

/-- The `B ⊗ C` marginal is a normalized state: `Tr ρ_BC = 1`. -/
lemma marginalBC_trace_one (T : PureTripartite dA dB dC) : T.marginalBC.toOp.trace = 1 :=
  T.marginalBC.trace_one

end PureTripartite

/-!
## Agreement with the CQ interface (the seam)

For a `CQState X n` (classical register `X`, quantum register `A` of dimension `n`), the CQ
conditional entropies `conditionalMinEntropyReal` / `conditionalMaxEntropyFidelityReal` compute
`H(X|A)`: they *keep* the classical register `X` and *condition on* the quantum register `A`.

The library realizes the joint state `ρ_XA` in a **quantum-first** layout
(`CQState.toJointDensity : SubDensityOp (n * card X)`, quantum register `A` first, classical
register `X` second — see its docstring). Consequently the conditioning register `A` is the
*first* tensor factor and the reference operator `I_X ⊗ σ_A` is realized as `σ_A ⊗ 1_X`, exactly
as `MaxEntropyFidelity.lean` builds its own reference (`conditionalMaxEntropyFidelityReferenceOp σ =
cqBlockPosSemidefOp (fun _ => σ) = σ ⊗ 1_X`).

The lemmas here therefore relate the CQ definitions to the general bipartite *primitives*
(`dmaxFeasibleLambda`, `fidelity`) evaluated on `CQState.toJointDensity` against the
quantum-first reference `σ ⊗ 1_X`. This is the general-bipartite entropy of `ρ_XA` with the
system register `X` and conditioning register `A` placed in the library's quantum-first order;
it is `bipartiteMinEntropyReal` / `bipartiteMaxEntropyReal` with the two tensor factors in the
opposite (system-first) order, the difference being the tensor-factor swap that reconciles the
library's quantum-first CQ convention with the standard system-first bipartite convention.
-/

open scoped BigOperators

/-- **Reference bridge.** The constant CQ block-diagonal operator `⊕_x M`, in the quantum-first
reindexing used by `CQState.toJointDensity`, is the tensor `M ⊗ 1_X`. This identifies the CQ
reference operator `I_X ⊗ σ_A` (realized quantum-first as `σ_A ⊗ 1_X`) with a genuine tensor. -/
lemma reindex_blockDiagonal_const_eq_tensor_one
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (M : Op n) :
    Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal (fun _ : X => M)) =
      Op.tensor M (1 : Op (Fintype.card X)) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Op.tensor,
    Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Matrix.one_apply, finProdFinEquiv_symm_apply]
  by_cases h : i.modNat = j.modNat
  · rw [h]; simp
  · rw [if_neg h, if_neg (fun hh => h ((Fintype.equivFin X).symm.injective hh)), mul_zero]

/-- The CQ max-entropy reference operator `I_X ⊗ σ_A` is, in the quantum-first layout, the tensor
`σ_A ⊗ 1_X`. Hence the CQ conditional max-entropy `conditionalMaxEntropyFidelityReal` is the
Uhlmann fidelity of the joint density against the genuine tensor reference `σ ⊗ 1_X` — the
quantum-first realization of the general bipartite max-entropy reference. -/
lemma conditionalMaxEntropyFidelityReferenceOp_toOp_eq_tensor
    {X : Type*} [Fintype X] {n : ℕ} (σ : DensityOp n) :
    (conditionalMaxEntropyFidelityReferenceOp (X := X) σ).toOp =
      Op.tensor σ.toOp (1 : Op (Fintype.card X)) := by
  classical
  rw [conditional_max_entropy_fidelity_reference_op_eq_cq_block (X := X) σ,
    cqBlockPosSemidefOp_toOp]
  exact reindex_blockDiagonal_const_eq_tensor_one σ.toOp

/-- **Min-entropy feasibility, forward inclusion.** A CQ min-entropy feasible scalar `t`
(blockwise domination `ρ_A(x) ≼ t · σ` for every outcome `x`) is `D_max`-feasible for the joint
density against the quantum-first reference `σ ⊗ 1_X`. This is the block-diagonal assembly
direction, via `opLe_reindex_blockDiagonal_of_forall` and the reference bridge. -/
lemma dmaxIsFeasible_toJointDensity_tensor_one_of_isFeasible
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ} (ht : isFeasible ρ σ t) :
    dmaxIsFeasible ρ.toJointDensity.toOp
      (Op.tensor σ.toOp (1 : Op (Fintype.card X))) t := by
  refine ⟨ht.1, ?_⟩
  have hbd := opLe_reindex_blockDiagonal_of_forall
    (fun x : X => (ρ.stateMap x).toOp)
    (fun _ : X => Complex.ofReal t • σ.toOp)
    (fun x => (ρ.stateMap x).isHermitian)
    (fun _ => SubDensityOp.toOp_smul_isHermitian σ ht.1)
    (fun x => ht.2 x)
  simp only at hbd
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rw [reindex_blockDiagonal_const_eq_tensor_one (Complex.ofReal t • σ.toOp),
    Op.tensor_smul_left] at hbd
  exact hbd

/-- The quadratic form of a quantum-first reindexed block-diagonal operator, evaluated at the
block-`x`-supported test vector `w_x(v)`, equals the block-`x` quadratic form at `v`. This is the
single-block restriction identity behind the reverse (block-extraction) inclusion. -/
private lemma quadraticForm_reindex_blockDiagonal_block_support
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (M : X → Op n) (x : X) (v : Fin n → ℂ) :
    let e : Fin n × X ≃ Fin (n * Fintype.card X) :=
      (Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv
    quadraticForm (Matrix.reindex e e (Matrix.blockDiagonal M))
        (fun p => if (e.symm p).2 = x then v (e.symm p).1 else 0) =
      quadraticForm (M x) v := by
  intro e
  set w : Fin (n * Fintype.card X) → ℂ :=
    fun p => if (e.symm p).2 = x then v (e.symm p).1 else 0 with hw
  set u : Fin n × X → ℂ := fun s => if s.2 = x then v s.1 else 0 with hu
  have hwe : ∀ s : Fin n × X, w (e s) = u s := by
    intro s
    simp only [hw, hu, Equiv.symm_apply_apply]
  -- Reduce the reindexed quadratic form to the block-diagonal form on `Fin n × X`.
  have hstep :
      quadraticForm (Matrix.reindex e e (Matrix.blockDiagonal M)) w =
        star u ⬝ᵥ (Matrix.blockDiagonal M).mulVec u := by
    unfold quadraticForm
    rw [Matrix.reindex_apply]
    rw [dotProduct, ← Equiv.sum_comp e (fun a => star w a * ((Matrix.blockDiagonal M).submatrix
      e.symm e.symm).mulVec w a)]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Matrix.mulVec, Matrix.submatrix_apply, Equiv.symm_apply_apply, Pi.star_apply]
    rw [hwe s]
    congr 1
    rw [dotProduct, dotProduct, ← Equiv.sum_comp e
      (fun b => (Matrix.blockDiagonal M) s (e.symm b) * w b)]
    apply Finset.sum_congr rfl
    intro r _
    rw [Equiv.symm_apply_apply, hwe r]
  rw [hstep]
  -- Evaluate the block-diagonal quadratic form on the single-block-supported vector.
  rw [dotProduct, Fintype.sum_prod_type]
  have hcol : ∀ k : X, (fun b => u (b, k)) = if k = x then v else 0 := by
    intro k
    funext b
    simp only [hu]
    by_cases hk : k = x <;> simp [hk]
  simp only [Pi.star_apply, blockDiagonal_mulVec_apply, hcol]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single x]
  · simp only [hu, if_pos rfl]
    rw [quadraticForm, dotProduct]
    apply Finset.sum_congr rfl
    intro a _
    simp [Pi.star_apply]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro a _
    simp [hu, hk]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- **Min-entropy feasibility, reverse inclusion.** If a scalar `t` is `D_max`-feasible for the
joint density against the quantum-first reference `σ ⊗ 1_X`, then it is CQ min-entropy feasible,
i.e. every classical block is dominated: `ρ_A(x) ≼ t · σ`. This is the block-extraction
direction, testing the joint Löwner domination against single-block-supported vectors. -/
lemma isFeasible_of_dmaxIsFeasible_toJointDensity_tensor_one
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) {t : ℝ}
    (ht : dmaxIsFeasible ρ.toJointDensity.toOp
      (Op.tensor σ.toOp (1 : Op (Fintype.card X))) t) :
    isFeasible ρ σ t := by
  refine ⟨ht.1, fun x v => ?_⟩
  have href : Complex.ofReal t • Op.tensor σ.toOp (1 : Op (Fintype.card X)) =
      Matrix.reindex
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans finProdFinEquiv)
        (Matrix.blockDiagonal (fun _ : X => Complex.ofReal t • σ.toOp)) := by
    rw [reindex_blockDiagonal_const_eq_tensor_one, Op.tensor_smul_left]
  have hle := ht.2 (fun p =>
    if (((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans
          finProdFinEquiv).symm p).2 = x
    then v ((((Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin X)).trans
          finProdFinEquiv).symm p).1)
    else 0)
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal, href] at hle
  rw [quadraticForm_reindex_blockDiagonal_block_support (fun y => (ρ.stateMap y).toOp) x v,
    quadraticForm_reindex_blockDiagonal_block_support (fun _ => Complex.ofReal t • σ.toOp) x v]
    at hle
  exact hle

/-- **CQ min-entropy SDP agreement.** The general `D_max` SDP scalar of the joint density
`ρ_XA` against the quantum-first reference `σ_A ⊗ 1_X` equals the CQ min-entropy SDP scalar
`minFeasibleLambda ρ σ`: the two feasible sets coincide (forward = block-diagonal assembly,
reverse = single-block extraction). -/
theorem dmaxFeasibleLambda_toJointDensity_tensor_one_eq_minFeasibleLambda
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    dmaxFeasibleLambda ρ.toJointDensity.toOp
      (Op.tensor σ.toOp (1 : Op (Fintype.card X))) = minFeasibleLambda ρ σ := by
  have hset : setOf (dmaxIsFeasible ρ.toJointDensity.toOp
      (Op.tensor σ.toOp (1 : Op (Fintype.card X)))) = setOf (isFeasible ρ σ) := by
    ext t
    exact ⟨isFeasible_of_dmaxIsFeasible_toJointDensity_tensor_one ρ σ,
      dmaxIsFeasible_toJointDensity_tensor_one_of_isFeasible ρ σ⟩
  unfold dmaxFeasibleLambda minFeasibleLambda
  rw [hset]

/-- **CQ min-entropy agreement.** The bipartite conditional min-entropy of a CQ state, evaluated
on its (quantum-first) joint density against the reference `σ_A ⊗ 1_X`, coincides with the CQ
conditional min-entropy `conditionalMinEntropyReal`.

This is the general bipartite `H_min(X|A)` of `ρ_XA` written in the library's quantum-first
layout (conditioning register `A` first, kept register `X` second); it is
`bipartiteMinEntropyReal` with the two tensor factors in the opposite (system-first) order,
the difference being only the tensor-factor swap reconciling the two register conventions. -/
theorem conditionalMinEntropyReal_eq_dmax_toJointDensity_tensor_one
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) :
    conditionalMinEntropyReal ρ σ =
      -Real.log (dmaxFeasibleLambda ρ.toJointDensity.toOp
        (Op.tensor σ.toOp (1 : Op (Fintype.card X)))) / Real.log 2 := by
  rw [dmaxFeasibleLambda_toJointDensity_tensor_one_eq_minFeasibleLambda]
  rfl

/-- The reference operator `σ_A ⊗ 1_X` as a positive semidefinite operator, in the quantum-first
layout (`σ` on the conditioning quantum register, identity on the kept classical register). This
is the quantum-first realization of the max-entropy reference `I_X ⊗ σ_A`. -/
noncomputable def quantumFirstTensorReferenceOp {n : ℕ} (dX : ℕ) (σ : DensityOp n) :
    PosSemidefOp (n * dX) where
  toOp := Op.tensor σ.toOp (1 : Op dX)
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Op.tensor_conjTranspose, conjTranspose_one, σ.isHermitian]
  pos_semidef :=
    Op.tensor_posSemidef σ.toOp (1 : Op dX) σ.isHermitian
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_one])
      σ.pos_semidef
      (fun x => posSemidef_re_quadraticForm_nonneg Matrix.PosSemidef.one x)

@[simp]
lemma quantumFirstTensorReferenceOp_toOp {n : ℕ} (dX : ℕ) (σ : DensityOp n) :
    (quantumFirstTensorReferenceOp dX σ).toOp = Op.tensor σ.toOp (1 : Op dX) :=
  rfl

/-- The CQ max-entropy reference operator equals the quantum-first tensor reference `σ_A ⊗ 1_X`. -/
lemma conditionalMaxEntropyFidelityReferenceOp_eq_quantumFirstTensorReferenceOp
    {X : Type*} [Fintype X] {n : ℕ} (σ : DensityOp n) :
    conditionalMaxEntropyFidelityReferenceOp (X := X) σ =
      quantumFirstTensorReferenceOp (Fintype.card X) σ :=
  PosSemidefOp.ext (conditionalMaxEntropyFidelityReferenceOp_toOp_eq_tensor σ)

/-- **CQ max-entropy agreement.** The CQ conditional max-entropy `conditionalMaxEntropyFidelityReal`
is the Uhlmann-fidelity conditional max-entropy of the joint density `ρ_XA` against the
quantum-first tensor reference `σ_A ⊗ 1_X`, provided the fidelity is positive:

`H_max(X|A)_{ρ|σ} = log₂ F(ρ_XA, σ_A ⊗ 1_X)²`.

This is the general bipartite `H_max(X|A)` of `ρ_XA` written in the library's quantum-first
layout; it is `bipartiteMaxEntropyReal` with the two tensor factors in the opposite
(system-first) order, the difference being only the tensor-factor swap reconciling the two
register conventions. The max side already factors through the general `fidelity`, so this is an
identification of the reference operator as a genuine tensor. -/
theorem conditionalMaxEntropyFidelityReal_eq_fidelity_quantumFirstTensorReferenceOp
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X] {n : ℕ} [NeZero n]
    [NeZero (n * Fintype.card X)]
    (ρ : CQState X n) (σ : DensityOp n)
    (hF : 0 < fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) :
    conditionalMaxEntropyFidelityReal ρ σ hF =
      Real.log ((fidelity ρ.toJointDensity.toPosSemidefOp
        (quantumFirstTensorReferenceOp (Fintype.card X) σ)) ^ 2) / Real.log 2 := by
  rw [conditionalMaxEntropyFidelityReal,
    conditionalMaxEntropyFidelityReferenceOp_eq_quantumFirstTensorReferenceOp]
  congr!

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
