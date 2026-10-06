import QCryptLean.InfoTheory.QuantumLHL.GeneralRefLHL
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernel
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.FilterKeepContraction
import QCryptLean.Quantum.TensorProducts.Rpow

/-!
# The collision-route classical-announce charge, and the collision-route coarsening step

The smooth-min-entropy route pays a classical announcement through
`InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorLeftKernel_ge_sub_log` (Renner 2005,
arXiv:quant-ph/0512258v2, `main.tex` Lemma 3.1.10 / Cor. 3.1.11). The **collision**
route — the one the low-QBER privacy-amplification chain uses, through
`seedKeyExtractor_traceDistanceGen_le_collisionRoot` — pays it through
`collisionQuantity` instead, and no analogue existed in the tree. This file supplies it, together
with the coarsening step the same chain needs.

## The announce charge

`collisionQuantity σ (fun x => ρ_x)` is Renner's `2^{−H₂(X|E)_{ρ|σ}}`
(arXiv:quant-ph/0512258v2, `main.tex:6889`, `\label{rem:Htworewr}`: for a cq state with
orthogonal conditional operators, `2^{−H₂(ρ_{XB}|σ_B)} = (1/tr ρ)·∑_x tr((σ^{−1/4} ρ_B^x
σ^{−1/4})²)`), and it is the quantity the collision-route privacy-amplification theorem
(`:7080`, `\label{thm:pa}`) consumes.

Tensoring a normalised announcement block `K x` on the **left** of every conditional operator,
against the correspondingly extended reference `(1/d_C)·1 ⊗ σ`, multiplies the collision quantity
by at most the domination constant `c` of the announcement,
`K x ≼ c · (1/d_C)·1` — the same constant, at the same register orientation, that
`opLe_bb84AnnounceKernel_smul_maxMixed` already supplies for the BB84 announcement. The proof
is three steps: the tensor factorisation of `weightedFrobeniusSq`, the evaluation of the
announcement factor against a scalar reference, and `tr(K²) ≤ ‖K‖_op · tr K`
(`Quantum.Operators.trace_sq_le_smul_trace_of_opLe_smul_one`, which sandwiches `K ⪯ t·1` into
`K² ⪯ t·K` and then uses positive-semidefinite trace monotonicity — the same trace-pairing
positivity as Renner's `:10368`, `\label{lem:trprod}`).

The bound is **tight**: for a deterministic announcement `K x = |a x⟩⟨a x|` the announcement factor
is exactly `d_C`, which is also the smallest admissible domination constant, so every inequality
below is an equality and no smaller charge is available. That evaluation is compiled for the
BB84 announcement kernel, where the `stdProj` block is in scope.

## The coarsening step

A classical coarsening `f : X → Y` of a cq state is in general *lossy* for the collision quantity in
the wrong direction — merging two blocks **increases** `tr(·²)`, since `tr((A+B)²) = tr A² + tr B² +
2·tr(AB) ≥ tr A² + tr B²` for `A, B ⪰ 0` (again `\label{lem:trprod}`). So a floor on the fine
register does **not** transfer to a coarsened one for free. It transfers exactly when `f` is
*injective on the support* of the state, and then the collision quantity is **unchanged**, not
merely bounded: `collisionQuantity_coarsen_eq_of_injOn`. The injectivity is what makes the statement
true, not merely what makes the proof work — and it is a real side condition, not a formality:
the BB84 engine exhibits a non-empty accept-and-agree keep set on which the
protocol's own Alice-key coarsening fails to be injective.

## Main statements

- `weightedFrobeniusSq_tensor`: `wfs (τ ⊗ σ) (A ⊗ B) = wfs τ A · wfs σ B`.
- `weightedFrobeniusSq_smul_one`: `wfs (c·1) A = c⁻¹ · ‖A‖_F²`.
- `weightedFrobeniusSq_maxMixed_le_of_opLe`: a normalised, `c`-dominated announcement block has
  `wfs ((1/d_C)·1) (K x) ≤ c`, with equality for a deterministic announcement.
- `collisionQuantity_tensorLeftKernel_le`: the announce charge.
- `collisionQuantity_coarsen_eq_of_injOn`, `collisionQuantity_coarsen_filterKeep_eq_of_injOn`: the
  coarsening step.

References: Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:6870` `\label{def:colentr}`,
`:6889` `\label{rem:Htworewr}`, `:7080` `\label{thm:pa}`, `:10368` `\label{lem:trprod}`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-! ## Real powers of a scalar reference -/

/-- The `NNReal`-algebra map into `Op d` is multiplication of the identity by the scalar. -/
private lemma algebraMapNNReal_eq_smul_one {d : ℕ} (t : NNReal) :
    algebraMap NNReal (Op d) t = ((t : ℝ) : ℂ) • (1 : Op d) := by
  rw [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, ← Complex.coe_smul]

/-- **Real power of a nonnegative multiple of the identity**: `((c·1))^y = (c^y)·1`, the
continuous functional calculus on a scalar operator. -/
private lemma smul_one_rpow {d : ℕ} (c : ℝ) (hc : 0 ≤ c) (y : ℝ) :
    ((c : ℂ) • (1 : Op d)) ^ y = ((c ^ y : ℝ) : ℂ) • (1 : Op d) := by
  have hc' : ((c.toNNReal : ℝ) : ℂ) = (c : ℂ) := by rw [Real.coe_toNNReal c hc]
  rw [← hc', ← algebraMapNNReal_eq_smul_one, CFC.rpow_algebraMap,
    algebraMapNNReal_eq_smul_one, NNReal.coe_rpow, Real.coe_toNNReal c hc]

/-! ## T1 — tensor factorisation of the weighted Hilbert–Schmidt square -/

/-- **Tensor factorisation of the σ-weighted Hilbert–Schmidt square.**

`weightedFrobeniusSq (τ ⊗ σ) (A ⊗ B) = weightedFrobeniusSq τ A · weightedFrobeniusSq σ B`
for positive-semidefinite references `τ, σ` and arbitrary `A, B`.

The functional calculus splits across the tensor product (`Op.tensor_rpow`,
`(τ ⊗ σ)^{−1/4} = τ^{−1/4} ⊗ σ^{−1/4}`), so the sandwiched operator is a tensor product, and the
Hilbert–Schmidt inner product of a tensor product factorises by `Op.trace_tensor`. The real parts
separate because each factor `Tr(CᴴC)` is a nonnegative real. -/
theorem weightedFrobeniusSq_tensor {dC dE : ℕ} (τ : Op dC) (σ : Op dE)
    (hτ : (0 : Op dC) ≤ τ) (hσ : (0 : Op dE) ≤ σ) (A : Op dC) (B : Op dE) :
    weightedFrobeniusSq (τ ⊗ σ) (A ⊗ B)
      = weightedFrobeniusSq τ A * weightedFrobeniusSq σ B := by
  have hsplit : (τ ⊗ σ) ^ (-1/4 : ℝ) * (A ⊗ B) * (τ ⊗ σ) ^ (-1/4 : ℝ)
      = (τ ^ (-1/4 : ℝ) * A * τ ^ (-1/4 : ℝ)) ⊗ (σ ^ (-1/4 : ℝ) * B * σ ^ (-1/4 : ℝ)) := by
    rw [Op.tensor_rpow τ σ hτ hσ, Op.tensor_mul, Op.tensor_mul]
  have him : ∀ C : Op dC, ((Cᴴ * C).trace).im = 0 := fun C =>
    ((Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self C).trace_nonneg).2).symm
  rw [weightedFrobeniusSq, weightedFrobeniusSq, weightedFrobeniusSq, hsplit,
    Op.tensor_conjTranspose, Op.tensor_mul, Op.trace_tensor, Complex.mul_re, him, zero_mul,
    sub_zero]

/-! ## T2 — the announcement factor against a scalar reference -/

/-- **The weighted Hilbert–Schmidt square at a scalar reference.**
`weightedFrobeniusSq (c·1) A = c⁻¹ · Re Tr(Aᴴ A)` for `c > 0`: the reference contributes only the
scalar `(c^{−1/4})⁴ = c⁻¹`. -/
theorem weightedFrobeniusSq_smul_one {d : ℕ} (c : ℝ) (hc : 0 < c) (A : Op d) :
    weightedFrobeniusSq ((c : ℂ) • (1 : Op d)) A = c⁻¹ * (Aᴴ * A).trace.re := by
  set r : ℝ := c ^ (-1/4 : ℝ) with hr
  have hmid : ((c : ℂ) • (1 : Op d)) ^ (-1/4 : ℝ) * A * ((c : ℂ) • (1 : Op d)) ^ (-1/4 : ℝ)
      = ((r * r : ℝ) : ℂ) • A := by
    rw [smul_one_rpow c hc.le, ← hr, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
      Matrix.mul_one, smul_smul, ← Complex.ofReal_mul]
  have hr2 : r * r = c ^ (-1/2 : ℝ) := by
    rw [hr, ← Real.rpow_add hc]
    norm_num
  have hr4 : (r * r) ^ 2 = c⁻¹ := by
    rw [hr2, sq, ← Real.rpow_add hc, show (-1/2 + -1/2 : ℝ) = -1 by norm_num,
      Real.rpow_neg_one]
  rw [weightedFrobeniusSq, hmid, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [show (star (((r * r : ℝ) : ℂ)) * ((r * r : ℝ) : ℂ)) = ((((r * r) ^ 2 : ℝ)) : ℂ) by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]; norm_num [sq]]
  rw [Complex.re_ofReal_mul, hr4]

/-- **The weighted Hilbert–Schmidt square at the maximally mixed reference.**
`weightedFrobeniusSq ((1/d)·1) A = d · Re Tr(Aᴴ A)`. -/
theorem weightedFrobeniusSq_maxMixed {d : ℕ} [NeZero d] (A : Op d) :
    weightedFrobeniusSq (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp A
      = (d : ℝ) * (Aᴴ * A).trace.re := by
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero d)
  have hcast : ((1 / (d : ℂ))) = (((1 / (d : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  rw [toSubDensityOp_maxMixed_toOp_eq, hcast,
    weightedFrobeniusSq_smul_one _ (by positivity) A]
  congr 1
  rw [one_div, inv_inv]

/-! ## T3 — the announcement factor is at most the domination constant -/

/-- **A `c`-dominated announcement block costs at most `c` times its trace.**

If the announcement block `K` on the register of dimension `d` is dominated by `c` times the
maximally mixed state — the hypothesis `opLe_bb84AnnounceKernel_smul_maxMixed` supplies for the
BB84 announcement — then its weighted Hilbert–Schmidt square against the maximally mixed
reference is at most `c · Tr K`; at a *normalised* announcement (`Tr K = 1`, which
`bb84AnnounceKernel_trace` supplies) that is exactly `c`.

`wfs ((1/d)·1) K = d · Tr(K²)` (`weightedFrobeniusSq_maxMixed`, `K` Hermitian) and
`Tr(K²) ≤ (c/d) · Tr K` (`trace_sq_le_smul_trace_of_opLe_smul_one`).

For a deterministic announcement `K = |a⟩⟨a|` at `c = d` both steps are equalities, so the charge
is tight. -/
theorem weightedFrobeniusSq_maxMixed_le_of_opLe {d : ℕ} [NeZero d]
    (K : SubDensityOp d) {c : ℝ}
    (hKdom : opLe K.toOp ((Complex.ofReal c) •
      (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp)) :
    weightedFrobeniusSq (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp K.toOp
      ≤ c * K.trace := by
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero d)
  have hdC : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hrhs : (Complex.ofReal c) • (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp
      = (Complex.ofReal (c / (d : ℝ))) • (1 : Op d) := by
    rw [toSubDensityOp_maxMixed_toOp_eq, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [hrhs] at hKdom
  have hdom' : opLe K.toOp ((Complex.ofReal (c / (d : ℝ))) • (1 : Op d)) := hKdom
  have hsq := Quantum.Operators.trace_sq_le_smul_trace_of_opLe_smul_one
    (Quantum.Operators.posSemidefOp_implies_mathlib K.toPosSemidefOp) hdom'
  have hherm : K.toOpᴴ = K.toOp := K.isHermitian
  rw [weightedFrobeniusSq_maxMixed, hherm]
  calc (d : ℝ) * (K.toOp * K.toOp).trace.re
      ≤ (d : ℝ) * ((c / (d : ℝ)) * K.toOp.trace.re) := by
        exact mul_le_mul_of_nonneg_left hsq hd.le
    _ = c * K.trace := by
        rw [SubDensityOp.trace]
        field_simp

/-! ## The announce charge -/

/-- **The collision-route classical-announce charge.**

Tensoring a normalised announcement block `K x` onto the **left** of every conditional operator of
a cq state — the layout `CQState.tensorLeftKernel`, announcement in the high digits, which is what
the BB84 pass-support bridge produces — and extending the reference correspondingly to
`(1/d_C)·1 ⊗ σ` multiplies the collision quantity by at most the announcement's domination
constant `c`:

`collisionQuantity ((1/d_C)·1 ⊗ σ) (K x ⊗ ρ_x)  ≤  c · collisionQuantity σ ρ_x`.

At `c = 2^(leakEC + ℓEV)` the two hypotheses are exactly `bb84AnnounceKernel_trace` and
`opLe_bb84AnnounceKernel_smul_maxMixed`, so the collision route pays **the same**
`leakEC + ℓEV` bits as the smooth route (`bb84_smoothMinEntropy_announce_ge_sub_leak`), and the
error-verification seed sub-register is likewise free: the seed factor of the kernel is
normalised on its own register and contributes `1` to `c`, not its dimension.

Tightness: for a deterministic announcement the inequality is an equality at `c = d_C`
(`weightedFrobeniusSq_maxMixed_le_of_opLe`), so no smaller collision-route charge exists.

Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:6889` `\label{rem:Htworewr}` (the collision
quantity), `:7080` `\label{thm:pa}` (the route that consumes it), `:10368` `\label{lem:trprod}`. -/
theorem collisionQuantity_tensorLeftKernel_le {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dC]
    (σ : Op dE) (hσ : (0 : Op dE) ≤ σ)
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (c : ℝ)
    (hKtr : ∀ x, (K x).trace = 1)
    (hKdom : ∀ x, opLe (K x).toOp ((Complex.ofReal c) •
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :
    collisionQuantity
        ((DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp ⊗ σ)
        (fun x => ((ρ.tensorLeftKernel K).stateMap x).toOp)
      ≤ c * collisionQuantity σ (fun x => (ρ.stateMap x).toOp) := by
  have hmm : (0 : Op dC) ≤ (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp :=
    Matrix.nonneg_iff_posSemidef.mpr
      (Quantum.Operators.posSemidefOp_implies_mathlib
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toPosSemidefOp)
  rw [collisionQuantity, collisionQuantity, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hstate : ((ρ.tensorLeftKernel K).stateMap x).toOp
      = (K x).toOp ⊗ (ρ.stateMap x).toOp := rfl
  rw [hstate, weightedFrobeniusSq_tensor _ _ hmm hσ]
  refine mul_le_mul_of_nonneg_right ?_ (weightedFrobeniusSq_nonneg _ _)
  have h := weightedFrobeniusSq_maxMixed_le_of_opLe (K x) (hKdom x)
  rwa [hKtr x, mul_one] at h

/-! ## The coarsening step -/

/-- `weightedFrobeniusSq σ 0 = 0`. -/
@[simp] lemma weightedFrobeniusSq_zero {d : ℕ} (σ : Op d) :
    weightedFrobeniusSq σ (0 : Op d) = 0 := by
  rw [weightedFrobeniusSq]
  simp

/-- **The collision quantity is unchanged by a coarsening injective on the support.**

If the coarsening map `f` is injective on the set where the state is kept (`keep`), and every
dropped block is the zero operator, then pushing the classical register forward along `f` permutes
the blocks rather than merging them, so the collision quantity is exactly preserved.

**Injectivity is load-bearing, not cosmetic.** Without it the `≤` direction is *false*: merging two
nonzero positive-semidefinite blocks strictly increases the collision quantity,
`tr((A+B)²) = tr A² + tr B² + 2·tr(AB) ≥ tr A² + tr B²` with `tr(AB) ≥ 0` for `A, B ⪰ 0`
(Renner 2005, arXiv:quant-ph/0512258v2, `main.tex:10368` `\label{lem:trprod}`); at
`A = B = |0⟩⟨0|/2` merging doubles `tr(·²)`. A coarsening therefore transfers a *floor* on the
collision quantity in the wrong direction unless it is injective. -/
theorem collisionQuantity_coarsen_eq_of_injOn
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE : ℕ}
    (f : X → Y) (keep : X → Bool) (hinj : Set.InjOn f {x | keep x = true})
    (σ : Op dE) (ρ : CQState X dE)
    (hzero : ∀ x, keep x = false → (ρ.stateMap x).toOp = 0) :
    collisionQuantity σ (fun y => ((CQState.coarsen f ρ).stateMap y).toOp)
      = collisionQuantity σ (fun x => (ρ.stateMap x).toOp) := by
  classical
  set S : Finset X := Finset.univ.filter fun x => keep x = true with hS
  have hmemS : ∀ x, x ∈ S ↔ keep x = true := by
    intro x; simp [hS]
  have hVzero : ∀ x ∉ S, (ρ.stateMap x).toOp = 0 := by
    intro x hx
    exact hzero x (Bool.eq_false_iff.mpr fun h => hx ((hmemS x).mpr h))
  -- the coarsened block at `f x` for a kept `x` is exactly the `x` block
  have hblock_image : ∀ x ∈ S,
      ((CQState.coarsen f ρ).stateMap (f x)).toOp = (ρ.stateMap x).toOp := by
    intro x hx
    rw [CQState.coarsen_stateMap_toOp]
    have hsingle : ∀ x' ∈ (Finset.univ : Finset X), x' ≠ x →
        (if f x' = f x then (ρ.stateMap x').toOp else 0) = 0 := by
      intro x' _ hx'ne
      by_cases hkeep : x' ∈ S
      · have hne : f x' ≠ f x := fun h =>
          hx'ne (hinj ((hmemS x').mp hkeep) ((hmemS x).mp hx) h)
        simp [hne]
      · simp [hVzero x' hkeep]
    rw [Finset.sum_eq_single x hsingle (fun h => absurd (Finset.mem_univ x) h)]
    simp
  -- the coarsened block off the image of the kept set is zero
  have hblock_off : ∀ y ∉ S.image f, ((CQState.coarsen f ρ).stateMap y).toOp = 0 := by
    intro y hy
    rw [CQState.coarsen_stateMap_toOp]
    refine Finset.sum_eq_zero fun x' _ => ?_
    by_cases hfx : f x' = y
    · by_cases hkeep : x' ∈ S
      · exact absurd (Finset.mem_image.mpr ⟨x', hkeep, hfx⟩) hy
      · rw [ite_eq_left hfx, hVzero x' hkeep]
    · rw [ite_eq_right hfx]
  rw [collisionQuantity, collisionQuantity]
  have hLHS : ∑ y : Y, weightedFrobeniusSq σ ((CQState.coarsen f ρ).stateMap y).toOp
      = ∑ y ∈ S.image f, weightedFrobeniusSq σ ((CQState.coarsen f ρ).stateMap y).toOp := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_).symm
    rw [hblock_off y hy, weightedFrobeniusSq_zero]
  have hRHS : ∑ x : X, weightedFrobeniusSq σ (ρ.stateMap x).toOp
      = ∑ x ∈ S, weightedFrobeniusSq σ (ρ.stateMap x).toOp := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    rw [hVzero x hx, weightedFrobeniusSq_zero]
  rw [hLHS, hRHS,
    Finset.sum_image
      (fun x hx x' hx' h => hinj ((hmemS x).mp hx) ((hmemS x').mp hx') h)]
  exact Finset.sum_congr rfl fun x hx => by rw [hblock_image x hx]

/-! ## σ-weighted Hilbert–Schmidt Pythagoras -/

/-- **Hilbert–Schmidt Pythagoras for the σ-weighted square.**

For a positive-definite reference `σ` and *Hermitian* blocks `A, B` whose σ-weighted
Hilbert–Schmidt pairing vanishes, `Tr[A σ^{−1/2} B σ^{−1/2}] = 0`, the weighted square is
additive:

`weightedFrobeniusSq σ (A + B) = weightedFrobeniusSq σ A + weightedFrobeniusSq σ B`.

This is the *only* way a coarsening can merge two blocks without changing the collision quantity
other than by being injective (`collisionQuantity_coarsen_eq_of_injOn`): the merged block
`A + B` costs exactly what the two summands cost separately.

On the hypotheses:

* `hA : Aᴴ = A` is load-bearing. `weightedFrobeniusSq` is the *symmetric* 4-2-4 form
  `‖σ^{−1/4} X σ^{−1/4}‖_F²`, so expanding the square produces the cross term
  `Tr[Aᴴ σ^{−1/2} B σ^{−1/2}]` and its conjugate. Only with `Aᴴ = A` is that the pairing `horth`
  names; without it the identity is about a different pairing.
* **`Bᴴ = B` is deliberately NOT a hypothesis.** One might expect it is needed, on the reading
  that the expansion produces two independent cross terms. It produces one and its complex conjugate
  (`Matrix.trace_conjTranspose`), so `hA` alone kills both, and `horth` gives the first as `0` in
  `ℂ`
  rather than merely `Re = 0`. Carrying the extra hypothesis would make this strictly weaker than
  what the proof establishes.
* The pairing `Tr[A σ^{−1/2} B σ^{−1/2}] = 0` is a genuinely **σ-dependent** condition, distinct
  from support orthogonality `A · B = 0`: it is the orthogonality of the *sandwiched* operators
  `σ^{−1/4} A σ^{−1/4}` and `σ^{−1/4} B σ^{−1/4}` in the Hilbert–Schmidt inner product, which is
  what the 4-2-4 form measures.

Elementary: no external reference is needed or claimed. The proof is the parallelogram expansion
`(X + Y)ᴴ(X + Y) = XᴴX + XᴴY + YᴴX + YᴴY` at `X = σ^{−1/4} A σ^{−1/4}`,
`Y = σ^{−1/4} B σ^{−1/4}`, with the second cross term the conjugate of the first
(`Matrix.trace_conjTranspose`). -/
theorem weightedFrobeniusSq_add_of_weightedOrthogonal {d : ℕ} [NeZero d]
    (σ : Op d) (hσ : σ.PosDef) (A B : Op d) (hA : Aᴴ = A)
    (horth : (A * σ ^ (-1 / 2 : ℝ) * B * σ ^ (-1 / 2 : ℝ)).trace = 0) :
    weightedFrobeniusSq σ (A + B) = weightedFrobeniusSq σ A + weightedFrobeniusSq σ B := by
  simp only [weightedFrobeniusSq]
  set F : Op d := σ ^ (-1/4 : ℝ) with hF
  have hFherm : Fᴴ = F :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := (-1/4 : ℝ)))).isHermitian.eq
  have hFF : F * F = σ ^ (-1/2 : ℝ) := by
    rw [hF, ← CFC.rpow_add hσ.isUnit, show (-1/4 + -1/4 : ℝ) = -1/2 by norm_num]
  -- the σ-weighted pairing of two blocks, in sandwiched form
  have key : ∀ X Y : Op d,
      ((F * X * F)ᴴ * (F * Y * F)).trace
        = (Xᴴ * σ ^ (-1/2 : ℝ) * Y * σ ^ (-1/2 : ℝ)).trace := by
    intro X Y
    have h1 : (F * X * F)ᴴ * (F * Y * F) = F * (Xᴴ * (F * F) * Y * F) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hFherm]
      noncomm_ring
    have h2 : Xᴴ * σ ^ (-1/2 : ℝ) * Y * F * F
        = Xᴴ * σ ^ (-1/2 : ℝ) * Y * (F * F) := by noncomm_ring
    rw [h1, hFF, Matrix.trace_mul_comm, h2, hFF]
  have hcross1 : ((F * A * F)ᴴ * (F * B * F)).trace = 0 := by
    rw [key A B, hA]; exact horth
  have hcross2 : ((F * B * F)ᴴ * (F * A * F)).trace = 0 := by
    have hconj : ((F * A * F)ᴴ * (F * B * F))ᴴ = (F * B * F)ᴴ * (F * A * F) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [← hconj, Matrix.trace_conjTranspose, hcross1, star_zero]
  have hsplit : F * (A + B) * F = F * A * F + F * B * F := by noncomm_ring
  have hmain : ((F * (A + B) * F)ᴴ * (F * (A + B) * F)).trace
      = ((F * A * F)ᴴ * (F * A * F)).trace + ((F * B * F)ᴴ * (F * B * F)).trace := by
    rw [hsplit, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, hcross1, hcross2]
    ring
  rw [hmain, Complex.add_re]

/-- **The coarsening step at a `filterKeep`-restricted state.**

`CQState.filterKeep` is the shape the BB84 accept gates produce
(`bb84PostMeasurementCQSiftedLocalPEPassFilter_eq_filterKeep`), so this is the directly usable
form of `collisionQuantity_coarsen_eq_of_injOn`. -/
theorem collisionQuantity_coarsen_filterKeep_eq_of_injOn
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE : ℕ}
    (f : X → Y) (keep : X → Bool) (hinj : Set.InjOn f {x | keep x = true})
    (σ : Op dE) (ρ : CQState X dE) :
    collisionQuantity σ
        (fun y => ((CQState.coarsen f (CQState.filterKeep keep ρ)).stateMap y).toOp)
      = collisionQuantity σ (fun x => ((CQState.filterKeep keep ρ).stateMap x).toOp) :=
  collisionQuantity_coarsen_eq_of_injOn f keep hinj σ (CQState.filterKeep keep ρ)
    (fun x hx => by rw [CQState.filterKeep_stateMap, hx]; rfl)

end InfoTheory.QuantumLHL

end
