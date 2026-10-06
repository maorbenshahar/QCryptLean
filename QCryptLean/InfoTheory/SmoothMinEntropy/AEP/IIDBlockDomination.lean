import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TraceBoundHelpers

/-!
# Always-smooth spectral-cut witness for bit-normalized Renner `thm:Hmincondrep`

This module supplies the explicit object-level constructions and the named results
for the always-smooth spectral cut of Renner's proof (main.tex:4575–4665).

Renner's construction is **always smooth**: for *every* threshold sign it uses the
same retained cumulative crossing projector `B_{z*}` at the separation scale
`2 ^ (-T)`, with `-log λ = T` (main.tex:4586–4604).

The retained mass is controlled by Renner's weight cap `p_{x,z} ≤ λ β_z`
(main.tex:4644–4665): the smoothed state is `ρ̄ = Σ_{x,z} p_{x,z} B_z|x⟩⟨x|B_z`
with `Σ_{z ≤ z'} p_{x,z} = min(p_x, λ q_{z'})`, giving
`λ·(id⊗σ)^{⊗n} − ρ̄ ≥ 0` unconditionally. This operator domination is
`iidAEPSpectralCutBlockDomination`.

Reusable infrastructure exported here, faithful to Renner:

* `iidAEPProjectorSandwichSubDensityOp` / `iidAEPProjectorSandwichCQState`
  — the explicit Hermitian-projector conjugation `ρ ↦ P · ρ · P`;
* `iidAEPCrossingCutIndex` — the explicit least sorted index reaching the
  separation scale (Renner's `z*`, main.tex:4600–4604);
* `iidAEPCrossingCutIndex_below_lt` — the sub-threshold support inequality
  (unconditional);
* `iidAEPReferenceEigenvalue_monotone` — monotonicity of the sorted
  reference spectrum (Renner's `β_z ≥ 0`).
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Projector-sandwich constructors -/

/-- Conjugate a sub-density operator by a Hermitian idempotent projector `P`:
`ρ ↦ P · ρ · P`. The result is again sub-normalized:

* conjugation preserves positive semidefiniteness
  (`Matrix.PosSemidef.mul_mul_conjTranspose_same`, using `P† = P`);
* Hermiticity follows from `Matrix.isHermitian_mul_mul_conjTranspose`;
* the trace does not increase under a Hermitian-projector sandwich
  (`tr_projector_sandwich_le_subDensityOp_trace`), so it stays `≤ 1`. -/
def iidAEPProjectorSandwichSubDensityOp {m : ℕ}
    (P : Op m) (hidem : P * P = P) (hherm : P† = P)
    (ρ : SubDensityOp m) : SubDensityOp m where
  toOp := P * ρ.toOp * P
  isHermitian := by
    have h := Matrix.isHermitian_mul_mul_conjTranspose (A := ρ.toOp) P ρ.isHermitian
    rwa [hherm] at h
  pos_semidef := by
    intro v
    have hpsd : (P * ρ.toOp * P).PosSemidef := by
      have h :=
        (Quantum.Operators.posSemidefOp_implies_mathlib
          ρ.toPosSemidefOp).mul_mul_conjTranspose_same P
      rwa [hherm] at h
    exact Quantum.Operators.posSemidef_re_quadraticForm_nonneg hpsd v
  trace_le_one := by
    have h :=
      DistTraceBoundHelpers.tr_projector_sandwich_le_subDensityOp_trace ρ P hidem hherm
    exact le_trans h ρ.trace_le_one

@[simp]
lemma iidAEPProjectorSandwichSubDensityOp_toOp {m : ℕ}
    (P : Op m) (hidem : P * P = P) (hherm : P† = P) (ρ : SubDensityOp m) :
    (iidAEPProjectorSandwichSubDensityOp P hidem hherm ρ).toOp =
      P * ρ.toOp * P := rfl

/-- Blockwise projector-sandwich of a CQ state: each conditional block is
conjugated by the Hermitian idempotent projector `P`. Sub-normalization of the
weights follows because each block trace does not increase under the sandwich. -/
def iidAEPProjectorSandwichCQState {Y : Type*} [Fintype Y] {m : ℕ}
    (P : Op m) (hidem : P * P = P) (hherm : P† = P)
    (ρ : CQState Y m) : CQState Y m where
  stateMap y := iidAEPProjectorSandwichSubDensityOp P hidem hherm (ρ.stateMap y)
  weight_le_one := by
    refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) ρ.weight_le_one
    exact
      DistTraceBoundHelpers.tr_projector_sandwich_le_subDensityOp_trace
        (ρ.stateMap y) P hidem hherm

@[simp]
lemma iidAEPProjectorSandwichCQState_stateMap_toOp {Y : Type*} [Fintype Y]
    {m : ℕ} (P : Op m) (hidem : P * P = P) (hherm : P† = P)
    (ρ : CQState Y m) (y : Y) :
    ((iidAEPProjectorSandwichCQState P hidem hherm ρ).stateMap y).toOp =
      P * (ρ.stateMap y).toOp * P := rfl

/-! ## Crossing cut index -/

/-- The crossing index selected by the always-smooth spectral cut (Renner's
`z*`, main.tex:4600–4604): the least eigenvalue label `z` whose reference
eigenvalue `lam z` reaches the separation scale `2 ^ (-T)`.

When the spectrum is sorted (monotone) this is exactly Renner's retained cut: all
strictly smaller indices lie below the scale. If no eigenvalue reaches the scale
the index defaults to `0`. The same crossing index parameterizes the cut for
every threshold sign; there is no `sign(T)` branch. -/
def iidAEPCrossingCutIndex {m : ℕ} [NeZero m]
    (lam : Fin m → ℝ) (T : ℝ) : Fin m :=
  if h : (Finset.univ.filter (fun z : Fin m => (2 : ℝ) ^ (-T) ≤ lam z)).Nonempty then
    (Finset.univ.filter (fun z : Fin m => (2 : ℝ) ^ (-T) ≤ lam z)).min' h
  else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

/-! ## Crossing inequalities

The below-crossing inequality follows from the cut-index definition alone (it is
the sub-threshold support the Chernoff tail step exploits). The eigenvalue
monotonicity of the sorted reference spectrum is Renner's `β_z ≥ 0` cumulative
coefficients. -/

/-- Below the crossing index every reference eigenvalue is strictly below the
separation scale. Direct consequence of minimality of the crossing index. -/
theorem iidAEPCrossingCutIndex_below_lt {m : ℕ} [NeZero m]
    (lam : Fin m → ℝ) (T : ℝ) (z : Fin m)
    (hz : z < iidAEPCrossingCutIndex lam T) :
    lam z < (2 : ℝ) ^ (-T) := by
  unfold iidAEPCrossingCutIndex at hz
  split_ifs at hz with h
  · by_contra hcon
    push_neg at hcon
    have hmem : z ∈ Finset.univ.filter (fun z : Fin m => (2 : ℝ) ^ (-T) ≤ lam z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hcon
    exact absurd hz (not_lt.mpr (Finset.min'_le _ z hmem))
  · simp only [Fin.lt_def] at hz; omega

/-- The sorted reference spectrum of a reference-stage witness is monotone
(Renner's `β_z ≥ 0` cumulative coefficients). Extracted from the
cumulative-resolution data. -/
theorem iidAEPReferenceEigenvalue_monotone {X : Type*} [Fintype X] {n : ℕ}
    [NeZero n] (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (href : iidAEPWitnessReferenceSpectralDecomposition ρ σ n_copies W) :
    Monotone W.referenceEigenvalue := by
  have cumres := href.2.2.2.2
  have hbeta := cumres.1
  have hform := cumres.2.2.2.2.2.2
  intro z z' hzz'
  rw [hform z, hform z']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact le_trans hw hzz'
  · intro i _ _
    exact hbeta i

end InfoTheory.SmoothMinEntropy
