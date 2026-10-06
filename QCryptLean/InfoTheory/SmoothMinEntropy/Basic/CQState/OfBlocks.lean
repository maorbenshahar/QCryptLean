import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState

/-!
# Building sub-density operators and CQ states from explicit blocks

`SubDensityOp` and `CQState` are bundled structures carrying positivity and normalization
side conditions.  This file supplies the missing *introduction* rules: it turns raw data —
a Mathlib positive-semidefinite matrix, or a family of such matrices with total trace at most
one — into those bundled objects, so that statements about `CQState`s can be instantiated at
explicitly constructed states rather than only at hypothetically given ones.

Three levels are provided, each a thin layer over the previous one:

* `Matrix.PosSemidef.toPosSemidefOp` / `SubDensityOp.ofPosSemidef` — single operator.
* `CQState.ofBlocks` — a family of positive-semidefinite blocks whose real traces sum to at
  most one.  Per-block subnormalization is *derived* from the total bound, not assumed.
* `CQState.ofBlockVectors` and `CQState.ofBlockVectorFamily` — the rank-one block
  `|u x⟩⟨u x|` and the dephased-mixture block `∑_{i ∈ J} |v x i⟩⟨v x i|`, whose traces are the
  squared norms `∑_j ‖u x j‖²` and `∑_{i ∈ J} ∑_j ‖v x i j‖²`.  These are the two block shapes
  of a Bouman–Fehr superposition/mixture pair.

Degenerate cases are covered without side conditions: an empty classical register or `d = 0`
gives the zero state, and `J = ∅` gives the zero mixture.

## Main definitions

* `Matrix.PosSemidef.toPosSemidefOp`, `SubDensityOp.ofPosSemidef`
* `InfoTheory.SmoothMinEntropy.CQState.ofBlocks`
* `InfoTheory.SmoothMinEntropy.CQState.ofBlockVectors`
* `InfoTheory.SmoothMinEntropy.CQState.ofBlockVectorFamily`
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {X : Type*} [Fintype X] {d : ℕ}

/-! ### From a Mathlib positive-semidefinite matrix -/

/-- Package a Mathlib positive-semidefinite matrix as the library's bundled `PosSemidefOp`.
This is the converse of `Quantum.Operators.posSemidefOp_implies_mathlib`. -/
def _root_.Matrix.PosSemidef.toPosSemidefOp {A : Op d} (hA : A.PosSemidef) : PosSemidefOp d where
  toOp := A
  isHermitian := hA.isHermitian
  pos_semidef x := posSemidef_re_quadraticForm_nonneg hA x

@[simp] lemma _root_.Matrix.PosSemidef.toPosSemidefOp_toOp {A : Op d} (hA : A.PosSemidef) :
    hA.toPosSemidefOp.toOp = A := rfl

/-- A positive-semidefinite operator of real trace at most one is a sub-density operator. -/
def SubDensityOp.ofPosSemidef {A : Op d} (hA : A.PosSemidef) (htr : A.trace.re ≤ 1) :
    SubDensityOp d where
  toPosSemidefOp := hA.toPosSemidefOp
  trace_le_one := htr

@[simp] lemma SubDensityOp.ofPosSemidef_toOp {A : Op d} (hA : A.PosSemidef)
    (htr : A.trace.re ≤ 1) : (SubDensityOp.ofPosSemidef hA htr).toOp = A := rfl

/-! ### From a family of blocks -/

/-- **The CQ state with prescribed positive-semidefinite blocks.**  Given blocks `B x` that are
positive semidefinite and whose real traces sum to at most one, `CQState.ofBlocks` is the CQ
state `ρ_{XA} = ∑_x |x⟩⟨x| ⊗ B x`.

Per-block subnormalization `Tr (B x) ≤ 1` is derived from the total bound together with
nonnegativity of the remaining traces, so the caller supplies only the honest normalization
condition of a CQ state. -/
def CQState.ofBlocks (B : X → Op d) (hpsd : ∀ x, (B x).PosSemidef)
    (hw : ∑ x : X, (B x).trace.re ≤ 1) : CQState X d where
  stateMap x :=
    SubDensityOp.ofPosSemidef (hpsd x)
      (le_trans
        (Finset.single_le_sum (f := fun y : X => (B y).trace.re)
          (fun y _ => (hpsd y).trace_re_nonneg) (Finset.mem_univ x)) hw)
  weight_le_one := hw

@[simp] lemma CQState.ofBlocks_stateMap_toOp (B : X → Op d) (hpsd : ∀ x, (B x).PosSemidef)
    (hw : ∑ x : X, (B x).trace.re ≤ 1) (x : X) :
    ((CQState.ofBlocks B hpsd hw).stateMap x).toOp = B x := rfl

/-! ### Rank-one and dephased-mixture blocks -/

/-- The real trace of the rank-one operator `|u⟩⟨u|` is the squared norm `∑_j ‖u j‖²`. -/
lemma trace_re_vecMulVec_self_star (u : Fin d → ℂ) :
    (Matrix.vecMulVec u (star u)).trace.re = ∑ j, Complex.normSq (u j) := by
  have h : ∀ z : ℂ, (z * star z).re = Complex.normSq z := fun z => by
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.ofReal_re]
  rw [Matrix.trace_vecMulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => h (u j)

/-- **The CQ state with rank-one blocks** `|u x⟩⟨u x|`.  This is the measured hybrid state of a
family of (generally unnormalized) conditional vectors; the normalization hypothesis is exactly
"the total probability is at most one". -/
def CQState.ofBlockVectors (u : X → Fin d → ℂ)
    (hw : ∑ x : X, ∑ j, Complex.normSq (u x j) ≤ 1) : CQState X d :=
  CQState.ofBlocks (fun x => Matrix.vecMulVec (u x) (star (u x)))
    (fun x => Matrix.posSemidef_vecMulVec_self_star (u x))
    (by simpa only [trace_re_vecMulVec_self_star] using hw)

@[simp] lemma CQState.ofBlockVectors_stateMap_toOp (u : X → Fin d → ℂ)
    (hw : ∑ x : X, ∑ j, Complex.normSq (u x j) ≤ 1) (x : X) :
    ((CQState.ofBlockVectors u hw).stateMap x).toOp = Matrix.vecMulVec (u x) (star (u x)) := rfl

/-- **The CQ state with dephased-mixture blocks** `∑_{i ∈ J} |v x i⟩⟨v x i|`: the state obtained
from the family `v` after destroying the coherences between the indices `i ∈ J`. -/
def CQState.ofBlockVectorFamily {ι : Type*} (J : Finset ι) (v : X → ι → Fin d → ℂ)
    (hw : ∑ x : X, ∑ i ∈ J, ∑ j, Complex.normSq (v x i j) ≤ 1) : CQState X d :=
  CQState.ofBlocks (fun x => ∑ i ∈ J, Matrix.vecMulVec (v x i) (star (v x i)))
    (fun x => Matrix.posSemidef_sum J fun i _ => Matrix.posSemidef_vecMulVec_self_star (v x i))
    (by
      refine le_trans (le_of_eq ?_) hw
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.trace_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => trace_re_vecMulVec_self_star (v x i))

@[simp] lemma CQState.ofBlockVectorFamily_stateMap_toOp {ι : Type*} (J : Finset ι)
    (v : X → ι → Fin d → ℂ) (hw : ∑ x : X, ∑ i ∈ J, ∑ j, Complex.normSq (v x i j) ≤ 1) (x : X) :
    ((CQState.ofBlockVectorFamily J v hw).stateMap x).toOp =
      ∑ i ∈ J, Matrix.vecMulVec (v x i) (star (v x i)) := rfl

end InfoTheory.SmoothMinEntropy

end
