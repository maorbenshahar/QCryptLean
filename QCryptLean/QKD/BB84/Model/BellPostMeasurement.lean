import QCryptLean.QKD.BB84.Model.BellMeasurement

/-!
# Density-operator conjugation, and the single-pair Bell rotation

General helpers for building a density operator from another one — conjugation by a unitary, and
the image under a CPTP map — plus the fixed single-pair Bell-basis-change unitary they support.

## Main definitions and results

* `densityOpUnitaryConj` — conjugation of a density operator by a unitary preserves the density
  operator structure.
* `cptpDensityOp` — the image of a density operator under a CPTP map is a density operator.
* `bb84BellSinglePairRotation` — the single-pair Bell rotation `V`, `V|β_k⟩ = |k⟩`.

## References

Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Basis.BellStates InfoTheory.DeFinetti InfoTheory.SmoothMinEntropy MeasureTheory
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## Unitary conjugation of a density operator
-/

/-- **Conjugation of a density operator by a unitary.**

`densityOpUnitaryConj U hU ρ := U ρ U†`, a valid density operator whenever
`U† U = 1`: conjugation by a unitary preserves Hermiticity, positive
semidefiniteness, and the trace.  Explicit; no `Classical.choose`. -/
def densityOpUnitaryConj {D : ℕ} (U : Op D) (hU : Uᴴ * U = 1) (ρ : DensityOp D) :
    DensityOp D :=
  let hpsd_conj : Matrix.PosSemidef (U * ρ.toOp * Uᴴ) :=
    (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same U
  ⟨⟨⟨U * ρ.toOp * Uᴴ, hpsd_conj.isHermitian⟩,
    fun x => by
      unfold quadraticForm
      exact le_trans (le_refl _)
        (RCLike.nonneg_iff.mp (hpsd_conj.dotProduct_mulVec_nonneg x)).1⟩,
   by
    rw [Matrix.trace_mul_comm (U * ρ.toOp) Uᴴ, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      ρ.trace_one]⟩

@[simp]
theorem densityOpUnitaryConj_toOp {D : ℕ} (U : Op D) (hU : Uᴴ * U = 1) (ρ : DensityOp D) :
    (densityOpUnitaryConj U hU ρ).toOp = U * ρ.toOp * Uᴴ := rfl

/-- **The image of a density operator under a CPTP map, as a density operator.**

`pre ρ` carries Hermiticity and positive semidefiniteness from `cptp_preserves_posSemidef`
and unit trace from the trace clause of `IsCPTP`.  Explicit; no `Classical.choose`, and
`(cptpDensityOp pre hpre ρ).toOp` is `⇑pre ρ.toOp` definitionally (`cptpDensityOp_toOp`).

The general-channel companion of `densityOpUnitaryConj`: that one takes the unitary-conjugation
special case, this one an arbitrary CPTP map.  Consumers index the retained-Eve side by a bare
dimension plus an opaque CPTP map (`bb84SiftedRotatedPreOutput`), so the attack object enters
only at the instantiation `pre := attackChannelLinear atk`. -/
def cptpDensityOp {A B : ℕ} [NeZero A] [NeZero B]
    (pre : Op A →ₗ[ℂ] Op B) (hpre : IsCPTP ⇑pre) (ρ : DensityOp A) : DensityOp B :=
  let hpsd : (pre ρ.toOp).PosSemidef :=
    cptp_preserves_posSemidef ⇑pre hpre ρ.toOp (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)
  ⟨⟨⟨pre ρ.toOp, hpsd.isHermitian⟩,
    fun x => by
      unfold quadraticForm
      exact (RCLike.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg x)).1⟩,
   (hpre.2.2 ρ.toOp).trans ρ.trace_one⟩

@[simp] theorem cptpDensityOp_toOp {A B : ℕ} [NeZero A] [NeZero B]
    (pre : Op A →ₗ[ℂ] Op B) (hpre : IsCPTP ⇑pre) (ρ : DensityOp A) :
    (cptpDensityOp pre hpre ρ).toOp = pre ρ.toOp := rfl

/-!
## The fixed single-pair Bell rotation `V` (`V|β_k⟩ = |k⟩`)
-/

/-- The single-pair Bell rotation `V`, `V|β_k⟩ = |k⟩`.

Matrix entries `V i j = conj((bb84BellState i).vec j)`, so the `k`-th column of `Vᴴ`
is `|β_k⟩` (`Vᴴ|k⟩ = |β_k⟩`) and `V|β_k⟩ = |k⟩` by Bell orthonormality.  Explicit;
no `Classical.choose`. -/
def bb84BellSinglePairRotation : Op signalDim :=
  Matrix.of fun i j => (starRingEnd ℂ) ((bb84BellState i).vec j)

end QKD.BB84.Model

end
