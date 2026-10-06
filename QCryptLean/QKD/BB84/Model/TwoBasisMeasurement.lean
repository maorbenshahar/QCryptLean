import QCryptLean.Quantum.Gates
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.RestrictedSymSpaceDecomp
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubDensityOpTraceZero
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricStatistics
import QCryptLean.Math.Concentration.BinomialHoeffding
import QCryptLean.Math.Combinatorics.FinsetGatedSum
import QCryptLean.QKD.BB84.Model.ProtocolPair

/-!
# The Hadamard basis rotation and phase observability

The `H ⊗ H` two-qubit basis-rotation unitary that turns the computational (`Z`) basis into the
Hadamard (`X`) basis on the Alice–Bob pair, and the resulting **phase observability** identity:
the bit-flip rate of a component read in the `X` basis equals its phase-flip rate read in the `Z`
basis. In the `Z`-only model every diagonal `σ` has phase rate identically `½`
(`phaseFlipProjector` is non-diagonal), so the joint condition `goodRateSet`
(`bit ≤ Q+δ ∧ phase ≤ Q+δ`) is unsatisfiable for a diagonal post-measurement state; the `X`-basis
measurement recovers it.

## The enabling identity

With `bb84HadamardPair := H ⊗ H` (Hermitian, unitary):
`bb84HadamardPair · bitFlipProjector · bb84HadamardPair = phaseFlipProjector`
(`bb84_hadamardPair_conj_bitFlipProjector_eq_phaseFlipProjector`).  Hence for
`σ_X := bb84XBasisConjugate σ = H⊗H · σ · H⊗H`,
`bitFlipErrorRate_single σ_X = phaseFlipErrorRate_single σ`
(`bb84_xBasisConjugate_bitRate_eq_phaseRate`).

## Faithfulness notes (Renner §6.5)

* **Two bases only (Z, X).**  Renner §6.5 as written is the six-state protocol
  (x, y, z); BB84 drops the circular/`Y` basis.
* **The X-POVM is pinned to `H ⊗ H`,** never an arbitrary unitary: only `H ⊗ H`
  makes the `X`-mismatch projector equal `phaseFlipProjector` exactly.

## Main definitions and results

* `bb84HadamardPair` — the `H ⊗ H` basis-rotation unitary on `Op signalDim`.
* `bb84_hadamardPair_conj_bitFlipProjector_eq_phaseFlipProjector` — the Hadamard pair
  exchanges the bit-flip and phase-flip projectors.
* `bb84XBasisConjugate` — the X-basis conjugate component `H⊗H · σ · H⊗H`.
* `bb84_xBasisConjugate_bitRate_eq_phaseRate` — phase observability: the X-basis bit
  rate of `σ` equals its phase rate.

## References

Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 / `lem:PEsec`
(`main.tex:7527`, `main.tex:9131–9180`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Gates
open Quantum.Basis.BellStates InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## Hadamard-pair primitives
-/

/-- The two-qubit Hadamard rotation `H ⊗ H` on `Op signalDim`, i.e. the
basis change mapping the computational (`Z`) basis to the Hadamard (`X`) basis on
both the Alice and Bob qubits.  Explicit; this is the BB84 X-basis rotation. -/
def bb84HadamardPair : Op signalDim :=
  Op.tensor Quantum.Gates.hadamard Quantum.Gates.hadamard

/-- `bb84HadamardPair` is Hermitian: `(H⊗H)† = H⊗H`. -/
theorem bb84HadamardPair_hermitian : bb84HadamardPair† = bb84HadamardPair := by
  unfold bb84HadamardPair
  rw [Op.tensor_conjTranspose, hadamard_hermitian]

/-- `bb84HadamardPair` is its own inverse (unitary, since Hermitian): `(H⊗H)(H⊗H) = 1`. -/
theorem bb84HadamardPair_unitary : bb84HadamardPair * bb84HadamardPair = (1 : Op signalDim) := by
  unfold bb84HadamardPair
  rw [Op.tensor_mul, hadamard_sq, Op.tensor_one]

/-- Explicit matrix form of `bb84HadamardPair = H ⊗ H` in the computational basis:
all entries are `±½`, with the negative sign exactly at the six entries
`(1,1), (1,3), (2,2), (2,3), (3,1), (3,2)`. -/
lemma bb84HadamardPair_eq_matrix :
    bb84HadamardPair =
      Matrix.of (fun i j : Fin signalDim =>
        if (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
            (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2) then (-1 / 2 : ℂ) else (1 / 2 : ℂ)) := by
  -- `H ⊗ H = ½ • (!![1,1;1,-1] ⊗ !![1,1;1,-1])`, then read off the sign pattern entrywise
  rw [bb84HadamardPair, hadamard_eq_matrix, Op.tensor_smul_left, Op.tensor_smul_right, smul_smul,
    inv_sqrt_two_mul_self, Op.tensor_fin_two_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.smul_apply, Matrix.of_apply] <;> simp [neg_div]

/-!
## The Hadamard pair exchanges the bit-flip and phase-flip projectors

`bitFlipProjector` projects onto `span{|β₀₁⟩, |β₁₁⟩}` and `phaseFlipProjector` onto
`span{|β₁₀⟩, |β₁₁⟩}`. The Hadamard pair `H ⊗ H` exchanges `|β₀₁⟩` and `|β₁₀⟩` and fixes `|β₁₁⟩`
up to sign (`Quantum.Basis.BellStates.hadamard_tensor_hadamard_mul_bellState01` and its
companions), so conjugation by `H ⊗ H` exchanges the two projectors. This is the identity on which
the phase arm rests. The explicit computational-basis matrices of the three operators are recorded
for entrywise consumers.
-/

/-- Explicit diagonal form of `bitFlipProjector`: `diag(0, 1, 1, 0)` (mismatch indices
`{1, 2}`). -/
lemma bitFlipProjector_eq_matrix :
    QKD.BB84.Model.bitFlipProjector =
      Matrix.of (fun i j : Fin signalDim =>
        if i = j ∧ (i = 1 ∨ i = 2) then (1 : ℂ) else 0) := by
  -- `|β₀₁⟩ = (√2)⁻¹ v` and `|β₁₁⟩ = (√2)⁻¹ w` for the real vectors `v = (0,1,1,0)`,
  -- `w = (0,1,-1,0)`, so `Π_bit i j = ½ (v i v j + w i w j)`; read it off entrywise
  have hfactor : ∀ c a b a' b' : ℂ,
      c * a * (c * b) + c * a' * (c * b') = (c * c) * (a * b + a' * b') := by
    intros; ring
  ext i j
  rw [QKD.BB84.Model.bitFlipProjector, Matrix.add_apply, ket_mul_bra_apply, ket_mul_bra_apply,
    Ket.dag_vec, Ket.dag_vec, bellState01_vec, bellState11_vec]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
  rw [hfactor, inv_sqrt_two_mul_self]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply] <;> norm_num [Fin.ext_iff]

/-- **Crux: the Hadamard pair conjugates the bit-flip projector to the phase-flip
projector.**

`bb84HadamardPair · bitFlipProjector · bb84HadamardPair = phaseFlipProjector`.

This is the decisive enabling fact of the two-basis model: it identifies the
`X⊗X` mismatch projector (`H⊗H · |1⟩⟨1|+|2⟩⟨2| · H⊗H`) with `phaseFlipProjector`,
so the X-basis Born statistic of `σ` equals the bit-flip statistic of the conjugate
`bb84XBasisConjugate σ` and the phase arm reduces to the bit arm (Renner §6.5; the `Z↔X` basis
duality). Conjugating a Bell projector by `H ⊗ H` gives the projector onto the image Bell
state. -/
theorem bb84_hadamardPair_conj_bitFlipProjector_eq_phaseFlipProjector :
    bb84HadamardPair * QKD.BB84.Model.bitFlipProjector * bb84HadamardPair =
      QKD.BB84.Model.phaseFlipProjector := by
  nth_rewrite 2 [← bb84HadamardPair_hermitian]
  unfold QKD.BB84.Model.bitFlipProjector QKD.BB84.Model.phaseFlipProjector bb84HadamardPair
  rw [Matrix.mul_add, Matrix.add_mul, op_mul_ketbra_mul_conjTranspose,
    op_mul_ketbra_mul_conjTranspose, hadamard_tensor_hadamard_mul_bellState01,
    hadamard_tensor_hadamard_mul_bellState11]
  congr 1
  simp

/-!
## The X-basis conjugate component and phase observability
-/

/-- The **X-basis conjugate** of a de Finetti component `σ`: `H⊗H · σ · H⊗H`.

This is again a valid density operator (conjugation by the Hermitian unitary
`bb84HadamardPair` preserves Hermiticity, positivity and trace).  Its computational
(`Z`) Born diagonal equals the `X⊗X` Born diagonal of `σ`, so reading `σ` in the
X-basis is the same as reading `bb84XBasisConjugate σ` in the Z-basis.  Explicit
construction; no `Classical.choose`. -/
def bb84XBasisConjugate (σ : DensityOp signalDim) : DensityOp signalDim :=
  ⟨⟨⟨bb84HadamardPair * σ.toOp * bb84HadamardPair,
      by
        have hpsd :
            Matrix.PosSemidef (bb84HadamardPair * σ.toOp * bb84HadamardPair†) :=
          (posSemidefOp_implies_mathlib σ.toPosSemidefOp).mul_mul_conjTranspose_same
            bb84HadamardPair
        rw [bb84HadamardPair_hermitian] at hpsd
        exact hpsd.isHermitian⟩,
    by
      have hpsd :
          Matrix.PosSemidef (bb84HadamardPair * σ.toOp * bb84HadamardPair†) :=
        (posSemidefOp_implies_mathlib σ.toPosSemidefOp).mul_mul_conjTranspose_same
          bb84HadamardPair
      rw [bb84HadamardPair_hermitian] at hpsd
      intro x
      unfold quadraticForm
      exact (RCLike.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg x)).1⟩,
   by
    rw [Matrix.trace_mul_comm (bb84HadamardPair * σ.toOp), ← Matrix.mul_assoc,
        bb84HadamardPair_unitary, Matrix.one_mul, σ.trace_one]⟩

@[simp]
theorem bb84XBasisConjugate_toOp (σ : DensityOp signalDim) :
    (bb84XBasisConjugate σ).toOp = bb84HadamardPair * σ.toOp * bb84HadamardPair := rfl

/-- The X-basis conjugation `σ ↦ H⊗H · σ · H⊗H` is continuous (the `DensityOp`
topology is induced by `toOp`, and matrix multiplication is continuous). -/
theorem bb84XBasisConjugate_continuous : Continuous bb84XBasisConjugate := by
  apply continuous_induced_rng.mpr
  have h : ((fun ρ : DensityOp signalDim => ρ.toOp) ∘ bb84XBasisConjugate)
      = fun σ : DensityOp signalDim =>
          bb84HadamardPair * σ.toOp * bb84HadamardPair := rfl
  rw [h]
  exact (continuous_const.matrix_mul continuous_induced_dom).matrix_mul continuous_const

/-- **Phase observability.**  The single-round bit-flip rate of the X-basis conjugate
`bb84XBasisConjugate σ` equals the single-round phase-flip rate of `σ`:
`bitFlipErrorRate_single (bb84XBasisConjugate σ) = phaseFlipErrorRate_single σ`.

This is the operational statement that the X-basis measurement makes the phase-error
rate observable.  It follows from the crux identity
`bb84_hadamardPair_conj_bitFlipProjector_eq_phaseFlipProjector` by trace cyclicity:
`Tr(Π_bit · H⊗H σ H⊗H) = Tr(H⊗H Π_bit H⊗H · σ) = Tr(Π_phase · σ)`. -/
theorem bb84_xBasisConjugate_bitRate_eq_phaseRate (σ : DensityOp signalDim) :
    QKD.BB84.Model.bitFlipErrorRate_single (bb84XBasisConjugate σ) =
      QKD.BB84.Model.phaseFlipErrorRate_single σ := by
  unfold QKD.BB84.Model.bitFlipErrorRate_single QKD.BB84.Model.phaseFlipErrorRate_single
  rw [bb84XBasisConjugate_toOp]
  congr 1
  -- Tr(Π_bit · (H⊗H σ H⊗H)) = Tr((H⊗H Π_bit H⊗H) · σ) = Tr(Π_phase · σ)
  calc (QKD.BB84.Model.bitFlipProjector * (bb84HadamardPair * σ.toOp * bb84HadamardPair)).trace
         = ((QKD.BB84.Model.bitFlipProjector * bb84HadamardPair * σ.toOp) *
              bb84HadamardPair).trace := by
        simp only [Matrix.mul_assoc]
    _ = (bb84HadamardPair * (QKD.BB84.Model.bitFlipProjector * bb84HadamardPair * σ.toOp)).trace :=
        Matrix.trace_mul_comm _ _
    _ = (bb84HadamardPair * QKD.BB84.Model.bitFlipProjector * bb84HadamardPair * σ.toOp).trace :=
        by
        simp only [Matrix.mul_assoc]
    _ = (QKD.BB84.Model.phaseFlipProjector * σ.toOp).trace := by
        rw [bb84_hadamardPair_conj_bitFlipProjector_eq_phaseFlipProjector]

end QKD.BB84.Model

end
