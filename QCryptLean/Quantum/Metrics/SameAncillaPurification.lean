import QCryptLean.InfoTheory.DeFinetti.MaxEntangled
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.Quantum.Metrics.PurificationUnitaryAction
import QCryptLean.Quantum.Channels.CPTP.SubstateExtraction
import QCryptLean.Quantum.Matrix.RectangularGramIsometry
import QCryptLean.Quantum.Metrics.PolarUnitary
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Operators.DensityOperator
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Same-Ancilla Purification — canonical purifications, overlaps, and Uhlmann witnesses

This file packages the same-ancilla algebraic extension
`(sqrt P ⊗ 1) Ω (sqrt P ⊗ 1)†`; when `P` is positive semidefinite, it is the
standard purification of `P` using the unnormalized maximally entangled ketbra
on an ancilla of the same dimension. It develops the operator-level
construction, its density-operator packaging, and the overlap identities used
in the fidelity bridge.

## Main definitions
- `sameAncillaPurification`: the purification operator `A * Ω * A†`
- `sameAncillaPurificationDensity`: the density-operator packaging of this
  purification
- `sameAncillaPurificationKet`: the explicit canonical purification ket

## Main statements

- `partialTraceB_sameAncillaPurification`: tracing out the ancilla recovers the
  original operator
- `partialTraceB_sameAncillaPurificationKet`: the explicit same-ancilla
  purification ket purifies its density operator
- `sameAncillaPurificationDensity_partialTraceA_toOp_transpose`: tracing out
  the first factor gives the transpose of the purified density matrix
- `sameAncillaPurificationDensity_isPure`: the packaged purification is pure
- `sameAncillaPurificationKet_left_mul_eq_trace`: purification overlaps compute
  the square-root trace expression
- `sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`:
  a tensor-unitary overlap realizes the mixed-state square-root trace
- `sameAncillaPurificationKet_ancilla_unitary_of_purifies`: any same-dimensional
  purification of `ρ` is the canonical purification up to an ancilla-side unitary
  (Watrous Thm 2.12 / Nielsen–Chuang Thm 2.5)
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrousPurification

private lemma quadraticForm_sandwich {n : ℕ} (A B : Op n) (x : Fin n → ℂ) :
    quadraticForm (A * B * A†) x = quadraticForm B (A†.mulVec x) := by
  unfold quadraticForm
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.star_mulVec, conjTranspose_conjTranspose]

/-- The algebraic same-ancilla construction
    `(sqrt P ⊗ 1) Ω (sqrt P ⊗ 1)†`, using the unnormalized maximally entangled
    ketbra `Ω`. Under `P.PosSemidef`, this is the standard purification whose
    partial trace recovers `P`. The definition is total (accepts arbitrary `Op d`);
    the partial-trace recovery identity `partialTraceB_sameAncillaPurification`
    requires the `PosSemidef` hypothesis. -/
def sameAncillaPurification {d : ℕ} (P : Op d) : Op (d * d) :=
  Op.tensor (CFC.sqrt P) (1 : Op d) *
    InfoTheory.DeFinetti.maxEntangledOp d *
    (Op.tensor (CFC.sqrt P) (1 : Op d))†

/-- The purification operator is Hermitian. -/
lemma sameAncillaPurification_isHermitian {d : ℕ} (P : Op d) :
    (sameAncillaPurification P).IsHermitian := by
  unfold sameAncillaPurification IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [InfoTheory.DeFinetti.maxEntangledOp_isHermitian, Matrix.mul_assoc]

/-- The purification operator is positive semidefinite. -/
lemma sameAncillaPurification_posSemidef {d : ℕ} (P : Op d) :
    (sameAncillaPurification P).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨sameAncillaPurification_isHermitian P, fun x => ?_⟩
  let A : Op (d * d) := Op.tensor (CFC.sqrt P) (1 : Op d)
  let Ψ : Op (d * d) := InfoTheory.DeFinetti.maxEntangledOp d
  have h_key : quadraticForm (A * Ψ * A†) x = quadraticForm Ψ (A†.mulVec x) :=
    quadraticForm_sandwich A Ψ x
  have h_re : 0 ≤ (quadraticForm Ψ (A†.mulVec x)).re :=
    posSemidef_re_quadraticForm_nonneg (InfoTheory.DeFinetti.maxEntangledOp_posSemidef d) _
  have h_conj := quadraticForm_hermitian_conj_eq_self Ψ
    (InfoTheory.DeFinetti.maxEntangledOp_isHermitian d) (A†.mulVec x)
  have h_im : (quadraticForm Ψ (A†.mulVec x)).im = 0 := by
    have := congr_arg Complex.im h_conj
    simp [Complex.conj_im] at this
    linarith
  have h_nonneg : 0 ≤ quadraticForm (A * Ψ * A†) x := by
    rw [h_key, Complex.nonneg_iff]
    exact ⟨h_re, h_im.symm⟩
  simpa [sameAncillaPurification, A, Ψ, quadraticForm] using h_nonneg

/-- Partial tracing the purification over the ancilla recovers `P`. -/
lemma partialTraceB_sameAncillaPurification {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) :
    partialTraceB (sameAncillaPurification P) = P := by
  unfold sameAncillaPurification
  rw [show (Op.tensor (CFC.sqrt P) (1 : Op d))† = Op.tensor (CFC.sqrt P) (1 : Op d) by
    rw [Op.tensor_conjTranspose, conjTranspose_one,
      Math.SpectralTheory.cfc_sqrt_conjTranspose_eq]]
  rw [Quantum.TensorProducts.partialTraceB_sandwich_tensor_one
    (CFC.sqrt P) (CFC.sqrt P) (InfoTheory.DeFinetti.maxEntangledOp d)]
  rw [InfoTheory.DeFinetti.maxEntangledOp_partialTraceB]
  simpa using CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)

/-- The purification has the same trace as `P`. -/
lemma trace_sameAncillaPurification {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) :
    (sameAncillaPurification P).trace = P.trace := by
  unfold sameAncillaPurification
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [Op.tensor_conjTranspose, conjTranspose_one, Math.SpectralTheory.cfc_sqrt_conjTranspose_eq,
    Op.tensor_mul, Matrix.one_mul]
  rw [CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)]
  exact InfoTheory.DeFinetti.trace_maxEntangled_mul_tensor_one P

/-- Left multiplication by `V ⊗ 1` before partial trace recovers `V * P`. -/
lemma partialTraceB_left_mul_sameAncillaPurification {d : ℕ}
    (V P : Op d) (hP : P.PosSemidef) :
    partialTraceB (Op.tensor V (1 : Op d) * sameAncillaPurification P) = V * P := by
  rw [show Op.tensor V (1 : Op d) * sameAncillaPurification P =
      Op.tensor V (1 : Op d) * sameAncillaPurification P * Op.tensor (1 : Op d) (1 : Op d) by
      simp]
  rw [Quantum.TensorProducts.partialTraceB_sandwich_tensor_one V (1 : Op d)
    (sameAncillaPurification P)]
  rw [partialTraceB_sameAncillaPurification P hP, Matrix.mul_one]

/-- The purification inherits the trace bound `Tr(P).re ≤ 1`. -/
lemma trace_re_sameAncillaPurification_le_one {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) (hP_tr : P.trace.re ≤ 1) :
    (sameAncillaPurification P).trace.re ≤ 1 := by
  rw [trace_sameAncillaPurification P hP]
  exact hP_tr

/-- The same-ancilla purification of a density operator, packaged as a density
    operator on the doubled space. -/
def sameAncillaPurificationDensity {d : ℕ} (σ : DensityOp d) :
    DensityOp (d * d) := by
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  refine ⟨⟨⟨sameAncillaPurification σ.toOp,
    sameAncillaPurification_isHermitian σ.toOp⟩,
    fun x => ?_⟩, ?_⟩
  · exact ((sameAncillaPurification_posSemidef σ.toOp).dotProduct_mulVec_nonneg x).1
  rw [trace_sameAncillaPurification σ.toOp hσ_psd, σ.trace_one]

/-- The explicit canonical same-ancilla purification ket built from `CFC.sqrt P`
    for an arbitrary operator `P`.  When `P` is positive semidefinite, this ket
    purifies `P`. -/
def sameAncillaPurificationKetOfOp {d : ℕ} (P : Op d) : Ket (d * d) :=
  (Op.tensor (CFC.sqrt P) (1 : Op d)) * InfoTheory.DeFinetti.maxEntangledKet d

/-- The explicit canonical purification ket built from `CFC.sqrt σ.toOp`. -/
def sameAncillaPurificationKet {d : ℕ} (σ : DensityOp d) : Ket (d * d) :=
  sameAncillaPurificationKetOfOp σ.toOp

/-- The operator-level canonical purification ket has outer product equal to
    `sameAncillaPurification P`. -/
lemma sameAncillaPurification_eq_ketbra_sameAncillaPurificationKetOfOp
    {d : ℕ} (P : Op d) :
    sameAncillaPurification P =
      sameAncillaPurificationKetOfOp P * (sameAncillaPurificationKetOfOp P).dag := by
  let A : Op (d * d) := Op.tensor (CFC.sqrt P) (1 : Op d)
  calc
    sameAncillaPurification P
      = A * InfoTheory.DeFinetti.maxEntangledOp d * A† := by
          simp [sameAncillaPurification, A]
    _ = A * (InfoTheory.DeFinetti.maxEntangledKet d *
          (InfoTheory.DeFinetti.maxEntangledKet d).dag) * A† := by
          rw [InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra]
    _ = (A * InfoTheory.DeFinetti.maxEntangledKet d) *
          (A * InfoTheory.DeFinetti.maxEntangledKet d).dag := by
          rw [op_mul_ketbra, ketbra_mul_op, dag_op_mul_ket]
    _ = sameAncillaPurificationKetOfOp P * (sameAncillaPurificationKetOfOp P).dag := by
          simp [sameAncillaPurificationKetOfOp, A]

/-- The operator-level canonical purification ket reduces to `P` after tracing
    out the same-dimensional ancilla. -/
lemma partialTraceB_sameAncillaPurificationKetOfOp
    {d : ℕ} (P : Op d) (hP : P.PosSemidef) :
    partialTraceB
      (sameAncillaPurificationKetOfOp P *
        (sameAncillaPurificationKetOfOp P).dag) = P := by
  rw [← sameAncillaPurification_eq_ketbra_sameAncillaPurificationKetOfOp P]
  exact partialTraceB_sameAncillaPurification P hP

/-- The explicit same-ancilla purification ket purifies its density operator. -/
theorem partialTraceB_sameAncillaPurificationKet {d : ℕ} (σ : DensityOp d) :
    partialTraceB (sameAncillaPurificationKet σ * (sameAncillaPurificationKet σ).dag) =
      σ.toOp := by
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  simpa [sameAncillaPurificationKet] using
    partialTraceB_sameAncillaPurificationKetOfOp σ.toOp hσ_psd

/-- The norm scalar of the operator-level canonical purification ket is
    `P.trace`. -/
lemma sameAncillaPurificationKetOfOp_norm
    {d : ℕ} (P : Op d) (hP : P.PosSemidef) :
    (sameAncillaPurificationKetOfOp P).dag *
        sameAncillaPurificationKetOfOp P = P.trace := by
  have htrace :
      ((sameAncillaPurificationKetOfOp P) *
          (sameAncillaPurificationKetOfOp P).dag : Op (d * d)).trace = P.trace := by
    rw [← sameAncillaPurification_eq_ketbra_sameAncillaPurificationKetOfOp P,
      trace_sameAncillaPurification P hP]
  have htrace' :
      ((sameAncillaPurificationKetOfOp P) *
          (sameAncillaPurificationKetOfOp P).dag : Op (d * d)).trace =
      (sameAncillaPurificationKetOfOp P).dag * sameAncillaPurificationKetOfOp P := by
    have htrace' := trace_ketbra_mul (sameAncillaPurificationKetOfOp P) (1 : Op (d * d))
    have hBraOne :
        (sameAncillaPurificationKetOfOp P).dag * (1 : Op (d * d)) =
          (sameAncillaPurificationKetOfOp P).dag := by
      ext j
      simp only [bra_mul_op_vec, Matrix.one_apply]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ j]
      simp
    simpa [hBraOne] using htrace'
  rw [htrace'] at htrace
  exact htrace

/-- The explicit canonical purification ket has outer product equal to
    `sameAncillaPurification σ.toOp`. -/
lemma sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet
    {d : ℕ} (σ : DensityOp d) :
    sameAncillaPurification σ.toOp =
      sameAncillaPurificationKet σ * (sameAncillaPurificationKet σ).dag := by
  simpa [sameAncillaPurificationKet] using
    sameAncillaPurification_eq_ketbra_sameAncillaPurificationKetOfOp σ.toOp

private lemma sameAncillaPurificationKet_cross
    {d : ℕ} (ρ σ : DensityOp d) :
    sameAncillaPurificationKet ρ * (sameAncillaPurificationKet σ).dag =
      Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
        InfoTheory.DeFinetti.maxEntangledOp d *
        (Op.tensor (CFC.sqrt σ.toOp) (1 : Op d))† := by
  let Aρ : Op (d * d) := Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d)
  let Aσ : Op (d * d) := Op.tensor (CFC.sqrt σ.toOp) (1 : Op d)
  calc
    sameAncillaPurificationKet ρ * (sameAncillaPurificationKet σ).dag
      = (Aρ * InfoTheory.DeFinetti.maxEntangledKet d) *
          (Aσ * InfoTheory.DeFinetti.maxEntangledKet d).dag := by
          simp [sameAncillaPurificationKet, sameAncillaPurificationKetOfOp, Aρ, Aσ]
    _ = (Aρ * InfoTheory.DeFinetti.maxEntangledKet d) *
          ((InfoTheory.DeFinetti.maxEntangledKet d).dag * Aσ†) := by
          rw [dag_op_mul_ket]
    _ = Aρ * (InfoTheory.DeFinetti.maxEntangledKet d *
          (InfoTheory.DeFinetti.maxEntangledKet d).dag) * Aσ† := by
          rw [op_mul_ketbra, ketbra_mul_op]
    _ = Aρ * InfoTheory.DeFinetti.maxEntangledOp d * Aσ† := by
          rw [InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra]
    _ = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
          InfoTheory.DeFinetti.maxEntangledOp d *
          (Op.tensor (CFC.sqrt σ.toOp) (1 : Op d))† := by
          simp [Aρ, Aσ]

/-- The explicit canonical purification ket is normalized. -/
lemma sameAncillaPurificationKet_normalized
    {d : ℕ} (σ : DensityOp d) :
    (sameAncillaPurificationKet σ).dag * sameAncillaPurificationKet σ = 1 := by
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  calc
    (sameAncillaPurificationKet σ).dag * sameAncillaPurificationKet σ =
        σ.toOp.trace := by
      simpa [sameAncillaPurificationKet] using
        sameAncillaPurificationKetOfOp_norm σ.toOp hσ_psd
    _ = 1 := σ.trace_one

/-- The packaged same-ancilla purification density is `DensityOp.fromPure` of
    the explicit canonical purification ket. -/
lemma sameAncillaPurificationDensity_eq_fromPure_sameAncillaPurificationKet
    {d : ℕ} (σ : DensityOp d) :
    sameAncillaPurificationDensity σ =
      DensityOp.fromPure (sameAncillaPurificationKet σ)
        (sameAncillaPurificationKet_normalized σ) := by
  apply DensityOp.ext
  simp only [sameAncillaPurificationDensity, DensityOp.fromPure]
  exact sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet σ

/-- The same-ancilla purification of a density operator is pure. -/
lemma sameAncillaPurificationDensity_isPure {d : ℕ}
    (σ : DensityOp d) :
    (sameAncillaPurificationDensity σ).IsPure := by
  unfold DensityOp.IsPure sameAncillaPurificationDensity
  simp only
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  let A : Op (d * d) := Op.tensor (CFC.sqrt σ.toOp) (1 : Op d)
  let Ω : Op (d * d) := InfoTheory.DeFinetti.maxEntangledOp d
  have lhs_eq : (A * Ω * A†) * (A * Ω * A†) =
      A * (Ω * (A† * A) * Ω) * A† := by
    simp only [Matrix.mul_assoc]
  have adjA_mul_A : A† * A = σ.toOp ⊗ (1 : Op d) := by
    simp only [A, Op.tensor_conjTranspose, Op.tensor_mul]
    rw [conjTranspose_one, Matrix.one_mul, Math.SpectralTheory.cfc_sqrt_conjTranspose_eq,
      CFC.sqrt_mul_sqrt_self σ.toOp (ha := hσ_psd.nonneg)]
  unfold sameAncillaPurification
  rw [lhs_eq, adjA_mul_A, InfoTheory.DeFinetti.maxEntangledOp_sandwich,
    σ.trace_one, one_smul]

/-- Partial tracing the same-ancilla purification density over the ancilla
    recovers the original density operator. -/
lemma partialTraceB_sameAncillaPurificationDensity {d : ℕ}
    (σ : DensityOp d) :
    partialTraceB (sameAncillaPurificationDensity σ).toOp = σ.toOp := by
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  unfold sameAncillaPurificationDensity
  simp only
  exact partialTraceB_sameAncillaPurification σ.toOp hσ_psd

/-- Reshaping the canonical same-ancilla purification ket gives the square root
of the purified density matrix. -/
theorem sameAncillaPurificationKet_reshapeVec {d : ℕ}
    (σ : DensityOp d) :
    reshapeVec (sameAncillaPurificationKet σ).vec = CFC.sqrt σ.toOp := by
  ext i j
  rw [Quantum.Channels.reshapeVec_apply]
  exact InfoTheory.DeFinetti.maxEntangledKet_tensor_one_apply (CFC.sqrt σ.toOp) i j

private lemma sameAncillaPurificationKet_partialTraceA_ketbra {d : ℕ}
    (σ : DensityOp d) :
    partialTraceA
      (sameAncillaPurificationKet σ * (sameAncillaPurificationKet σ).dag) =
        σ.toOp.transpose := by
  rw [Quantum.Operators.ket_mul_dag_eq_vecMulVec,
    Quantum.Channels.partialTraceA_vecMulVec_eq_transpose_mul_conjTranspose,
    sameAncillaPurificationKet_reshapeVec]
  let S : Op d := CFC.sqrt σ.toOp
  let hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hS_herm : Sᴴ = S := by
    simpa [S] using Math.SpectralTheory.cfc_sqrt_conjTranspose_eq σ.toOp
  have hS_transpose_conj : Sᵀᴴ = Sᵀ := by
    ext i j
    have h := congrArg (fun M : Op d => M j i) hS_herm
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
  rw [hS_transpose_conj]
  calc
    Sᵀ * Sᵀ = (S * S)ᵀ := by rw [Matrix.transpose_mul]
    _ = σ.toOpᵀ := by
      change (CFC.sqrt σ.toOp * CFC.sqrt σ.toOp)ᵀ = σ.toOpᵀ
      rw [CFC.sqrt_mul_sqrt_self σ.toOp (ha := hσ_psd.nonneg)]

/-- The left marginal of the same-ancilla purification is the transpose of the
purified density matrix. -/
theorem sameAncillaPurificationDensity_partialTraceA_toOp_transpose
    {m : ℕ} (ρ : DensityOp m) :
    partialTraceA (sameAncillaPurificationDensity ρ).toOp = ρ.toOp.transpose := by
  rw [sameAncillaPurificationDensity_eq_fromPure_sameAncillaPurificationKet]
  simp only [DensityOp.fromPure]
  exact sameAncillaPurificationKet_partialTraceA_ketbra ρ

lemma sameAncillaPurificationDensity_pureKetOf_eq_phase
    {d : ℕ} (σ : DensityOp d) :
    letI : NeZero d := neZero_of_densityOp σ
    ∃ θ : ℝ, ∀ i : Fin (d * d),
      ((sameAncillaPurificationDensity σ).pureKetOf
          (sameAncillaPurificationDensity_isPure σ)).vec i =
        Complex.exp (Complex.I * θ) * (sameAncillaPurificationKet σ).vec i := by
  let : NeZero d := neZero_of_densityOp σ
  change ∃ θ : ℝ, ∀ i : Fin (d * d),
      ((sameAncillaPurificationDensity σ).pureKetOf
          (sameAncillaPurificationDensity_isPure σ)).vec i =
        Complex.exp (Complex.I * θ) * (sameAncillaPurificationKet σ).vec i
  have hphase := Quantum.Operators.fromPure_pureKetOf_eq_mod_phase
    (sameAncillaPurificationKet σ) (sameAncillaPurificationKet_normalized σ)
  simpa [sameAncillaPurificationDensity_eq_fromPure_sameAncillaPurificationKet σ]
    using hphase


/-- Overlaps between same-ancilla purification kets compute left-multiplied traces. -/
lemma sameAncillaPurificationDensity_pureKet_left_mul_eq_trace {d : ℕ}
    (σ : DensityOp d) (V : Op d) :
    letI : NeZero d := neZero_of_densityOp σ
    let τ := sameAncillaPurificationDensity σ
    let hpure := sameAncillaPurificationDensity_isPure σ
    let ψ := τ.pureKetOf hpure
    ψ.dag * (Op.tensor V (1 : Op d)) * ψ = (V * σ.toOp).trace := by
  let : NeZero d := neZero_of_densityOp σ
  change
    let τ := sameAncillaPurificationDensity σ
    let hpure := sameAncillaPurificationDensity_isPure σ
    let ψ := τ.pureKetOf hpure
    ψ.dag * (Op.tensor V (1 : Op d)) * ψ = (V * σ.toOp).trace
  intro τ hpure ψ
  have hψ : τ.toOp = ψ * ψ.dag := DensityOp.pureKetOf_spec τ hpure
  calc ψ.dag * (Op.tensor V (1 : Op d)) * ψ
      = (((ψ * ψ.dag) * (Op.tensor V (1 : Op d))).trace) := by
          symm
          exact trace_ketbra_mul ψ (Op.tensor V (1 : Op d))
    _ = (((τ.toOp) * (Op.tensor V (1 : Op d))).trace) := by rw [hψ]
    _ = ((Op.tensor V (1 : Op d) * τ.toOp).trace) := by
          rw [Matrix.trace_mul_comm]
    _ = (V * σ.toOp).trace := by
          change (Op.tensor V (1 : Op d) * sameAncillaPurification σ.toOp).trace =
            (V * σ.toOp).trace
          let hσ_psd : σ.toOp.PosSemidef :=
            Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
          rw [← trace_partialTraceB]
          rw [partialTraceB_left_mul_sameAncillaPurification V σ.toOp hσ_psd]

/-- Cross-overlaps of the explicit canonical same-ancilla purification kets are
    traces against the mixed square-root expression. -/
lemma sameAncillaPurificationKet_left_mul_eq_trace
    {d : ℕ} (ρ σ : DensityOp d) (V : Op d) :
    let ψρ := sameAncillaPurificationKet ρ
    let ψσ := sameAncillaPurificationKet σ
    ψσ.dag * (Op.tensor V (1 : Op d)) * ψρ =
      (CFC.sqrt σ.toOp * V * CFC.sqrt ρ.toOp).trace := by
  intro ψρ ψσ
  let Aρ : Op (d * d) := Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d)
  let Aσ : Op (d * d) := Op.tensor (CFC.sqrt σ.toOp) (1 : Op d)
  let Ω : Op (d * d) := InfoTheory.DeFinetti.maxEntangledOp d
  let T : Op (d * d) := Op.tensor V (1 : Op d)
  have hσ_sqrt : (CFC.sqrt σ.toOp)† = CFC.sqrt σ.toOp :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq σ.toOp
  calc
    ψσ.dag * T * ψρ
      = ((ψρ * ψσ.dag) * T).trace := by
          symm
          exact trace_cross_ketbra_mul ψρ ψσ T
    _ = ((Aρ * Ω * Aσ†) * T).trace := by
          rw [sameAncillaPurificationKet_cross ρ σ]
    _ = (((Aσ† * T) * (Aρ * Ω)).trace) := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm (Aρ * Ω) (Aσ† * T)]
    _ = ((Ω * (Aσ† * T * Aρ)).trace) := by
          calc
            (((Aσ† * T) * (Aρ * Ω)).trace) = (((Aσ† * T * Aρ) * Ω).trace) := by
              simp [Matrix.mul_assoc]
            _ = ((Ω * (Aσ† * T * Aρ)).trace) := by
              rw [Matrix.trace_mul_comm]
    _ = (Ω * (Op.tensor (CFC.sqrt σ.toOp * V * CFC.sqrt ρ.toOp) (1 : Op d))).trace := by
          have hAσ :
              Aσ† = Op.tensor (CFC.sqrt σ.toOp) (1 : Op d) := by
            simp [Aσ, Op.tensor_conjTranspose, hσ_sqrt]
          rw [hAσ]
          simp [Aρ, T, Op.tensor_mul, Matrix.mul_assoc]
    _ = (CFC.sqrt σ.toOp * V * CFC.sqrt ρ.toOp).trace := by
          rw [InfoTheory.DeFinetti.trace_maxEntangled_mul_tensor_one]

/-- Ancilla-side analogue of `sameAncillaPurificationKet_left_mul_eq_trace`:
    inserting an ancilla-side operator `1 ⊗ V` between the canonical kets gives a
    trace against the mixed square-root expression folded with the *transpose* `Vᵀ`. -/
lemma sameAncillaPurificationKet_ancilla_left_mul_eq_trace
    {d : ℕ} (ρ τ : DensityOp d) (V : Op d) :
    (sameAncillaPurificationKet ρ).dag * (Op.tensor (1 : Op d) V) *
        (sameAncillaPurificationKet τ) =
      (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp * V.transpose).trace := by
  let Aρ : Op (d * d) := Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d)
  let Aτ : Op (d * d) := Op.tensor (CFC.sqrt τ.toOp) (1 : Op d)
  let Ω : Op (d * d) := InfoTheory.DeFinetti.maxEntangledOp d
  let T : Op (d * d) := Op.tensor (1 : Op d) V
  have hρ_sqrt : (CFC.sqrt ρ.toOp)† = CFC.sqrt ρ.toOp :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq ρ.toOp
  calc
    (sameAncillaPurificationKet ρ).dag * T * (sameAncillaPurificationKet τ)
      = ((sameAncillaPurificationKet τ * (sameAncillaPurificationKet ρ).dag) * T).trace := by
          symm
          exact trace_cross_ketbra_mul (sameAncillaPurificationKet τ)
            (sameAncillaPurificationKet ρ) T
    _ = ((Aτ * Ω * Aρ†) * T).trace := by
          rw [sameAncillaPurificationKet_cross τ ρ]
    _ = (((Aρ† * T) * (Aτ * Ω)).trace) := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm (Aτ * Ω) (Aρ† * T)]
    _ = ((Ω * (Aρ† * T * Aτ)).trace) := by
          calc
            (((Aρ† * T) * (Aτ * Ω)).trace) = (((Aρ† * T * Aτ) * Ω).trace) := by
              simp [Matrix.mul_assoc]
            _ = ((Ω * (Aρ† * T * Aτ)).trace) := by
              rw [Matrix.trace_mul_comm]
    _ = (Ω * (Op.tensor (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp) V)).trace := by
          have hAρ :
              Aρ† = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) := by
            simp [Aρ, Op.tensor_conjTranspose, hρ_sqrt]
          rw [hAρ]
          simp [Aτ, T, Op.tensor_mul]
    _ = (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp * V.transpose).trace := by
          rw [InfoTheory.DeFinetti.trace_maxEntangled_mul_tensor]

/-- The same-ancilla purification overlap against a tensor-unitary is bounded by `1`. -/
lemma sameAncillaPurificationDensity_pureKet_tensorUnitary_overlap_re_le_one
    {d : ℕ} (ρ σ : DensityOp d) (U : UnitaryOp d) :
    letI : NeZero d := neZero_of_densityOp ρ
    let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
      (sameAncillaPurificationDensity_isPure ρ)
    let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
      (sameAncillaPurificationDensity_isPure σ)
    (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re ≤ 1 := by
  let : NeZero d := neZero_of_densityOp ρ
  change
    let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
      (sameAncillaPurificationDensity_isPure ρ)
    let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
      (sameAncillaPurificationDensity_isPure σ)
    (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re ≤ 1
  intro ψρ ψσ
  let Ut : UnitaryOp (d * d) := tensorUnitary U
  let χ : Ket (d * d) := ⟨Ut.toOp.mulVec ψρ.vec⟩
  have hχ_norm : χ.dag * χ = 1 := by
    change dotProduct (star (Ut.toOp.mulVec ψρ.vec)) (Ut.toOp.mulVec ψρ.vec) = 1
    rw [Ut.preserves_inner]
    exact
      (sameAncillaPurificationDensity ρ).pureKetOf_normalized
        (sameAncillaPurificationDensity_isPure ρ)
  have hψσ_norm : ψσ.dag * ψσ = 1 :=
    (sameAncillaPurificationDensity σ).pureKetOf_normalized
      (sameAncillaPurificationDensity_isPure σ)
  have hoverlap : ‖(ψσ.dag * χ : ℂ)‖ ≤ 1 :=
    Quantum.Operators.ket_overlap_norm_le_one ψσ χ hψσ_norm hχ_norm
  have hre : (ψσ.dag * χ : ℂ).re ≤ ‖(ψσ.dag * χ : ℂ)‖ := Complex.re_le_norm _
  have happly : Ut.toOp.mulVec ψρ.vec = χ.vec := rfl
  have hop :
      ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ = ψσ.dag * χ := by
    exact operator_action_in_bra_ket (Op.tensor U.toOp (1 : Op d)) ψσ ψρ χ happly
  rw [hop]
  exact le_trans hre hoverlap

/-- For positive semidefinite `Q`, the polar-style product `√P √Q` satisfies
`(√P √Q)(√P √Q)† = √P Q √P`. -/
lemma cfcSqrt_mul_cfcSqrt_mul_conjTranspose_self {d : ℕ} (P Q : Op d)
    (hQ : Q.PosSemidef) :
    (CFC.sqrt P * CFC.sqrt Q) * (CFC.sqrt P * CFC.sqrt Q)† =
      CFC.sqrt P * Q * CFC.sqrt P := by
  rw [conjTranspose_mul, Math.SpectralTheory.cfc_sqrt_conjTranspose_eq P,
      Math.SpectralTheory.cfc_sqrt_conjTranspose_eq Q,
      show CFC.sqrt P * CFC.sqrt Q * (CFC.sqrt Q * CFC.sqrt P) =
          CFC.sqrt P * (CFC.sqrt Q * CFC.sqrt Q) * CFC.sqrt P from by
        simp [Matrix.mul_assoc],
      CFC.sqrt_mul_sqrt_self Q (ha := hQ.nonneg)]

/-- Canonical-ket version of the same-ancilla Uhlmann witness.

This isolates the finite-dimensional polar-unitary step from the later
`pureKetOf` phase transport. -/
lemma sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
    {d : ℕ} (ρ σ : DensityOp d) :
    ∃ U : UnitaryOp d,
      let ψρ := sameAncillaPurificationKet ρ
      let ψσ := sameAncillaPurificationKet σ
      (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp))).re := by
  let X : Op d := CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose X
  refine ⟨U, ?_⟩
  simp only
  have hσ_psd : σ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hXX :
      X * X.conjTranspose = CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp :=
    cfcSqrt_mul_cfcSqrt_mul_conjTranspose_self ρ.toOp σ.toOp hσ_psd
  have hpolar :
      (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace =
        (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp)).trace := by
    have hpolar' := hU
    rw [hXX] at hpolar'
    simpa [X] using hpolar'
  have hoverlap := sameAncillaPurificationKet_left_mul_eq_trace ρ σ U.toOp
  have htrace_cycle :
      (CFC.sqrt σ.toOp * U.toOp * CFC.sqrt ρ.toOp).trace =
        (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace := by
    calc
      (CFC.sqrt σ.toOp * U.toOp * CFC.sqrt ρ.toOp).trace
          = (CFC.sqrt ρ.toOp * (CFC.sqrt σ.toOp * U.toOp)).trace := by
              rw [Matrix.trace_mul_comm]
      _ = ((CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp) * U.toOp).trace := by
              simp [Matrix.mul_assoc]
      _ = (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace := by
              rw [Matrix.trace_mul_comm]
  calc
    ((sameAncillaPurificationKet σ).dag * (Op.tensor U.toOp (1 : Op d)) *
          sameAncillaPurificationKet ρ).re
        = (CFC.sqrt σ.toOp * U.toOp * CFC.sqrt ρ.toOp).trace.re := by
            exact congrArg Complex.re hoverlap
    _ = (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace.re := by
            rw [htrace_cycle]
    _ = (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp)).trace.re := by
            rw [hpolar]

/-- The relative phase between two unit complex numbers cancels with its inverse. -/
lemma relative_phase_cancel_of_norm_eq_one (αρ ασ : ℂ)
    (hαρ : ‖αρ‖ = 1) (hασ : ‖ασ‖ = 1) :
    (star ασ * αρ) * (ασ * star αρ) = 1 := by
  have hσ_unit : star ασ * ασ = 1 :=
    star_mul_self_eq_one_of_norm_eq_one ασ hασ
  have hρ_unit : αρ * star αρ = 1 := by
    rw [mul_comm, star_mul_self_eq_one_of_norm_eq_one αρ hαρ]
  calc
    (star ασ * αρ) * (ασ * star αρ) = (star ασ * ασ) * (αρ * star αρ) := by
      ring
    _ = 1 := by
      rw [hσ_unit, hρ_unit, one_mul]

/-- Scalar multiplication of the left operator scales canonical purification overlaps. -/
lemma sameAncillaPurificationKet_smul_left_mul_eq
    {d : ℕ} (ρ σ : DensityOp d) (α : ℂ) (V : Op d) :
    let ψρ := sameAncillaPurificationKet ρ
    let ψσ := sameAncillaPurificationKet σ
    ψσ.dag * (Op.tensor (α • V) (1 : Op d)) * ψρ =
      α * (ψσ.dag * (Op.tensor V (1 : Op d)) * ψρ) := by
  intro ψρ ψσ
  have htrace_phase :
      (CFC.sqrt σ.toOp * (α • V) * CFC.sqrt ρ.toOp).trace =
        α * (CFC.sqrt σ.toOp * V * CFC.sqrt ρ.toOp).trace := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
    rfl
  have hscaled := sameAncillaPurificationKet_left_mul_eq_trace ρ σ (α • V)
  have hbase := sameAncillaPurificationKet_left_mul_eq_trace ρ σ V
  rw [hscaled, hbase, htrace_phase]

/-- The arbitrary `pureKetOf` phases can be absorbed into the tensor unitary. -/
lemma sameAncillaPurificationDensity_exists_tensorUnitary_overlap_eq_sameAncillaPurificationKet
    {d : ℕ} (ρ σ : DensityOp d) (U₀ : UnitaryOp d) :
    letI : NeZero d := neZero_of_densityOp ρ
    ∃ U : UnitaryOp d,
      let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
        (sameAncillaPurificationDensity_isPure ρ)
      let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
        (sameAncillaPurificationDensity_isPure σ)
      let ψρ₀ := sameAncillaPurificationKet ρ
      let ψσ₀ := sameAncillaPurificationKet σ
      ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ =
        ψσ₀.dag * (Op.tensor U₀.toOp (1 : Op d)) * ψρ₀ := by
  let : NeZero d := neZero_of_densityOp ρ
  change ∃ U : UnitaryOp d,
      let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
        (sameAncillaPurificationDensity_isPure ρ)
      let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
        (sameAncillaPurificationDensity_isPure σ)
      let ψρ₀ := sameAncillaPurificationKet ρ
      let ψσ₀ := sameAncillaPurificationKet σ
      ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ =
        ψσ₀.dag * (Op.tensor U₀.toOp (1 : Op d)) * ψρ₀
  obtain ⟨θρ, hθρ⟩ := sameAncillaPurificationDensity_pureKetOf_eq_phase ρ
  obtain ⟨θσ, hθσ⟩ := sameAncillaPurificationDensity_pureKetOf_eq_phase σ
  let αρ : ℂ := Complex.exp (Complex.I * θρ)
  let ασ : ℂ := Complex.exp (Complex.I * θσ)
  let phase : ℂ := ασ * star αρ
  have hαρ_norm : ‖αρ‖ = 1 := by
    simp [αρ, Complex.norm_exp_I_mul_ofReal θρ]
  have hασ_norm : ‖ασ‖ = 1 := by
    simp [ασ, Complex.norm_exp_I_mul_ofReal θσ]
  have hphase_norm : ‖phase‖ = 1 := by
    simp [phase, hασ_norm, hαρ_norm]
  let U : UnitaryOp d := phaseUnitary phase hphase_norm U₀
  refine ⟨U, ?_⟩
  simp only
  let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
    (sameAncillaPurificationDensity_isPure ρ)
  let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
    (sameAncillaPurificationDensity_isPure σ)
  let ψρ₀ := sameAncillaPurificationKet ρ
  let ψσ₀ := sameAncillaPurificationKet σ
  let T : Op (d * d) := Op.tensor U.toOp (1 : Op d)
  let T₀ : Op (d * d) := Op.tensor U₀.toOp (1 : Op d)
  have hψρ : ψρ = αρ • ψρ₀ := by
    ext i
    simpa [ψρ, ψρ₀, αρ] using hθρ i
  have hψσ : ψσ = ασ • ψσ₀ := by
    ext i
    simpa [ψσ, ψσ₀, ασ] using hθσ i
  have hphase_cancel : (star ασ * αρ) * phase = 1 := by
    simpa [phase] using relative_phase_cancel_of_norm_eq_one αρ ασ hαρ_norm hασ_norm
  have hpure_phase :
      ψσ.dag * T * ψρ = (star ασ * αρ) * (ψσ₀.dag * T * ψρ₀) :=
    ket_scalar_overlap ψρ ψρ₀ ψσ ψσ₀ T αρ ασ hψρ hψσ
  have hcanon_phase :
      ψσ₀.dag * T * ψρ₀ = phase * (ψσ₀.dag * T₀ * ψρ₀) := by
    change ψσ₀.dag * (Op.tensor (phase • U₀.toOp) (1 : Op d)) * ψρ₀ =
      phase * (ψσ₀.dag * (Op.tensor U₀.toOp (1 : Op d)) * ψρ₀)
    exact sameAncillaPurificationKet_smul_left_mul_eq ρ σ phase U₀.toOp
  calc
    ψσ.dag * T * ψρ = (star ασ * αρ) * (ψσ₀.dag * T * ψρ₀) := hpure_phase
    _ = (star ασ * αρ) * (phase * (ψσ₀.dag * T₀ * ψρ₀)) := by
      rw [hcanon_phase]
    _ = ψσ₀.dag * T₀ * ψρ₀ := by
      rw [← mul_assoc, hphase_cancel, one_mul]

/-- After absorbing the `pureKetOf` phases into the tensor unitary, the real
part of the packaged overlap agrees with the canonical-ket overlap. -/
lemma sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_sameAncillaPurificationKet
    {d : ℕ} (ρ σ : DensityOp d) (U₀ : UnitaryOp d) :
    letI : NeZero d := neZero_of_densityOp ρ
    ∃ U : UnitaryOp d,
      let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
        (sameAncillaPurificationDensity_isPure ρ)
      let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
        (sameAncillaPurificationDensity_isPure σ)
      (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re =
        ((sameAncillaPurificationKet σ).dag * (Op.tensor U₀.toOp (1 : Op d)) *
          sameAncillaPurificationKet ρ).re := by
  let : NeZero d := neZero_of_densityOp ρ
  change ∃ U : UnitaryOp d,
      let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
        (sameAncillaPurificationDensity_isPure ρ)
      let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
        (sameAncillaPurificationDensity_isPure σ)
      (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re =
        ((sameAncillaPurificationKet σ).dag * (Op.tensor U₀.toOp (1 : Op d)) *
          sameAncillaPurificationKet ρ).re
  obtain ⟨U, hoverlap⟩ :=
    sameAncillaPurificationDensity_exists_tensorUnitary_overlap_eq_sameAncillaPurificationKet
      ρ σ U₀
  refine ⟨U, ?_⟩
  simp only
  exact congrArg Complex.re hoverlap

/-- Mixed-state cross-overlap witness for same-ancilla purifications.

Some first-factor unitary realizes `Tr √(√ρ · σ · √ρ)` as the real part of the
overlap between the chosen `pureKetOf` representatives. -/
theorem sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
    {d : ℕ} (ρ σ : DensityOp d) :
    letI : NeZero d := neZero_of_densityOp ρ
    ∃ U : UnitaryOp d,
      let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
        (sameAncillaPurificationDensity_isPure ρ)
      let ψσ := (sameAncillaPurificationDensity σ).pureKetOf
        (sameAncillaPurificationDensity_isPure σ)
      (ψσ.dag * (Op.tensor U.toOp (1 : Op d)) * ψρ).re =
        (Matrix.trace (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp))).re := by
  let : NeZero d := neZero_of_densityOp ρ
  obtain ⟨U₀, hU₀⟩ :=
    sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich ρ σ
  obtain ⟨U, hre⟩ :=
    sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_sameAncillaPurificationKet
      ρ σ U₀
  exact ⟨U, hre.trans (by simpa using hU₀)⟩

/-- **Phase-transport at the norm level**: the modulus of the
canonical-purification overlap is unchanged by going from the
`sameAncillaPurificationKet` packaging to the `pureKetOf` packaging. -/
lemma sameAncillaPurificationDensity_pureKet_tensorUnitary_overlap_norm_eq_canonical
    {d : ℕ} (ρ τ : DensityOp d) (V : Op d) :
    letI : NeZero d := neZero_of_densityOp ρ
    let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
      (sameAncillaPurificationDensity_isPure ρ)
    let ψτ := (sameAncillaPurificationDensity τ).pureKetOf
      (sameAncillaPurificationDensity_isPure τ)
    ‖(ψτ.dag * Op.tensor V (1 : Op d) * ψρ : ℂ)‖ =
      ‖((sameAncillaPurificationKet τ).dag * Op.tensor V (1 : Op d) *
          sameAncillaPurificationKet ρ : ℂ)‖ := by
  let : NeZero d := neZero_of_densityOp ρ
  change
    let ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
      (sameAncillaPurificationDensity_isPure ρ)
    let ψτ := (sameAncillaPurificationDensity τ).pureKetOf
      (sameAncillaPurificationDensity_isPure τ)
    ‖(ψτ.dag * Op.tensor V (1 : Op d) * ψρ : ℂ)‖ =
      ‖((sameAncillaPurificationKet τ).dag * Op.tensor V (1 : Op d) *
          sameAncillaPurificationKet ρ : ℂ)‖
  intro ψρ ψτ
  obtain ⟨θρ, hθρ⟩ := sameAncillaPurificationDensity_pureKetOf_eq_phase ρ
  obtain ⟨θτ, hθτ⟩ := sameAncillaPurificationDensity_pureKetOf_eq_phase τ
  let αρ : ℂ := Complex.exp (Complex.I * θρ)
  let ατ : ℂ := Complex.exp (Complex.I * θτ)
  have hαρ_norm : ‖αρ‖ = 1 := by
    simp [αρ, Complex.norm_exp_I_mul_ofReal θρ]
  have hατ_norm : ‖ατ‖ = 1 := by
    simp [ατ, Complex.norm_exp_I_mul_ofReal θτ]
  have hψρ : ψρ = αρ • sameAncillaPurificationKet ρ := by
    ext i
    simpa [ψρ, αρ] using hθρ i
  have hψτ : ψτ = ατ • sameAncillaPurificationKet τ := by
    ext i
    simpa [ψτ, ατ] using hθτ i
  have hoverlap :
      ψτ.dag * Op.tensor V (1 : Op d) * ψρ =
        (star ατ * αρ) *
          ((sameAncillaPurificationKet τ).dag * Op.tensor V (1 : Op d) *
            sameAncillaPurificationKet ρ) :=
    ket_scalar_overlap ψρ (sameAncillaPurificationKet ρ)
      ψτ (sameAncillaPurificationKet τ)
      (Op.tensor V (1 : Op d)) αρ ατ hψρ hψτ
  rw [hoverlap, norm_mul]
  have hscalar_norm : ‖(star ατ * αρ : ℂ)‖ = 1 := by
    rw [norm_mul, norm_star, hατ_norm, hαρ_norm, one_mul]
  rw [hscalar_norm, one_mul]

/-- Equality of reshaped coefficient matrices determines kets on a tensor product. -/
lemma ket_eq_of_reshapeVec_eq {d : ℕ} {ψ φ : Ket (d * d)}
    (h : reshapeVec ψ.vec = reshapeVec φ.vec) :
    ψ = φ := by
  apply Ket.ext
  intro p
  have hp := congrFun (congrArg unreshapeVec h) p
  have hpidx : finProdFinEquiv (p.divNat, p.modNat) = p := by
    simpa [finProdFinEquiv_symm_apply] using finProdFinEquiv.apply_symm_apply p
  simpa [hpidx] using hp

/-- A ket whose outer product has a prescribed `B`-partial trace has the
corresponding reshaped Gram matrix. -/
lemma reshapeVec_mul_conjTranspose_eq_of_partialTraceB_ketbra
    {d : ℕ} (ψ : Ket (d * d)) (P : Op d)
    (hψ_purif : partialTraceB (ψ * ψ.dag) = P) :
    reshapeVec ψ.vec * (reshapeVec ψ.vec)† = P := by
  rw [← Quantum.Channels.partialTraceB_vecMulVec_eq_mul_conjTranspose ψ.vec,
    ← Quantum.Operators.ket_mul_dag_eq_vecMulVec ψ]
  exact hψ_purif

/-- Right multiplication of the reshaped canonical purification by `Uᵀ`
corresponds to applying `1 ⊗ U` to the ket. -/
lemma ket_eq_one_tensor_unitary_mul_sameAncillaPurificationKet_of_reshapeVec_eq
    {d : ℕ} (ρ : DensityOp d) (ψ : Ket (d * d)) (U : UnitaryOp d)
    (hψ : reshapeVec ψ.vec = CFC.sqrt ρ.toOp * U.toOp.transpose) :
    ψ = (Op.tensor (1 : Op d) U.toOp) * sameAncillaPurificationKet ρ := by
  refine ket_eq_of_reshapeVec_eq (hψ.trans ?_)
  have hright :=
    Quantum.Channels.reshapeVec_one_tensor_mul_ket U.toOp (sameAncillaPurificationKet ρ)
  simpa [sameAncillaPurificationKet_reshapeVec] using hright.symm

/-- The CFC square root of a positive semidefinite matrix has Gram matrix equal
to the original matrix. -/
lemma cfc_sqrt_mul_conjTranspose_self_of_posSemidef {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) :
    CFC.sqrt P * (CFC.sqrt P)† = P := by
  rw [Math.SpectralTheory.cfc_sqrt_conjTranspose_eq P]
  exact CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)

/-- A same-ancilla ket purification has reshaped coefficient matrix `√ρ`
times a right unitary. -/
lemma exists_unitary_reshapeVec_eq_cfcSqrt_mul_of_partialTraceB_ketbra
    {d : ℕ} (ρ : DensityOp d) (ψ : Ket (d * d))
    (hψ_purif : partialTraceB (ψ * ψ.dag) = ρ.toOp) :
    ∃ W : UnitaryOp d, reshapeVec ψ.vec = CFC.sqrt ρ.toOp * W.toOp := by
  have hρ_psd : ρ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have hS_purif : CFC.sqrt ρ.toOp * (CFC.sqrt ρ.toOp)† = ρ.toOp :=
    cfc_sqrt_mul_conjTranspose_self_of_posSemidef ρ.toOp hρ_psd
  have hM_purif : reshapeVec ψ.vec * (reshapeVec ψ.vec)† = ρ.toOp :=
    reshapeVec_mul_conjTranspose_eq_of_partialTraceB_ketbra ψ ρ.toOp hψ_purif
  have hgram :
      CFC.sqrt ρ.toOp * (CFC.sqrt ρ.toOp)† =
        reshapeVec ψ.vec * (reshapeVec ψ.vec)† :=
    hS_purif.trans hM_purif.symm
  exact Matrix.exists_unitary_right_mul_of_mul_conjTranspose_eq
    (A := CFC.sqrt ρ.toOp) (B := reshapeVec ψ.vec) hgram

/-- **Vec representation of a bipartite ket.**

Every ket on `d * d` is `(M ⊗ 1) |Ω⟩` for some matrix `M : Op d` (whose entries
are the components of `ψ` read off through `finProdFinEquiv`). -/
lemma Ket.exists_vec_repr {d : ℕ} (ψ : Ket (d * d)) :
    ∃ M : Op d,
      ψ = (Op.tensor M (1 : Op d)) *
        InfoTheory.DeFinetti.maxEntangledKet d := by
  refine ⟨Matrix.of fun i j => ψ.vec (finProdFinEquiv (i, j)), ?_⟩
  apply Quantum.Operators.Ket.ext
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ p : Fin d × Fin d, finProdFinEquiv p = k :=
    ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
  rw [InfoTheory.DeFinetti.maxEntangledKet_tensor_one_apply]
  rfl

/-- Partial trace of `(M ⊗ 1)|Ω⟩⟨Ω|(M† ⊗ 1)` equals `M M†`. -/
lemma partialTraceB_vec_outer_eq_mul_conjTranspose
    {d : ℕ} (M : Op d) :
    partialTraceB (Op.tensor M (1 : Op d) *
        InfoTheory.DeFinetti.maxEntangledOp d *
        Op.tensor M.conjTranspose (1 : Op d)) =
      M * M.conjTranspose := by
  rw [Quantum.TensorProducts.partialTraceB_sandwich_tensor_one M M.conjTranspose
        (InfoTheory.DeFinetti.maxEntangledOp d),
      InfoTheory.DeFinetti.maxEntangledOp_partialTraceB,
      Matrix.mul_one]

/-- **Maximally-entangled ricochet identity.**

For every matrix `A : Op d`, acting on the maximally entangled ket by `A ⊗ 1`
on the left equals acting by `1 ⊗ Aᵀ` (un-conjugated transpose). -/
lemma tensor_one_maxEntangledKet_ricochet
    {d : ℕ} (A : Op d) :
    (Op.tensor A (1 : Op d)) * InfoTheory.DeFinetti.maxEntangledKet d =
      (Op.tensor (1 : Op d) A.transpose) *
        InfoTheory.DeFinetti.maxEntangledKet d := by
  apply Quantum.Operators.Ket.ext
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ p : Fin d × Fin d, finProdFinEquiv p = k :=
    ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
  rw [InfoTheory.DeFinetti.maxEntangledKet_tensor_one_apply,
      InfoTheory.DeFinetti.maxEntangledKet_one_tensor_apply,
      Matrix.transpose_apply]

/-- **Purification uniqueness via ancilla unitary** (Watrous Thm 2.12 / Nielsen–Chuang Thm 2.5).

Any normalized purification of a density operator `ρ` on a same-dimensional
ancilla is related to the canonical same-ancilla purification by an ancilla-side
unitary.

Formally: if `ψ : Ket (d * d)` is normalized (`ψ.dag * ψ = 1`) and satisfies
`partialTraceB (ψ * ψ.dag) = ρ.toOp`, then there exists `U : UnitaryOp d` such
that `ψ = Op.tensor (1 : Op d) U.toOp * sameAncillaPurificationKet ρ`. -/
theorem sameAncillaPurificationKet_ancilla_unitary_of_purifies
    {d : ℕ} [NeZero d] (ρ : DensityOp d)
    (ψ : Ket (d * d))
    (_hψ_norm : ψ.dag * ψ = 1)
    (hψ_purif : partialTraceB (ψ * ψ.dag) = ρ.toOp) :
    ∃ U : UnitaryOp d,
      ψ = (Op.tensor (1 : Op d) U.toOp) * sameAncillaPurificationKet ρ := by
  obtain ⟨M, hM⟩ := Quantum.Metrics.KitaevWatrousPurification.Ket.exists_vec_repr ψ
  have hMM : M * M.conjTranspose = ρ.toOp := by
    have hψ_outer :
        ψ * ψ.dag =
          Op.tensor M (1 : Op d) *
            InfoTheory.DeFinetti.maxEntangledOp d *
            Op.tensor M.conjTranspose (1 : Op d) := by
      rw [hM, dag_op_mul_ket, Op.tensor_conjTranspose, conjTranspose_one,
          InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra, op_mul_ketbra, ketbra_mul_op]
    have hptrace :=
      Quantum.Metrics.KitaevWatrousPurification.partialTraceB_vec_outer_eq_mul_conjTranspose M
    rw [← hptrace, ← hψ_outer]
    exact hψ_purif
  obtain ⟨W₀, hW₀⟩ := Quantum.Metrics.PolarUnitary.Op.exists_unitary_polar_left M
  rw [hMM] at hW₀
  refine ⟨UnitaryOp.transpose W₀, ?_⟩
  have hMrew : Op.tensor M (1 : Op d) =
      Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
        Op.tensor W₀.toOp (1 : Op d) := by
    rw [hW₀, Op.tensor_mul, Matrix.mul_one]
  have hricochet := Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet
      W₀.toOp
  calc
    ψ
        = (Op.tensor M (1 : Op d)) *
            InfoTheory.DeFinetti.maxEntangledKet d := hM
    _ = (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            Op.tensor W₀.toOp (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d := by rw [hMrew]
    _ = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            ((Op.tensor W₀.toOp (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [← op_op_mul_ket_assoc]
    _ = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            ((Op.tensor (1 : Op d) W₀.toOp.transpose) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [hricochet]
    _ = (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            Op.tensor (1 : Op d) W₀.toOp.transpose) *
              InfoTheory.DeFinetti.maxEntangledKet d := by
          rw [op_op_mul_ket_assoc]
    _ = (Op.tensor (1 : Op d) W₀.toOp.transpose *
            Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d := by
          rw [Op.tensor_one_mul_one_tensor_comm]
    _ = Op.tensor (1 : Op d) W₀.toOp.transpose *
            (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [← op_op_mul_ket_assoc]
    _ = Op.tensor (1 : Op d) (UnitaryOp.transpose W₀).toOp *
            sameAncillaPurificationKet ρ := by
          rfl

end Quantum.Metrics.KitaevWatrousPurification
