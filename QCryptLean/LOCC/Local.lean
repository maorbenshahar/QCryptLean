import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.Quantum.Channels.KrausRecord
import QCryptLean.Math.LinearAlgebra.IsometricEncoding

/-!
# Finite Kraus instruments

Matrix conjugations, finite branching of channels, and completeness-carrying local instruments.
The results depend only on finite-dimensional operators and do not impose a laboratory partition.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace LOCC

/-! ## 1. Matrix conjugation as a linear map -/

/-- Conjugation by an arbitrary (possibly rectangular) matrix, `ρ ↦ K ρ Kᴴ`, as a linear map
on operators — no Kraus condition on `K` is required. A single local branch of an instrument
is exactly this. -/
def matrixConjLinear {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) : Op p →ₗ[ℂ] Op q where
  toFun ρ := K * ρ * Kᴴ
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem matrixConjLinear_apply {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (ρ : Op p) :
    matrixConjLinear K ρ = K * ρ * Kᴴ := rfl

/-- Conjugation by the zero matrix is the zero map. -/
theorem matrixConjLinear_zero {p q : ℕ} :
    matrixConjLinear (0 : Matrix (Fin q) (Fin p) ℂ) = 0 := by
  refine LinearMap.ext fun ρ => ?_
  simp [matrixConjLinear]

/-- Conjugations compose by multiplying the matrices. -/
theorem matrixConjLinear_comp {p q r : ℕ} (A : Matrix (Fin r) (Fin q) ℂ)
    (B : Matrix (Fin q) (Fin p) ℂ) :
    (matrixConjLinear A).comp (matrixConjLinear B) = matrixConjLinear (A * B) := by
  refine LinearMap.ext fun ρ => ?_
  simp only [LinearMap.comp_apply, matrixConjLinear_apply, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A one-element family is a matrix conjugation. This is the bridge to the library's
`krausMapFintype` API, and hence to `krausMapFintype_isCPTP`. -/
theorem matrixConjLinear_eq_krausMapFintype {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) :
    matrixConjLinear K = krausMapFintype (fun _ : Unit => K) := by
  refine LinearMap.ext fun ρ => ?_
  simp [matrixConjLinear, krausMapFintype]

/-- **An isometric Kraus conjugation is CPTP.** `Kᴴ K = 1` is exactly the one-branch
completeness relation. -/
theorem matrixConjLinear_isCPTP {p q : ℕ} [NeZero p] [NeZero q] (K : Matrix (Fin q) (Fin p) ℂ)
    (hK : Kᴴ * K = 1) : IsCPTP ⇑(matrixConjLinear K) := by
  rw [matrixConjLinear_eq_krausMapFintype]
  refine krausMapFintype_isCPTP _ ?_
  simpa using hK

/-! ## 2. Branching: the assembly lemma -/

/-- The Choi matrix is additive in the map. -/
theorem choiMatrix_sum {n m : ℕ} [NeZero n] [NeZero m] {κ : Type*} [Fintype κ]
    (Φ : κ → (Op n →ₗ[ℂ] Op m)) :
    ChoiMatrix n m ⇑(∑ x, Φ x) = ∑ x, ChoiMatrix n m ⇑(Φ x) := by
  ext p q
  simp only [ChoiMatrix, Matrix.of_apply, Matrix.sum_apply, LinearMap.sum_apply]

/-- **The assembly lemma.** If `{Aₓ}` is a complete Kraus family on the input register and each
`Ψₓ` is a CPTP map out of the `x`-branch, then the branching map `ρ ↦ ∑ₓ Ψₓ(Aₓ ρ Aₓᴴ)` is CPTP.

Complete positivity is branchwise; **trace preservation is not** — each branch alone is
trace-decreasing, and only the completeness relation `∑ₓ Aₓᴴ Aₓ = 1` makes the sum preserve the
trace. This is the exact point at which `LocalInstrument.complete` earns its place as a field. -/
theorem isCPTP_sum_comp_krausConj {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {κ : Type*} [Fintype κ] (A : κ → Matrix (Fin q) (Fin p) ℂ) (Ψ : κ → (Op q →ₗ[ℂ] Op r))
    (hA : ∑ x, (A x)ᴴ * A x = 1) (hΨ : ∀ x, IsCPTP ⇑(Ψ x)) :
    IsCPTP ⇑(∑ x, (Ψ x).comp (matrixConjLinear (A x))) := by
  refine ⟨(∑ x, (Ψ x).comp (matrixConjLinear (A x))).isLinear, ?_, ?_⟩
  · -- Complete positivity: branchwise, then sum.
    change ((ChoiMatrix p r ⇑(∑ x, (Ψ x).comp (matrixConjLinear (A x))))).PosSemidef
    rw [choiMatrix_sum]
    refine Matrix.posSemidef_sum _ fun x _ => ?_
    have hcomp : ⇑((Ψ x).comp (matrixConjLinear (A x))) =
        ⇑(Ψ x) ∘ ⇑(matrixConjLinear (A x)) := rfl
    have hCP : IsCompletelyPositive ⇑(matrixConjLinear (A x)) := by
      rw [matrixConjLinear_eq_krausMapFintype]
      exact krausMapFintype_isCompletelyPositive _
    rw [hcomp]
    exact isCompletelyPositive_comp _ _ (hΨ x).2.1 hCP (hΨ x).1
  · -- Trace preservation: the completeness relation.
    intro M
    rw [LinearMap.sum_apply, Matrix.trace_sum]
    have hbranch : ∀ x : κ, (((Ψ x).comp (matrixConjLinear (A x))) M).trace =
        ((A x)ᴴ * A x * M).trace := by
      intro x
      have h1 : (((Ψ x).comp (matrixConjLinear (A x))) M).trace = (A x * M * (A x)ᴴ).trace :=
        (hΨ x).2.2 _
      rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp_rw [hbranch]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hA, Matrix.one_mul]

/-! ## 3. Local instruments -/

/-- A finite Kraus family whose completeness equation makes its branch sum trace preserving. -/
structure LocalInstrument (dIn dOut : ℕ) (Xo : Type) [Fintype Xo] where
  /-- The Kraus operator of the branch in which this party observes outcome `x`. -/
  kraus : Xo → Matrix (Fin dOut) (Fin dIn) ℂ
  /-- The Kraus completeness equation makes the sum of all branches trace preserving. -/
  complete : ∑ x, (kraus x)ᴴ * kraus x = 1

/-- An instrument on a nonzero-dimensional register has at least one outcome. -/
theorem LocalInstrument.nonempty {dIn dOut : ℕ} [NeZero dIn] {Xo : Type} [Fintype Xo]
    (I : LocalInstrument dIn dOut Xo) : Nonempty Xo := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have hzero : (0 : Op dIn) = 1 := by
    rw [← I.complete, Finset.univ_eq_empty, Finset.sum_empty]
  have hpos : 0 < dIn := Nat.pos_of_ne_zero (NeZero.ne dIn)
  have hentry := congrFun (congrFun hzero ⟨0, hpos⟩) ⟨0, hpos⟩
  rw [Matrix.one_apply_eq] at hentry
  exact zero_ne_one hentry

/-- The outcome count of an instrument on a nonzero-dimensional register is nonzero. -/
theorem LocalInstrument.card_ne_zero {dIn dOut : ℕ} [NeZero dIn] {Xo : Type} [Fintype Xo]
    (I : LocalInstrument dIn dOut Xo) : Fintype.card Xo ≠ 0 := by
  haveI := I.nonempty
  exact Fintype.card_ne_zero

/-- The instrument whose single Kraus operator keeps the outcome as a coherent record. -/
def LocalInstrument.recorded {dIn dOut : ℕ} {Xo : Type} [Fintype Xo]
    (I : LocalInstrument dIn dOut Xo) :
    LocalInstrument dIn (dOut * Fintype.card Xo) Unit where
  kraus _ := recordKraus I.kraus
  complete := by
    simpa using recordKraus_conjTranspose_mul_self I.kraus I.complete

/-- A complete Kraus family cannot compress beyond its outcome count. -/
theorem LocalInstrument.dim_le_mul_card {dIn dOut : ℕ} {Xo : Type} [Fintype Xo]
    (I : LocalInstrument dIn dOut Xo) : dIn ≤ dOut * Fintype.card Xo := by
  simpa using Matrix.isometry_dim_le (recordKraus I.kraus)
    (recordKraus_conjTranspose_mul_self I.kraus I.complete)

end LOCC
