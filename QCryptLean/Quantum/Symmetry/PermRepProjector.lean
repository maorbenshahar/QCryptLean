import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Math.SpectralTheory.KyFan.Basic

/-!
# Finite permutation unitary representations and the group-average projector

The bundled finite-symmetric-group unitary representation `FinitePermUnitaryRep D n`
and its group-average projector `P_R = (1/n!)·Σ_π R(π)`: idempotence, hermiticity,
positive-semidefiniteness, and the real trace `symComponentDim = Tr P_R = rank P_R`
(the symmetric-component dimension).

This self-contained rep-theory core is stated over an arbitrary `Op D` and needs only
`PSDOrder` + `KyFan` + Mathlib.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A finite-symmetric-group unitary representation on `ℂ^D`:
`rep : Sₙ → U(ℂ^D)` together with the group-homomorphism and unitarity laws.

This packages a permutation-covariance witness `R : Equiv.Perm (Fin n) → Op eveDim` with
`R π * (R π)† = 1`, `(R π)† * R π = 1`, and the multiplicativity `R π · R τ = R (π·τ)` implied
by a covariance intertwining law together with the standard signal representation being a
homomorphism.  Bundling it here lets the symmetric-subspace machinery be stated once and
instantiated for BB84. -/
structure FinitePermUnitaryRep (D n : ℕ) where
  /-- The representing operator for each permutation. -/
  rep : Equiv.Perm (Fin n) → Op D
  /-- The identity permutation maps to the identity operator. -/
  rep_one : rep 1 = 1
  /-- The representation is multiplicative: `R(π) · R(τ) = R(π·τ)`. -/
  rep_mul : ∀ π τ : Equiv.Perm (Fin n), rep π * rep τ = rep (π * τ)
  /-- Each `R(π)` is unitary: `R(π)† · R(π) = 1`. -/
  rep_unitary_left : ∀ π : Equiv.Perm (Fin n), (rep π)ᴴ * rep π = 1
  /-- Each `R(π)` is unitary: `R(π) · R(π)† = 1`. -/
  rep_unitary_right : ∀ π : Equiv.Perm (Fin n), rep π * (rep π)ᴴ = 1
  /-- The inverse permutation represents the adjoint: `R(π⁻¹) = R(π)†`. -/
  rep_inv : ∀ π : Equiv.Perm (Fin n), rep π⁻¹ = (rep π)ᴴ

namespace FinitePermUnitaryRep

variable {D n : ℕ}

/-- The unnormalized group sum `Σ_π R(π)`. -/
def groupSum (R : FinitePermUnitaryRep D n) : Op D :=
  ∑ π : Equiv.Perm (Fin n), R.rep π

/-- **(a) The group-average projector** `P_R = (1/n!)·Σ_π R(π)`.

For a unitary homomorphic representation this is the orthogonal projector onto
the `R`-invariant (symmetric) subspace of `ℂ^D`.  It is the abstract analogue of
`Quantum.Symmetry.symmetricProjector`, which is this object for the standard
permutation representation `permutationRepresentation`. -/
def groupAverageProjector (R : FinitePermUnitaryRep D n) : Op D :=
  (1 / (Nat.factorial n : ℂ)) • R.groupSum

/-- Left-invariance of the group sum: `R(π) · (Σ_τ R(τ)) = Σ_τ R(τ)`. -/
lemma rep_mul_groupSum (R : FinitePermUnitaryRep D n) (π : Equiv.Perm (Fin n)) :
    R.rep π * R.groupSum = R.groupSum := by
  unfold groupSum
  rw [Finset.mul_sum]
  simp_rw [R.rep_mul]
  exact Fintype.sum_bijective (π * ·) (Group.mulLeft_bijective π) _ _ (fun _ => rfl)

/-- Squaring the unnormalized group sum multiplies it by `n!`. -/
lemma groupSum_mul_self (R : FinitePermUnitaryRep D n) :
    R.groupSum * R.groupSum =
      (Fintype.card (Equiv.Perm (Fin n))) • R.groupSum := by
  rw [show R.groupSum * R.groupSum
        = (∑ π : Equiv.Perm (Fin n), R.rep π) * R.groupSum from by rw [groupSum],
      Finset.sum_mul]
  simp_rw [R.rep_mul_groupSum]
  rw [Finset.sum_const, Finset.card_univ]

/-- The unnormalized group sum is self-adjoint. -/
lemma groupSum_conjTranspose (R : FinitePermUnitaryRep D n) :
    (R.groupSum)ᴴ = R.groupSum := by
  unfold groupSum
  rw [conjTranspose_sum]
  simp_rw [← R.rep_inv]
  exact Fintype.sum_bijective (·⁻¹) inv_involutive.bijective _ _ (fun _ => rfl)

/-- **The group-average projector is a projector**: `P² = P` and `P† = P`.

PROVED, unconditionally.  Idempotence uses left-invariance of the group sum;
hermiticity uses the inverse-adjoint law `R(π⁻¹) = R(π)†` and the relabeling
`π ↦ π⁻¹`. -/
theorem groupAverageProjector_is_projector (R : FinitePermUnitaryRep D n) :
    R.groupAverageProjector * R.groupAverageProjector = R.groupAverageProjector ∧
      (R.groupAverageProjector)ᴴ = R.groupAverageProjector := by
  constructor
  · unfold groupAverageProjector
    rw [smul_mul_smul_comm, R.groupSum_mul_self, Fintype.card_perm, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    have hn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  · unfold groupAverageProjector
    rw [conjTranspose_smul]
    congr 1
    · rw [star_div₀, star_one, star_natCast]
    · rw [R.groupSum_conjTranspose]

/-- The group-average projector is Hermitian. -/
lemma groupAverageProjector_isHermitian (R : FinitePermUnitaryRep D n) :
    (R.groupAverageProjector).IsHermitian :=
  (R.groupAverageProjector_is_projector).2

/-- The group-average projector is positive semidefinite (it is a Hermitian
idempotent). -/
lemma groupAverageProjector_posSemidef (R : FinitePermUnitaryRep D n) :
    (R.groupAverageProjector).PosSemidef := by
  obtain ⟨hidem, hherm⟩ := R.groupAverageProjector_is_projector
  rw [show R.groupAverageProjector
      = (R.groupAverageProjector)ᴴ * R.groupAverageProjector from by rw [hherm, hidem]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **The symmetric-component dimension** `dim_R := Tr P_R`, the real-valued trace
of the group-average projector.

For a projector this is the dimension of the invariant (symmetric) subspace of
`ℂ^D` that `R` fixes.  It is the dimension whose logarithm is the honest
conditional min-entropy penalty against the symmetric-component maximally mixed
reference `P_R / Tr P_R`.  By Schur/Renner `lem:SymPOVM` it is bounded by the
symmetric subspace dimension. -/
def symComponentDim (R : FinitePermUnitaryRep D n) : ℝ :=
  (R.groupAverageProjector).trace.re

/-- The trace of the group-average projector is self-adjoint (real). -/
lemma groupAverageProjector_trace_selfAdjoint (R : FinitePermUnitaryRep D n) :
    starRingEnd ℂ (R.groupAverageProjector).trace = (R.groupAverageProjector).trace := by
  have hP := R.groupAverageProjector_isHermitian
  change star (R.groupAverageProjector).trace = _
  rw [← Matrix.trace_conjTranspose]
  exact congrArg Matrix.trace hP

/-- The trace of the group-average projector is real-valued: its complex trace is
the cast of `symComponentDim`. -/
lemma groupAverageProjector_trace_ofReal (R : FinitePermUnitaryRep D n) :
    (R.groupAverageProjector).trace = (R.symComponentDim : ℂ) := by
  unfold symComponentDim
  exact (Complex.conj_eq_iff_re.mp R.groupAverageProjector_trace_selfAdjoint).symm

/-- **The symmetric-component dimension is the rank of the projector.**

For the Hermitian idempotent `P_R`, the real trace `symComponentDim = (P_R).trace.re`
equals `Matrix.rank P_R`, the dimension of the symmetric (invariant) subspace.
PROVED via `Math.SpectralTheory.hermitian_idempotent_trace_re_eq_rank`. -/
theorem symComponentDim_eq_rank (R : FinitePermUnitaryRep D n) [NeZero D] :
    R.symComponentDim = (Matrix.rank R.groupAverageProjector : ℝ) := by
  obtain ⟨hidem, hherm⟩ := R.groupAverageProjector_is_projector
  exact Math.SpectralTheory.hermitian_idempotent_trace_re_eq_rank
    R.groupAverageProjector hherm hidem

/-- The symmetric-component dimension is at least one, **given that it is positive**.

The hypothesis `0 < symComponentDim` is genuinely required: it is *false* without
it.  For instance the sign representation `R(π) = sign(π)·1` on `ℂ^D` (with `D ≥ 1`,
`n ≥ 2`) has `groupSum = (Σ_π sign π)·1 = 0`, hence `P_R = 0` and
`symComponentDim = Tr 0 = 0`.  The positivity of the symmetric component
(nonemptiness of the invariant subspace) is supplied by the caller — for the BB84
combined representation it holds because the trivial component contains the
purifier-side symmetric subspace `Sym^n(ℂ^{16})`.

Under `0 < symComponentDim`, the statement is mechanical: `symComponentDim` is the
real cast of `Matrix.rank P_R` (`symComponentDim_eq_rank`), so positivity of a
natural-number cast forces the natural number to be `≥ 1`. -/
theorem one_le_symComponentDim (R : FinitePermUnitaryRep D n) [NeZero D]
    (hPos : 0 < R.symComponentDim) :
    1 ≤ R.symComponentDim := by
  rw [R.symComponentDim_eq_rank] at hPos ⊢
  have hrank_pos : 0 < Matrix.rank R.groupAverageProjector := by
    exact_mod_cast hPos
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hrank_pos.ne'

end FinitePermUnitaryRep

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
