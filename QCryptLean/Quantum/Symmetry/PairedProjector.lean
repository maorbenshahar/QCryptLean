import QCryptLean.Quantum.TensorProducts.RoundRegrouping
import QCryptLean.Quantum.Operators.PSDTraceBound
import QCryptLean.Math.SpectralTheory.KyFan.Basic

/-!
# Symmetric projector on paired registers

The simultaneous permutation average on two blocks is the symmetric projector after regrouping.
Its trace and rank are `Nat.choose (n + dA * dR - 1) (dA * dR - 1)`. It dominates every
positive semidefinite operator of trace at most one supported in its range.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- The symmetric projector on paired registers in block order:
`P = (1 / n!) • ∑ σ, permutationRepresentation dA n σ ⊗ permutationRepresentation dR n σ`. -/
def symmetricProjectorPairedGen (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] :
    Op (dA ^ n * dR ^ n) :=
  (1 / (Nat.factorial n : ℂ)) •
    ∑ σ : Equiv.Perm (Fin n),
      Op.tensor (permutationRepresentation dA n σ)
                (permutationRepresentation dR n σ)

/-- The paired symmetric projector is idempotent and Hermitian. -/
lemma symmetricProjectorPairedGen_is_projector (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    let P := symmetricProjectorPairedGen dA dR n
    P * P = P ∧ Pᴴ = P := by
  dsimp only
  let e := Matrix.reindexAlgEquiv ℂ ℂ (Equiv.roundGroupEquiv dA dR n)
  have heq : e (symmetricProjectorRep (dA * dR) n) =
      symmetricProjectorPairedGen dA dR n := by
    simp only [e, Matrix.reindexAlgEquiv_apply, symmetricProjectorRep,
      symmetricProjectorPairedGen, Matrix.reindex_smul, Matrix.reindex_sum,
      reindex_roundGroupEquiv_permRep]
  obtain ⟨hidp, hherm⟩ := symmetricProjectorRep_is_projector (dA * dR) n
  rw [← heq]
  constructor
  · rw [← map_mul, hidp]
  · simp only [e, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex, hherm]

/-- The paired symmetric projector is Hermitian. -/
lemma symmetricProjectorPairedGen_isHermitian (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (symmetricProjectorPairedGen dA dR n).IsHermitian :=
  (symmetricProjectorPairedGen_is_projector dA dR n).2

/-- The paired symmetric projector is positive semidefinite. -/
lemma symmetricProjectorPairedGen_posSemidef (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (symmetricProjectorPairedGen dA dR n).PosSemidef := by
  have ⟨hidp, hherm⟩ := symmetricProjectorPairedGen_is_projector dA dR n
  rw [show symmetricProjectorPairedGen dA dR n =
    (symmetricProjectorPairedGen dA dR n)ᴴ * symmetricProjectorPairedGen dA dR n
    from by rw [hherm, hidp]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the paired symmetric projector is the dimension of the symmetric subspace:
`Nat.choose (n + dA * dR - 1) (dA * dR - 1)`. -/
lemma symmetricProjectorPairedGen_trace_eq (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (symmetricProjectorPairedGen dA dR n).trace =
      (Nat.choose (n + dA * dR - 1) (dA * dR - 1) : ℂ) := by
  let e := Matrix.reindexAlgEquiv ℂ ℂ (Equiv.roundGroupEquiv dA dR n)
  have heq : e (symmetricProjectorRep (dA * dR) n) =
      symmetricProjectorPairedGen dA dR n := by
    simp only [e, Matrix.reindexAlgEquiv_apply, symmetricProjectorRep,
      symmetricProjectorPairedGen, Matrix.reindex_smul, Matrix.reindex_sum,
      reindex_roundGroupEquiv_permRep]
  rw [← heq, Matrix.trace_map, symmetricProjectorRep_trace]

/-- The rank of the paired symmetric projector is the dimension of the symmetric subspace:
`Nat.choose (n + dA * dR - 1) (dA * dR - 1)`. -/
lemma symmetricProjectorPairedGen_rank_eq_polyDim (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    Matrix.rank (symmetricProjectorPairedGen dA dR n) =
      Nat.choose (n + dA * dR - 1) (dA * dR - 1) := by
  have ⟨hP_idem, hP_herm⟩ := symmetricProjectorPairedGen_is_projector dA dR n
  have h_trace_re_eq_rank :=
    Math.SpectralTheory.hermitian_idempotent_trace_re_eq_rank
      (symmetricProjectorPairedGen dA dR n) hP_herm hP_idem
  have h_re : (symmetricProjectorPairedGen dA dR n).trace.re =
      (Nat.choose (n + dA * dR - 1) (dA * dR - 1) : ℝ) := by
    rw [symmetricProjectorPairedGen_trace_eq, Complex.natCast_re]
  exact_mod_cast h_trace_re_eq_rank.symm.trans h_re

/-- The paired symmetric projector dominates every positive semidefinite operator of trace
at most one supported in its range. -/
lemma symmetricProjectorPairedGen_sub_psd_of_support (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n]
    (ρ' : Op (dA ^ n * dR ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (hρ'_trace : ρ'.trace.re ≤ 1)
    (hρ'_support : symmetricProjectorPairedGen dA dR n * ρ' * symmetricProjectorPairedGen dA dR n
      = ρ') :
    (symmetricProjectorPairedGen dA dR n - ρ').PosSemidef := by
  have ⟨hP_idem, hP_herm⟩ := symmetricProjectorPairedGen_is_projector dA dR n
  have h := (psd_le_one_of_trace_le_one ρ' hρ'_psd hρ'_trace).mul_mul_conjTranspose_same
    (symmetricProjectorPairedGen dA dR n)
  simpa only [hP_herm, mul_sub, sub_mul, mul_one, hP_idem, hρ'_support] using h

end Quantum.Symmetry
