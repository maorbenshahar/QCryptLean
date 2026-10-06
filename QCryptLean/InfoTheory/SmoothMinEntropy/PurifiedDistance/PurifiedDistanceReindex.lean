import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Purified Distance Reindex Invariance — fidelity, sub-density reindex, permutation conjugation

A `Matrix.reindex e e` of a matrix by a single equivalence on rows and
columns is a unitary conjugation by the corresponding permutation matrix.
Such a conjugation preserves trace, the PSD order, the CFC functional
calculus (in particular `CFC.sqrt`), and the Uhlmann fidelity. Hence
`fidelityGen` and the purified distance are invariant under simultaneous
reindex of both arguments.

This module packages the layered invariance lemmas:

- `Matrix.reindex_sqrt` — CFC `sqrt` commutes with reindex.
- `Quantum.Metrics.fidelity_reindex` — Uhlmann fidelity is reindex-invariant
  (relies on the previous + trace invariance).
- `InfoTheory.SmoothMinEntropy.fidelityGen_reindex` — generalized fidelity is
  reindex-invariant, derived from `fidelity_reindex` + trace invariance.
- `InfoTheory.SmoothMinEntropy.purifiedDistance_reindex` — purified distance
  is reindex-invariant, derived directly from `fidelityGen_reindex`.

The strict matrix-level CFC commutation `Matrix.reindex_sqrt` — the genuinely
deep CFC content — is proved directly (via `cfc_sqrt_isometry_conj` on the PSD
branch, and the non-unital-CFC zero collapse off it). The two upper layers
(`fidelityGen_reindex`, `purifiedDistance_reindex`) are proved in terms of it.

The wrapper `SubDensityOp.reindex` lifts a permutation `e : Fin n ≃ Fin n`
to an action on `SubDensityOp n`; this is the natural object to feed the
`purifiedDistance` reindex invariance lemma.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- `Matrix.reindex` lifted to `SubDensityOp` along a permutation of `Fin n`.
    Reindex by a single equiv on rows and columns is unitary conjugation by
    the permutation, hence preserves the PSD order and the trace. -/
noncomputable def SubDensityOp.reindex {n : ℕ} (e : Fin n ≃ Fin n) (ρ : SubDensityOp n) :
    SubDensityOp n where
  toOp := Matrix.reindex e e ρ.toOp
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).reindex e).isHermitian
  pos_semidef :=
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).reindex e)
  trace_le_one := by
    rw [Matrix.trace_reindex_self]
    exact ρ.trace_le_one

/-- The trace of a `SubDensityOp` is invariant under simultaneous reindex. -/
lemma SubDensityOp.reindex_trace {n : ℕ} (e : Fin n ≃ Fin n) (ρ : SubDensityOp n) :
    (SubDensityOp.reindex e ρ).trace = ρ.trace := by
  change ((Matrix.reindex e e ρ.toOp).trace).re = (ρ.toOp.trace).re
  rw [Matrix.trace_reindex_self]

/-- `Matrix.reindex e e M = P * M * Pᴴ` where `P := e.symm.permMatrix ℂ`.

    The reindex by a single equivalence on rows and columns equals two-sided
    conjugation by the permutation matrix of `e.symm`. Combined with
    `conjTranspose_permMatrix` (giving `Pᴴ = e.permMatrix ℂ`), this exhibits
    `Matrix.reindex e e` as unitary conjugation. -/
lemma Matrix.reindex_eq_permMatrix_conj {n : ℕ} (e : Fin n ≃ Fin n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex e e M =
      (Equiv.Perm.permMatrix ℂ e.symm) * M *
        (Equiv.Perm.permMatrix ℂ e.symm).conjTranspose := by
  rw [Matrix.conjTranspose_permMatrix,
    show (e.symm)⁻¹ = e from inv_inv (G := Equiv.Perm (Fin n)) e ▸ rfl,
    show Equiv.Perm.permMatrix ℂ e.symm = e.symm.toPEquiv.toMatrix from rfl,
    show Equiv.Perm.permMatrix ℂ e = e.toPEquiv.toMatrix from rfl,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The permutation matrix of `e.symm` is an isometry: `Pᴴ * P = 1`. -/
lemma Matrix.permMatrix_isometry {n : ℕ} (e : Fin n ≃ Fin n) :
    (Equiv.Perm.permMatrix ℂ e.symm).conjTranspose *
        Equiv.Perm.permMatrix ℂ e.symm = 1 := by
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel (e.symm), Matrix.permMatrix_one]

/-- `CFC.sqrt` commutes with `Matrix.reindex e e`. The reindex map is a
    `*`-isomorphism on the matrix algebra (`Matrix.reindexAlgEquiv`), and
    concretely equals two-sided conjugation by `e.symm.permMatrix`, so the
    statement reduces to `cfc_sqrt_isometry_conj`. -/
lemma Matrix.reindex_sqrt {n : ℕ} (e : Fin n ≃ Fin n) (A : Matrix (Fin n) (Fin n) ℂ) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    CFC.sqrt (Matrix.reindex e e A) = Matrix.reindex e e (CFC.sqrt A) := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  set P := Equiv.Perm.permMatrix ℂ e.symm with hP_def
  have hP_iso : P.conjTranspose * P = 1 := Matrix.permMatrix_isometry e
  have hreindex_M : Matrix.reindex e e A = P * A * P.conjTranspose :=
    Matrix.reindex_eq_permMatrix_conj e A
  by_cases hA : A.PosSemidef
  · have hreindex_sqrt :
        Matrix.reindex e e (CFC.sqrt A) = P * CFC.sqrt A * P.conjTranspose :=
      Matrix.reindex_eq_permMatrix_conj e (CFC.sqrt A)
    rw [hreindex_M, hreindex_sqrt]
    exact Quantum.Metrics.TraceNormHoelder.cfc_sqrt_isometry_conj P A hP_iso hA
  · -- `A` is not PSD ⇒ `CFC.sqrt A = 0` (non-unital CFC default outside the predicate).
    -- Reindex preserves PSD, so `Matrix.reindex e e A` is also not PSD, and both
    -- sides of the equality collapse to `0`.
    have hA_not_nn : ¬ (0 ≤ A) := fun h => hA (Matrix.nonneg_iff_posSemidef.mp h)
    have hreindex_not_nn : ¬ (0 ≤ Matrix.reindex e e A) := by
      intro h
      apply hA_not_nn
      have hpsd : (Matrix.reindex e e A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp h
      have hback : Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
        ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [← hback, Matrix.nonneg_iff_posSemidef]
      exact hpsd.reindex e.symm
    rw [show (CFC.sqrt A : Op n) = cfcₙ NNReal.sqrt A from rfl,
        show (CFC.sqrt (Matrix.reindex e e A) : Op n) = cfcₙ NNReal.sqrt (Matrix.reindex e e A)
          from rfl,
        cfcₙ_apply_of_not_predicate _ hA_not_nn,
        cfcₙ_apply_of_not_predicate _ hreindex_not_nn]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Uhlmann fidelity is invariant under simultaneous `Matrix.reindex` of
    both PSD operators. The reindex by a single equiv is unitary
    conjugation by the corresponding permutation matrix
    (`Matrix.reindex_eq_permMatrix_conj`); trace and CFC are both invariant
    under unitary conjugation (`fidelity_isometry_conj_of_toOp_eq`). -/
lemma _root_.Quantum.Metrics.fidelity_reindex {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) (e : Fin n ≃ Fin n)
    (hA : (Matrix.reindex e e A.toOp).PosSemidef)
    (hB : (Matrix.reindex e e B.toOp).PosSemidef) :
    Quantum.Metrics.fidelity
        ⟨⟨Matrix.reindex e e A.toOp, hA.isHermitian⟩,
          posSemidef_re_quadraticForm_nonneg hA⟩
        ⟨⟨Matrix.reindex e e B.toOp, hB.isHermitian⟩,
          posSemidef_re_quadraticForm_nonneg hB⟩
      = Quantum.Metrics.fidelity A B := by
  set P := Equiv.Perm.permMatrix ℂ e.symm with hP_def
  have hP_iso : P.conjTranspose * P = 1 := Matrix.permMatrix_isometry e
  have hA_eq :
      (⟨⟨Matrix.reindex e e A.toOp, hA.isHermitian⟩,
        posSemidef_re_quadraticForm_nonneg hA⟩ : PosSemidefOp n).toOp =
      P * A.toOp * P.conjTranspose := Matrix.reindex_eq_permMatrix_conj e A.toOp
  have hB_eq :
      (⟨⟨Matrix.reindex e e B.toOp, hB.isHermitian⟩,
        posSemidef_re_quadraticForm_nonneg hB⟩ : PosSemidefOp n).toOp =
      P * B.toOp * P.conjTranspose := Matrix.reindex_eq_permMatrix_conj e B.toOp
  exact Quantum.Metrics.fidelity_isometry_conj_of_toOp_eq P A B _ _ hP_iso hA_eq hB_eq

/-- Generalized fidelity (Tomamichel 2016, §3.3.1) is invariant under
    simultaneous `SubDensityOp.reindex` of both arguments. -/
lemma fidelityGen_reindex {n : ℕ} [NeZero n] (e : Fin n ≃ Fin n)
    (ρ σ : SubDensityOp n) :
    fidelityGen (SubDensityOp.reindex e ρ) (SubDensityOp.reindex e σ) =
      fidelityGen ρ σ := by
  unfold fidelityGen
  have hρ_psd : (Matrix.reindex e e ρ.toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).reindex e
  have hσ_psd : (Matrix.reindex e e σ.toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib σ.toPosSemidefOp).reindex e
  have hF :=
    Quantum.Metrics.fidelity_reindex ρ.toPosSemidefOp σ.toPosSemidefOp e hρ_psd hσ_psd
  -- The PSD operators built inside `fidelity_reindex`'s LHS are definitionally
  -- equal to `(SubDensityOp.reindex e _).toPosSemidefOp`.
  have eA :
      (⟨⟨Matrix.reindex e e ρ.toOp, hρ_psd.isHermitian⟩,
          posSemidef_re_quadraticForm_nonneg hρ_psd⟩ : PosSemidefOp n) =
        (SubDensityOp.reindex e ρ).toPosSemidefOp :=
    PosSemidefOp.ext rfl
  have eB :
      (⟨⟨Matrix.reindex e e σ.toOp, hσ_psd.isHermitian⟩,
          posSemidef_re_quadraticForm_nonneg hσ_psd⟩ : PosSemidefOp n) =
        (SubDensityOp.reindex e σ).toPosSemidefOp :=
    PosSemidefOp.ext rfl
  rw [eA, eB] at hF
  rw [hF, SubDensityOp.reindex_trace, SubDensityOp.reindex_trace]

/-- **Purified distance reindex invariance.** For any permutation
    `e : Fin n ≃ Fin n`, simultaneous reindexing by `e` of both
    sub-normalized operators leaves their purified distance unchanged.

    This is the operator-level statement of unitary invariance of the
    purified distance, specialized to the unitaries that arise from
    permutations of the index set (i.e. `Matrix.reindex e e`).

    The proof reduces to `fidelityGen_reindex`, which packages the
    fidelity- and trace-level invariance. -/
theorem purifiedDistance_reindex {n : ℕ} [NeZero n] (e : Fin n ≃ Fin n)
    (ρ σ : SubDensityOp n) :
    purifiedDistance (SubDensityOp.reindex e ρ) (SubDensityOp.reindex e σ) =
      purifiedDistance ρ σ := by
  unfold purifiedDistance
  rw [fidelityGen_reindex]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
