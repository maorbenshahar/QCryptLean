import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order

/-!
# Rectangular Left-Isometry Conjugation Helpers

Generic helpers for blockwise rectangular left-isometry conjugation of CQ
states and sub-density operators. These lemmas form the algebraic backbone of
several invariance results for the conditional min-entropy (e.g. Eve-unitary
invariance, dimension-penalty embeddings).

The lemmas are stated generically for rectangular `K : Matrix (Fin dTgt)
(Fin dSrc) ℂ` and specialize trivially to the square unitary case via
`K := V.toOp` together with `V.unitary_left : V.toOpᴴ * V.toOp = 1`.

## Main statements

- `Quantum.Channels.quadraticForm_kraus_sandwich`: `⟨v, (K · A · Kᴴ) v⟩ = ⟨Kᴴ v, A · (Kᴴ v)⟩`.
- `Quantum.Channels.opLe_kraus_sandwich`: PSD order is monotone under rectangular conjugation.
- `opLe_of_conj_opLe`: PSD order reflects through conjugation by a left
  isometry (`Kᴴ * K = 1`).
- `isFeasible_left_isometry_embed_iff`: feasibility for `(ρ, σ)` is preserved
  bijectively under blockwise rectangular conjugation by a left isometry.
- `minFeasibleLambda_left_isometry_embed_eq`: the resulting equality of
  `minFeasibleLambda`s.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- PSD order reflects through conjugation by a left isometry.

If `Kᴴ * K = 1` and `opLe (K · A · Kᴴ) (K · B · Kᴴ)`, then `opLe A B`. -/
lemma opLe_of_conj_opLe
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    {A B : Op dSrc}
    (hAB : opLe (K * A * Kᴴ) (K * B * Kᴴ)) :
    opLe A B := by
  intro v
  have h := hAB (K.mulVec v)
  rw [Quantum.Channels.quadraticForm_kraus_sandwich K A (K.mulVec v),
    Quantum.Channels.quadraticForm_kraus_sandwich K B (K.mulVec v)] at h
  have hKv : Kᴴ.mulVec (K.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hK_iso]
    simp
  simpa [hKv] using h

/-- Conjugating a scalar Löwner bound by a rectangular `K`.

If `A ⪯ s · 1` (in the `opLe` order), then `K · A · Kᴴ ⪯ s · (K · Kᴴ)`.  The
nonnegativity slot `_hs : 0 ≤ s` is kept to match the Petz-recovery call contract
(where `s = polyDim · ctx.t ≥ 0`); the bound itself holds for any real `s`.

Proof: `Quantum.Channels.opLe_kraus_sandwich K` gives `K · A · Kᴴ ⪯ K · (s·1) · Kᴴ`, and
`K · (s·1) · Kᴴ = s · (K · Kᴴ)` by pulling the scalar out and `K · 1 = K`.  This
packages the "conjugate a scalar bound" step used in the Petz-recovery chain. -/
lemma opLe_conj_smul_one
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    {A : Op dSrc} {s : ℝ} (_hs : 0 ≤ s)
    (hA : opLe A ((Complex.ofReal s) • (1 : Op dSrc))) :
    opLe (K * A * Kᴴ) ((Complex.ofReal s) • (K * Kᴴ)) := by
  have h := Quantum.Channels.opLe_kraus_sandwich K hA
  have heq : K * ((Complex.ofReal s) • (1 : Op dSrc)) * Kᴴ
      = (Complex.ofReal s) • (K * Kᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [heq] at h
  exact h

/-- Feasibility is preserved bijectively under blockwise rectangular conjugation
by a left isometry. -/
lemma isFeasible_left_isometry_embed_iff
    (α : Type*) [Fintype α]
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc)
    (σ : SubDensityOp dSrc)
    (ρ_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * Kᴴ)
    (σ_embed : SubDensityOp dTgt)
    (hσ_embed : σ_embed.toOp = K * σ.toOp * Kᴴ)
    (t : ℝ) :
    isFeasible ρ_embed σ_embed t ↔ isFeasible ρ σ t := by
  constructor
  · intro ht
    refine ⟨ht.1, fun x => ?_⟩
    have hx : opLe
        (K * (ρ.stateMap x).toOp * Kᴴ)
        (K * ((Complex.ofReal t) • σ.toOp) * Kᴴ) := by
      have hdom := ht.2 x
      rw [hρ_embed x, hσ_embed] at hdom
      simpa [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc] using hdom
    exact opLe_of_conj_opLe K hK_iso hx
  · intro ht
    refine ⟨ht.1, fun x => ?_⟩
    have hx := Quantum.Channels.opLe_kraus_sandwich K (ht.2 x)
    rw [hρ_embed x, hσ_embed]
    simpa [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc] using hx

/-- `minFeasibleLambda` is invariant under blockwise rectangular conjugation
by a left isometry. -/
lemma minFeasibleLambda_left_isometry_embed_eq
    (α : Type*) [Fintype α]
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc)
    (σ : SubDensityOp dSrc)
    (ρ_embed : CQState α dTgt)
    (hρ_embed : ∀ x : α,
      (ρ_embed.stateMap x).toOp =
        K * (ρ.stateMap x).toOp * Kᴴ)
    (σ_embed : SubDensityOp dTgt)
    (hσ_embed : σ_embed.toOp = K * σ.toOp * Kᴴ) :
    minFeasibleLambda ρ_embed σ_embed =
      minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_left_isometry_embed_iff
    α K hK_iso ρ σ ρ_embed hρ_embed σ_embed hσ_embed t

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
