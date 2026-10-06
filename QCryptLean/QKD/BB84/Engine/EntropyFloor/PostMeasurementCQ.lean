import QCryptLean.QKD.BB84.Model.Measurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PostselectionBound
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Mixed
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState

/-!
# BB84 outcome/Eve(-reference) register embeddings, and the CKR polynomial dimension

The register-embedding bookkeeping used to index Eve's (and a CKR reference register's) diagonal
block by a BB84 outcome string `ω : Fin n → Fin signalDim`, and the polynomial-subspace dimension
`bb84PolyDim` used throughout as the CKR de Finetti regularisation denominator.

## Main definitions

- `QKD.BB84.Model.bb84OutcomeEveEmbedding` (moved to `QKD.BB84.Model.Measurement`, imported here):
  embeds Eve's index into the joint outcome-Eve register at a fixed outcome.
- `bb84TauOutcomeEveRefEmbedding`: embeds an Eve-reference index into the attacked CKR state
  `(outcome, Eve, R)` register at a fixed outcome.
- `bb84TauOutputOp` / `bb84TauOutputDensity`: the pre-channel applied to the signal register of a
  CKR purification, leaving the reference register untouched.
- `bb84PolyDim`: CKR polynomial dimension `C(n + 15, 15)` for BB84.

## Main results

- `QKD.BB84.Model.bb84OutcomeEveEmbedding_injective`, `bb84TauOutcomeEveRefEmbedding_injective`:
  the fixed-outcome embeddings are injective in the Eve(-reference) index.
- `QKD.BB84.Model.bb84OutcomeEveEmbedding_diag_sum_eq_one`,
  `bb84TauOutcomeEveRefEmbedding_diag_sum_eq_one`: the outcome/Eve(-reference) diagonal blocks
  partition the ambient diagonal trace sum.
- `bb84PolyDim_pos`, `bb84PolyDim_ge_16`: positivity, and the structural lower bound
  `bb84PolyDim n ≥ 16` for `n ≥ 1`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts Quantum.Channels
open InfoTheory.SmoothMinEntropy
open scoped ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
## Eve's conditional sub-density

For outcome string `ω : Fin n → Fin signalDim`, `bb84OutcomeIndex` packs
the string into an index `ωIdx : Fin (4^n)`. Eve's conditional sub-density is
the `(ωIdx, ωIdx)`-diagonal block of the joint attack output
`σ = attackChannel ρ_initial : DensityOp (4^n * eveDim)`, viewed as a
`eveDim × eveDim` matrix.
-/

-- `bb84OutcomeEveEmbedding`, `bb84OutcomeEveEmbedding_injective` and
-- `bb84OutcomeEveEmbedding_diag_sum_eq_one` now live in `QKD.BB84.Model.Measurement` (imported
-- above): they are the model's outcome/Eve register bookkeeping, not Engine-specific analysis.

/-!
## CKR-reference post-measurement CQ state

The CKR tensor trace norm evaluates the protocol difference on
`(attackChannelLinear atk ⊗ id_R)(τ)`. Privacy amplification must therefore use
the post-measurement CQ state whose quantum side contains both Eve's attack
register and the CKR reference register.
-/

/-- Embedding of Eve-reference indices into the attacked CKR state at a fixed
BB84 outcome. The attacked CKR state is indexed as `(outcome, Eve, R)`, while the
conditioned block is indexed by `(Eve, R)`. -/
def bb84TauOutcomeEveRefEmbedding {n eveDim dimR : ℕ}
    (ωIdx : Fin (4 ^ n)) :
    Fin (eveDim * dimR) → Fin ((4 ^ n * eveDim) * dimR) :=
  fun er =>
    let er' : Fin eveDim × Fin dimR := finProdFinEquiv.symm er
    finProdFinEquiv (finProdFinEquiv (ωIdx, er'.1), er'.2)

/-- The fixed-outcome Eve-reference embedding is injective in the
Eve-reference index. -/
lemma bb84TauOutcomeEveRefEmbedding_injective {n eveDim dimR : ℕ}
    (ωIdx : Fin (4 ^ n)) :
    Function.Injective
      (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) ωIdx) := by
  intro er er' h
  let p : Fin eveDim × Fin dimR := finProdFinEquiv.symm er
  let q : Fin eveDim × Fin dimR := finProdFinEquiv.symm er'
  change finProdFinEquiv (finProdFinEquiv (ωIdx, p.1), p.2) =
    finProdFinEquiv (finProdFinEquiv (ωIdx, q.1), q.2) at h
  have h_outer :
      (finProdFinEquiv (ωIdx, p.1), p.2) =
        (finProdFinEquiv (ωIdx, q.1), q.2) :=
    finProdFinEquiv.injective h
  have h_second : p.2 = q.2 :=
    congrArg (fun r : Fin (4 ^ n * eveDim) × Fin dimR => r.2) h_outer
  have h_inner_fin :
      finProdFinEquiv (ωIdx, p.1) = finProdFinEquiv (ωIdx, q.1) :=
    congrArg (fun r : Fin (4 ^ n * eveDim) × Fin dimR => r.1) h_outer
  have h_inner : (ωIdx, p.1) = (ωIdx, q.1) :=
    finProdFinEquiv.injective h_inner_fin
  have h_first : p.1 = q.1 :=
    congrArg (fun r : Fin (4 ^ n) × Fin eveDim => r.2) h_inner
  have hpq : p = q := Prod.ext h_first h_second
  have hsymm : finProdFinEquiv.symm er = finProdFinEquiv.symm er' := by
    simpa [p, q] using hpq
  exact finProdFinEquiv.symm.injective hsymm

/-- Operator obtained by applying a pre-channel to the signal register of a CKR
purification and leaving the CKR reference register untouched.

Indexed by a bare retained-Eve dimension `eveDim` and an opaque pre-channel `pre` rather than
by an attack object: the attack instantiation is `eveDim := atk.eveDim`,
`pre := attackChannelLinear atk`. -/
noncomputable def bb84TauOutputOp {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    Op ((4 ^ n * eveDim) * dimR) :=
  mapTensorId pre τ.toOp

/-- Density-operator version of `bb84TauOutputOp`, valid whenever the pre-channel is CPTP. -/
noncomputable def bb84TauOutputDensity {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    DensityOp ((4 ^ n * eveDim) * dimR) := by
  let Φ : Op ((signalDim ^ n) * dimR) →
      Op ((4 ^ n * eveDim) * dimR) :=
    fun x => mapTensorId pre x
  have hΦ : IsCPTP Φ := by
    simpa [Φ] using (mapTensorId_isCPTP pre hpre)
  exact
    { toOp := bb84TauOutputOp eveDim pre τ
      isHermitian := by
        dsimp [bb84TauOutputOp]
        simpa [Φ] using IsCPTP.preserves_hermitian Φ hΦ τ.toOp τ.isHermitian
      pos_semidef := by
        dsimp [bb84TauOutputOp]
        have hpsd : (mapTensorId pre τ.toOp).PosSemidef :=
          by
            simpa [Φ] using
              cptp_preserves_posSemidef Φ hΦ τ.toOp
                (posSemidefOp_implies_mathlib τ.toPosSemidefOp)
        intro v
        exact (Complex.nonneg_iff.mp
          (by simpa [quadraticForm] using hpsd.dotProduct_mulVec_nonneg v)).1
      trace_one := by
        dsimp [bb84TauOutputOp]
        have htp := hΦ.2.2
        calc
          (mapTensorId pre τ.toOp).trace
              = τ.toOp.trace := by simpa [Φ] using htp τ.toOp
          _ = 1 := τ.trace_one }

/-- The BB84 tau outcome/Eve-reference diagonal blocks partition the diagonal trace sum. -/
lemma bb84TauOutcomeEveRefEmbedding_diag_sum_eq_one {n eveDim dimR : ℕ}
    (ρ : DensityOp ((4 ^ n * eveDim) * dimR)) :
    (∑ ω : Fin n → Fin signalDim, ∑ er : Fin (eveDim * dimR),
      (ρ.toOp
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) (bb84OutcomeIndex ω) er)
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) (bb84OutcomeIndex ω)
            er)).re) = 1 := by
  rw [bb84OutcomeIndex_sum (n := n)
    (f := fun ωIdx : Fin (4 ^ n) => ∑ er : Fin (eveDim * dimR),
      (ρ.toOp
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) ωIdx er)
        (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR) ωIdx er)).re)]
  rw [← densityOp_sum_diag_re_eq_one ρ]
  rw [← Fintype.sum_prod_type']
  let e : Fin (4 ^ n) × Fin (eveDim * dimR) ≃ Fin ((4 ^ n * eveDim) * dimR) :=
    ((Equiv.refl _).prodCongr finProdFinEquiv.symm).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv))
  apply Fintype.sum_equiv e
  intro ⟨ωIdx, er⟩
  congr 1

/-!
## The CKR polynomial dimension

`polyDim = C(n + signalDim² − 1, signalDim² − 1)` is the regularisation denominator used
throughout the CKR de Finetti reference constructions.
-/

/-- The polynomial-subspace dimension `C(n + d² − 1, d² − 1)` used as the
regularization denominator.  For `d = signalDim = 4` this equals `C(n + 15, 15)`. -/
noncomputable def bb84PolyDim (n : ℕ) : ℕ :=
  Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1)

/-- `bb84PolyDim n ≥ 1` for all `n`. -/
lemma bb84PolyDim_pos (n : ℕ) : 0 < bb84PolyDim n :=
  Nat.choose_pos (by simp [signalDim])

/-- `bb84PolyDim n ≥ 16` for every `n ≥ 1` (i.e. `[NeZero n]`).  Since
`bb84PolyDim n = C(n + 15, 15)` and `C(·, 15)` is monotone in its first argument,
`bb84PolyDim n ≥ C(1 + 15, 15) = C(16, 15) = 16`. -/
lemma bb84PolyDim_ge_16 {n : ℕ} [NeZero n] : 16 ≤ bb84PolyDim n := by
  unfold bb84PolyDim
  have hb : signalDim ^ 2 - 1 = 15 := by decide
  rw [hb]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  calc (16 : ℕ) = Nat.choose (1 + 15) 15 := by decide
    _ ≤ Nat.choose (n + 15) 15 := Nat.choose_le_choose 15 (by omega)

end QKD.BB84.Engine

end -- noncomputable section
