import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Channels.CPTP.CKRBound.FullRank
import QCryptLean.Quantum.Metrics.PurificationFreedom
import QCryptLean.Quantum.Metrics.PurificationUhlmannUniqueness
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.SameAncillaTransport
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# CKR Reference Purifications — canonical purification, rank bound, Uhlmann transport

This file packages CKR-specific purification facts for the Hilbert-Schmidt
de Finetti reference state.  It builds the canonical same-ancilla purification
of `ckrDeFinettiState`, proves its marginal identities, and records the
Uhlmann transport statements used by downstream CKR and BB84 reference
arguments.

## Main definitions
- `ckrDeFinettiCanonicalPurification`: the canonical square-ancilla purification
  of `ckrDeFinettiState`.

## Main statements
- `ckrDeFinettiCanonicalPurification_isCKRDeFinettiPurification`: the canonical
  purification satisfies `IsCKRDeFinettiPurification`.
- `ckrDeFinettiCanonicalPurification_partialTraceA_toOp`: the canonical
  purification has the CKR marginal on the left factor.
- `ckrDeFinetti_squareAncilla_unitary_transport`: square-ancilla CKR
  purifications are right-unitary transports of the canonical purification.
- `isCKRDeFinettiPurification_dimR_ge`: any CKR purification has reference
  dimension at least `d ^ n`.
- `ckrDeFinettiPurification_relate_canonical_via_partial_isometry`: any CKR
  purification is a reference-side left-isometry transport of the canonical one.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open Quantum.Metrics.KitaevWatrousPurification
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Channels

/-! ## Canonical CKR de Finetti purification -/

/-- **Canonical CKR de Finetti purification** (square ancilla, standard construction).

The standard same-ancilla purification of `ckrDeFinettiState d n` lives on
`(d^n) * (d^n)` and is given by

  `τ_canon := sameAncillaPurificationDensity (ckrDeFinettiState d n)`,

i.e. the density operator whose underlying operator is
`(√ρ ⊗ 1) Ω (√ρ ⊗ 1)†`
where `ρ = ckrDeFinettiState d n` and `Ω = |Ω⟩⟨Ω|` is the unnormalized maximally
entangled ketbra on `ℂ^{d^n}`.

The ancilla dimension `d^n` is the minimal dimension supporting a purification of
`ckrDeFinettiState d n`, since `ckrDeFinettiState d n` has full rank `d^n`
(every eigenvalue is positive, by Schur-Weyl positivity). -/
noncomputable def ckrDeFinettiCanonicalPurification (d n : ℕ) [NeZero d] [NeZero n]
    [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)] :
    DensityOp (d ^ n * d ^ n) :=
  sameAncillaPurificationDensity (ckrDeFinettiState d n)

/-- The canonical CKR purification operator is the ketbra of the canonical
same-ancilla ket. -/
theorem ckrDeFinettiCanonicalPurification_toOp_eq_ketbra
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)] :
    (ckrDeFinettiCanonicalPurification d n).toOp =
      sameAncillaPurificationKet (ckrDeFinettiState d n) *
        (sameAncillaPurificationKet (ckrDeFinettiState d n)).dag := by
  simpa [ckrDeFinettiCanonicalPurification] using
    (sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet
      (ckrDeFinettiState d n))

/-- The canonical CKR de Finetti purification satisfies `IsCKRDeFinettiPurification`.

Two things must be verified:
1. It is pure: follows from `sameAncillaPurificationDensity_isPure`.
2. Its `H^n` marginal is `ckrDeFinettiState d n`: follows from
   `partialTraceB_sameAncillaPurification` and the trace normalization of `ckrDeFinettiState`.

**Reference.** This is the standard canonical purification; see Renner (2005), §4.2.2. -/
theorem ckrDeFinettiCanonicalPurification_isCKRDeFinettiPurification
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)] :
    IsCKRDeFinettiPurification (ckrDeFinettiCanonicalPurification d n) where
  isPure := sameAncillaPurificationDensity_isPure _
  marginal := by
    apply DensityOp.ext
    simpa [ckrDeFinettiCanonicalPurification, DensityOp.partialTraceB,
      PosSemidefOp.partialTraceB] using
      partialTraceB_sameAncillaPurificationDensity
        (ckrDeFinettiState d n)

/-- The canonical same-ancilla CKR purification has CKR marginal on the left
factor. -/
theorem ckrDeFinettiCanonicalPurification_partialTraceA_toOp
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)] :
    partialTraceA (ckrDeFinettiCanonicalPurification d n).toOp =
      (ckrDeFinettiState d n).toOp := by
  calc
    partialTraceA (ckrDeFinettiCanonicalPurification d n).toOp =
        (ckrDeFinettiState d n).toOp.transpose := by
      simpa [ckrDeFinettiCanonicalPurification] using
        sameAncillaPurificationDensity_partialTraceA_toOp_transpose
          (ckrDeFinettiState d n)
    _ = (ckrDeFinettiState d n).toOp :=
      ckrDeFinettiState_toOp_transpose d n

/-- The pure ket extracted from a CKR de Finetti purification has CKR marginal. -/
theorem IsCKRDeFinettiPurification.partialTraceB_pureKetOf
    {d n dimR : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR)) (hτ : IsCKRDeFinettiPurification τ) :
    partialTraceB ((τ.pureKetOf hτ.isPure) * (τ.pureKetOf hτ.isPure).dag) =
      (ckrDeFinettiState d n).toOp := by
  calc
    partialTraceB ((τ.pureKetOf hτ.isPure) * (τ.pureKetOf hτ.isPure).dag) =
        τ.partialTraceB.toOp :=
      Quantum.Operators.DensityOp.partialTraceB_pureKetOf_ketbra τ hτ.isPure
    _ = (ckrDeFinettiState d n).toOp :=
      congrArg (fun σ : DensityOp (d ^ n) => σ.toOp) hτ.marginal

/-- A square-ancilla CKR purification is a right-factor unitary transport of the
canonical CKR purification. -/
theorem ckrDeFinetti_squareAncilla_unitary_transport
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    (τ : DensityOp ((d ^ n) * (d ^ n)))
    (hτ : IsCKRDeFinettiPurification τ) :
    ∃ W : UnitaryOp (d ^ n),
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (ckrDeFinettiCanonicalPurification d n).toOp := by
  simpa only [ckrDeFinettiCanonicalPurification] using
    (Quantum.Metrics.purification_squareAncilla_rightTensorUnitaryConj
      (ckrDeFinettiState d n) τ hτ.isPure hτ.marginal)

/-! ## Dimension bound from IsCKRDeFinettiPurification -/

/-- **Any CKR de Finetti purification has `d^n ≤ dimR`.**

A pure state `τ : DensityOp ((d^n) * dimR)` with marginal `ckrDeFinettiState d n`
must satisfy `d^n ≤ dimR`.

**Proof outline.** The Schmidt rank of a bipartite pure state on `ℂ^{d^n} ⊗ ℂ^{dimR}`
equals the rank of each marginal.  The marginal `ckrDeFinettiState d n` has full rank
`d^n` (every Schur-Weyl weight appears with positive multiplicity; Christandl-König-Renner
(2009) main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}` :291–:301,
Lemma `\label{lem:extractpart}` :319–:328), Renner (2005) §6.4).  The Schmidt rank is at most
`min(d^n, dimR)`, so
`d^n ≤ dimR`.

**References.**
- Watrous, *Quantum Information* (2018), §2.1 (Schmidt decomposition).
- Renner, *Security of QKD* (2005), Remark 4.2.4. -/
theorem isCKRDeFinettiPurification_dimR_ge
    {d n dimR : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ) :
    d ^ n ≤ dimR := by
  have h_marginal_rank_le :
      Matrix.rank τ.partialTraceB.toOp ≤ dimR :=
    Quantum.Metrics.bipartitePure_partialTraceB_rank_le_right_dim
      (d := d ^ n) (dimR := dimR) τ hτ.isPure
  rw [hτ.marginal] at h_marginal_rank_le
  have h_full_rank :
      Matrix.rank (ckrDeFinettiState d n).toOp = d ^ n :=
    Quantum.Channels.ckrDeFinettiState_rank_toOp_of_openPosIntegral d n
  rw [h_full_rank] at h_marginal_rank_le
  exact h_marginal_rank_le

/-! ## Uhlmann transfer for CKR purifications -/

/-- **Any CKR de Finetti purification relates to the canonical one via a left-isometry.**

For any `τ : DensityOp ((d^n) * dimR)` satisfying `IsCKRDeFinettiPurification τ`
and any `dimR` with `d^n ≤ dimR`, there exists a left-isometry
`V : Matrix (Fin dimR) (Fin (d^n)) ℂ` (satisfying `Vᴴ * V = 1`) such that:
the pure ket of `τ` equals `(1_{d^n} ⊗ V)` times the canonical pure ket
`sameAncillaPurificationKet (ckrDeFinettiState d n)`.

For `dimR = d^n`, the partial isometry is a full unitary and the statement reduces to
`purification_unitary_freedom_canonical`.

**Proof outline.** Extract the pure ket of `τ` via `τ.pureKetOf hτ.isPure`.
Apply `purification_unique_up_to_partial_isometry_on_reference` to the pair
`(sameAncillaPurificationKet (ckrDeFinettiState d n), ψτ)`, noting that both have
the same `H^n` marginal `ckrDeFinettiState d n` (canonical by
`ckrDeFinettiCanonicalPurification_isCKRDeFinettiPurification`, arbitrary by
`hτ.marginal`).

**References.**
- Watrous (2018), §2.2 Theorem 2.21.
- Renner (2005), §4.2.2. -/
theorem ckrDeFinettiPurification_relate_canonical_via_partial_isometry
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (hdim : d ^ n ≤ dimR) :
    ∃ V : Matrix (Fin dimR) (Fin (d ^ n)) ℂ,
      Vᴴ * V = (1 : Op (d ^ n)) ∧
      (τ.pureKetOf hτ.isPure).vec = fun k =>
        ∑ (pair : Fin (d ^ n) × Fin (d ^ n)),
          ((1 : Op (d ^ n)) pair.1 (finProdFinEquiv.symm k).1 *
            V (finProdFinEquiv.symm k).2 pair.2) *
          (KitaevWatrousPurification.sameAncillaPurificationKet
            (ckrDeFinettiState d n)).vec (finProdFinEquiv pair) := by
  let ψ_canon : Ket ((d ^ n) * (d ^ n)) :=
    KitaevWatrousPurification.sameAncillaPurificationKet (ckrDeFinettiState d n)
  let ψτ : Ket ((d ^ n) * dimR) := τ.pureKetOf hτ.isPure
  have hψ_canon_norm : ψ_canon.dag * ψ_canon = 1 := by
    simpa [ψ_canon] using
      KitaevWatrousPurification.sameAncillaPurificationKet_normalized
      (ckrDeFinettiState d n)
  have hψτ_norm : ψτ.dag * ψτ = 1 := by
    simpa [ψτ] using DensityOp.pureKetOf_normalized τ hτ.isPure
  have hψ_canon_pu :
      partialTraceB (ψ_canon * ψ_canon.dag) = (ckrDeFinettiState d n).toOp := by
    simpa [ψ_canon] using
      KitaevWatrousPurification.partialTraceB_sameAncillaPurificationKet
        (ckrDeFinettiState d n)
  have hψτ_pu :
      partialTraceB (ψτ * ψτ.dag) = (ckrDeFinettiState d n).toOp := by
    simpa [ψτ] using
      IsCKRDeFinettiPurification.partialTraceB_pureKetOf τ hτ
  exact
    Quantum.Metrics.purification_unique_up_to_partial_isometry_on_reference
      (ckrDeFinettiState d n) ψ_canon ψτ hψ_canon_norm hψτ_norm
      hψ_canon_pu hψτ_pu hdim

end Quantum.Channels

end -- noncomputable section
