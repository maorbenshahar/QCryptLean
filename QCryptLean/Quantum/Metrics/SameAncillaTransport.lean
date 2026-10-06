import QCryptLean.Quantum.Metrics.PurificationFreedom
import QCryptLean.Quantum.Metrics.PurificationUhlmannUniqueness
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.ReferenceTransport

/-!
# Same-Ancilla Transport — square-ancilla purifications and their reference marginals

Unitary freedom (`Quantum.Metrics.purification_unitary_freedom_canonical`) says that a
purifying *ket* on `ℂ^d ⊗ ℂ^d` is `(1 ⊗ W)` applied to the canonical same-ancilla ket.
This file records the consequences at the level of density operators and of the
*reference* marginal `partialTraceA`, which is the marginal that purification does **not**
prescribe.

The three facts are:

* every square-ancilla purification of `ρ` is `rightTensorUnitaryConj W` of the canonical
  purification, for some unitary `W` on the reference factor;
* the reference marginal of such a transport is `W ρᵀ W†`; hence
* the reference marginal of an arbitrary square-ancilla purification of `ρ` ranges exactly
  over the unitary orbit of `ρᵀ`, and equals `ρᵀ` precisely when the transporting unitary
  commutes with `ρᵀ`.

Only the *square* ancilla `ℂ^d` is treated.  For a strictly larger reference the freedom is
a left isometry rather than a unitary
(`Quantum.Metrics.purification_unique_up_to_partial_isometry_on_reference`), and the
reference marginal is then supported on a `rank ρ`-dimensional subspace instead of being
unitarily equivalent to `ρᵀ` on the nose.

## Main definitions
- This file defines no new data structures.

## Main statements
- `purification_squareAncilla_rightTensorUnitaryConj`: a square-ancilla purification is a
  right-unitary transport of the canonical same-ancilla purification.
- `isPurification_squareAncilla_iff_exists_rightTensorUnitaryConj`: and conversely, so that
  the square-ancilla purifications of `ρ` are *exactly* the right-unitary transports.
- `partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity`: the reference
  marginal of a right-unitary transport is `W ρᵀ W†`.
- `purification_squareAncilla_partialTraceA_mem_unitary_orbit_transpose`: the reference
  marginal of any square-ancilla purification of `ρ` is a unitary conjugate of `ρᵀ`.
- `partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity_eq_iff_commutes`:
  the transported reference marginal is `ρᵀ` exactly when `W` commutes with `ρᵀ`.

**References.**
- Watrous, *The Theory of Quantum Information* (2018), Theorem 2.21 and Corollary 2.22
  (unitary/isometric equivalence of purifications; equality of the two marginals' spectra).
- Nielsen–Chuang, §2.5 (unitary freedom in the ensemble/purification).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Metrics.KitaevWatrousPurification
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-- **Square-ancilla purifications are right-unitary transports of the canonical one.**

If `τ : DensityOp (d * d)` is pure with `partialTraceB τ = ρ`, then there is a unitary `W`
on the reference factor with

  `τ = (1 ⊗ W) · sameAncillaPurificationDensity ρ · (1 ⊗ W)†`.

This is `purification_unitary_freedom_canonical` transported from kets to density
operators; it needs no rank or full-rank hypothesis on `ρ`, because both purifications sit
on the *same* reference dimension. -/
theorem purification_squareAncilla_rightTensorUnitaryConj
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (τ : DensityOp (d * d))
    (hpure : τ.IsPure) (hmarginal : τ.partialTraceB = ρ) :
    ∃ W : UnitaryOp d,
      τ.toOp =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity ρ).toOp := by
  have : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  let ψτ : Ket (d * d) := τ.pureKetOf hpure
  have hψτ_pu : partialTraceB (ψτ * ψτ.dag) = ρ.toOp := by
    calc
      partialTraceB (ψτ * ψτ.dag) = τ.partialTraceB.toOp :=
        Quantum.Operators.DensityOp.partialTraceB_pureKetOf_ketbra τ hpure
      _ = ρ.toOp := congrArg (fun σ : DensityOp d => σ.toOp) hmarginal
  obtain ⟨W, hW⟩ := purification_unitary_freedom_canonical ρ ψτ hψτ_pu
  refine ⟨W, ?_⟩
  let A : Op (d * d) := Op.tensor (1 : Op d) W.toOp
  let ψcanon : Ket (d * d) := sameAncillaPurificationKet ρ
  have hτ_op : τ.toOp = ψτ * ψτ.dag := DensityOp.pureKetOf_spec τ hpure
  have hcanon_op :
      (sameAncillaPurificationDensity ρ).toOp = ψcanon * ψcanon.dag :=
    sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet ρ
  calc
    τ.toOp = ψτ * ψτ.dag := hτ_op
    _ = (A * ψcanon) * (A * ψcanon).dag := by rw [hW]
    _ = A * (ψcanon * ψcanon.dag) * A† :=
      (Quantum.Operators.op_mul_ketbra_mul_conjTranspose A ψcanon).symm
    _ = Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity ρ).toOp := by
      rw [Quantum.TensorProducts.rightTensorUnitaryConj, ← hcanon_op]

/-- **Conversely, every right-unitary transport of the canonical purification is again a
square-ancilla purification of `ρ`**, so the two descriptions agree exactly.

Only the reference marginal moves under the transport; the purified marginal is fixed by
`Quantum.TensorProducts.partialTraceB_rightTensorUnitaryConj`. -/
theorem isPurification_squareAncilla_iff_exists_rightTensorUnitaryConj
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (τ : DensityOp (d * d)) :
    (τ.IsPure ∧ τ.partialTraceB = ρ) ↔
      ∃ W : UnitaryOp d,
        τ.toOp =
          Quantum.TensorProducts.rightTensorUnitaryConj W
            (sameAncillaPurificationDensity ρ).toOp := by
  refine ⟨fun h => purification_squareAncilla_rightTensorUnitaryConj ρ τ h.1 h.2,
    fun ⟨W, hW⟩ => ?_⟩
  have hτ_eq :
      τ = UnitaryOp.evolve (Quantum.TensorProducts.rightTensorUnitary (n := d) W)
        (sameAncillaPurificationDensity ρ) :=
    Quantum.Operators.DensityOp.ext hW
  refine ⟨?_, ?_⟩
  · rw [hτ_eq]
    exact Quantum.TensorProducts.DensityOp.isPure_rightTensorUnitaryEvolve W
      (sameAncillaPurificationDensity_isPure ρ)
  · rw [hτ_eq,
      Quantum.TensorProducts.DensityOp.partialTraceB_rightTensorUnitaryEvolve]
    exact Quantum.Operators.DensityOp.ext
      (partialTraceB_sameAncillaPurificationDensity ρ)

/-- The **reference** marginal of a right-unitary transport of the canonical same-ancilla
purification is the conjugated transpose `W ρᵀ W†`.

The transpose appears because the canonical purification is the vectorization of `√ρ`:
tracing out the *purified* factor leaves `(√ρ)ᵀ (√ρ)ᵀ = ρᵀ`, whereas tracing out the
*reference* factor leaves `ρ` itself. -/
theorem partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity
    {d : ℕ} (ρ : DensityOp d) (W : UnitaryOp d) :
    partialTraceA
        (Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity ρ).toOp) =
      W.toOp * ρ.toOpᵀ * W.toOp† := by
  rw [Quantum.TensorProducts.partialTraceA_rightTensorUnitaryConj,
    sameAncillaPurificationDensity_partialTraceA_toOp_transpose]

/-- **The reference marginal of a square-ancilla purification lies in the unitary orbit of
`ρᵀ`.**

Purification prescribes only the `partialTraceB` marginal; the `partialTraceA` marginal is
free up to a unitary.  In particular every square-ancilla purification of `ρ` has reference
marginal isospectral to `ρ`, and therefore of the same rank. -/
theorem purification_squareAncilla_partialTraceA_mem_unitary_orbit_transpose
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (τ : DensityOp (d * d))
    (hpure : τ.IsPure) (hmarginal : τ.partialTraceB = ρ) :
    ∃ W : UnitaryOp d, partialTraceA τ.toOp = W.toOp * ρ.toOpᵀ * W.toOp† := by
  obtain ⟨W, hW⟩ :=
    purification_squareAncilla_rightTensorUnitaryConj ρ τ hpure hmarginal
  exact ⟨W, by
    rw [hW, partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity]⟩

/-- **The transported reference marginal equals `ρᵀ` exactly when the transport commutes
with `ρᵀ`.**

This follows from the transported-marginal formula and cancellation of the unitary. -/
theorem partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity_eq_iff_commutes
    {d : ℕ} (ρ : DensityOp d) (W : UnitaryOp d) :
    partialTraceA
        (Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity ρ).toOp) = ρ.toOpᵀ ↔
      W.toOp * ρ.toOpᵀ = ρ.toOpᵀ * W.toOp := by
  rw [partialTraceA_rightTensorUnitaryConj_sameAncillaPurificationDensity]
  refine ⟨fun hconj => ?_, fun hcomm =>
    Quantum.Operators.unitary_conj_eq_of_mul_comm W ρ.toOpᵀ hcomm⟩
  calc
    W.toOp * ρ.toOpᵀ = (W.toOp * ρ.toOpᵀ * W.toOp†) * W.toOp := by
      simp only [Matrix.mul_assoc]
      rw [W.unitary_left, Matrix.mul_one]
    _ = ρ.toOpᵀ * W.toOp := by rw [hconj]

end Quantum.Metrics

end -- noncomputable section
