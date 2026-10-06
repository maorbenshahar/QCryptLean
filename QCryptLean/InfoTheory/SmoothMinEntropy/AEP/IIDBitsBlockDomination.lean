import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID

/-!
# Bit-normalized entropy-floor definitions for Renner `thm:Hmincondrep`

This module carries the bit-normalized entropy quantities that parameterize the
Renner single-letter floor:

* `cqConditionalEntropyRelBits` — the σ-relative conditional von Neumann entropy
  `H(X|B)_{ρ|σ} = (S(ρ_XB) − S(ρ_B) − D(ρ_B ‖ σ)) / log 2`, in bits;
* `iidAEPBitEntropyContribution` — definitionally the same scalar, the
  von-Neumann-entropy contribution of the bit floor;
* `iidAEPBitEntropyFloor`, `iidAEPBitBlockEntropyFloor` — the per-copy
  and block-length-scaled bit floors `contribution − δ_iidAEP_general`.

These are the entropy scalars the spectral/Chernoff witness of Renner
`thm:Hmincondrep` is built against. This module is
purely definitional plus the `rfl`-level identity tying the contribution term to
`cqConditionalEntropyRelBits`; the analytic content of the Renner bound lives in
the spectral/Chernoff apparatus elsewhere in this directory.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The σ-relative conditional von Neumann entropy `H(X|B)_{ρ|σ}` of a
normalized CQ state, expressed in **bits**:
`(S(ρ_XB) − S(ρ_B) − D(ρ_B ‖ σ)) / log 2`.

This is the conditional-entropy quantity `−D(ρ_XB ‖ id_X ⊗ σ_B)/log 2` on the
right of Renner's single-shot bound. It is, by construction, the same scalar as
the floor's `iidAEPBitEntropyContribution`; see
`iidAEPBitEntropyContribution_eq_cqConditionalEntropyRelBits`. -/
noncomputable def cqConditionalEntropyRelBits
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) : ℝ :=
  (vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
      - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)
      - InfoTheory.RelativeEntropy.relativeEntropyReal
          (ρ.quantumMarginalDensityOp hρ_norm) σ) / Real.log 2

/-- Base-two entropy contribution in Renner `thm:Hmincondrep`.

The von Neumann and relative-entropy terms are natural-log quantities in this
development. This definition is the explicit unit conversion used by the
bit-normalized spectral threshold. -/
noncomputable def iidAEPBitEntropyContribution
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) : ℝ :=
  (vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
      - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)
      - InfoTheory.RelativeEntropy.relativeEntropyReal
          (ρ.quantumMarginalDensityOp hρ_norm) σ) / Real.log 2

/-- Bit-normalized single-copy entropy floor for Renner `thm:Hmincondrep`.

The von Neumann and relative-entropy terms are natural-log quantities and are
therefore divided by `Real.log 2`; the Renner correction
`δ_iidAEP_general` is already base-two. -/
noncomputable def iidAEPBitEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  iidAEPBitEntropyContribution ρ hρ_norm σ
    - δ_iidAEP_general ρ σ n_copies ε

/-- Block-length-scaled bit-normalized entropy floor. -/
noncomputable def iidAEPBitBlockEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (n_copies : ℝ) * iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε

/-- The floor's bit entropy contribution is exactly the σ-relative conditional
von Neumann entropy in bits, `H(X|B)_{ρ|σ}`. -/
theorem iidAEPBitEntropyContribution_eq_cqConditionalEntropyRelBits
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) :
    iidAEPBitEntropyContribution ρ hρ_norm σ
      = cqConditionalEntropyRelBits ρ hρ_norm σ := rfl

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
