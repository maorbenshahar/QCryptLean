import QCryptLean.Quantum.Channels.CPTP.PetzPartialTrace
import QCryptLean.Quantum.Operators.MarginalTransport
import QCryptLean.InfoTheory.DeFinetti.MaxEntangled

/-!
# Petz recovery versus marginal transport

Two constructions attach to a bipartite reference `ρ_ER` with positive-definite
`E`-marginal `ρ_E`:

* the **Petz transpose map** `Quantum.Channels.petzTranspose` — a genuine channel
  (linear, completely positive, trace preserving) that recovers `ρ_ER` from `ρ_E`;
* **marginal transport** `Quantum.Operators.marginalTransport` — a positive,
  marginal-exact but *nonlinear* assignment.

Neither dominates the other, and this file proves both separations on the same
correlated reference `ρ_ER = maxEntangledOp m` (unnormalized, so `Tr_R ρ_ER = 1_m` is
positive definite):

* `Quantum.Operators.marginalTransport_not_additive` — marginal transport fails
  additivity on positive-semidefinite inputs, so it is **not** a completely positive
  map and not a physically implementable channel, even though every output is positive
  and has exactly the requested marginal.
* `Quantum.Channels.petzTranspose_not_marginal_exact` — the Petz channel is **not** a
  right inverse of `Tr_R`: it recovers the reference, not an arbitrary marginal.

The separating computation is exact, not numerical: on the maximally entangled
reference the Petz map collapses to `Y ↦ (Tr Y / m) · Ω`
(`Quantum.Channels.petzTranspose_maxEntangledOp_apply`), while marginal transport
compresses `Ω` by `Y^{1/2} ⊗ 1` and destroys its off-diagonal coherence.

## Worked example

`Quantum.Channels.petzTranspose_maxEntangledOp_reference` together with
`InfoTheory.DeFinetti.maxEntangledOp_ne_zero` give a concrete nonzero correlated
instance of the recovery identity, and
`Quantum.Channels.petzTranspose_maxEntangledOp_isCPTP` certifies that this instance
really is a channel.

The generic ingredients live with their subjects: the `Ω` facts in
`QCryptLean.InfoTheory.DeFinetti.MaxEntangled`, the standard-basis projector
and diagonal facts in `QCryptLean.Quantum.Operators.BraKet.Projector`, and the
square root of a projection in `QCryptLean.Quantum.Operators.MatrixSqrt`.
Only the two `Fin 2` instances used by the separating computation are kept here, and
they are `private`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-! ## Local instances of the standard-basis diagonal API -/

/-- The square root of a standard-basis diagonal projector is the projector itself:
the instance of `Matrix.PosSemidef.sqrt_eq_self_of_isIdempotentElem` that the
compression computation below consumes. -/
private lemma sqrt_diagonal_single {m : ℕ} (i : Fin m) :
    CFC.sqrt (Matrix.diagonal (Pi.single i (1 : ℂ)) : Op m)
      = Matrix.diagonal (Pi.single i (1 : ℂ)) :=
  (posSemidef_diagonal_single i).sqrt_eq_self_of_isIdempotentElem
    (isIdempotentElem_diagonal_single i)

/-- The `Fin 2` instance of `Quantum.Operators.sum_diagonal_single`, in the two-term
form the counterexample consumes. -/
private lemma diagonal_single_add_two :
    Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ))
        + Matrix.diagonal (Pi.single (1 : Fin 2) (1 : ℂ))
      = (1 : Op 2) := by
  rw [← Fin.sum_univ_two (fun i : Fin 2 => Matrix.diagonal (Pi.single i (1 : ℂ)))]
  exact sum_diagonal_single 2

/-- A diagonal two-sided compression acts entrywise. -/
private lemma diagonal_sandwich_apply {N : ℕ} (d : Fin N → ℂ) (M : Op N) (α β : Fin N) :
    (Matrix.diagonal d * M * Matrix.diagonal d) α β = d α * M α β * d β := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end Quantum.Operators

namespace Quantum.Channels

/-! ## The Petz channel on the maximally entangled reference -/

/-- On the maximally entangled reference the Petz transpose map collapses to
`Y ↦ (Tr Y / m) · Ω`.  In particular it forgets everything about `Y` except its
trace, which is exactly why it is not marginal exact. -/
theorem petzTranspose_maxEntangledOp_apply (m : ℕ) [NeZero m]
    (h : (1 : Op m).PosDef) (Y : Op m) :
    petzTranspose (maxEntangledOp m) h Y = (Y.trace / (m : ℂ)) • maxEntangledOp m := by
  have hcR : (1 / Real.sqrt m : ℝ) * (1 / Real.sqrt m) = 1 / (m : ℝ) := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hmR.le]
  have hc : ((1 / Real.sqrt m : ℝ) : ℂ) * ((1 / Real.sqrt m : ℝ) : ℂ) = 1 / (m : ℂ) := by
    rw [← Complex.ofReal_mul, hcR]
    push_cast
    ring
  rw [petzTranspose_apply, Matrix.PosDef.inverseSqrt_one h, Matrix.one_mul, Matrix.mul_one,
    sqrt_maxEntangledOp m, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, hc, maxEntangledOp_sandwich, smul_smul]
  congr 1
  ring

/-- The worked correlated instance of the recovery identity: on `Ω` with reference
`1_m`, the Petz transpose map returns `Ω` itself. -/
theorem petzTranspose_maxEntangledOp_reference (m : ℕ) (h : (1 : Op m).PosDef) :
    petzTranspose (maxEntangledOp m) h (1 : Op m) = maxEntangledOp m :=
  petzTranspose_reference _ (maxEntangledOp_posSemidef m) h

/-- …and that instance really is a channel. -/
theorem petzTranspose_maxEntangledOp_isCPTP (m : ℕ) [NeZero m] [NeZero (m * m)]
    (h : (1 : Op m).PosDef) :
    IsCPTP ⇑(petzTranspose (maxEntangledOp m) h) :=
  petzTranspose_isCPTP _ (maxEntangledOp_posSemidef m) h (maxEntangledOp_partialTraceB m)

/-- **The Petz transpose map is not marginal exact**: `Tr_R ∘ R₀ ≠ id`.

All hypotheses of `petzTranspose_isCPTP` hold for the witness, so this is a genuine
property of the Petz channel, not an artifact of a degenerate reference.  Contrast
`Quantum.Operators.marginalTransport_partialTraceB`, which *is* marginal exact — at
the price of not being a channel. -/
theorem petzTranspose_not_marginal_exact :
    ∃ (dE dR : ℕ) (rhoER : Op (dE * dR)) (rhoE : Op dE) (hrhoE : rhoE.PosDef)
      (Y : Op dE), rhoER.PosSemidef ∧ partialTraceB rhoER = rhoE ∧ Y.PosSemidef ∧
        partialTraceB (petzTranspose rhoER hrhoE Y) ≠ Y := by
  refine ⟨2, 2, maxEntangledOp 2, 1, Matrix.PosDef.one,
    Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ)), maxEntangledOp_posSemidef 2,
    maxEntangledOp_partialTraceB 2, posSemidef_diagonal_single _, ?_⟩
  intro hcontra
  have htr : (Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ))).trace = 1 := by
    rw [Matrix.trace_diagonal]
    simp
  rw [petzTranspose_maxEntangledOp_apply, partialTraceB_smul,
    maxEntangledOp_partialTraceB, htr] at hcontra
  have h11 := congrFun (congrFun hcontra (1 : Fin 2)) (1 : Fin 2)
  simp at h11

end Quantum.Channels

namespace Quantum.Operators

/-! ## Marginal transport is not additive -/

/-- On the maximally entangled reference with `W = 1`, marginal transport is the
`Y^{1/2} ⊗ 1` compression of `Ω`. -/
lemma marginalTransport_maxEntangledOp_eq {m : ℕ} (h : (1 : Op m).PosDef) (Y : Op m) :
    marginalTransport (maxEntangledOp m) h (UnitaryOp.one m) Y
      = Op.tensor (CFC.sqrt Y) (1 : Op m) * maxEntangledOp m
          * Op.tensor (CFC.sqrt Y) (1 : Op m) := by
  have hSY : (CFC.sqrt Y).IsHermitian := (CFC.sqrt_nonneg Y).posSemidef.isHermitian
  rw [marginalTransport_unitaryOne, Matrix.PosDef.inverseSqrt_one h, Matrix.mul_one,
    Op.tensor_conjTranspose, hSY.eq, Matrix.conjTranspose_one]

/-- **Marginal transport is not additive**, hence not a completely positive map.

Every hypothesis of `Quantum.Operators.marginalTransport_posSemidef` and
`Quantum.Operators.marginalTransport_partialTraceB` holds for the witness: the
reference is positive semidefinite with the stated marginal and both inputs are
positive semidefinite rank-one projections.  Additivity still fails, so positivity of
the output together with exactness of the marginal does **not** make the construction
a channel. -/
theorem marginalTransport_not_additive :
    ∃ (dE dR : ℕ) (rhoER : Op (dE * dR)) (rhoE : Op dE) (hrhoE : rhoE.PosDef)
      (W : UnitaryOp dE) (Y₁ Y₂ : Op dE),
      rhoER.PosSemidef ∧ partialTraceB rhoER = rhoE ∧ Y₁.PosSemidef ∧ Y₂.PosSemidef ∧
        marginalTransport rhoER hrhoE W (Y₁ + Y₂) ≠
          marginalTransport rhoER hrhoE W Y₁ + marginalTransport rhoER hrhoE W Y₂ := by
  refine ⟨2, 2, maxEntangledOp 2, 1, Matrix.PosDef.one, UnitaryOp.one 2,
    Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ)),
    Matrix.diagonal (Pi.single (1 : Fin 2) (1 : ℂ)),
    maxEntangledOp_posSemidef 2, maxEntangledOp_partialTraceB 2,
    posSemidef_diagonal_single _, posSemidef_diagonal_single _, ?_⟩
  intro hcontra
  set α : Fin (2 * 2) := finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) with hα
  set β : Fin (2 * 2) := finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)) with hβ
  have hΩ : maxEntangledOp 2 α β = 1 := by
    simp [maxEntangledOp, hα, hβ, Equiv.symm_apply_apply]
  have hcompress : ∀ i : Fin 2,
      marginalTransport (maxEntangledOp 2) (Matrix.PosDef.one (n := Fin 2))
          (UnitaryOp.one 2) (Matrix.diagonal (Pi.single i (1 : ℂ))) α β
        = (Pi.single i (1 : ℂ) : Fin 2 → ℂ) (finProdFinEquiv.symm α).1
            * maxEntangledOp 2 α β
            * (Pi.single i (1 : ℂ) : Fin 2 → ℂ) (finProdFinEquiv.symm β).1 := by
    intro i
    rw [marginalTransport_maxEntangledOp_eq, sqrt_diagonal_single,
      Op.tensor_diagonal_one, diagonal_sandwich_apply]
  have hL : marginalTransport (maxEntangledOp 2) (Matrix.PosDef.one (n := Fin 2))
      (UnitaryOp.one 2) (Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ))
        + Matrix.diagonal (Pi.single (1 : Fin 2) (1 : ℂ))) α β = 1 := by
    rw [diagonal_single_add_two, marginalTransport_maxEntangledOp_eq, CFC.sqrt_one,
      Op.tensor_one, Matrix.one_mul, Matrix.mul_one]
    exact hΩ
  have hR : (marginalTransport (maxEntangledOp 2) (Matrix.PosDef.one (n := Fin 2))
        (UnitaryOp.one 2) (Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℂ)))
      + marginalTransport (maxEntangledOp 2) (Matrix.PosDef.one (n := Fin 2))
        (UnitaryOp.one 2) (Matrix.diagonal (Pi.single (1 : Fin 2) (1 : ℂ)))) α β = 0 := by
    rw [Matrix.add_apply, hcompress 0, hcompress 1, hΩ, hα, hβ]
    simp [Equiv.symm_apply_apply]
  rw [hcontra, hR] at hL
  exact zero_ne_one hL

end Quantum.Operators

end -- noncomputable section
