import QCryptLean.InfoTheory.QuantumLHL.CollisionBlockRef

/-!
# Discharging the support hypothesis of the collision-route LHL entry, explicitly

`seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized` (`CollisionBlockRef.lean`) — the
consumer-shaped packaging of the collision leftover-hash bound at a γ-regularised announced
reference — carries the factorisation obligation

`hfac : ∀ x, ρ_x = ν_{ann x}^{1/4} · B x · ν_{ann x}^{1/4}`.

That hypothesis is **not** decoration.  It is the checkable form of "`ρ_x` lies in the support of
its
own reference block", and `weightedFrobeniusSq_mix_smul_one_le` — the γ-comparison it ultimately
feeds — is *false* without it at a singular block. This file supplies the witness as
an **explicit definition** — never `Classical.choose` — together with everything a consumer needs to
apply the entry without carrying `hfac` at all.

## What the consumer actually needs of `B`

**Nothing beyond the factorisation.**  In
`seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized` the witness enters as a bare
`(Bfac : X → Op dE)` constrained only by `hfac`, and it does not occur in the conclusion.  Following
it down: `collisionQuantity_tensorLeftKernel_blockDiagRefRegularized_le` passes it straight to
`weightedFrobeniusSq_blockFamilyRegularized_le`, which passes it to
`weightedFrobeniusSq_mix_smul_one_le`, where `B` is used only inside the two sandwiches `P₀ B P₀`
and
`C B C`; the sandwiched-norm step `sandwich_frobenius_le` reads nothing about its middle factor.  So
no positivity, no trace bound and no norm bound on `B` is required, and none is proved here.

## The witness

`collisionRootFactor σ A = σ^{−1/4} · A · σ^{−1/4}`, with Lean's `CFC.rpow` pseudo-power convention
`0 ^ y = 0`, so the definition also makes sense (and is the right one) at a singular `σ`.

* `collisionRootFactor_spec_of_supportProj` — the general statement: the witness factors `A`
  **iff** `A` is fixed by the support projector `σ^{1/4} σ^{−1/4}` on both sides.  Pure
  associativity;
  no positivity is used, and the two hypotheses are exactly the support condition, written in the
  same
  pseudo-power form the weighted square uses.
* `collisionRootFactor_spec_of_posDef` — at a **positive definite** `σ` the support projector is `1`
  (`CFC.rpow_mul_rpow_neg`), so the witness factors *every* `A`, with no side condition.

## Positive definite regularised references

The collision consumer needs a positive definite reference anyway
(`seedKeyExtractor_traceDistanceGen_le_collisionRoot`), which is why the announced reference is
assembled through `blockDiagRefRegularized`.  `blockFamilyRegularized_posDef` records that the
γ-regularised *blocks* are individually positive definite for every `0 < γ ≤ 1` — the per-block
sibling of `blockDiagRefRegularized_posDef`.  Feeding the entry the **regularised** family therefore
discharges `hfac` unconditionally
(`seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized_of_posDef`),
and it costs nothing, because regularising twice is regularising once:

`blockDiagRefRegularized (blockFamilyRegularized ν γ₀) γ = blockDiagRefRegularized ν (γ + γ₀ −
γ·γ₀)`

exactly, as operators (`blockDiagRefRegularized_blockFamilyRegularized_toOp`).  The reference the
`γ₀`-instantiation is scored against **is** the regularised reference, at effective parameter
`Γ = 1 − (1−γ)(1−γ₀)`. The original family may be singular, so `hfac` remains necessary.
Applying the entry to an already regularized family discharges this obligation.

At a singular `σ`, the witness reconstructs `P A P`, where `P` is the support projector.
This need not equal a generic `A`; the support hypothesis is essential for the γ-comparison.

References: Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:6889` `\label{rem:Htworewr}` (the
collision quantity), `:7080` `\label{thm:pa}` (the privacy-amplification theorem that consumes it);
Bhatia, *Matrix Analysis*, Springer GTM 169, §IV.2 (the sandwiched-norm inequality
`weightedFrobeniusSq_mix_smul_one_le` specialises).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-! ## The explicit witness -/

/-- **The explicit fourth-root factor** `σ^{−1/4} · A · σ^{−1/4}`.

This is the witness the collision-route support hypothesis
`A = σ^{1/4} · B · σ^{1/4}` asks for.  It is a definition, not a choice function: at a positive
definite `σ` it factors every `A` (`collisionRootFactor_spec_of_posDef`), and at a singular `σ` it
factors exactly the `A` supported by `σ` (`collisionRootFactor_spec_of_supportProj`), with Lean's
`CFC.rpow` pseudo-power convention `0 ^ y = 0` doing the truncation. -/
def collisionRootFactor {d : ℕ} (σ A : Op d) : Op d :=
  σ ^ (-1 / 4 : ℝ) * A * σ ^ (-1 / 4 : ℝ)

/-- **The witness factors `A` exactly when `A` is fixed by the support projector.**

`σ^{1/4} σ^{−1/4}` is the projector onto the support of `σ` (the pseudo-power convention kills the
kernel), and

`σ^{1/4} · (σ^{−1/4} A σ^{−1/4}) · σ^{1/4} = (σ^{1/4} σ^{−1/4}) · A · (σ^{−1/4} σ^{1/4})`

by associativity alone.  So the two support identities `P A = A` and `A P = A` are precisely what
turns the explicit witness into a factorisation — no positivity, no spectral theory. -/
theorem collisionRootFactor_spec_of_supportProj {d : ℕ} (σ A : Op d)
    (hL : σ ^ (1 / 4 : ℝ) * σ ^ (-1 / 4 : ℝ) * A = A)
    (hR : A * (σ ^ (-1 / 4 : ℝ) * σ ^ (1 / 4 : ℝ)) = A) :
    A = σ ^ (1 / 4 : ℝ) * collisionRootFactor σ A * σ ^ (1 / 4 : ℝ) := by
  have h : σ ^ (1 / 4 : ℝ) * collisionRootFactor σ A * σ ^ (1 / 4 : ℝ)
      = (σ ^ (1 / 4 : ℝ) * σ ^ (-1 / 4 : ℝ) * A) * (σ ^ (-1 / 4 : ℝ) * σ ^ (1 / 4 : ℝ)) := by
    rw [collisionRootFactor]
    simp only [Matrix.mul_assoc]
  rw [h, hL, hR]

/-- At a positive definite `σ` the support projector is the identity: `σ^{1/4} σ^{−1/4} = 1`
(`CFC.rpow_mul_rpow_neg`, using `Matrix.PosDef.isStrictlyPositive`). -/
theorem rpow_quarter_mul_rpow_neg_quarter {d : ℕ} {σ : Op d} (hσ : σ.PosDef) :
    σ ^ (1 / 4 : ℝ) * σ ^ (-1 / 4 : ℝ) = 1 := by
  have h := CFC.rpow_mul_rpow_neg (a := σ) (1 / 4 : ℝ) hσ.isStrictlyPositive
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num]
  exact h

/-- The other order, by finite-dimensional invertibility (`mul_eq_one_comm`). -/
theorem rpow_neg_quarter_mul_rpow_quarter {d : ℕ} {σ : Op d} (hσ : σ.PosDef) :
    σ ^ (-1 / 4 : ℝ) * σ ^ (1 / 4 : ℝ) = 1 :=
  mul_eq_one_comm.mp (rpow_quarter_mul_rpow_neg_quarter hσ)

/-- **At a positive definite reference the support hypothesis is free.**

`A = σ^{1/4} · (σ^{−1/4} A σ^{−1/4}) · σ^{1/4}` for *every* `A`, with no side condition: the two
support identities of `collisionRootFactor_spec_of_supportProj` collapse to `1 * A = A` and
`A * 1 = A`. -/
theorem collisionRootFactor_spec_of_posDef {d : ℕ} {σ : Op d} (hσ : σ.PosDef) (A : Op d) :
    A = σ ^ (1 / 4 : ℝ) * collisionRootFactor σ A * σ ^ (1 / 4 : ℝ) :=
  collisionRootFactor_spec_of_supportProj σ A
    (by rw [rpow_quarter_mul_rpow_neg_quarter hσ, Matrix.one_mul])
    (by rw [rpow_neg_quarter_mul_rpow_quarter hσ, Matrix.mul_one])

/-! ## The γ-regularised blocks are positive definite, one by one -/

/-- **Each γ-regularised block is positive definite** for `0 < γ ≤ 1`, with least eigenvalue at
least
`γ/(d_C·d_E)`.

The per-block sibling of `blockDiagRefRegularized_posDef` (which states the same for the *assembled*
reference `Σ_p |p⟩⟨p| ⊗ ν^γ_p`).  `blockFamilyRegularized ν γ p = (1−γ)·ν_p + (γ/d_C)·maxMixed_E` is
a
positive semidefinite operator plus a strictly positive multiple of the identity. -/
theorem blockFamilyRegularized_posDef {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (p : Fin dC) :
    (blockFamilyRegularized ν γ hγ0.le hγ1 p).toOp.PosDef := by
  have hmm : (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp
      = (1 / (dE : ℂ)) • (1 : Op dE) := rfl
  have hdC : (0 : ℝ) < (dC : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dC)
  have hdE : (0 : ℝ) < (dE : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dE)
  rw [blockFamilyRegularized_toOp, hmm, smul_smul]
  refine Matrix.PosDef.posSemidef_add ?_ ?_
  · exact (posSemidefOp_implies_mathlib (ν p).toPosSemidefOp).smul
      (Complex.zero_le_real.mpr (sub_nonneg.mpr hγ1))
  · refine Matrix.PosDef.smul Matrix.PosDef.one ?_
    have hval : ((γ / (dC : ℝ) : ℝ) : ℂ) * (1 / (dE : ℂ))
        = ((γ / ((dC : ℝ) * (dE : ℝ)) : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [hval]
    exact_mod_cast Complex.zero_lt_real.mpr
      (by positivity : (0 : ℝ) < γ / ((dC : ℝ) * (dE : ℝ)))

/-- **Regularising twice is regularising once.**

`blockDiagRefRegularized (blockFamilyRegularized ν γ₀) γ = blockDiagRefRegularized ν (γ + γ₀ −
γ·γ₀)`,
an operator identity: both sides are `(1−Γ)·blockDiagRefOp ν + (Γ/(d_C·d_E))·1` with
`1 − Γ = (1−γ)(1−γ₀)` (`blockDiagRefOp_blockFamilyRegularized_eq`, applied three times).

This is what makes the positive-definite instantiation below free of charge: handing the collision
entry the already-regularised family does **not** move the reference off the live object — it moves
its regularisation parameter from `γ` to `Γ = 1 − (1−γ)(1−γ₀)`, and nothing else. -/
theorem blockDiagRefRegularized_blockFamilyRegularized_toOp {dE dC : ℕ} [NeZero dE] [NeZero dC]
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1)
    (γ₀ : ℝ) (hγ₀0 : 0 ≤ γ₀) (hγ₀1 : γ₀ ≤ 1) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (blockDiagRefRegularized (blockFamilyRegularized ν γ₀ hγ₀0 hγ₀1)
        (sum_blockFamilyRegularized_trace_le_one ν hν γ₀ hγ₀0 hγ₀1) γ hγ0 hγ1).toOp
      = (blockDiagRefRegularized ν hν (γ + γ₀ - γ * γ₀) (by nlinarith) (by nlinarith)).toOp := by
  rw [blockDiagRefRegularized_toOp, blockDiagRefRegularized_toOp,
    blockDiagRefOp_blockFamilyRegularized_eq, blockDiagRefOp_blockFamilyRegularized_eq,
    blockDiagRefOp_blockFamilyRegularized_eq, smul_add, smul_smul, smul_smul, add_assoc,
    ← add_smul]
  congr 2
  · push_cast
    ring
  · push_cast
    ring

/-! ## The collision entry, with the support hypothesis discharged -/

/-- **(A5, `hfac`-free) The consumer-shaped collision bound at a positive definite block family.**

`seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized` with its factorisation obligation
discharged by the explicit witness `collisionRootFactor`, which needs no side condition once the
blocks are positive definite (`collisionRootFactor_spec_of_posDef`).

The state `ρ` is arbitrary because the supplied block family is positive definite. The general
entry also permits singular original blocks, for which `hfac` remains necessary. Instantiating `ν`
with a `γ₀`-regularized family discharges this condition;
`blockDiagRefRegularized_blockFamilyRegularized_toOp` identifies the assembled reference with the
original family’s regularization at `1 − (1−γ)(1−γ₀)`. -/
theorem seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized_of_posDef
    {S X Z : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    [Fintype X] [Fintype Z] [Nonempty Z] [DecidableEq Z]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star)
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hνpd : ∀ p, (ν p).toOp.PosDef)
    (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (hν1 : ∑ p : Fin dC, (ν p).trace = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H (ρ.tensorLeftKernel K)).toJointDensity.toOp
        (seedUniformOutputState (S := S)
          (ρ.tensorLeftKernel K).quantumMarginal).toJointDensity.toOp
      ≤ (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * ((1 - γ)⁻¹
            * ∑ x : X, weightedFrobeniusSq (ν (ann x)).toOp ((ρ.stateMap x).toOp))) :=
  seedKeyExtractor_traceDistanceGen_le_blockDiagRefRegularized h2 ρ ann K hK ν hν hν1 γ hγ0 hγ1
    (fun x => collisionRootFactor (ν (ann x)).toOp ((ρ.stateMap x).toOp))
    (fun x => collisionRootFactor_spec_of_posDef (hνpd (ann x)) ((ρ.stateMap x).toOp))

end InfoTheory.QuantumLHL

end -- noncomputable section
