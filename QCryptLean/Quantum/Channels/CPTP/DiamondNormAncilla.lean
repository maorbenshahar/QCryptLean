import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.Quantum.Metrics.KitaevWatrousAncilla

/-!
# Diamond norm — arbitrary ancilla, and invariance under an output dimension cast

`Quantum.Channels.diamondNorm` (`CPTP/DiamondNorm.lean`) is defined as a supremum over inputs
`X : Op (dIn * dIn)` — i.e. with the ancilla register pinned to the *input* dimension. Two
consequences of that definition are collected here.

* `traceNorm_mapTensorId_le_diamondNorm` — the diamond norm dominates `‖(Δ ⊗ id_k)(ρ)‖₁` for a
  density operator `ρ` on `dIn ⊗ k` with an **arbitrary** ancilla dimension `k`, not only for
  `k = dIn`. This is the completely-bounded content of the definition: an ancilla of the input
  dimension already realises the worst case. The proof is the standard purification argument in
  the form the library already carries: the marginal `Tr_k ρ` is purified into a *square*-ancilla
  pure state `Ψ` on `dIn ⊗ dIn` (`InfoTheory.DeFinetti.purificationDensityOp`), whose marginal
  equals `Tr_k ρ`, and the substate-extraction engine
  `traceNorm_mapTensorId_substate_bound` then gives
  `‖(Δ ⊗ id_k)(ρ)‖₁ ≤ ‖(Δ ⊗ id_{dIn})(Ψ)‖₁` at dominance factor `α = 1`; `Ψ` is admissible in the
  defining supremum because `‖Ψ‖₁ = 1`.
  It strengthens `diamondNorm_ge_traceNorm_apply`, which is the
  ancilla-free case `‖Δ(ρ)‖₁ ≤ ‖Δ‖_◇`.

* `traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving` — the same domination for an
  **arbitrary** `W` of trace norm at most `1`, not only for a density operator, provided `Δ` is
  Hermitian-preserving. This is the diamond norm's completely-bounded reading in full: the
  supremum in the definition of `diamondNorm` ranges over all `‖X‖₁ ≤ 1` but at the pinned ancilla
  `dIn`, and this statement removes the pin. The proof is Kitaev–Watrous at a free ancilla
  (`Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction_ancilla`), whose PSD hypothesis at the
  square ancilla is immediate from the defining supremum because a positive semidefinite operator
  of trace at most `1` has trace norm at most `1`.

  The two statements are incomparable: this one drops the density-operator restriction and pays a
  Hermitian-preservation hypothesis; `traceNorm_mapTensorId_le_diamondNorm` needs no hypothesis on
  `Δ` at all.

* `diamondNorm_castDimLinear_comp` — post-composing with a dimension cast `Op.castDimLinear h`
  (a relabelling of the output register along a `Nat` identity `h`) leaves the diamond norm
  unchanged.

The register shape is written `dIn = d ^ n` because that is the shape
`InfoTheory.DeFinetti.purificationDensityOp` is stated at; it is the shape of every register these
bounds are used on (`(d_A d_B)^n` for an `n`-round protocol).

Both statements are register-generic and protocol-agnostic.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **The diamond norm dominates the trace norm at an arbitrary ancilla.** For every linear map
`Δ : Op (d^n) →ₗ[ℂ] Op dimOut`, every ancilla dimension `k` and every density operator `ρ` on
`d^n ⊗ k`,

`‖(Δ ⊗ id_k)(ρ)‖₁ ≤ ‖Δ‖_◇`.

`diamondNorm` pins the ancilla of its defining supremum to the input dimension `d^n`; this lemma
says nothing is lost by that choice. The arbitrary ancilla `k` is folded into the square-ancilla
purification `Ψ` of `ρ`'s own marginal `Tr_k ρ`: the two marginals are equal, so the substate
dominance holds at factor `α = 1`, and `traceNorm_mapTensorId_substate_bound` transports the
trace norm from `ρ` to `Ψ`. `Ψ` is a
density operator on `d^n ⊗ d^n`, hence has trace norm `1` and is admissible in the supremum. -/
theorem traceNorm_mapTensorId_le_diamondNorm {d n dimOut k : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut] [NeZero k] [NeZero (d ^ n)]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) (ρ : DensityOp (d ^ n * k)) :
    traceNorm (mapTensorId Δ ρ.toOp) ≤ diamondNorm Δ := by
  have : NeZero (d ^ n * d ^ n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (dimOut * d ^ n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  set Ψ : DensityOp (d ^ n * d ^ n) := purificationDensityOp ρ.partialTraceB with hΨ_def
  have hΨ_pure : Ψ.IsPure := purificationDensityOp_isPure _
  have hΨ_marg : Ψ.partialTraceB = ρ.partialTraceB := purificationDensityOp_partialTraceB _
  -- The marginals agree, so the substate dominance holds with factor `α = 1`.
  have hdom : (((1 : ℝ) : ℂ) • Ψ.partialTraceB.toOp - partialTraceB ρ.toOp).PosSemidef := by
    have hpt : Ψ.partialTraceB.toOp = partialTraceB ρ.toOp := by rw [hΨ_marg]; rfl
    rw [Complex.ofReal_one, one_smul, hpt, sub_self]
    exact Matrix.PosSemidef.zero
  have step1 : traceNorm (mapTensorId Δ ρ.toOp) ≤ 1 * traceNorm (mapTensorId Δ Ψ.toOp) :=
    traceNorm_mapTensorId_substate_bound Δ ρ.toOp
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) Ψ hΨ_pure 1 one_pos hdom
  have step2 : traceNorm (mapTensorId Δ Ψ.toOp) ≤ diamondNorm Δ := by
    unfold diamondNorm
    exact le_csSup (diamondNorm_bddAbove Δ)
      ⟨Ψ.toOp, le_of_eq (traceNorm_densityOp_eq_one Ψ), rfl⟩
  linarith

/-- **The diamond norm dominates the trace norm at an arbitrary ancilla and an arbitrary
trace-class input**, for a Hermitian-preserving map. For every linear map
`Δ : Op dIn →ₗ[ℂ] Op dOut` with `Δ(M†) = Δ(M)†`, every ancilla dimension `k` and every
`W : Op (dIn * k)` with `‖W‖₁ ≤ 1`,

`‖(Δ ⊗ id_k)(W)‖₁ ≤ ‖Δ‖_◇`.

`diamondNorm Δ` is the supremum of `‖(Δ ⊗ id)(X)‖₁` over all `X` of trace norm at most `1`, at the
ancilla pinned to `dIn`. This lemma says the pin costs nothing: the same supremum is attained
already at `k = dIn`.

The proof is `Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction_ancilla` at `B = ‖Δ‖_◇`. Its
hypothesis is the bound at the *square* ancilla for positive semidefinite inputs of trace at most
`1`, and that is immediate from the definition: such an input has trace norm equal to its trace, so
it is admissible in the defining supremum. Hermitian preservation is where it is spent — it is what
makes the Hermitianizing dilation inside the Kitaev–Watrous argument lossless. -/
theorem traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving {dIn dOut k : ℕ}
    [NeZero dIn] [NeZero dOut] [NeZero k]
    (Δ : Op dIn →ₗ[ℂ] Op dOut)
    (hHP : ∀ M : Op dIn, Δ M.conjTranspose = (Δ M).conjTranspose)
    (W : Op (dIn * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId Δ W) ≤ diamondNorm Δ := by
  have : NeZero (dIn * dIn) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (dOut * dIn) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  refine Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction_ancilla Δ (diamondNorm Δ)
    (diamondNorm_nonneg Δ) hHP (fun ρ hρ htr => ?_) W hW
  have hρ_tn : traceNorm ρ ≤ 1 := by
    rw [traceNorm_posSemidef_eq_trace ρ hρ]; exact htr
  unfold diamondNorm
  exact le_csSup (diamondNorm_bddAbove Δ) ⟨ρ, hρ_tn, rfl⟩

/-- **The diamond norm does not see an output dimension cast.** `Op.castDimLinear h` relabels the
output register along a `Nat` identity `h : d = e`, so post-composing with it changes neither the
inputs the defining supremum ranges over nor any trace norm in it. -/
theorem diamondNorm_castDimLinear_comp {A d e : ℕ} [NeZero A] [NeZero d] [NeZero e]
    (h : d = e) (Δ : Op A →ₗ[ℂ] Op d) :
    diamondNorm ((Op.castDimLinear h) ∘ₗ Δ) = diamondNorm Δ := by
  subst h
  have hid : (Op.castDimLinear (rfl : d = d)) ∘ₗ Δ = Δ := by
    refine LinearMap.ext fun M => ?_
    simp [Op.castDimLinear, Op.castDim]
  rw [hid]

end Quantum.Channels

end
