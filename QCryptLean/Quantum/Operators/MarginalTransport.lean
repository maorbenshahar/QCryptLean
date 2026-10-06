import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.MatrixSqrt

/-!
# Marginal transport of a bipartite operator

Let `ρ_ER` be a positive-semidefinite operator on `E ⊗ R` whose `E`-marginal
`ρ_E = Tr_R ρ_ER` is positive definite.  For a target `Y ⪰ 0` on `E` and a unitary
`W` on `E` put

`Φ(Y) = (Y^{1/2} · W · ρ_E^{-1/2} ⊗ 1_R) · ρ_ER · (Y^{1/2} · W · ρ_E^{-1/2} ⊗ 1_R)†`.

This is *marginal transport*: `Φ(Y)` is positive semidefinite and its `E`-marginal is
exactly `Y`, for every unitary `W` (`marginalTransport_partialTraceB`).  It is the
standard way to move a bipartite operator onto a prescribed marginal while keeping the
correlations of `ρ_ER`.

## This is not a quantum channel

`Y^{1/2}` occurs on **both** sides of the fixed operator `ρ_ER`, so the "Kraus
operator" `Y^{1/2} W ρ_E^{-1/2}` depends on the input.  `Φ` is positively homogeneous
of degree one (`marginalTransport_real_smul`) but **not additive**: an explicit
counterexample on a correlated reference is
`Quantum.Operators.marginalTransport_not_additive` in
`QCryptLean.Quantum.Channels.CPTP.PetzMarginalTransport`.  In particular `Φ`
is not a completely positive map and is not physically implementable as a channel,
even though every output is positive and has the requested marginal.

The genuinely linear recovery map for the partial-trace channel is the Petz transpose
map `Quantum.Channels.petzTranspose`, and its rotated (Sutter–Fawzi–Renner) family
`Quantum.Channels.petzTransposeRotated`; neither of those is marginal exact.  The two
constructions are compared in
`QCryptLean.Quantum.Channels.CPTP.PetzMarginalTransport`.

## Main definitions

* `Quantum.Operators.marginalTransport`

## Main statements

* `Quantum.Operators.marginalTransport_posSemidef`
* `Quantum.Operators.marginalTransport_partialTraceB` — marginal exactness
* `Quantum.Operators.marginalTransport_real_smul` — positive homogeneity
* `Quantum.Operators.marginalTransport_unitaryOne` — the `W = 1` form
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

variable {dE dR : ℕ}

/-- The `E`-side transport operator `Y^{1/2} · W · ρ_E^{-1/2}` of marginal transport. -/
def marginalTransportOp {rhoE : Op dE} (hrhoE : rhoE.PosDef) (W : UnitaryOp dE)
    (Y : Op dE) : Op dE :=
  CFC.sqrt Y * W.toOp * hrhoE.inverseSqrt

/-- **Marginal transport.**  Moves the bipartite operator `rhoER` onto the prescribed
`E`-marginal `Y`, using the Uhlmann freedom `W` on `E`:

`Φ(Y) = (Y^{1/2} W ρ_E^{-1/2} ⊗ 1_R) · rhoER · (Y^{1/2} W ρ_E^{-1/2} ⊗ 1_R)†`.

This is **not** linear in `Y`; see the module docstring. -/
def marginalTransport (rhoER : Op (dE * dR)) {rhoE : Op dE} (hrhoE : rhoE.PosDef)
    (W : UnitaryOp dE) (Y : Op dE) : Op (dE * dR) :=
  Op.tensor (marginalTransportOp hrhoE W Y) (1 : Op dR) * rhoER *
    (Op.tensor (marginalTransportOp hrhoE W Y) (1 : Op dR))†

/-- The `W = 1` form: transport by the plain `Y^{1/2} ρ_E^{-1/2}` intertwiner. -/
lemma marginalTransport_unitaryOne (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (Y : Op dE) :
    marginalTransport rhoER hrhoE (UnitaryOp.one dE) Y
      = Op.tensor (CFC.sqrt Y * hrhoE.inverseSqrt) (1 : Op dR) * rhoER *
        (Op.tensor (CFC.sqrt Y * hrhoE.inverseSqrt) (1 : Op dR))† := by
  rw [marginalTransport, marginalTransportOp,
    show (UnitaryOp.one dE).toOp = (1 : Op dE) from rfl, Matrix.mul_one]

@[simp] lemma marginalTransport_zero (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (W : UnitaryOp dE) :
    marginalTransport rhoER hrhoE W (0 : Op dE) = 0 := by
  rw [marginalTransport, marginalTransportOp, CFC.sqrt_zero, Matrix.zero_mul,
    Matrix.zero_mul, Op.tensor_zero_left, Matrix.zero_mul, Matrix.zero_mul]

/-- Marginal transport of a positive-semidefinite reference is positive semidefinite,
for every target `Y` and every unitary `W`. -/
lemma marginalTransport_posSemidef (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef)
    {rhoE : Op dE} (hrhoE : rhoE.PosDef) (W : UnitaryOp dE) (Y : Op dE) :
    (marginalTransport rhoER hrhoE W Y).PosSemidef :=
  hrhoER.mul_mul_conjTranspose_same _

/-- **Marginal exactness.**  For every unitary `W` and every positive-semidefinite `Y`,
the transported operator has `E`-marginal exactly `Y`.

The unitary drops out because it acts on `E` only and `W Wᴴ = 1`; the two
`ρ_E^{-1/2}` factors are absorbed by the marginal hypothesis. -/
theorem marginalTransport_partialTraceB (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (W : UnitaryOp dE) {Y : Op dE} (hY : Y.PosSemidef)
    (hmarg : partialTraceB rhoER = rhoE) :
    partialTraceB (marginalTransport rhoER hrhoE W Y) = Y := by
  set L : Op dE := marginalTransportOp hrhoE W Y with hL
  have hSY : (CFC.sqrt Y).IsHermitian := (CFC.sqrt_nonneg Y).posSemidef.isHermitian
  have hSinv : hrhoE.inverseSqrt.IsHermitian := hrhoE.inverseSqrt_isHermitian
  have hLdag : (Op.tensor L (1 : Op dR))† = Op.tensor L.conjTranspose (1 : Op dR) := by
    rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one]
  rw [marginalTransport, ← hL, hLdag,
    partialTraceB_sandwich_tensor_one L L.conjTranspose rhoER, hmarg]
  have hLdag' : L.conjTranspose
      = hrhoE.inverseSqrt * W.toOp.conjTranspose * CFC.sqrt Y := by
    rw [hL, marginalTransportOp, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hSinv.eq, hSY.eq, Matrix.mul_assoc]
  rw [hLdag', hL, marginalTransportOp]
  calc CFC.sqrt Y * W.toOp * hrhoE.inverseSqrt * rhoE
          * (hrhoE.inverseSqrt * W.toOp.conjTranspose * CFC.sqrt Y)
      = CFC.sqrt Y * W.toOp * (hrhoE.inverseSqrt * rhoE * hrhoE.inverseSqrt)
          * W.toOp.conjTranspose * CFC.sqrt Y := by
        simp only [Matrix.mul_assoc]
    _ = CFC.sqrt Y * (W.toOp * W.toOp.conjTranspose) * CFC.sqrt Y := by
        rw [hrhoE.inverseSqrt_sandwich_eq_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = CFC.sqrt Y * CFC.sqrt Y := by rw [W.unitary_right, Matrix.mul_one]
    _ = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg

/-- **Positive homogeneity of degree one.**  Marginal transport commutes with
multiplication of the target by a nonnegative real scalar.  Together with
`Quantum.Operators.marginalTransport_not_additive` this is the precise sense in which
the construction is nonlinear: homogeneous, but not additive. -/
lemma marginalTransport_real_smul (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (W : UnitaryOp dE) {c : ℝ} (hc : 0 ≤ c) {Y : Op dE}
    (hY : Y.PosSemidef) :
    marginalTransport rhoER hrhoE W ((c : ℂ) • Y)
      = (c : ℂ) • marginalTransport rhoER hrhoE W Y := by
  have hs : marginalTransportOp hrhoE W ((c : ℂ) • Y)
      = ((Real.sqrt c : ℝ) : ℂ) • marginalTransportOp hrhoE W Y := by
    rw [marginalTransportOp, marginalTransportOp, sqrt_ofReal_smul hc hY,
      Matrix.smul_mul, Matrix.smul_mul]
  rw [marginalTransport, marginalTransport, hs, Op.tensor_smul_left,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

end Quantum.Operators

end -- noncomputable section
