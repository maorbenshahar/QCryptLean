import QCryptLean.Quantum.Channels.CPTP.PetzMap

/-!
# The Petz transpose map of the partial-trace channel, and its rotated family

Specialize `Quantum.Channels.petzMap` to the partial-trace channel
`Tr_R = Quantum.TensorProducts.partialTraceB : Op (dE * dR) → Op dE`.  Because the
Hilbert–Schmidt adjoint of `Tr_R` is `M ↦ M ⊗ 1_R`
(`Quantum.Channels.krausAdjoint_partialTraceBKraus`), HJPW eq. (8) becomes the closed
formula

`R₀(Y) = ρ_ER^{1/2} · ((ρ_E^{-1/2} Y ρ_E^{-1/2}) ⊗ 1_R) · ρ_ER^{1/2}`

with the reference `ρ_ER` on `E ⊗ R` and `ρ_E` positive definite on `E`.

Conjugating by unitaries `U` on `E` and `V` on `E ⊗ R` gives the *rotated* family of
[Sutter–Fawzi–Renner, arXiv:1504.07251v3](https://arxiv.org/pdf/1504.07251), eq. (6):

`X_B ↦ V_BC ρ_BC^{1/2} (ρ_B^{-1/2} U_B X_B U_B† ρ_B^{-1/2} ⊗ id_C) ρ_BC^{1/2} V_BC†`

(their `B` is our `E`, their `C` is our `R`).  SFR say explicitly that `U = id`,
`V = id` is "sometimes referred to as transpose map or Petz recovery map".  Every
member of the family is a channel; the unitaries are **fixed**, so the family is
linear in the input.  SFR's universality statement (their eq. (11)) averages such
maps over a probability measure with `U` commuting with `ρ_B` and `V` with `ρ_BC`;
that averaging, and their eq. (10) with a general unital trace-preserving inner map,
are not formalized here.

## Main definitions

* `Quantum.Channels.petzTranspose` — the Petz transpose map of `partialTraceB`.
* `Quantum.Channels.petzTransposeRotated` — SFR eq. (6).

## Main statements

* `Quantum.Channels.petzTranspose_apply` — the closed formula above.
* `Quantum.Channels.petzTranspose_posSemidef`,
  `Quantum.Channels.petzTranspose_isHermitian`,
  `Quantum.Channels.petzTranspose_isCompletelyPositive` — positivity for an arbitrary
  reference (`ρ_ER` need not be positive, and no marginal relation is used).
* `Quantum.Channels.petzTranspose_isCPTP` — a channel, under
  `ρ_ER ⪰ 0` and `Tr_R ρ_ER = ρ_E`.
* `Quantum.Channels.petzTranspose_reference` — the recovery identity `R₀(ρ_E) = ρ_ER`.
  It needs only `ρ_ER ⪰ 0` and does **not** assume that `ρ_E` is the `E`-marginal of
  `ρ_ER`, which is why it is named for the *reference* rather than for the marginal
  (compare the general `Quantum.Channels.petzMap_reference`).
  `Quantum.Channels.petzTranspose_apply_partialTraceB` is the same fact in HJPW's
  `T̂ T ρ = ρ` reading, and it is the one that does consume the marginal
  hypothesis.
* `Quantum.Channels.petzTransposeRotated_eq_conj`,
  `Quantum.Channels.petzTransposeRotated_apply`,
  `Quantum.Channels.petzTransposeRotated_unitaryOne`,
  `Quantum.Channels.petzTransposeRotated_isCPTP`,
  `Quantum.Channels.petzTransposeRotated_reference`.

`R₀` is **not** a right inverse of `Tr_R`; see
`Quantum.Channels.petzTranspose_not_marginal_exact` in
`QCryptLean.Quantum.Channels.CPTP.PetzMarginalTransport`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Channels

variable {dE dR : ℕ}

/-! ## The Petz transpose map of `partialTraceB` -/

/-- The **Petz transpose map** of the partial-trace channel `Tr_R` with respect to the
reference `rhoER` on `E ⊗ R` and the positive-definite `rhoE` on `E`.

See `petzTranspose_apply` for the closed formula; `rhoE` is intended to be the
`E`-marginal `Tr_R rhoER`, and that hypothesis is what makes the map a channel. -/
def petzTranspose (rhoER : Op (dE * dR)) {rhoE : Op dE} (hrhoE : rhoE.PosDef) :
    Op dE →ₗ[ℂ] Op (dE * dR) :=
  petzMap (partialTraceBKraus dE dR) rhoER hrhoE

/-- **HJPW eq. (8) for the partial-trace channel**:
`R₀(Y) = ρ_ER^{1/2} · ((ρ_E^{-1/2} Y ρ_E^{-1/2}) ⊗ 1_R) · ρ_ER^{1/2}`. -/
theorem petzTranspose_apply (rhoER : Op (dE * dR)) {rhoE : Op dE} (hrhoE : rhoE.PosDef)
    (Y : Op dE) :
    petzTranspose rhoER hrhoE Y =
      CFC.sqrt rhoER *
          Op.tensor (hrhoE.inverseSqrt * Y * hrhoE.inverseSqrt) (1 : Op dR) *
        CFC.sqrt rhoER := by
  rw [petzTranspose, petzMap_apply, krausAdjoint_partialTraceBKraus]

/-! ## Positivity, for an arbitrary reference -/

lemma petzTranspose_posSemidef (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) {Y : Op dE} (hY : Y.PosSemidef) :
    (petzTranspose rhoER hrhoE Y).PosSemidef :=
  petzMap_posSemidef _ _ _ hY

lemma petzTranspose_isHermitian (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) {Y : Op dE} (hY : Y.IsHermitian) :
    (petzTranspose rhoER hrhoE Y).IsHermitian :=
  petzMap_isHermitian _ _ _ hY

/-- **Genuine complete positivity**, for an arbitrary reference: the Kraus operators
`ρ_ER^{1/2} (1_E ⊗ ⟨k|) ρ_E^{-1/2}` do not depend on the input. -/
theorem petzTranspose_isCompletelyPositive [NeZero dE] [NeZero (dE * dR)]
    (rhoER : Op (dE * dR)) {rhoE : Op dE} (hrhoE : rhoE.PosDef) :
    IsCompletelyPositive ⇑(petzTranspose rhoER hrhoE) :=
  petzMap_isCompletelyPositive _ _ _

/-! ## Trace preservation under the marginal hypothesis -/

/-- The marginal hypothesis in the form the general `petzMap` API consumes. -/
private lemma krausMapFintype_partialTraceBKraus_eq (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hmarg : partialTraceB rhoER = rhoE) :
    krausMapFintype (partialTraceBKraus dE dR) rhoER = rhoE := by
  rw [← hmarg]
  exact congrFun (krausMapFintype_partialTraceBKraus dE dR) rhoER

theorem petzTranspose_isTracePreserving [NeZero dE] [NeZero (dE * dR)]
    (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (hmarg : partialTraceB rhoER = rhoE) :
    IsTracePreserving ⇑(petzTranspose rhoER hrhoE) :=
  petzMap_isTracePreserving hrhoE hrhoER
    (krausMapFintype_partialTraceBKraus_eq rhoER hmarg)

/-- **The Petz transpose map of the partial-trace channel is a channel.** -/
theorem petzTranspose_isCPTP [NeZero dE] [NeZero (dE * dR)]
    (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (hmarg : partialTraceB rhoER = rhoE) :
    IsCPTP ⇑(petzTranspose rhoER hrhoE) :=
  petzMap_isCPTP hrhoE hrhoER (krausMapFintype_partialTraceBKraus_eq rhoER hmarg)

/-! ## The recovery identity -/

/-- **The recovery identity** `R₀(ρ_E) = ρ_ER`.

Only positivity of the reference is needed: the `ρ_E^{-1/2}` factors cancel against
`ρ_E` and `1_E ⊗ 1_R = 1`, so `R₀(ρ_E) = ρ_ER^{1/2} ρ_ER^{1/2} = ρ_ER`.  No marginal
hypothesis and no `NeZero` enter, and in particular `rhoE` is **not** assumed to be
`Tr_R rhoER`: the marginal hypothesis is what makes the map a channel, not what makes
it recover.  This is the partial-trace instance of `petzMap_reference`. -/
theorem petzTranspose_reference (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef)
    {rhoE : Op dE} (hrhoE : rhoE.PosDef) :
    petzTranspose rhoER hrhoE rhoE = rhoER := by
  rw [petzTranspose_apply, hrhoE.inverseSqrt_sandwich_eq_one, Op.tensor_one,
    Matrix.mul_one, CFC.sqrt_mul_sqrt_self rhoER hrhoER.nonneg]

/-- **HJPW `T̂ T ρ = ρ`** for `T = Tr_R`: the Petz transpose map recovers the joint
reference from its own `E`-marginal. -/
theorem petzTranspose_apply_partialTraceB (rhoER : Op (dE * dR))
    (hrhoER : rhoER.PosSemidef) {rhoE : Op dE} (hrhoE : rhoE.PosDef)
    (hmarg : partialTraceB rhoER = rhoE) :
    petzTranspose rhoER hrhoE (partialTraceB rhoER) = rhoER := by
  rw [hmarg, petzTranspose_reference rhoER hrhoER hrhoE]

/-! ## The rotated (Sutter–Fawzi–Renner) family -/

/-- **The rotated Petz family**, SFR eq. (6): conjugate the input by a unitary `U` on
`E` and the output by a unitary `V` on `E ⊗ R`.

`U = 1`, `V = 1` is `petzTranspose` (`petzTransposeRotated_unitaryOne`). -/
def petzTransposeRotated (rhoER : Op (dE * dR)) {rhoE : Op dE} (hrhoE : rhoE.PosDef)
    (U : UnitaryOp dE) (V : UnitaryOp (dE * dR)) : Op dE →ₗ[ℂ] Op (dE * dR) :=
  krausMapFintype fun k =>
    V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp

/-- The rotated family is the Petz map conjugated by the two unitaries. -/
theorem petzTransposeRotated_eq_conj (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (U : UnitaryOp dE) (V : UnitaryOp (dE * dR)) (Y : Op dE) :
    petzTransposeRotated rhoER hrhoE U V Y =
      V.toOp * petzTranspose rhoER hrhoE (U.toOp * Y * U.toOp†) * V.toOp† := by
  change (∑ k, (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)
      * Y * (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)ᴴ) = _
  change _ = V.toOp *
    (∑ k, petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * (U.toOp * Y * U.toOp†)
      * (petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k)ᴴ) * V.toOp†
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **SFR eq. (6)** in closed form. -/
theorem petzTransposeRotated_apply (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (U : UnitaryOp dE) (V : UnitaryOp (dE * dR)) (Y : Op dE) :
    petzTransposeRotated rhoER hrhoE U V Y =
      V.toOp * CFC.sqrt rhoER *
            Op.tensor
              (hrhoE.inverseSqrt * (U.toOp * Y * U.toOp†) * hrhoE.inverseSqrt)
              (1 : Op dR) *
          CFC.sqrt rhoER * V.toOp† := by
  rw [petzTransposeRotated_eq_conj, petzTranspose_apply]
  simp only [Matrix.mul_assoc]

/-- At `U = 1` and `V = 1` the rotated family is the Petz transpose map. -/
@[simp] theorem petzTransposeRotated_unitaryOne (rhoER : Op (dE * dR)) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (Y : Op dE) :
    petzTransposeRotated rhoER hrhoE (UnitaryOp.one dE) (UnitaryOp.one (dE * dR)) Y
      = petzTranspose rhoER hrhoE Y := by
  rw [petzTransposeRotated_eq_conj,
    show (UnitaryOp.one dE).toOp = (1 : Op dE) from rfl,
    show (UnitaryOp.one (dE * dR)).toOp = (1 : Op (dE * dR)) from rfl]
  simp

/-- Kraus completeness of the rotated family: the unitaries cancel. -/
theorem petzTransposeRotated_completeness (rhoER : Op (dE * dR))
    (hrhoER : rhoER.PosSemidef) {rhoE : Op dE} (hrhoE : rhoE.PosDef)
    (hmarg : partialTraceB rhoER = rhoE) (U : UnitaryOp dE) (V : UnitaryOp (dE * dR)) :
    ∑ k, (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)ᴴ *
        (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)
      = 1 := by
  have hstep : ∀ k : Fin dR,
      (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)ᴴ *
          (V.toOp * petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k * U.toOp)
        = U.toOp† * ((petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k)ᴴ *
            petzKraus (partialTraceBKraus dE dR) rhoER hrhoE k) * U.toOp := by
    intro k
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V.toOp† V.toOp, V.unitary_left, Matrix.one_mul]
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.sum_mul, ← Matrix.mul_sum,
    petzKraus_completeness hrhoE hrhoER
      (krausMapFintype_partialTraceBKraus_eq rhoER hmarg),
    Matrix.mul_one, U.unitary_left]

/-- **Every member of the rotated family is a channel.** -/
theorem petzTransposeRotated_isCPTP [NeZero dE] [NeZero (dE * dR)]
    (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef) {rhoE : Op dE}
    (hrhoE : rhoE.PosDef) (hmarg : partialTraceB rhoER = rhoE) (U : UnitaryOp dE)
    (V : UnitaryOp (dE * dR)) :
    IsCPTP ⇑(petzTransposeRotated rhoER hrhoE U V) :=
  krausMapFintype_isCPTP _
    (petzTransposeRotated_completeness rhoER hrhoER hrhoE hmarg U V)

/-- Recovery for the rotated family: the reference is recovered **up to the output
rotation**, from the correspondingly rotated reference `Uᴴ ρ_E U`.

As in `petzTranspose_reference`, `rhoE` is not assumed to be the `E`-marginal of
`rhoER`.  This is why SFR's universal recovery map (their eq. (11)) needs `U` to
commute with `ρ_B` and `V` with `ρ_BC`: only then does the rotated map recover the
same reference as `petzTranspose`. -/
theorem petzTransposeRotated_reference (rhoER : Op (dE * dR)) (hrhoER : rhoER.PosSemidef)
    {rhoE : Op dE} (hrhoE : rhoE.PosDef) (U : UnitaryOp dE)
    (V : UnitaryOp (dE * dR)) :
    petzTransposeRotated rhoER hrhoE U V (U.toOp† * rhoE * U.toOp)
      = V.toOp * rhoER * V.toOp† := by
  rw [petzTransposeRotated_eq_conj]
  have hU : U.toOp * (U.toOp† * rhoE * U.toOp) * U.toOp† = rhoE := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.toOp U.toOp†, U.unitary_right, Matrix.one_mul,
      Matrix.mul_one]
  rw [hU, petzTranspose_reference rhoER hrhoER hrhoE]

end Quantum.Channels

end -- noncomputable section
