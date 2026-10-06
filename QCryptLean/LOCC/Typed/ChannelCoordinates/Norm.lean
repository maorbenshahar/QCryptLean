import QCryptLean.LOCC.Typed.ChannelCoordinates
import QCryptLean.Quantum.Channels.CPTP.Reindex
import QCryptLean.Quantum.Channels.CPTP.DiamondNormReindex
import QCryptLean.Quantum.Channels.CPTP.CKRBound.TightPostselectionBound

/-!
# The diamond norm of a typed finite-register map

Two explicit numeral presentations of one typed-register linear map are conjugate by basis
renumberings (`coordinateLinear_conj_eq`).  Consequently the diamond norm does not depend on the
chosen coordinates (`diamondNorm_coordinateLinear_eq`), and `TypedLOCC.diamondNorm` below is well
defined *without* any coordinate argument: it is the completely bounded trace norm of the map,
computed in the standard enumeration `Fintype.equivFin` and, by `diamondNorm_coordinateLinear`, in
every other explicit numbering as well.  `TypedLOCC.diamondDist` is the induced distance between
two maps. The norm is homogeneous and satisfies the triangle inequality; the normalized
distance between two channels is at most one (`IsChannel.diamondDist_le_one`).

Being completely positive and trace preserving is likewise a coordinate-free property of a typed
map (`IsChannel`, `isChannel_iff_coordinateLinear`), and the two facts combine into the two
contraction principles a composable security interface needs: post-composing a channel changes
neither the reference scope nor the budget
(`IsChannel.diamondNorm_comp_le`, `IsChannel.diamondDist_comp_le`).  A channel has norm exactly
one (`IsChannel.diamondNorm_eq_one`), so `diamondNorm` is not identically zero.

Both registers are assumed nonempty.  That is exactly the hypothesis the numeral diamond norm
`Quantum.Channels.diamondNorm` needs (`NeZero` of both dimensions): an empty register has no
numeral presentation at all.

These are protocol-independent coordinate laws: no protocol, key layout, security notion or
finite-key estimate occurs.
-/

open scoped Matrix BigOperators

noncomputable section

namespace TypedLOCC

/-- An output relabelling in explicit numeral coordinates is again a relabelling. -/
theorem coordinateLinear_reindexOp {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {dA dB : ℕ}
    (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (V : A ≃ B) :
    coordinateLinear eA eB (reindexOp V) =
      (Matrix.reindexLinearEquiv ℂ ℂ (eA.symm.trans (V.trans eB))
        (eA.symm.trans (V.trans eB))).toLinearMap := by
  apply LinearMap.ext
  intro M
  ext i j
  rfl

/-- A structural register relabelling is a channel in any explicit finite coordinates. -/
theorem coordinateLinear_reindexOp_isCPTP {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (V : A ≃ B) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eA eB (reindexOp V)) := by
  rw [coordinateLinear_reindexOp]
  exact Quantum.Channels.reindexLinearEquiv_isCPTP _

/-- **Two explicit finite coordinate presentations of one and the same typed-register linear map
are conjugate by basis renumberings.**  This is the single structural identity behind both the
coordinate independence of the diamond norm and the coordinate independence of the CPTP
property. -/
theorem coordinateLinear_conj_eq {alpha beta : Type}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    {dA dA' dB dB' : ℕ}
    (eA : alpha ≃ Fin dA) (eA' : alpha ≃ Fin dA')
    (eB : beta ≃ Fin dB) (eB' : beta ≃ Fin dB')
    (Phi : TypedLOCC.Op alpha →ₗ[ℂ] TypedLOCC.Op beta) :
    coordinateLinear eA' eB' Phi =
      ((Matrix.reindexLinearEquiv ℂ ℂ (eB.symm.trans eB')
              (eB.symm.trans eB')).toLinearMap.comp
            (coordinateLinear eA eB Phi)).comp
        (Matrix.reindexLinearEquiv ℂ ℂ (eA'.symm.trans eA)
          (eA'.symm.trans eA)).toLinearMap := by
  have hcomp : ((eA' : alpha → Fin dA') ∘ (eA.symm : Fin dA → alpha)) ∘
      (eA : alpha → Fin dA) = (eA' : alpha → Fin dA') := by
    funext x
    simp
  apply LinearMap.ext
  intro rho
  ext i j
  simp [coordinateLinear, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, hcomp]

/-- **Two explicit finite coordinate presentations of one and the same typed-register linear map
have the same diamond norm.**  Only basis renumberings relate them, and
`Quantum.Channels.diamondNorm_reindex_conj_eq` is hypothesis-free. -/
theorem diamondNorm_coordinateLinear_eq {alpha beta : Type}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    {dA dA' dB dB' : ℕ} [NeZero dA] [NeZero dA'] [NeZero dB] [NeZero dB']
    (eA : alpha ≃ Fin dA) (eA' : alpha ≃ Fin dA')
    (eB : beta ≃ Fin dB) (eB' : beta ≃ Fin dB')
    (Phi : TypedLOCC.Op alpha →ₗ[ℂ] TypedLOCC.Op beta) :
    Quantum.Channels.diamondNorm (coordinateLinear eA' eB' Phi) =
      Quantum.Channels.diamondNorm (coordinateLinear eA eB Phi) := by
  rw [coordinateLinear_conj_eq eA eA' eB eB']
  exact Quantum.Channels.diamondNorm_reindex_conj_eq _ _ _

/-- **Being completely positive and trace preserving does not depend on the numbering.**  The two
presentations differ by pre- and post-composition with basis renumberings, which are channels. -/
theorem isCPTP_coordinateLinear_congr {alpha beta : Type}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    {dA dA' dB dB' : ℕ} [NeZero dA] [NeZero dA'] [NeZero dB] [NeZero dB']
    (eA : alpha ≃ Fin dA) (eA' : alpha ≃ Fin dA')
    (eB : beta ≃ Fin dB) (eB' : beta ≃ Fin dB')
    (Phi : TypedLOCC.Op alpha →ₗ[ℂ] TypedLOCC.Op beta)
    (h : Quantum.Channels.IsCPTP ⇑(coordinateLinear eA eB Phi)) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eA' eB' Phi) := by
  rw [coordinateLinear_conj_eq eA eA' eB eB']
  simp only [LinearMap.coe_comp]
  exact Quantum.Channels.cptp_comp _ _
    (Quantum.Channels.cptp_comp _ _
      (Quantum.Channels.reindexLinearEquiv_isCPTP (eB.symm.trans eB')) h)
    (Quantum.Channels.reindexLinearEquiv_isCPTP (eA'.symm.trans eA))

/-! ## The coordinate-free norm and distance -/

variable {alpha beta : Type} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
  [Fintype beta] [DecidableEq beta] [Nonempty beta]

/-- **The diamond norm of a typed finite-register linear map.**

This is the completely bounded trace norm `Quantum.Channels.diamondNorm` of the map, read in the
standard enumeration of the two registers.  The choice of enumeration is immaterial: by
`diamondNorm_coordinateLinear` every explicit numbering gives this same value. -/
noncomputable def diamondNorm (Phi : Op alpha →ₗ[ℂ] Op beta) : ℝ :=
  Quantum.Channels.diamondNorm
    (coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin beta) Phi)

/-- **Every explicit numeral presentation of a typed map computes its diamond norm.**

This is the bridge between the coordinate-free norm and the numeral channel API: a low-level
estimate proved for one coordinate package is an estimate for the typed map itself. -/
theorem diamondNorm_coordinateLinear {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (eA : alpha ≃ Fin dA) (eB : beta ≃ Fin dB) (Phi : Op alpha →ₗ[ℂ] Op beta) :
    Quantum.Channels.diamondNorm (coordinateLinear eA eB Phi) = diamondNorm Phi :=
  diamondNorm_coordinateLinear_eq (Fintype.equivFin alpha) eA (Fintype.equivFin beta) eB Phi

/-- The diamond norm is nonnegative. -/
theorem diamondNorm_nonneg (Phi : Op alpha →ₗ[ℂ] Op beta) : 0 ≤ diamondNorm Phi :=
  Quantum.Channels.diamondNorm_nonneg _

/-- The zero map has zero diamond norm. -/
@[simp] theorem diamondNorm_zero : diamondNorm (0 : Op alpha →ₗ[ℂ] Op beta) = 0 := by
  simp only [diamondNorm, coordinateLinear, LinearMap.zero_comp, LinearMap.comp_zero,
    Quantum.Channels.diamondNorm_zero]

/-- The diamond norm satisfies the triangle inequality. -/
theorem diamondNorm_add_le (Phi Psi : Op alpha →ₗ[ℂ] Op beta) :
    diamondNorm (Phi + Psi) ≤ diamondNorm Phi + diamondNorm Psi := by
  simpa only [diamondNorm, coordinateLinear, LinearMap.add_comp, LinearMap.comp_add] using
    Quantum.Channels.diamondNorm_add_le
      (coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin beta) Phi)
      (coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin beta) Psi)

/-- Scalar multiplication scales the diamond norm by the complex norm of the scalar. -/
@[simp] theorem diamondNorm_smul (c : ℂ) (Phi : Op alpha →ₗ[ℂ] Op beta) :
    diamondNorm (c • Phi) = ‖c‖ * diamondNorm Phi := by
  simp only [diamondNorm, coordinateLinear, LinearMap.smul_comp, LinearMap.comp_smul,
    Quantum.Channels.diamondNorm_smul]

/-- Negation preserves the diamond norm. -/
@[simp] theorem diamondNorm_neg (Phi : Op alpha →ₗ[ℂ] Op beta) :
    diamondNorm (-Phi) = diamondNorm Phi := by
  simp only [diamondNorm, coordinateLinear, LinearMap.neg_comp, LinearMap.comp_neg,
    Quantum.Channels.diamondNorm_neg]

/-- The diamond norm of a difference is at most the sum of the diamond norms. -/
theorem diamondNorm_sub_le (Phi Psi : Op alpha →ₗ[ℂ] Op beta) :
    diamondNorm (Phi - Psi) ≤ diamondNorm Phi + diamondNorm Psi := by
  simpa only [sub_eq_add_neg, diamondNorm_neg] using diamondNorm_add_le Phi (-Psi)

/-- The normalized diamond distance: half the diamond norm of the difference. -/
noncomputable def diamondDist (Phi Psi : Op alpha →ₗ[ℂ] Op beta) : ℝ :=
  (1 / 2) * diamondNorm (Phi - Psi)

/-- The diamond distance is half the diamond norm of the difference, by definition. -/
theorem diamondDist_eq_half_diamondNorm_sub (Phi Psi : Op alpha →ₗ[ℂ] Op beta) :
    diamondDist Phi Psi = (1 / 2) * diamondNorm (Phi - Psi) := rfl

/-- The diamond distance is nonnegative. -/
theorem diamondDist_nonneg (Phi Psi : Op alpha →ₗ[ℂ] Op beta) : 0 ≤ diamondDist Phi Psi :=
  mul_nonneg (by norm_num) (diamondNorm_nonneg _)

/-- A map is at diamond distance zero from itself. -/
@[simp] theorem diamondDist_self (Phi : Op alpha →ₗ[ℂ] Op beta) : diamondDist Phi Phi = 0 := by
  simp [diamondDist]

/-- The diamond distance is symmetric. -/
theorem diamondDist_comm (Phi Psi : Op alpha →ₗ[ℂ] Op beta) :
    diamondDist Phi Psi = diamondDist Psi Phi := by
  unfold diamondDist
  rw [← neg_sub Psi Phi, diamondNorm_neg]

/-- The diamond distance satisfies the triangle inequality. -/
theorem diamondDist_triangle (Phi Psi Chi : Op alpha →ₗ[ℂ] Op beta) :
    diamondDist Phi Chi ≤ diamondDist Phi Psi + diamondDist Psi Chi := by
  have h := diamondNorm_add_le (Phi - Psi) (Psi - Chi)
  simp only [sub_add_sub_cancel] at h
  unfold diamondDist
  linarith

/-- Explicit numeral coordinates compute the diamond distance as well. -/
theorem diamondDist_coordinateLinear {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (eA : alpha ≃ Fin dA) (eB : beta ≃ Fin dB) (Phi Psi : Op alpha →ₗ[ℂ] Op beta) :
    (1 / 2) * Quantum.Channels.diamondNorm
        (coordinateLinear eA eB Phi - coordinateLinear eA eB Psi) = diamondDist Phi Psi := by
  rw [← coordinateLinear_sub, diamondNorm_coordinateLinear, diamondDist]

/-! ## Typed channels and the contraction principles -/

/-- **A typed finite-register linear map is a channel** when it is completely positive and trace
preserving in the standard enumeration of its two registers.

By `isChannel_iff_coordinateLinear` this is equivalent to being CPTP in *every* explicit
numbering, so the notion carries no coordinate convention.  The existing typed CPTP facts are all
stated for arbitrary numberings and therefore give this predicate directly. -/
def IsChannel (Phi : Op alpha →ₗ[ℂ] Op beta) : Prop :=
  Quantum.Channels.IsCPTP
    ⇑(coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin beta) Phi)

/-- Being a channel is exactly being CPTP in any one explicit numbering. -/
theorem isChannel_iff_coordinateLinear {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (eA : alpha ≃ Fin dA) (eB : beta ≃ Fin dB) (Phi : Op alpha →ₗ[ℂ] Op beta) :
    IsChannel Phi ↔ Quantum.Channels.IsCPTP ⇑(coordinateLinear eA eB Phi) :=
  ⟨fun h => isCPTP_coordinateLinear_congr _ eA _ eB Phi h,
    fun h => isCPTP_coordinateLinear_congr eA _ eB _ Phi h⟩

/-- A structural register relabelling is a channel. -/
theorem isChannel_reindexOp (V : alpha ≃ beta) : IsChannel (reindexOp V) :=
  coordinateLinear_reindexOp_isCPTP _ _ V

/-- **A channel has diamond norm exactly one.**  In particular `diamondNorm` is not identically
zero, so a bound `diamondDist real ideal ≤ epsilon` is not a statement about a constant. -/
theorem IsChannel.diamondNorm_eq_one {Phi : Op alpha →ₗ[ℂ] Op beta} (h : IsChannel Phi) :
    diamondNorm Phi = 1 :=
  Quantum.Channels.diamondNorm_cptp_eq_one _ h

/-- The distance between channels is the supremum of the output trace distances over joint
input states with a reference register of the input dimension, in any finite coordinates. -/
theorem IsChannel.diamondDist_eq_sSup_traceDistance
    {Phi Psi : Op alpha →ₗ[ℂ] Op beta} (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (eA : alpha ≃ Fin dA) (eB : beta ≃ Fin dB) :
    diamondDist Phi Psi = sSup (Set.range fun ρ : Quantum.Operators.DensityOp (dA * dA) =>
      Quantum.Metrics.traceDistance
        (Quantum.Channels.mapTensorId (coordinateLinear eA eB Phi) ρ.toOp)
        (Quantum.Channels.mapTensorId (coordinateLinear eA eB Psi) ρ.toOp)) := by
  have hPhi' := (isChannel_iff_coordinateLinear eA eB Phi).mp hPhi
  have hPsi' := (isChannel_iff_coordinateLinear eA eB Psi).mp hPsi
  let Δ := coordinateLinear eA eB Phi - coordinateLinear eA eB Psi
  let f (ρ : Quantum.Operators.DensityOp (dA * dA)) : ℝ :=
    (1 / 2) * Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ ρ.toOp)
  have hΔ : ∀ M, Δ M.conjTranspose = (Δ M).conjTranspose := by
    intro M
    simp only [Δ, LinearMap.sub_apply, Matrix.conjTranspose_sub,
      Quantum.Channels.cptp_preserves_conjTranspose _ hPhi',
      Quantum.Channels.cptp_preserves_conjTranspose _ hPsi']
  have hbound (ρ : Quantum.Operators.DensityOp (dA * dA)) :
      f ρ ≤ (1 / 2) * Quantum.Channels.diamondNorm Δ :=
    mul_le_mul_of_nonneg_left (Quantum.Channels.traceNorm_mapTensorId_le_diamondNorm_pinned
      Δ ρ.toOp (le_of_eq (Quantum.Channels.traceNorm_densityOp_eq_one ρ))) (by norm_num)
  have hbdd : BddAbove (Set.range f) := ⟨_, fun _ ⟨ρ, hρ⟩ => hρ ▸ hbound ρ⟩
  have hne : (Set.range f).Nonempty :=
    ⟨_, Set.mem_range_self (Quantum.Operators.DensityOp.maxMixed (dA * dA))⟩
  have hnonneg : 0 ≤ sSup (Set.range f) := le_csSup_of_le hbdd
    (Set.mem_range_self (Quantum.Operators.DensityOp.maxMixed (dA * dA)))
    (mul_nonneg (by norm_num) (Quantum.Metrics.traceNorm_nonneg _))
  have hnorm := QKD.BB84.Engine.diamondNorm_le_of_density_bound Δ hΔ
    (2 * sSup (Set.range f)) (by positivity) (fun ρ => by
      have h := le_csSup hbdd (Set.mem_range_self ρ)
      dsimp only [f] at h
      linarith)
  have heq : (1 / 2) * Quantum.Channels.diamondNorm Δ = sSup (Set.range f) :=
    le_antisymm (by linarith) (csSup_le hne (fun _ ⟨ρ, hρ⟩ => hρ ▸ hbound ρ))
  rw [← diamondDist_coordinateLinear eA eB]
  simpa only [f, Δ, Quantum.Metrics.traceDistance,
    Quantum.Channels.mapTensorId_linearMap_sub] using heq

/-- The normalized diamond distance between two channels is at most one. -/
theorem IsChannel.diamondDist_le_one {Phi Psi : Op alpha →ₗ[ℂ] Op beta}
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) : diamondDist Phi Psi ≤ 1 := by
  have h := diamondNorm_sub_le Phi Psi
  rw [hPhi.diamondNorm_eq_one, hPsi.diamondNorm_eq_one] at h
  unfold diamondDist
  linarith

variable {gamma : Type} [Fintype gamma] [DecidableEq gamma] [Nonempty gamma]

/-- **Post-composing a channel cannot increase the diamond norm.**  This is the typed form of
`Quantum.Channels.diamondNorm_postcomp_cptp_le`: the estimate is made at the outer supremum's own
ancilla, so no reference system is fixed and no constant is lost. -/
theorem IsChannel.diamondNorm_comp_le {Psi : Op beta →ₗ[ℂ] Op gamma} (h : IsChannel Psi)
    (Phi : Op alpha →ₗ[ℂ] Op beta) :
    diamondNorm (Psi.comp Phi) ≤ diamondNorm Phi := by
  rw [← diamondNorm_coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin gamma)
      (Psi.comp Phi),
    ← diamondNorm_coordinateLinear (Fintype.equivFin alpha) (Fintype.equivFin beta) Phi,
    coordinateLinear_comp (Fintype.equivFin alpha) (Fintype.equivFin beta)
      (Fintype.equivFin gamma) Phi Psi]
  exact Quantum.Channels.diamondNorm_postcomp_cptp_le _ h _

/-- **A common channel postprocessing cannot increase the diamond distance.**  A real/ideal pair
followed by one and the same channel obeys the same normalized budget, with no simulator and no
change of reference scope. -/
theorem IsChannel.diamondDist_comp_le {Psi : Op beta →ₗ[ℂ] Op gamma} (h : IsChannel Psi)
    (Phi Phi' : Op alpha →ₗ[ℂ] Op beta) :
    diamondDist (Psi.comp Phi) (Psi.comp Phi') ≤ diamondDist Phi Phi' := by
  rw [diamondDist_eq_half_diamondNorm_sub, diamondDist_eq_half_diamondNorm_sub,
    ← LinearMap.comp_sub]
  exact mul_le_mul_of_nonneg_left (h.diamondNorm_comp_le _) (by norm_num)

end TypedLOCC
