import QCryptLean.QKD.BB84.TailOutput

/-!
# The complete output of the BB84 program

After the measurement and public-selection prefix of `program`, the public control is
`ω : Sampling.RawControl N`. The continuation has output boundary `completeContinuationBoundary`
at that exit: the classical-tail boundary when `ω` meets every quota (`Sampling.HasQuotas`), and
the key-free abort leaf otherwise. This module describes the complete output space
`(boundary …).space` over both branches.

* **Success.**  `successCompleteOutputEmbedding` prefixes the literal exit
  `Measurement.lateSelectionExit … ω` to a classical-tail output `RawClassicalTailOutput`.  It
  preserves the complete exit (`successExitMap`), the accept/abort disposition, the ordered accepted
  keys and the residual coordinates; `successCompleteOutputHom` packages it as a morphism of key
  layouts.  Its range is exactly the fibre over that exit
  (`mem_range_successCompleteOutputEmbedding_iff`, `graftSpaceEquiv_symm_success_fibre`).
* **Shortage.**  `shortageCompleteOutput` keeps the raw control at its outer exit, has abort
  disposition and carries the `Unit`/`Unit` payload, and it is the only complete output over a
  shortage exit (`graftSpaceEquiv_symm_shortage_fibre`).

These coordinate maps and laws are this library's. Finite-round LOCC instruments are described by
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II. Pfister et al.,
arXiv:1506.07502v3, Section IV, Protocol 3, Step 5', likewise aborts when fixed-round quotas cannot
be met, and their Appendix C analyzes the sifting outputs and the abort probability; this is
context for the shortage branch, not an identity for these coordinates.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC QKD.BB84 TypedLOCC.TwoParty

/-- At the literal late-selection exit of a raw control that meets every quota, the complete
continuation boundary is the raw classical-tail boundary
(`completeContinuationBoundary_of_hasQuotas` states this at an arbitrary exit). -/
theorem completeContinuationBoundary_success
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC :=
  QKD.BB84.completeContinuationBoundary_of_hasQuotas N nK mZ mX ℓ ℓEV leakEC _ (by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω from
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω)

/-- At the literal late-selection exit of a raw control with a quota shortage, the complete
continuation boundary is the key-free abort leaf (`completeContinuationBoundary_of_shortage`
states this at an arbitrary exit). -/
theorem completeContinuationBoundary_shortage
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      .leaf Measurement.lateSelectionAbortSystem :=
  QKD.BB84.completeContinuationBoundary_of_shortage N nK mZ mX ℓ ℓEV leakEC _ (by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω from
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω)

/-- At the literal successful late-selection exit, the continuation layout is the raw
classical-tail layout transported along `completeContinuationBoundary_success`. -/
theorem completeContinuationOutputLayout_success
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX ω) =
      QKD.OutputLayout.transport
        (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC ω hω).symm
        (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC) := by
  have hquota : Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω)) := by
    rw [show QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) = ω
      from (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact hω
  unfold QKD.BB84.completeContinuationOutputLayout
  rw [dite_eq_left hquota]

/-- Identifies the raw classical-tail output space with the continuation space at a
successful late-selection exit. -/
def successContinuationSpaceEquiv
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega) :
    RawClassicalTailOutput
        (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC ≃
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit
          N nK mZ mX omega)).space :=
  Equiv.cast
    (congrArg Boundary.space
      (completeContinuationBoundary_success
        N nK mZ mX ell ellEV leakEC omega homega).symm)

/-- The outer public exit of `lateSelectionAbortAt` is the literal exit determined by the same
raw control. -/
private theorem lateSelectionAbortAt_exit
    (N nK mZ mX : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 =
      Measurement.lateSelectionExit N nK mZ mX ω := by
  apply (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).injective
  calc
    QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 = ω := by
      rcases ω with ⟨a, b, order⟩
      rfl
    _ = QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX ω) :=
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv ω).symm

/-- Prefix one successful raw control to a complete raw classical-tail output.  The construction is
choice-free: it uses the literal late-selection exit, the success boundary equality, and the
inverse outer graft-space equivalence. -/
def successCompleteOutputEmbedding
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC ↪
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space where
  toFun q :=
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)).symm
        ⟨Measurement.lateSelectionExit N nK mZ mX ω,
          Equiv.cast (congrArg Boundary.space
            (completeContinuationBoundary_success
              N nK mZ mX ℓ ℓEV leakEC ω hω).symm) q⟩
  inj' := by
    intro q r hqr
    have hpair := congrArg
      (Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)) hqr
    simp only [Equiv.apply_symm_apply] at hpair
    exact (Equiv.cast (congrArg Boundary.space
      (completeContinuationBoundary_success
        N nK mZ mX ℓ ℓEV leakEC ω hω).symm)).injective
          (eq_of_heq (Sigma.mk.inj_iff.mp hpair).2)

/-- Applying the outer graft equivalence to a successful embedded tail returns the literal public
exit and the explicit success-child coordinate.  This is the implementation form of the successful
public-tree branch; the structural protocol context is Chitambar et al., arXiv:1210.4583, §II. -/
theorem graftSpaceEquiv_successCompleteOutputEmbedding
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (q : RawClassicalTailOutput
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary
          N nK mZ mX ell ellEV leakEC)
        (successCompleteOutputEmbedding
          N nK mZ mX ell ellEV leakEC omega homega q) =
      ⟨Measurement.lateSelectionExit N nK mZ mX omega,
        successContinuationSpaceEquiv
          N nK mZ mX ell ellEV leakEC omega homega q⟩ := by
  exact Equiv.apply_symm_apply _ _

/-- The inverse graft map on the literal successful fibre is exactly the successful complete-output
embedding after the explicit child-space transport.  This is an implementation coordinate
identity. -/
theorem graftSpaceEquiv_symm_success_fibre
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (c :
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit
          N nK mZ mX omega)).space) :
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC)).symm
        ⟨Measurement.lateSelectionExit N nK mZ mX omega, c⟩ =
      successCompleteOutputEmbedding
        N nK mZ mX ell ellEV leakEC omega homega
        ((successContinuationSpaceEquiv
          N nK mZ mX ell ellEV leakEC omega homega).symm c) := by
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary
      N nK mZ mX ell ellEV leakEC)
  apply G.injective
  rw [G.apply_symm_apply,
    graftSpaceEquiv_successCompleteOutputEmbedding]
  rw [(successContinuationSpaceEquiv
    N nK mZ mX ell ellEV leakEC omega homega).apply_symm_apply]

/-- An ambient complete output lies in the successful embedding precisely when its outer public exit
is the literal exit for that raw control.  This is the implementation range characterization of the
successful fixed-quota public-tree fibre, not a reachability statement. -/
theorem mem_range_successCompleteOutputEmbedding_iff
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : Sampling.RawControl N)
    (homega : Sampling.HasQuotas nK mZ mX omega)
    (y :
      (QKD.BB84.boundary
        N nK mZ mX ell ellEV leakEC).space) :
    y ∈ Set.range
        (successCompleteOutputEmbedding
          N nK mZ mX ell ellEV leakEC omega homega) ↔
      (Boundary.graftSpaceEquiv
        (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary
          N nK mZ mX ell ellEV leakEC) y).1 =
        Measurement.lateSelectionExit N nK mZ mX omega := by
  constructor
  · rintro ⟨q, rfl⟩
    exact congrArg Sigma.fst
      (graftSpaceEquiv_successCompleteOutputEmbedding
        N nK mZ mX ell ellEV leakEC omega homega q)
  · intro hy
    let G := Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ell ellEV leakEC)
    let E := successContinuationSpaceEquiv
      N nK mZ mX ell ellEV leakEC omega homega
    rcases hGy : G y with ⟨e, c⟩
    have he : e = Measurement.lateSelectionExit N nK mZ mX omega := by
      change (G y).1 = Measurement.lateSelectionExit N nK mZ mX omega at hy
      exact (congrArg Sigma.fst hGy).symm.trans hy
    subst e
    refine ⟨E.symm c, ?_⟩
    rw [← graftSpaceEquiv_symm_success_fibre
      N nK mZ mX ell ellEV leakEC omega homega c]
    apply G.injective
    rw [G.apply_symm_apply, hGy]

/-- Prefix one successful raw control to a complete raw classical-tail exit. -/
def successExitMap
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).Exit →
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit :=
  fun e =>
    (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm
      ⟨Measurement.lateSelectionExit N nK mZ mX ω,
        Equiv.cast (congrArg Boundary.Exit
          (completeContinuationBoundary_success
            N nK mZ mX ℓ ℓEV leakEC ω hω).symm) e⟩

/-- The successful complete-exit prefix map is injective. -/
theorem successExitMap_injective
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    Function.Injective
      (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω) := by
  intro e f hef
  have hpair := congrArg
    (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC) hef
  simp only [successExitMap, Equiv.apply_symm_apply] at hpair
  exact (Equiv.cast (congrArg Boundary.Exit
    (completeContinuationBoundary_success
      N nK mZ mX ℓ ℓEV leakEC ω hω).symm)).injective
        (eq_of_heq (Sigma.mk.inj_iff.mp hpair).2)

/-- The complete exit of the successful point embedding is the literal prefixed exit. -/
theorem successCompleteOutputEmbedding_exit
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1 =
      successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω q.1 := by
  have cast_graft_exit (B : Boundary Party) (C : B.Exit → Boundary Party)
      {D : Boundary Party} (e : B.Exit) (h : D = C e) (r : D.space) :
      ((Boundary.graftSpaceEquiv B C).symm
        ⟨e, Equiv.cast (congrArg Boundary.space h) r⟩).1 =
        (Boundary.graftExitEquiv B C).symm
          ⟨e, Equiv.cast (congrArg Boundary.Exit h) r.1⟩ := by
    subst D
    exact Boundary.graftSpaceEquiv_symm_fst B C e r
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let e := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  have hspec := cast_graft_exit B C e h q
  delta successCompleteOutputEmbedding successExitMap QKD.BB84.exitEquiv
  delta QKD.BB84.boundary
  with_reducible_and_instances exact hspec

/-- Prefixing a successful raw control preserves the actual output disposition. -/
theorem successExitMap_disposition
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) =
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).disposition e := by
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let g := Boundary.graftExitEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
  delta QKD.BB84.outputLayout successExitMap QKD.BB84.exitEquiv
  delta QKD.BB84.boundary QKD.OutputLayout.graftFixedParties
  with_reducible_and_instances
    change (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (g (g.symm ⟨outer, Equiv.cast (congrArg Boundary.Exit h) e⟩)).1).disposition
          (g (g.symm ⟨outer, Equiv.cast (congrArg Boundary.Exit h) e⟩)).2 = _
  rw [g.apply_symm_apply]
  rw [show QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC outer =
      QKD.OutputLayout.transport h (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX)
        ℓ ℓEV (@Sampling.packedPESel nK mZ mX) leakEC) from
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω]
  exact QKD.OutputLayout.transport_disposition h _ e

/-- On an accepting raw classical-tail point, the successful complete-output embedding preserves
Alice's and Bob's key coordinates in that order.  The target acceptance proof is derived from
the source acceptance proof through `successExitMap_disposition`. -/
theorem successCompleteOutputEmbedding_acceptedKeys
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (haccept :
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).disposition q.1 = .accept ℓ) :
    let V := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω
    let L := (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout
    let R := (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
    let htarget : L.disposition (V q).1 = .accept ℓ := by
      change (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (V q).1 = .accept ℓ
      rw [successCompleteOutputEmbedding_exit]
      rw [successExitMap_disposition]
      exact haccept
    ((L.acceptCoordinates htarget (V q).2).1,
      (L.acceptCoordinates htarget (V q).2).2.1) =
      ((R.acceptCoordinates haccept q.2).1,
        (R.acceptCoordinates haccept q.2).2.1) := by
  have accepted_pair {B₁ B₂ : Boundary Party}
      (L₁ : QKD.OutputLayout B₁) (L₂ : QKD.OutputLayout B₂)
      (x : B₁.space) (y : B₂.space)
      (h₁ : L₁.disposition x.1 = .accept ℓ)
      (h₂ : L₂.disposition y.1 = .accept ℓ)
      (hk : (L₁.coordinates x.1 x.2).1 ≍ (L₂.coordinates y.1 y.2).1 ∧
        (L₁.coordinates x.1 x.2).2.1 ≍ (L₂.coordinates y.1 y.2).2.1) :
      ((L₁.toBoundaryKeyLayout.acceptCoordinates h₁ x.2).1,
        (L₁.toBoundaryKeyLayout.acceptCoordinates h₁ x.2).2.1) =
      ((L₂.toBoundaryKeyLayout.acceptCoordinates h₂ y.2).1,
        (L₂.toBoundaryKeyLayout.acceptCoordinates h₂ y.2).2.1) := by
    apply Prod.ext
    · exact BoundaryKeyLayout.acceptCoordinates_fst_eq_of_coordinates_fst_heq
        L₁.toBoundaryKeyLayout L₂.toBoundaryKeyLayout h₁ h₂ x.2 y.2 hk.1
    · exact BoundaryKeyLayout.acceptCoordinates_snd_fst_eq_of_coordinates_snd_fst_heq
        L₁.toBoundaryKeyLayout L₂.toBoundaryKeyLayout h₁ h₂ x.2 y.2 hk.2
  have transport_keys {B C : Boundary Party} (h : B = C)
      (L : QKD.OutputLayout B) (r : B.space) :
      let x := Equiv.cast (congrArg Boundary.space h) r
      ((QKD.OutputLayout.transport h L).coordinates x.1 x.2).1 ≍
          (L.coordinates r.1 r.2).1 ∧
        ((QKD.OutputLayout.transport h L).coordinates x.1 x.2).2.1 ≍
          (L.coordinates r.1 r.2).2.1 := by
    cases h
    exact ⟨HEq.rfl, HEq.rfl⟩
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let qc := Equiv.cast (congrArg Boundary.space h) q
  have hLc : Lc outer = QKD.OutputLayout.transport h R :=
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω
  have hc := transport_keys h R q
  rw [← hLc] at hc
  have hp : successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q =
      (Boundary.graftSpaceEquiv B C).symm ⟨outer, qc⟩ := by
    delta successCompleteOutputEmbedding QKD.BB84.boundary
    with_reducible_and_instances rfl
  have hg := QKD.OutputLayout.graftFixedParties_coordinates_keys_heq B C Lc .alice .bob
    (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer qc
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q) hp
  let L := QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC
  let x := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q
  have htarget : L.disposition x.1 = .accept ℓ := by
    change (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
      (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1 = _
    rw [successCompleteOutputEmbedding_exit, successExitMap_disposition]
    exact haccept
  have hk :
      ((QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2).1 ≍
          (R.coordinates q.1 q.2).1 ∧
      ((QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2).2.1 ≍
          (R.coordinates q.1 q.2).2.1 := by
    delta QKD.BB84.outputLayout
    delta QKD.BB84.boundary
    with_reducible_and_instances exact ⟨hg.1.trans hc.1, hg.2.trans hc.2⟩
  with_reducible_and_instances
    exact accepted_pair L R x q htarget haccept hk

/-- The raw-tail and complete actual residual types agree at the explicit successful exit map.
This is the well-typedness law for the residual-coordinate embedding; it is a named obligation,
not a caller premise. -/
theorem successExitMap_residual_type
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.Residual e =
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV
        leakEC).toBoundaryKeyLayout.Residual
          (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) := by
  have cast_graft_residual (B : Boundary Party) (C : B.Exit → Boundary Party)
      (L : ∀ e, QKD.OutputLayout (C e)) (a b : Party) (hab : a ≠ b)
      (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
      {D : Boundary Party} (e : B.Exit) (h : D = C e) (R : QKD.OutputLayout D)
      (hL : L e = QKD.OutputLayout.transport h R) (f : D.Exit) :
      R.Residual f =
        (QKD.OutputLayout.graftFixedParties a b hab L hA hB).Residual
          ((Boundary.graftExitEquiv B C).symm
            ⟨e, Equiv.cast (congrArg Boundary.Exit h) f⟩) := by
    subst D
    exact (congrArg (fun M : QKD.OutputLayout (C e) => M.Residual f) hL).symm.trans
      (QKD.OutputLayout.graftFixedParties_residual B C L a b hab hA hB e f).symm
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success
    N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  have hLc : Lc outer = QKD.OutputLayout.transport h R :=
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω
  have hspec := cast_graft_residual B C Lc .alice .bob (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer h R hLc e
  delta QKD.OutputLayout.toBoundaryKeyLayout QKD.BB84.outputLayout
  delta successExitMap QKD.BB84.exitEquiv QKD.BB84.boundary
  with_reducible_and_instances exact hspec

/-- The explicit residual-coordinate embedding at one successful raw classical-tail exit.  It
depends only on the raw control, source exit, and source residual; it does not inspect either key
or a complete source output. -/
def successResidualEmbedding
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (e : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.Residual e ↪
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV
        leakEC).toBoundaryKeyLayout.Residual
          (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω e) :=
  (Equiv.cast (successExitMap_residual_type
    N nK mZ mX ℓ ℓEV leakEC ω hω e)).toEmbedding

/-- The residual read from the embedded point is the image of the raw residual under the explicit
residual-coordinate map, at the same complete actual exit. -/
theorem successCompleteOutputEmbedding_residual
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    let V := successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω
    let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC
    let L := QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC
    let hexit : (V q).1 = successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω q.1 :=
      successCompleteOutputEmbedding_exit N nK mZ mX ℓ ℓEV leakEC ω hω q
    successResidualEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q.1
        (R.coordinates q.1 q.2).2.2 =
      Equiv.cast (congrArg L.toBoundaryKeyLayout.Residual hexit)
        (L.coordinates (V q).1 (V q).2).2.2 := by
  apply (Equiv.cast (successExitMap_residual_type
    N nK mZ mX ℓ ℓEV leakEC ω hω q.1)).symm.injective
  apply Prod.ext
  · apply Prod.ext <;> exact Unit.ext _ _
  · funext i
    rcases i with ⟨⟨p, hp⟩, hpb⟩
    cases p with
    | alice => exact (hp rfl).elim
    | bob => exact (hpb (Subtype.ext rfl)).elim

/-- The complete output layout reads, at a successfully embedded tail, exactly the output
coordinates of the raw classical tail. -/
theorem successCompleteOutputEmbedding_coordinates_heq
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω)
    (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).coordinates
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).1
        (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q).2 ≍
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).coordinates q.1 q.2 := by
  let B := Measurement.lateSelectionBoundary N nK mZ mX
  let C := QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
  let Lc := QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
  let R := QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) leakEC
  let outer := Measurement.lateSelectionExit N nK mZ mX ω
  let h := (completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC ω hω).symm
  let qc := Equiv.cast (congrArg Boundary.space h) q
  have hc := QKD.OutputLayout.transport_coordinates_heq h R q
  rw [← show Lc outer = QKD.OutputLayout.transport h R from
    completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω hω] at hc
  have hp : successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q =
      (Boundary.graftSpaceEquiv B C).symm ⟨outer, qc⟩ := by
    delta successCompleteOutputEmbedding QKD.BB84.boundary
    with_reducible_and_instances rfl
  have hg := QKD.OutputLayout.graftFixedParties_coordinates_heq B C Lc .alice .bob (by decide)
    (QKD.BB84.completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (QKD.BB84.completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) outer qc
    (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω q) hp
  delta QKD.BB84.outputLayout
  delta QKD.BB84.boundary
  with_reducible_and_instances exact hg.trans hc

/-- **The successful complete-output embedding is a morphism of key layouts** from the raw
classical tail to the complete output.  Its exit renaming is `successExitMap`, and the complete
layout has the disposition, residual type and coordinates of the raw classical tail on its
image. -/
def successCompleteOutputHom
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    BoundaryKeyLayout.Hom
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).toBoundaryKeyLayout :=
  BoundaryKeyLayout.Hom.ofHEq (successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap_injective N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successCompleteOutputEmbedding_exit N nK mZ mX ℓ ℓEV leakEC ω hω)
    (successExitMap_disposition N nK mZ mX ℓ ℓEV leakEC ω hω)
    (fun e => (successExitMap_residual_type N nK mZ mX ℓ ℓEV leakEC ω hω e).symm)
    (successCompleteOutputEmbedding_coordinates_heq N nK mZ mX ℓ ℓEV leakEC ω hω)

@[simp] theorem coe_successCompleteOutputHom
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : Sampling.HasQuotas nK mZ mX ω) :
    ⇑(successCompleteOutputHom N nK mZ mX ℓ ℓEV leakEC ω hω) =
      ⇑(successCompleteOutputEmbedding N nK mZ mX ℓ ℓEV leakEC ω hω) :=
  rfl

/-- The metadata-bearing complete output for a quota shortage.  Its outer exit is read from the
actual `lateSelectionAbortAt` point, while its child coordinate is the unique Unit/Unit abort
payload. -/
def shortageCompleteOutput
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space :=
  let outer := Measurement.lateSelectionAbortAt N nK mZ mX ω hω
  let houter := lateSelectionAbortAt_exit N nK mZ mX ω hω
  let hchild : QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC outer.1 =
      .leaf Measurement.lateSelectionAbortSystem := by
    rw [houter]
    exact completeContinuationBoundary_shortage N nK mZ mX ℓ ℓEV leakEC ω hω
  (Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)).symm
      ⟨outer.1,
        Equiv.cast (congrArg Boundary.space hchild.symm)
          ((Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).symm
            ((TwoParty.pairEquiv Unit Unit).symm ((), ())))⟩

/-- The shortage complete output recovers the original raw control at its outer public exit. -/
theorem shortageCompleteOutput_rawControl
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC)
          (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1).1 =
      ω := by
  have recover (B : Boundary Party) (C : B.Exit → Boundary Party)
      {T : Type} (f : B.Exit → T) (z : Σ e : B.Exit, (C e).space)
      (t : T) (hz : f z.1 = t) :
      f ((Boundary.graftExitEquiv B C
        ((Boundary.graftSpaceEquiv B C).symm z).1).1) = t := by
    rw [← Boundary.graftSpaceEquiv_fst, Equiv.apply_symm_apply]
    exact hz
  have hlast : QKD.BB84.lateSelectionExitEquiv N nK mZ mX
      (Measurement.lateSelectionAbortAt N nK mZ mX ω hω).1 = ω := by
    rw [lateSelectionAbortAt_exit]
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω
  delta shortageCompleteOutput QKD.BB84.exitEquiv QKD.BB84.boundary
  with_reducible_and_instances
    exact recover (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX) _ ω hlast

/-- The actual complete-output disposition at the metadata-bearing shortage point is abort. -/
theorem shortageCompleteOutput_disposition
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) (ω : Sampling.RawControl N)
    (hω : ¬Sampling.HasQuotas nK mZ mX ω) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
        (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1 = .abort := by
  have graft_disposition (B : Boundary Party) (C : B.Exit → Boundary Party)
      (L : ∀ e, QKD.OutputLayout (C e)) (a b : Party) (hab : a ≠ b)
      (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b)
      (e : (B.graft C).Exit) :
      (QKD.OutputLayout.graftFixedParties a b hab L hA hB).disposition e =
        (L (Boundary.graftExitEquiv B C e).1).disposition
          (Boundary.graftExitEquiv B C e).2 := by
    rfl
  have hshort : ¬Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC)
          (shortageCompleteOutput N nK mZ mX ℓ ℓEV leakEC ω hω).1).1) := by
    rw [shortageCompleteOutput_rawControl]
    exact hω
  delta QKD.BB84.exitEquiv at hshort
  delta QKD.BB84.outputLayout
  refine (graft_disposition (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC) .alice .bob
    (by decide) _ _ _).trans ?_
  unfold QKD.BB84.completeContinuationOutputLayout
  split
  · rename_i hquota
    exact (hshort hquota).elim
  · have transport_disposition {B C : Boundary Party} (h : B = C)
        (L : QKD.OutputLayout B) (x : C.Exit) :
        (QKD.OutputLayout.transport h L).disposition x =
          L.disposition (h.symm ▸ x) := by
      cases h
      rfl
    rw [transport_disposition]
    rfl

section ShortageFibre

open QKD.BB84.Measurement QKD.BB84.Sampling

/-- Every point over a fixed shortage exit is the literal metadata-bearing shortage output. -/
theorem graftSpaceEquiv_symm_shortage_fibre
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (c : (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space) :
    let G := Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
    G.symm ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, c⟩ =
      shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort := by
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  let s := shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort
  have hsubLit : Subsingleton
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
        (Measurement.lateSelectionExit N nK mZ mX omega)).space := by
    rw [completeContinuationBoundary_shortage
      N nK mZ mX ell ellEV leakEC omega hshort]
    constructor
    intro u v
    apply (Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).injective
    apply (TwoParty.pairEquiv Unit Unit).injective
    apply Prod.ext
    · exact Unit.ext _ _
    · exact Unit.ext _ _
  have hsub : Subsingleton
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
        ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space := by
    exact hsubLit
  have hfst : (G s).1 =
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega := by
    apply (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).injective
    rw [(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply]
    dsimp only [G, s]
    refine (congrArg (lateSelectionExitEquiv N nK mZ mX)
      (Boundary.graftSpaceEquiv_fst (lateSelectionBoundary N nK mZ mX)
        (completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort))).trans ?_
    exact shortageCompleteOutput_rawControl N nK mZ mX ell ellEV leakEC omega hshort
  apply G.injective
  rw [G.apply_symm_apply]
  generalize hgs : G s = gs
  rcases gs with ⟨e, d⟩
  have he : e = (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega := by
    exact (congrArg Sigma.fst hgs).symm.trans hfst
  subst e
  have hcd : c = d := hsub.elim _ _
  subst d
  rfl

end ShortageFibre

end QKD.BB84
