import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.LOCC.Typed.Instrument.Classical
import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import QCryptLean.LOCC.Typed.LocalAction
import QCryptLean.LOCC.Typed.Program

/-!
# The fused seed, verification-tag and syndrome announcement

After the parameter-estimation bits, the fourth stage of `QKD.BB84.program` ends with one public
cell written by Alice.  `fusedAnnouncement` samples a seed index uniformly inside its instrument,
reads her verification tag and error-correction syndrome at that seed from her raw register, and
publishes the pair through `fusedPublicEquiv`.  The announced cell therefore determines both the
sampled seed index and the tag/syndrome value; no unannounced shared seed is supplied.
`fusedStage` runs this announcement before an arbitrary continuation indexed by the cell.

The local instrument follows Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section
II.  The cell retains the established BB84 seed, verification-tag and syndrome encoding
`QKD.BB84.Model.bb84AnnounceCard`; Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, Section
V.C describes the corresponding public error-correction and hashing data. -/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## Uniform fused seed, tag, and syndrome readout -/

/-- The numeral seed coordinate used by `QKD.BB84.Model.evTagSynOf`. -/
abbrev FusedSeedIndex (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :=
  Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))

/-- Alice's semantic verification-tag/syndrome value at a fixed seed index. -/
abbrev FusedValue (ℓEV leakEC : ℕ) := Fin (2 ^ ℓEV * 2 ^ leakEC)

/-- The public coordinate encoding the seed index, verification tag, and syndrome. -/
abbrev FusedPublic
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :=
  Fin (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC)

/-- Exact equivalence between the semantic pair and the raw public cell.

The semantic product is first encoded with `finProdFinEquiv`; `outcomeDigit.symm` then converts it
to the raw instrument coordinate. -/
noncomputable def fusedPublicEquiv
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    FusedSeedIndex n ℓ ℓEV peSel × FusedValue ℓEV leakEC ≃
      FusedPublic n ℓ ℓEV peSel leakEC :=
  finProdFinEquiv.trans
    (LOCC.outcomeDigit
      (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC)).symm

/-- The uniformly seeded readout of Alice's tag/syndrome function.

At seed index `r`, the member instrument is the nondemolition readout of
`QKD.BB84.Model.evTagSynOf ... r`. The observed physical outcome is the semantic pair `(r, v)`; its
hidden Kraus fibre remains `Unit`. -/
noncomputable def fusedReadoutInstrument
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    Instrument (Fin (2 ^ n)) (Fin (2 ^ n))
      (FusedSeedIndex n ℓ ℓEV peSel × FusedValue ℓEV leakEC) := by
  letI : Nonempty (FusedSeedIndex n ℓ ℓEV peSel) :=
    ⟨⟨0, Fintype.card_pos⟩⟩
  exact Instrument.uniformChoice fun r : FusedSeedIndex n ℓ ℓEV peSel =>
    Instrument.nondemolitionReadout
      (QKD.BB84.Model.evTagSynOf n ℓ ℓEV peSel leakEC ec r)

/-- Alice's fused public action.

The action samples the seed index inside `fusedReadoutInstrument` and publishes the result through
`fusedPublicEquiv`. Consequently the raw cell received by the continuation determines both the
sampled seed index and the tag/syndrome value; there is no unannounced shared seed. -/
noncomputable def fusedAnnouncement
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    AnnouncedAction (FinalStage.rawSystem n)
      (FusedPublic n ℓ ℓEV peSel leakEC) :=
  AnnouncedAction.ofInstrument (R := FinalStage.rawSystem n)
    Party.alice
    (fusedReadoutInstrument n ℓ ℓEV peSel leakEC ec)
    (fusedPublicEquiv n ℓ ℓEV peSel leakEC)

/-- Run the fused public action before an arbitrary continuation indexed by the announced cell.
This one-node stage is not a complete BB84 program. -/
def fusedStage
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    {B : FusedPublic n ℓ ℓEV peSel leakEC → Boundary Party}
    (k : ∀ o, Program (FinalStage.rawSystem n) (B o)) :
    Program (FinalStage.rawSystem n)
      (.announce (FusedPublic n ℓ ℓEV peSel leakEC) B) :=
  (fusedAnnouncement n ℓ ℓEV peSel leakEC ec).then fun y =>
    cast (by
      apply congrArg (fun R => Program R (B y))
      change FinalStage.rawSystem n = (FinalStage.rawSystem n).set .alice (Fin (2 ^ n))
      exact (TwoParty.set_alice _ _ _).symm) (k y)

/-- Decoding a raw fused public cell gives the seed index and tag/syndrome value using the
`outcomeDigit`/`finProdFinEquiv` encoding. -/
theorem fusedPublicEquiv_symm_apply
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (o : FusedPublic n ℓ ℓEV peSel leakEC) :
    (fusedPublicEquiv n ℓ ℓEV peSel leakEC).symm o =
      finProdFinEquiv.symm
        (LOCC.outcomeDigit
          (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC) o) := by
  rfl

/-- Encoding the semantic outcome and decoding the announced cell recovers the same
seed-index/value pair. The continuation index is the announced cell. -/
theorem fusedAnnouncement_decode_announce
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (rv : FusedSeedIndex n ℓ ℓEV peSel × FusedValue ℓEV leakEC) :
    finProdFinEquiv.symm
        (LOCC.outcomeDigit
          (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC)
          ((fusedAnnouncement n ℓ ℓEV peSel leakEC ec).announce rv)) =
      rv := by
  unfold fusedAnnouncement
  change (fusedPublicEquiv n ℓ ℓEV peSel leakEC).symm
      (fusedPublicEquiv n ℓ ℓEV peSel leakEC rv) = rv
  exact Equiv.symm_apply_apply _ _

/-- Exact joint-register branch operation of the fused readout.

For every operator, a fixed semantic branch `(r, v)` retains precisely the entries for which Alice's
row and column coordinates both give value `v`, weighted by the uniform seed probability. Bob's
spectator row and column coordinates remain independent; no density, diagonality, reachability, or
selector-count hypothesis is used. -/
theorem fusedAnnouncement_liftedOperation_apply
    (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (r : FusedSeedIndex n ℓ ℓEV peSel) (v : FusedValue ℓEV leakEC)
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : (FinalStage.rawSystem n).total) :
    ((fusedAnnouncement n ℓ ℓEV peSel leakEC ec).liftedOperation (r, v) rho)
        (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))).symm
          ((FinalStage.rawSystem n).splitAt .alice q))
        (((FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))).symm
          ((FinalStage.rawSystem n).splitAt .alice q')) =
      if QKD.BB84.Model.evTagSynOf n ℓ ℓEV peSel leakEC ec r
            (((FinalStage.rawSystem n).splitAt .alice q).1) = v ∧
          QKD.BB84.Model.evTagSynOf n ℓ ℓEV peSel leakEC ec r
            (((FinalStage.rawSystem n).splitAt .alice q').1) = v then
        (Fintype.card (FusedSeedIndex n ℓ ℓEV peSel) : ℂ)⁻¹ * rho q q'
      else 0 := by
  change (((fusedReadoutInstrument n ℓ ℓEV peSel leakEC ec).liftAt
    (FinalStage.rawSystem n) .alice).operation (r, v) rho) _ _ = _
  rw [Instrument.liftAt_operation_apply (R := FinalStage.rawSystem n) .alice
    (fusedReadoutInstrument n ℓ ℓEV peSel leakEC ec)]
  let E : (FinalStage.rawSystem n).total ≃
      Fin (2 ^ n) × (FinalStage.rawSystem n).rest .alice :=
    (FinalStage.rawSystem n).splitAt .alice
  let O : ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).total ≃
      Fin (2 ^ n) × (FinalStage.rawSystem n).rest .alice :=
    (FinalStage.rawSystem n).splitAtSet .alice (Fin (2 ^ n))
  change (fusedReadoutInstrument n ℓ ℓEV peSel leakEC ec).operation (r, v)
    (rho.submatrix (fun x => E.symm (x, (O (O.symm (E q))).2))
      (fun x => E.symm (x, (O (O.symm (E q'))).2)))
    (O (O.symm (E q))).1 (O (O.symm (E q'))).1 = _
  simp only [Equiv.apply_symm_apply]
  unfold fusedReadoutInstrument
  refine (congrFun (congrFun (LinearMap.congr_fun
    (Instrument.uniformChoice_operation
      (fun r => Instrument.nondemolitionReadout
        (Model.evTagSynOf n ℓ ℓEV peSel leakEC ec r)) r v) _) _) _).trans ?_
  have h := congrArg (fun z => (Fintype.card (FusedSeedIndex n ℓ ℓEV peSel) : ℂ)⁻¹ * z)
      (Instrument.nondemolitionReadout_operation_apply
        (QKD.BB84.Model.evTagSynOf n ℓ ℓEV peSel leakEC ec r) v
        (rho.submatrix
          (fun x => ((FinalStage.rawSystem n).splitAt .alice).symm
            (x, ((FinalStage.rawSystem n).splitAt .alice q).2))
          (fun x => ((FinalStage.rawSystem n).splitAt .alice).symm
            (x, ((FinalStage.rawSystem n).splitAt .alice q').2)))
        ((FinalStage.rawSystem n).splitAt .alice q).1
        ((FinalStage.rawSystem n).splitAt .alice q').1)
  simp only [mul_ite, mul_zero] at h
  refine h.trans ?_
  congr 1
  exact congrArg ((Fintype.card (FusedSeedIndex n ℓ ℓEV peSel) : ℂ)⁻¹ * ·)
    (congrArg₂ rho (((FinalStage.rawSystem n).splitAt .alice).symm_apply_apply q)
      (((FinalStage.rawSystem n).splitAt .alice).symm_apply_apply q'))

end QKD.BB84
