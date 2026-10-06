import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.Transcript
import QCryptLean.LOCC.Typed.Boundary.Uniform

/-!
# Public disclosure of the parameter-estimation bits

In the fourth stage of `QKD.BB84.program`, Bob and then Alice publicly announce the bit each holds
at every designated test round, while both retain their raw `2 ^ n`-element registers.
`peBitAnnouncement` is one such announcement: a nondemolition readout of the selected bit of the
actor's register, published as a raw transcript coordinate that `LOCC.outcomeDigit 2`
decodes back to the observed bit.  `peAnnouncementLoop` runs these announcements at the listed
positions `idx`, Bob's cell before Alice's at each position, and hands the decoded Alice and Bob
strings to an arbitrary continuation; stage 4 of `QKD.BB84.program` applies it to the test
positions.  The error-rate decision on those strings belongs to the FinalStage module.

The local-instrument construction follows Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section II; the public-data chronology follows
Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, Section V.C.
-/

open scoped Matrix BigOperators

noncomputable section

namespace QKD.BB84

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.PE

/-! ## Bob-then-Alice bit announcements -/

/-- Read the selected bit from the local register of either named party.

Both factors of `FinalStage.rawSystem n` have type `Fin (2 ^ n)`; the dependent match records which
local factor is being read without identifying the two parties. -/
def localRegisterBit (n : ℕ) (i : Fin n) (actor : Party) :
    (FinalStage.rawSystem n).reg actor → Fin 2 :=
  match actor with
  | .alice => LOCC.registerBit n i
  | .bob => LOCC.registerBit n i

/-- Read the selected bit from party `actor` and publish its raw transcript coordinate.

The physical outcome of `nondemolitionReadout` is the semantic bit `x`. The public map announces
`(LOCC.outcomeDigit 2).symm x`, so applying `outcomeDigit 2` to the public cell
recovers `x`.
Only that announced value indexes the continuation. -/
def peBitAnnouncement (n : ℕ) (i : Fin n) (actor : Party) :
    AnnouncedAction (FinalStage.rawSystem n) (Fin 2) := by
  letI : Fintype ((FinalStage.rawSystem n).reg actor) :=
    (FinalStage.rawSystem n).finReg actor
  letI : DecidableEq ((FinalStage.rawSystem n).reg actor) :=
    (FinalStage.rawSystem n).decReg actor
  exact AnnouncedAction.ofInstrument actor
    (Instrument.nondemolitionReadout (localRegisterBit n i actor))
    (LOCC.outcomeDigit 2).symm

/-- Decoding the raw public cell of a PE bit announcement recovers its physical semantic
outcome exactly. -/
@[simp] theorem peBitAnnouncement_decode_announce
    (n : ℕ) (i : Fin n) (actor : Party) (x : Fin 2) :
    LOCC.outcomeDigit 2 ((peBitAnnouncement n i actor).announce x) = x := by
  exact Equiv.apply_symm_apply _ _

/-- Exact joint-register branch operation of the PE bit readout.

The readout preserves every matrix entry whose two acting-party coordinates have semantic bit
`x`, including coherence within that fibre and independent spectator row/column coordinates. -/
theorem peBitAnnouncement_liftedOperation_apply
    (n : ℕ) (i : Fin n) (actor : Party) (x : Fin 2)
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : (FinalStage.rawSystem n).total) :
    ((peBitAnnouncement n i actor).liftedOperation x rho)
        (((FinalStage.rawSystem n).splitAtSet actor
          ((FinalStage.rawSystem n).reg actor)).symm
            ((FinalStage.rawSystem n).splitAt actor q))
        (((FinalStage.rawSystem n).splitAtSet actor
          ((FinalStage.rawSystem n).reg actor)).symm
            ((FinalStage.rawSystem n).splitAt actor q')) =
      if localRegisterBit n i actor (((FinalStage.rawSystem n).splitAt actor q).1) = x ∧
          localRegisterBit n i actor (((FinalStage.rawSystem n).splitAt actor q').1) = x then
        rho q q'
      else 0 := by
  change (((Instrument.nondemolitionReadout (localRegisterBit n i actor)).liftAt
    (FinalStage.rawSystem n) actor).operation x rho) _ _ = _
  rw [Instrument.liftAt_operation_apply (R := FinalStage.rawSystem n) actor
    (Instrument.nondemolitionReadout (localRegisterBit n i actor))]
  simp only [Equiv.apply_symm_apply, Instrument.nondemolitionReadout_operation_apply]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Prod.eta]

/-- Bob's public PE bit readout at the designated round. -/
def bobPEBitAnnouncement (n : ℕ) (i : Fin n) :
    AnnouncedAction (FinalStage.rawSystem n) (Fin 2) :=
  peBitAnnouncement n i .bob

/-- Alice's public PE bit readout at the designated round. -/
def alicePEBitAnnouncement (n : ℕ) (i : Fin n) :
    AnnouncedAction (FinalStage.rawSystem n) (Fin 2) :=
  peBitAnnouncement n i .alice

/-! ## The parameter-estimation recursion -/

/-- Bob-then-Alice recursion over the designated PE positions.

At a successor, Bob's raw public cell is first and Alice's is second. The recursive continuation
receives semantic strings in Alice-then-Bob order, with the current semantic values prepended by
`Fin.cons`, while retaining `FinalStage.rawSystem n` before all decision and key actions. -/
def peAnnouncementLoop
    (n : ℕ) {T : TList} (r : ℕ) (idx : Fin r → Fin n)
    (cont : (Fin r → Fin 2) → (Fin r → Fin 2) →
      Program (FinalStage.rawSystem n)
        (Boundary.uniform (FinalStage.rawSystem n) T)) :
    Program (FinalStage.rawSystem n)
      (Boundary.uniform (FinalStage.rawSystem n) (transcriptWord r T)) :=
  match r, idx, cont with
  | 0, _, cont => cont Fin.elim0 Fin.elim0
  | r + 1, idx, cont =>
      (bobPEBitAnnouncement n (idx 0)).then fun b =>
        cast (by
          simp only [bobPEBitAnnouncement, peBitAnnouncement,
            AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]
          rfl)
          ((alicePEBitAnnouncement n (idx 0)).then
            (B := fun _ => Boundary.uniform (FinalStage.rawSystem n) (transcriptWord r T))
            fun a => cast (by
              simp only [alicePEBitAnnouncement, peBitAnnouncement,
                AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self])
              (peAnnouncementLoop n r (fun j => idx j.succ)
                (fun as bs => cont
                  (Fin.cons (LOCC.outcomeDigit 2 a) as)
                  (Fin.cons (LOCC.outcomeDigit 2 b) bs))))

/-- The successor recursion exposes Bob's cell before Alice's and prepends the decoded semantic
values to the corresponding Alice/Bob continuation strings. -/
theorem peAnnouncementLoop_succ
    (n : ℕ) {T : TList} (r : ℕ) (idx : Fin (r + 1) → Fin n)
    (cont : (Fin (r + 1) → Fin 2) → (Fin (r + 1) → Fin 2) →
      Program (FinalStage.rawSystem n)
        (Boundary.uniform (FinalStage.rawSystem n) T)) :
    peAnnouncementLoop n (r + 1) idx cont =
      (bobPEBitAnnouncement n (idx 0)).then fun b =>
        cast (by
          simp only [bobPEBitAnnouncement, peBitAnnouncement,
            AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]
          rfl)
          ((alicePEBitAnnouncement n (idx 0)).then
            (B := fun _ => Boundary.uniform (FinalStage.rawSystem n) (transcriptWord r T))
            fun a => cast (by
              simp only [alicePEBitAnnouncement, peBitAnnouncement,
                AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self])
              (peAnnouncementLoop n r (fun j => idx j.succ)
                (fun as bs => cont
                  (Fin.cons (LOCC.outcomeDigit 2 a) as)
                  (Fin.cons (LOCC.outcomeDigit 2 b) bs)))) := by
  rfl

end QKD.BB84
