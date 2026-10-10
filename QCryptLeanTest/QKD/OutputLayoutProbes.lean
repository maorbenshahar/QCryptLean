import QCryptLean.QKD.OutputLayout
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for locally owned QKD output coordinates

These probes exercise `OutputLayout` by reduction, independently of its named coordinate laws.
The negative controls distinguish a rejected constructor or identifier from an unproved claim.
-/

namespace QCryptLeanTest.OutputLayoutProbes

open _root_.LOCC

open QKD

inductive Party where
  | alice
  | bob
  | spectator
deriving DecidableEq

inductive ExitTag where
  | abort
  | acceptZero
  | acceptOne
deriving DecidableEq

protected abbrev Party.enumList : List Party := [.alice, .bob, .spectator]

protected theorem Party.enumList_getElem?_ctorIdx_eq (x : Party) :
    Party.enumList[Party.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem Party.enumList_nodup : Party.enumList.Nodup := by decide

instance instFintypeParty : Fintype Party where
  elems := ⟨Party.enumList, Party.enumList_nodup⟩
  complete x := by
    change x ∈ Party.enumList
    exact List.mem_iff_getElem?.mpr ⟨Party.ctorIdx x, Party.enumList_getElem?_ctorIdx_eq x⟩

protected abbrev ExitTag.enumList : List ExitTag := [.abort, .acceptZero, .acceptOne]

protected theorem ExitTag.enumList_getElem?_ctorIdx_eq (x : ExitTag) :
    ExitTag.enumList[ExitTag.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem ExitTag.enumList_nodup : ExitTag.enumList.Nodup := by decide

instance instFintypeExitTag : Fintype ExitTag where
  elems := ⟨ExitTag.enumList, ExitTag.enumList_nodup⟩
  complete x := by
    change x ∈ ExitTag.enumList
    exact List.mem_iff_getElem?.mpr ⟨ExitTag.ctorIdx x, ExitTag.enumList_getElem?_ctorIdx_eq x⟩

def LocalReg (t : ExitTag) (p : Party) : Type :=
  match t with
  | .abort =>
      match p with
      | .alice => Unit × Fin 2
      | .bob => Unit × Fin 3
      | .spectator => Fin 5
  | .acceptZero =>
      match p with
      | .alice => (Fin 0 → Fin 2) × Fin 2
      | .bob => (Fin 0 → Fin 2) × Fin 3
      | .spectator => Fin 5
  | .acceptOne =>
      match p with
      | .alice => (Fin 1 → Fin 2) × Fin 2
      | .bob => (Fin 1 → Fin 2) × Fin 3
      | .spectator => Fin 5

def exitSystem (t : ExitTag) : MultipartiteSystem Party where
  reg := LocalReg t
  finReg i := by cases t <;> cases i <;> dsimp [LocalReg] <;> infer_instance
  decReg i := by cases t <;> cases i <;> dsimp [LocalReg] <;> infer_instance

/-- A public boundary with abort, zero-bit, and one-bit accepted leaves. -/
def boundary : Boundary Party :=
  .announce ExitTag (fun t => .leaf (exitSystem t))
def abortExit : boundary.Exit := ⟨.abort, ()⟩
def acceptZeroExit : boundary.Exit := ⟨.acceptZero, ()⟩
def acceptOneExit : boundary.Exit := ⟨.acceptOne, ()⟩

def layout : OutputLayout boundary where
  alice := .alice
  bob := .bob
  alice_ne_bob := by decide
  disposition e :=
    match e.1 with
    | .abort => .abort
    | .acceptZero => .accept 0
    | .acceptOne => .accept 1
  AliceResidual _ := Fin 2
  BobResidual _ := Fin 3
  finAliceResidual _ := inferInstance
  decAliceResidual _ := inferInstance
  nonemptyAliceResidual _ := inferInstance
  finBobResidual _ := inferInstance
  decBobResidual _ := inferInstance
  nonemptyBobResidual _ := inferInstance
  aliceSplit e := by
    rcases e with ⟨t, ⟨⟩⟩
    cases t <;> exact Equiv.refl _
  bobSplit e := by
    rcases e with ⟨t, ⟨⟩⟩
    cases t <;> exact Equiv.refl _

theorem abort_key_type : (layout.disposition abortExit).Key = Unit := rfl
theorem accept_zero_key_type : (layout.disposition acceptZeroExit).Key = (Fin 0 → Fin 2) := rfl
theorem accept_one_key_type : (layout.disposition acceptOneExit).Key = (Fin 1 → Fin 2) := rfl

/-- Concrete joint coordinates at the three leaves. -/
def abortJoint (ar : Fin 2) (br : Fin 3) (s : Fin 5) :
    (boundary.system abortExit).total := fun p =>
  match p with
  | .alice => ((), ar)
  | .bob => ((), br)
  | .spectator => s
def acceptZeroJoint (a : Fin 0 → Fin 2) (ar : Fin 2) (b : Fin 0 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (boundary.system acceptZeroExit).total := fun p =>
  match p with
  | .alice => (a, ar)
  | .bob => (b, br)
  | .spectator => s
def acceptOneJoint (a : Fin 1 → Fin 2) (ar : Fin 2) (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (boundary.system acceptOneExit).total := fun p =>
  match p with
  | .alice => (a, ar)
  | .bob => (b, br)
  | .spectator => s
def spectatorIndex : layout.SpectatorParty := ⟨⟨.spectator, by decide⟩, by decide⟩

theorem accept_one_alice_key (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptOneExit (acceptOneJoint a ar b br s)).1 = a := by rfl
theorem accept_one_bob_key (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptOneExit (acceptOneJoint a ar b br s)).2.1 = b := by rfl
theorem accept_one_alice_residual (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptOneExit (acceptOneJoint a ar b br s)).2.2.1.1 = ar := by rfl
theorem accept_one_bob_residual (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptOneExit (acceptOneJoint a ar b br s)).2.2.1.2 = br := by rfl
theorem accept_one_spectator (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b : Fin 1 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptOneExit
      (acceptOneJoint a ar b br s)).2.2.2 spectatorIndex = s := by
  rfl
theorem alice_key_noninterference (a : Fin 1 → Fin 2) (ar : Fin 2)
    (b₁ b₂ : Fin 1 → Fin 2) (br₁ br₂ : Fin 3) (s₁ s₂ : Fin 5) :
    (layout.coordinates acceptOneExit (acceptOneJoint a ar b₁ br₁ s₁)).1 =
      (layout.coordinates acceptOneExit (acceptOneJoint a ar b₂ br₂ s₂)).1 := by rfl
theorem abort_alice_key (ar : Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates abortExit (abortJoint ar br s)).1 = () := by rfl
theorem accept_zero_alice_key (a : Fin 0 → Fin 2) (ar : Fin 2)
    (b : Fin 0 → Fin 2) (br : Fin 3) (s : Fin 5) :
    (layout.coordinates acceptZeroExit (acceptZeroJoint a ar b br s)).1 = a := by rfl

example (L : OutputLayout boundary) : L.alice ≠ L.bob := L.alice_ne_bob
example : True := by
  fail_if_success have _sameParty : Party.alice ≠ Party.alice := by decide
  trivial
example (e : boundary.Exit) : (boundary.system e).reg layout.alice ≃
    (layout.disposition e).Key × layout.AliceResidual e := by
  fail_if_success exact layout.bobSplit e
  exact layout.aliceSplit e
example : True := by
  fail_if_success
    let _bad : OutputLayout boundary :=
      { layout with coordinates := fun e => layout.coordinates e }
  trivial
example : True := by
  fail_if_success have _false : (1 : Nat) = 2 := rfl
  trivial
/- This declaration-level typo must remain an unknown identifier under the package option
`relaxedAutoImplicit = false`; no local option override is used here. -/
/--
error: Unknown identifier `misspelledNumber`

Note: It is not possible to treat `misspelledNumber` as an implicitly bound variable here because it
has multiple characters while the `relaxedAutoImplicit` option is set to `false`. -/
#guard_msgs (error) in
example (n : Nat) : n = misspelledNumber := rfl

end QCryptLeanTest.OutputLayoutProbes
