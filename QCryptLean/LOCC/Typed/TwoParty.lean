import QCryptLean.LOCC.Typed.MultipartiteSystem

/-!
# Type-indexed two-party multipartite systems

This module supplies the neutral Alice/Bob party type and the corresponding typed multipartite
system and coordinate API. Its joint register is the product of the supplied local register types.
-/

namespace TypedLOCC.TwoParty

/-- The two named parties used by two-party typed programs. -/
inductive Party | alice | bob
  deriving DecidableEq, Nonempty

instance : Fintype Party := ⟨{.alice, .bob}, fun p => by cases p <;> decide⟩

/-- A two-party typed multipartite system with the supplied Alice and Bob register types. -/
@[implicit_reducible] def system (AliceRegister BobRegister : Type)
    [Nonempty AliceRegister] [Fintype AliceRegister] [DecidableEq AliceRegister]
    [Nonempty BobRegister] [Fintype BobRegister] [DecidableEq BobRegister] : MultipartiteSystem
      Party where
  reg p :=
    match p with
    | .alice => AliceRegister
    | .bob => BobRegister
  nonemptyReg p := by cases p <;> infer_instance
  finReg p := by cases p <;> infer_instance
  decReg p := by cases p <;> infer_instance

/-- Split a two-party joint register into Alice's coordinate followed by Bob's coordinate. -/
def pairEquiv (AliceRegister BobRegister : Type)
    [Nonempty AliceRegister] [Fintype AliceRegister] [DecidableEq AliceRegister]
    [Nonempty BobRegister] [Fintype BobRegister] [DecidableEq BobRegister] :
    (system AliceRegister BobRegister).total ≃ AliceRegister × BobRegister where
  toFun q := (q .alice, q .bob)
  invFun q := fun p =>
    match p with
    | .alice => q.1
    | .bob => q.2
  left_inv q := by
    funext p
    cases p <;> rfl
  right_inv q := by
    rcases q with ⟨a, b⟩
    rfl

/-- Updating Alice's register changes only the first register of the two-party system. -/
@[simp] theorem set_alice (AliceRegister BobRegister HH : Type)
    [Nonempty AliceRegister] [Fintype AliceRegister] [DecidableEq AliceRegister]
    [Nonempty BobRegister] [Fintype BobRegister] [DecidableEq BobRegister]
    [Nonempty HH] [Fintype HH] [DecidableEq HH] :
    (system AliceRegister BobRegister).set .alice HH = system HH BobRegister := by
  apply MultipartiteSystem.ext'
  funext p
  cases p <;> simp [system]

/-- Updating Bob's register changes only the second register of the two-party system. -/
@[simp] theorem set_bob (AliceRegister BobRegister HH : Type)
    [Nonempty AliceRegister] [Fintype AliceRegister] [DecidableEq AliceRegister]
    [Nonempty BobRegister] [Fintype BobRegister] [DecidableEq BobRegister]
    [Nonempty HH] [Fintype HH] [DecidableEq HH] :
    (system AliceRegister BobRegister).set .bob HH = system AliceRegister HH := by
  apply MultipartiteSystem.ext'
  funext p
  cases p <;> simp [system]

end TypedLOCC.TwoParty

namespace TypedLOCC.MultipartiteSystem

open TwoParty

/-- Split the joint register of any two-party system into its two local coordinates. -/
def pairEquiv (R : MultipartiteSystem Party) :
    R.total ≃ R.reg .alice × R.reg .bob where
  toFun q := (q .alice, q .bob)
  invFun q := fun p =>
    match p with
    | .alice => q.1
    | .bob => q.2
  left_inv q := by
    funext p
    cases p <;> rfl
  right_inv q := by
    rcases q with ⟨a, b⟩
    rfl

/-- The two-party coordinate equivalence reads Alice's and Bob's registers. -/
@[simp] theorem pairEquiv_apply (R : MultipartiteSystem Party) (q : R.total) :
    R.pairEquiv q = (q .alice, q .bob) := rfl

/-- Reconstructing a joint register returns Alice's supplied coordinate. -/
@[simp] theorem pairEquiv_symm_apply_alice (R : MultipartiteSystem Party)
    (q : R.reg .alice × R.reg .bob) : (R.pairEquiv.symm q) .alice = q.1 := rfl

/-- Reconstructing a joint register returns Bob's supplied coordinate. -/
@[simp] theorem pairEquiv_symm_apply_bob (R : MultipartiteSystem Party)
    (q : R.reg .alice × R.reg .bob) : (R.pairEquiv.symm q) .bob = q.2 := rfl

/-- Transporting a joint register transports its two local coordinates. -/
@[simp] theorem cast_pairEquiv_symm {R S : MultipartiteSystem Party} (h : R = S)
    (q : R.reg .alice × R.reg .bob) :
    cast (congrArg MultipartiteSystem.total h) (R.pairEquiv.symm q) =
      S.pairEquiv.symm (cast (congrArg (fun T => T.reg .alice) h) q.1,
        cast (congrArg (fun T => T.reg .bob) h) q.2) := by
  cases h
  rfl

/-- The general coordinate equivalence agrees with the specified two-party coordinates. -/
@[simp] theorem pairEquiv_system (AliceRegister BobRegister : Type)
    [Nonempty AliceRegister] [Fintype AliceRegister] [DecidableEq AliceRegister]
    [Nonempty BobRegister] [Fintype BobRegister] [DecidableEq BobRegister] :
    (TwoParty.system AliceRegister BobRegister).pairEquiv =
      TwoParty.pairEquiv AliceRegister BobRegister := rfl

end TypedLOCC.MultipartiteSystem
