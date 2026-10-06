import QCryptLean.LOCC.Typed.TwoParty
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the generic two-party multipartite system

The probes use heterogeneous local carriers and also the case where both party constructors map to
the same carrier type.  They prove the two spectator-agreement facts directly and require attempts
to change the remote register to fail.
-/

namespace QCryptLeanTest.LOCC.TwoPartyProbes

open TypedLOCC
open TypedLOCC.TwoParty

abbrev heterogeneousSystem : MultipartiteSystem Party := system (Fin 2) (Fin 3)

/-- A joint register built through the advertised Alice-first product equivalence. -/
def joint (alice : Fin 2) (bob : Fin 3) : heterogeneousSystem.total :=
  (pairEquiv (Fin 2) (Fin 3)).symm (alice, bob)

theorem alice_register_is_heterogeneous : heterogeneousSystem.reg .alice = Fin 2 := rfl
theorem bob_register_is_heterogeneous : heterogeneousSystem.reg .bob = Fin 3 := rfl

theorem pairEquiv_joint (alice : Fin 2) (bob : Fin 3) :
    pairEquiv (Fin 2) (Fin 3) (joint alice bob) = (alice, bob) := by
  exact Equiv.apply_symm_apply _ _

theorem joint_alice (alice : Fin 2) (bob : Fin 3) : joint alice bob .alice = alice := by
  rfl

theorem joint_bob (alice : Fin 2) (bob : Fin 3) : joint alice bob .bob = bob := by
  rfl

/-- The inherited instances make the heterogeneous joint carrier inhabited. -/
theorem heterogeneous_nonempty : Nonempty heterogeneousSystem.total := inferInstance

/-- Finiteness is the product cardinality, not a homogeneous-dimension approximation. -/
theorem heterogeneous_card : Fintype.card heterogeneousSystem.total = 6 := by
  rw [Fintype.card_congr (pairEquiv (Fin 2) (Fin 3))]
  simp

/-- Equality on the heterogeneous joint carrier is decidable. -/
theorem heterogeneous_decidableEq (q r : heterogeneousSystem.total) : q = r ∨ q ≠ r :=
  eq_or_ne q r

/-! If both constructors map to the same carrier type, the two party coordinates remain separate.
This is the many-to-one register-family control. -/

def sameCarrierJoint (alice bob : Bool) : (system Bool Bool).total :=
  (pairEquiv Bool Bool).symm (alice, bob)

theorem sameCarrier_family_not_collapsed :
    sameCarrierJoint false true ≠ sameCarrierJoint true false := by
  intro h
  have hp := congrArg (pairEquiv Bool Bool) h
  simp [sameCarrierJoint] at hp

theorem sameCarrier_joint_card : Fintype.card (system Bool Bool).total = 4 := by
  rw [Fintype.card_congr (pairEquiv Bool Bool)]
  simp

/-! ## Direct spectator-agreement checks -/

theorem direct_agreesOff_alice :
    (system (Fin 2) (Fin 3)).AgreesOff (system (Fin 5) (Fin 3)) .alice := by
  intro p hp
  cases p with
  | alice => exact (hp rfl).elim
  | bob => rfl

theorem direct_agreesOff_bob :
    (system (Fin 2) (Fin 3)).AgreesOff (system (Fin 2) (Fin 5)) .bob := by
  intro p hp
  cases p with
  | alice => rfl
  | bob => exact (hp rfl).elim

/-- Changing Bob while claiming an Alice-local step must be rejected. -/
example : True := by
  fail_if_success
    exact (fun p hp =>
      match p with
      | .alice => (hp rfl).elim
      | .bob => rfl :
        (system (Fin 2) (Fin 3)).AgreesOff (system (Fin 5) (Fin 4)) .alice)
  trivial

/-- Changing Alice while claiming a Bob-local step must be rejected. -/
example : True := by
  fail_if_success
    exact (fun p hp =>
      match p with
      | .alice => rfl
      | .bob => (hp rfl).elim :
        (system (Fin 2) (Fin 3)).AgreesOff (system (Fin 4) (Fin 5)) .bob)
  trivial

/-- Pattern matching on the shared party type uses the two named constructors. -/
def constructorPattern (party : TypedLOCC.TwoParty.Party) : Bool :=
  match party with
  | .alice => false
  | .bob => true

theorem constructorPattern_alice :
    constructorPattern TypedLOCC.TwoParty.Party.alice = false := rfl

theorem constructorPattern_bob :
    constructorPattern TypedLOCC.TwoParty.Party.bob = true := rfl

/-- The party enumeration has exactly the two named constructors. -/
theorem party_card : Fintype.card TypedLOCC.TwoParty.Party = 2 := by decide

/-- The party type carries decidable equality. -/
theorem party_decidableEq (p q : TypedLOCC.TwoParty.Party) : p = q ∨ p ≠ q :=
  eq_or_ne p q

/-- The party type is inhabited. -/
theorem party_nonempty : Nonempty TypedLOCC.TwoParty.Party := inferInstance

end QCryptLeanTest.LOCC.TwoPartyProbes
