import QCryptLean.Math.FiniteEmbedding.RegisterFamily
import Mathlib.Data.Fin.VecNotation

/-!
# Finite-register family regressions

Concrete two- and three-party sums, a Bell-matrix trace calculation, and heterogeneous
instance inference exercise the generic provider. Negative guards distinguish stored
instances from extra computational instances that require a reducible family.
-/

open Math
open scoped BigOperators

namespace QCryptLeanTest.Math.FiniteRegisters
namespace Enumeration

/-- Two laboratories for the four-term expansion. -/
inductive Party
  | alice
  | bob
deriving DecidableEq

instance : Fintype Party := ⟨{Party.alice, Party.bob}, fun i => by cases i <;> decide⟩

/-- One qubit at each laboratory. -/
def qubitPair : FiniteRegisterFamily Party where
  reg := fun _ => Fin 2

/-- A joint two-qubit configuration. -/
def cfg (a b : Fin 2) : qubitPair.total := fun i => match i with | .alice => a | .bob => b

/-- The explicit four-term dependent-product sum. -/
theorem qubitPair_sum_univ {M : Type*} [AddCommMonoid M] (f : qubitPair.total → M) :
    ∑ x, f x = f (cfg 0 0) + f (cfg 0 1) + f (cfg 1 0) + f (cfg 1 1) := by
  rw [Fintype.sum_univ_eq_list_sum [cfg 0 0, cfg 0 1, cfg 1 0, cfg 1 1]
    (by decide) (by decide)]
  simp [add_assoc]

/-- The four real Bell amplitude tables, without normalization. -/
def bellTable : Fin 4 → Fin 2 → Fin 2 → ℂ :=
  ![![![1, 0], ![0, 1]], ![![0, 1], ![1, 0]], ![![1, 0], ![0, -1]], ![![0, 1], ![-1, 0]]]

/-- Read a Bell amplitude table at a joint configuration. -/
def bellSignTyped (k : Fin 4) (x : qubitPair.total) : ℂ := bellTable k (x .alice) (x .bob)

/-- The matrix associated with a Bell amplitude table. -/
noncomputable def bellPOVMTyped (k : Fin 4) : Matrix qubitPair.total qubitPair.total ℂ :=
  Matrix.of fun x y => (1 / 2 : ℂ) * (bellSignTyped k x * bellSignTyped k y)

/-- Each displayed Bell matrix has trace one. -/
theorem bellPOVMTyped_trace (k : Fin 4) : (bellPOVMTyped k).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [qubitPair_sum_univ]
  fin_cases k <;>
    norm_num [bellPOVMTyped, bellSignTyped, bellTable, cfg, Matrix.of_apply]

/-- Three named laboratories. -/
inductive Party3
  | a
  | b
  | c
deriving DecidableEq

instance : Fintype Party3 :=
  ⟨{Party3.a, Party3.b, Party3.c}, fun i => by cases i <;> decide⟩

/-- A Boolean register at each of three laboratories. -/
def bitTriple : FiniteRegisterFamily Party3 where
  reg := fun _ => Bool

/-- A joint three-bit configuration. -/
def cfg3 (x y z : Bool) : bitTriple.total :=
  fun i => match i with | .a => x | .b => y | .c => z

/-- The explicit eight-term dependent-product sum. -/
theorem bitTriple_sum_univ {M : Type*} [AddCommMonoid M] (f : bitTriple.total → M) :
    ∑ x, f x =
      f (cfg3 false false false) + f (cfg3 false false true) + f (cfg3 false true false)
        + f (cfg3 false true true) + f (cfg3 true false false) + f (cfg3 true false true)
        + f (cfg3 true true false) + f (cfg3 true true true) := by
  rw [Fintype.sum_univ_eq_list_sum
    [cfg3 false false false, cfg3 false false true, cfg3 false true false, cfg3 false true true,
      cfg3 true false false, cfg3 true false true, cfg3 true true false, cfg3 true true true]
    (by decide) (by decide)]
  simp [add_assoc]

end Enumeration

namespace Instances

/-- Two indices for heterogeneous-instance tests. -/
inductive DemoParty
  | alice
  | bob
  deriving DecidableEq

instance : Fintype DemoParty :=
  ⟨{DemoParty.alice, DemoParty.bob}, fun i => by cases i <;> decide⟩

/-- An unbundled heterogeneous type family. -/
@[reducible] def hetRegDirect : DemoParty → Type := fun i =>
  match i with
  | .alice => Fin 4
  | .bob => Bool × Bool

example : Fintype (hetRegDirect DemoParty.alice) := inferInstance
example : DecidableEq (hetRegDirect DemoParty.bob) := inferInstance
example : hetRegDirect DemoParty.alice := 0

/--
error: failed to synthesize
  (i : DemoParty) → Fintype (hetRegDirect i)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true`
command. -/
#guard_msgs in
#synth ∀ i, Fintype (hetRegDirect i)

/--
error: failed to synthesize
  (i : DemoParty) → DecidableEq (hetRegDirect i)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true`
command. -/
#guard_msgs in
#synth ∀ i, DecidableEq (hetRegDirect i)

/--
error: failed to synthesize instance of type class
  (i : DemoParty) → Fintype (hetRegDirect i)

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command. -/
#guard_msgs in
example : FiniteRegisterFamily DemoParty := ⟨hetRegDirect⟩

/-- Explicit finiteness instances for the direct family. -/
@[implicit_reducible]
def hetFinDirect : ∀ i, Fintype (hetRegDirect i) := fun i =>
  match i with
  | .alice => inferInstance
  | .bob => inferInstance

/-- Explicit equality instances for the direct family. -/
def hetDecDirect : ∀ i, DecidableEq (hetRegDirect i) := fun i =>
  match i with
  | .alice => inferInstance
  | .bob => inferInstance

/-- The direct construction with hand-written instance families. -/
def hetCutDirect : FiniteRegisterFamily DemoParty :=
  FiniteRegisterFamily.mk hetRegDirect (finReg := hetFinDirect) (decReg := hetDecDirect)

/-- The same heterogeneous registers, bundled. -/
def hetFam : DemoParty → FiniteRegister := fun i =>
  match i with
  | .alice => ⟨Fin 4⟩
  | .bob => ⟨Bool × Bool⟩

/-- A family built by projecting instances from its bundles. -/
def hetCut : FiniteRegisterFamily DemoParty := FiniteRegisterFamily.ofFam hetFam

example : ∀ i, Fintype (hetCut.reg i) := inferInstance
example : ∀ i, DecidableEq (hetCut.reg i) := inferInstance
example : Fintype (hetCut.reg DemoParty.alice) := inferInstance
example : DecidableEq (hetCut.reg DemoParty.bob) := inferInstance

example : Fintype hetCut.total := inferInstance
example : DecidableEq hetCut.total := inferInstance
example : Fintype.card hetCut.total = 16 := by decide

/-- Direct and bundled construction retain the same register types. -/
theorem hetCut_reg_eq (i : DemoParty) : hetCut.reg i = hetCutDirect.reg i := by
  cases i <;> rfl

example : hetCut.reg DemoParty.alice = Fin 4 := rfl
example : hetCut.reg DemoParty.bob = (Bool × Bool) := rfl

/--
error: failed to synthesize instance of type class
  OfNat (hetCut.reg DemoParty.alice) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected
type is
  hetCut.reg DemoParty.alice
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command. -/
#guard_msgs in
example : hetCut.reg DemoParty.alice := 0

/-- A reducible bundled family, exposing literal-index numeral instances. -/
@[reducible] def hetFamRed : DemoParty → FiniteRegister := fun i =>
  match i with
  | .alice => ⟨Fin 4⟩
  | .bob => ⟨Bool × Bool⟩

/-- The reducible family construction. -/
@[reducible] def hetCutRed : FiniteRegisterFamily DemoParty := FiniteRegisterFamily.ofFam hetFamRed

example : hetCutRed.reg DemoParty.alice := 0
example : ∀ i, Fintype (hetCutRed.reg i) := inferInstance
example : ∀ i, DecidableEq (hetCutRed.reg i) := inferInstance

/-- Three indices for a heterogeneous bundled family. -/
inductive TriParty
  | alice
  | bob
  | charlie
  deriving DecidableEq

instance : Fintype TriParty :=
  ⟨{TriParty.alice, TriParty.bob, TriParty.charlie}, fun i => by cases i <;> decide⟩

/-- Three heterogeneous registers with projected instance families. -/
def triCut : FiniteRegisterFamily TriParty := FiniteRegisterFamily.ofFam fun i =>
  match i with
  | .alice => ⟨Fin 4⟩
  | .bob => ⟨Bool × Bool⟩
  | .charlie => ⟨Fin 2 → Bool⟩

example : ∀ i, Fintype (triCut.reg i) := inferInstance
example : ∀ i, DecidableEq (triCut.reg i) := inferInstance
example : Fintype triCut.total := inferInstance
example : DecidableEq triCut.total := inferInstance
example : Fintype.card triCut.total = 64 := by decide

end Instances

namespace EmptyEdges

/-- A nonempty index type may carry an empty register. -/
def emptyRegister : FiniteRegisterFamily Unit where
  reg _ := Empty

example : IsEmpty emptyRegister.total := ⟨fun x => nomatch x ()⟩

example (f : emptyRegister.total → ℕ) : ∑ x, f x = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  exact Empty.elim (x ())

/-- With no indices, the dependent product contains the empty function. -/
def emptyParties : FiniteRegisterFamily Empty where
  reg _ := Empty

example : Nonempty emptyParties.total := ⟨fun i => nomatch i⟩

end EmptyEdges
end QCryptLeanTest.Math.FiniteRegisters
