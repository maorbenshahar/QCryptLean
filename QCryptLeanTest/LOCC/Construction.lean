import QCryptLeanTest.LOCC.Examples.HeterogeneousProgram

/-!
# Dependent actions and unused public labels

Direct action chains preserve unequal successor dimensions and retain public values with no
physical support. The program computes its boundary in both cases.
-/

open Quantum.Operators (Op)

namespace LOCC.ConstructionExample
open Examples.HeterogeneousProgram

/-- Run the explicit action with a one-dimensional and a four-dimensional output. -/
def dependentProgram : Program privateMeasure.out :=
  branchAction.then fun _ => .done PUnit.unit

example : Fintype.card ((dependentProgram.boundary.system ⟨false, ()⟩).reg Party.alice) = 1 := by
  decide

example : Fintype.card ((dependentProgram.boundary.system ⟨true, ()⟩).reg Party.alice) = 4 := by
  decide

/-- The action's true public value is retained even though it has no physical support. -/
def withUnusedLabel : Program inputSystem :=
  unusedLabelAction.then fun _ => .done PUnit.unit

example : Fintype.card withUnusedLabel.boundary.Exit = 2 := by decide

end LOCC.ConstructionExample
