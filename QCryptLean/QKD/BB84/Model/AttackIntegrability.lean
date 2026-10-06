import Mathlib.MeasureTheory.SpecificCodomains.Pi
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Constants
import QCryptLean.InfoTheory.DeFinetti.Measure

/-!
# Matrix-valued integrability from entrywise integrability

A finite-dimensional integrability helper: treats a matrix-valued map as a nested finite function
space and reduces matrix-valued integrability to scalar entries.

## Main results

- `matrix_integrable_of_entry_integrable`: finite matrix-valued integrability from entries.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace QKD.BB84.Model

private local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- A matrix-valued map into a finite matrix space is integrable if all scalar
entries are integrable. -/
lemma matrix_integrable_of_entry_integrable
    {α m n : Type*} [MeasurableSpace α] [Fintype m] [Fintype n]
    {μ : MeasureTheory.Measure α} {F : α → Matrix m n ℂ}
    (hF : ∀ i j, MeasureTheory.Integrable (fun x => F x i j) μ) :
    MeasureTheory.Integrable F μ := by
  let G : α → m → n → ℂ := fun x i j => F x i j
  have hG : MeasureTheory.Integrable G μ := by
    exact MeasureTheory.Integrable.of_eval fun i =>
      MeasureTheory.Integrable.of_eval fun j => hF i j
  let toMatrix : (m → n → ℂ) →L[ℝ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact toMatrix.integrable_comp hG

end QKD.BB84.Model
