import QCryptLean.QKD.Ideal.BoundaryKey
import Mathlib.Util.AssertNoSorry

/-!
# Proved probes for cross-layout accepted-coordinate transport

The two layouts below have different boundaries and different residual types. Their key length is
the same, so the fixture checks the heterogeneous unspecialized relation, the homogeneous accepted
result, and named applications of both proved generic transport laws.

The eight definition-driven theorem names and the two accepted cross-by-transport application
names correspond exactly to the accepted external proved-probe source.
-/

namespace QCryptLeanTest.QKD.AcceptedCoordinateTransportProbes

open TypedLOCC
open TypedLOCC.BoundaryKeyLayout

/-- A one-party multipartite system with a three-element retained coordinate. -/
def leftSystem : MultipartiteSystem Unit where
  reg _ := Fin (2 ^ 1) × Fin (2 ^ 1) × Fin 3
  nonemptyReg _ := by infer_instance
  finReg _ := by infer_instance
  decReg _ := by infer_instance

/-- A one-party multipartite system with a five-element retained coordinate. -/
def rightSystem : MultipartiteSystem Unit where
  reg _ := Fin (2 ^ 1) × Fin (2 ^ 1) × Fin 5
  nonemptyReg _ := by infer_instance
  finReg _ := by infer_instance
  decReg _ := by infer_instance

/-- The left terminal boundary. -/
def leftBoundary : Boundary Unit := .leaf leftSystem

/-- The right terminal boundary. -/
def rightBoundary : Boundary Unit := .leaf rightSystem

/-- The unique exit of the left terminal boundary. -/
def leftExit : leftBoundary.Exit := ()

/-- The unique exit of the right terminal boundary. -/
def rightExit : rightBoundary.Exit := ()

/-- Accepted coordinates on the left boundary. -/
def leftLayout : BoundaryKeyLayout leftBoundary where
  disposition _ := .accept 1
  Residual _ := Fin 3
  finResidual _ := by infer_instance
  decResidual _ := by infer_instance
  nonemptyResidual _ := by infer_instance
  coordinates _ := Equiv.funUnique Unit _

/-- Accepted coordinates on the right boundary. -/
def rightLayout : BoundaryKeyLayout rightBoundary where
  disposition _ := .accept 1
  Residual _ := Fin 5
  finResidual _ := by infer_instance
  decResidual _ := by infer_instance
  nonemptyResidual _ := by infer_instance
  coordinates _ := Equiv.funUnique Unit _

/-- A nonliteral acceptance witness for the left layout. -/
theorem leftAccepted : leftLayout.disposition leftExit = .accept 1 := by
  decide

/-- A nonliteral acceptance witness for the right layout. -/
theorem rightAccepted : rightLayout.disposition rightExit = .accept 1 := by
  decide

/-- A left point with distinct key values and a nontrivial residual. -/
def leftPoint : (leftBoundary.system leftExit).total :=
  fun _ => (1, 0, 2)

/-- A right point with the same keys and a different residual type and value. -/
def rightPoint : (rightBoundary.system rightExit).total :=
  fun _ => (1, 0, 4)

/-- The left accepted specialization preserves Alice's key. -/
theorem left_fst_definition :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).1 = 1 := by
  change Equiv.cast _ (1 : Fin (2 ^ 1)) = 1
  rfl

/-- The left accepted specialization preserves Bob's key. -/
theorem left_snd_fst_definition :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).2.1 = 0 := by
  change Equiv.cast _ (0 : Fin (2 ^ 1)) = 0
  rfl

/-- The right accepted specialization preserves Alice's key. -/
theorem right_fst_definition :
    (rightLayout.acceptCoordinates rightAccepted rightPoint).1 = 1 := by
  change Equiv.cast _ (1 : Fin (2 ^ 1)) = 1
  rfl

/-- The right accepted specialization preserves Bob's key. -/
theorem right_snd_fst_definition :
    (rightLayout.acceptCoordinates rightAccepted rightPoint).2.1 = 0 := by
  change Equiv.cast _ (0 : Fin (2 ^ 1)) = 0
  rfl

/-- Alice's two unspecialized key coordinates are heterogeneously equal. -/
theorem coordinates_fst_heq :
    (leftLayout.coordinates leftExit leftPoint).1 ≍
      (rightLayout.coordinates rightExit rightPoint).1 := by
  exact heq_of_eq rfl

/-- Bob's two unspecialized key coordinates are heterogeneously equal. -/
theorem coordinates_snd_fst_heq :
    (leftLayout.coordinates leftExit leftPoint).2.1 ≍
      (rightLayout.coordinates rightExit rightPoint).2.1 := by
  exact heq_of_eq rfl

/-- Alice's accepted coordinates agree across the two residual layouts by direct reduction. -/
theorem accepted_fst_cross_definition :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).1 =
      (rightLayout.acceptCoordinates rightAccepted rightPoint).1 := by
  exact left_fst_definition.trans right_fst_definition.symm

/-- Bob's accepted coordinates agree across the two residual layouts by direct reduction. -/
theorem accepted_snd_fst_cross_definition :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).2.1 =
      (rightLayout.acceptCoordinates rightAccepted rightPoint).2.1 := by
  exact left_snd_fst_definition.trans right_snd_fst_definition.symm

/-- Concrete Alice-coordinate application of the generic cross-layout transport theorem. -/
theorem accepted_fst_cross_by_transport :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).1 =
      (rightLayout.acceptCoordinates rightAccepted rightPoint).1 :=
  acceptCoordinates_fst_eq_of_coordinates_fst_heq
    leftLayout rightLayout leftAccepted rightAccepted leftPoint rightPoint coordinates_fst_heq

/-- Concrete Bob-coordinate application of the generic cross-layout transport theorem. -/
theorem accepted_snd_fst_cross_by_transport :
    (leftLayout.acceptCoordinates leftAccepted leftPoint).2.1 =
      (rightLayout.acceptCoordinates rightAccepted rightPoint).2.1 :=
  acceptCoordinates_snd_fst_eq_of_coordinates_snd_fst_heq
    leftLayout rightLayout leftAccepted rightAccepted leftPoint rightPoint
      coordinates_snd_fst_heq

end QCryptLeanTest.QKD.AcceptedCoordinateTransportProbes
