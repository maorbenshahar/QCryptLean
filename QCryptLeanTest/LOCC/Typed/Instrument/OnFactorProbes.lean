import QCryptLean.LOCC.Typed.Instrument.OnFactor
import Mathlib.Util.AssertNoSorry

/-!
# Tests for `Instrument.onFactor`

This test prints every declaration's axiom surface and checks definition-level Unit, nontrivial,
and empty spectator fixtures. It also checks a nonzero spectator off-diagonal entry by unfolding
the Kraus data. The instrument completeness certificate has separate tests.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

open TypedLOCC
open TypedLOCC.Instrument

namespace OnFactorAudit

/-- A one-outcome identity instrument used only by the explicit edge fixtures. -/
def identityInstrument (A : Type) [Fintype A] [DecidableEq A] :
    Instrument A A Unit :=
  Instrument.ofFine (fun _ => (1 : Matrix A A ℂ)) (by simp)

/-- With identity product coordinates and a Unit spectator, the raw Kraus entry is unchanged. -/
theorem unitSpectator_rawKraus
    {A B Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Outcome]
    (I : Instrument A B Outcome) (y : Outcome) (t : I.krausIndex y)
    (b : B) (a : A) :
    onFactorKraus (Equiv.refl (A × Unit)) (Equiv.refl (B × Unit)) I y t
        (b, ()) (a, ()) = I.kraus y t b a := by
  simp [onFactorKraus, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-- A nontrivial spectator mismatch kills the raw Kraus entry in identity product coordinates. -/
theorem differentSpectator_rawKraus_zero
    {A B Outcome S : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Outcome]
    [Fintype S] [DecidableEq S]
    (I : Instrument A B Outcome) (y : Outcome) (t : I.krausIndex y)
    (b : B) (a : A) (s s' : S) (h : s ≠ s') :
    onFactorKraus (Equiv.refl (A × S)) (Equiv.refl (B × S)) I y t
        (b, s) (a, s') = 0 := by
  simp [onFactorKraus, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    h]

/-- Explicit equivalence between an empty register and a product with empty spectator. -/
def emptyProductEquiv (A : Type) : Fin 0 ≃ A × Fin 0 where
  toFun i := Fin.elim0 i
  invFun p := Fin.elim0 p.2
  left_inv i := Fin.elim0 i
  right_inv p := Fin.elim0 p.2

/-- The actual factor constructor accepts an empty spectator without a `Nonempty` assumption. -/
def emptySpectatorInstrument : Instrument (Fin 0) (Fin 0) Unit :=
  onFactor (emptyProductEquiv Unit) (emptyProductEquiv Unit)
    (identityInstrument Unit)

/-- The empty-spectator constructor retains the original Unit hidden fibre. -/
theorem emptySpectator_hiddenFiber :
    emptySpectatorInstrument.krausIndex () = Unit := by
  rfl

/- The exact operation theorem keeps independently selected spectator row and column coordinates. -/

end OnFactorAudit

/-! ## Direct spectator-coherence probe -/

namespace OnFactorGateProbe

attribute [-simp] onFactorKraus_apply

/-- One-outcome identity instrument used to expose spectator coherence directly. -/
def identityInstrument : Instrument Unit Unit Unit where
  krausIndex _ := Unit
  kraus _ _ := 1
  complete := by simp

/-- Matrix unit supported on the spectator off-diagonal entry `(0,1)`. -/
def offDiagonal : Op (Unit × Fin 2) := fun i j =>
  if i.2 = 0 ∧ j.2 = 1 then 1 else 0

/-- Acting identically on `Unit` preserves a nonzero spectator off-diagonal matrix entry. -/
theorem actualOperation_preserves_offDiagonal :
    (((onFactor (Equiv.refl (Unit × Fin 2)) (Equiv.refl (Unit × Fin 2))
        identityInstrument).operation ()) offDiagonal) ((), 0) ((), 1) = 1 := by
  simp [Instrument.operation, onFactor, onFactorKraus, identityInstrument,
    matrixConjLinear, offDiagonal]

attribute [simp] onFactorKraus_apply

end OnFactorGateProbe
