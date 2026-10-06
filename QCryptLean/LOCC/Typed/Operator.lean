import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import QCryptLean.Quantum.Channels.CPTP.Reindex

/-!
# Finite-register operator primitives

This module defines finite-dimensional operator matrices `Op HH`, structural reindexing, and the
elementary matrix operations used by the typed LOCC layers above it.  It contains no multipartite
system, instrument, program, boundary, or protocol syntax.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC

/-! ## Registers are indexed by the type they range over -/

/-- **An operator on the register `HH`.**  Compare the source library's `Op (n : ℕ)`, which names a
register by its *dimension*; every regrouping of a composite register is then a `ℕ` equation and
every boundary an `Op.castDimLinear`. -/
abbrev Op (HH : Type) [Fintype HH] [DecidableEq HH] := Matrix HH HH ℂ

/-! ## Reindexing a register is an `Equiv`, never a cast -/

/-- Transport an operator along a bijection of its register.  In the numeral-indexed library this
is `Op.castDimLinear` along a `ℕ` equation; here it is a structural `Equiv`, and it composes. -/
def reindexOp {HH HH' : Type} [Fintype HH] [DecidableEq HH] [Fintype HH'] [DecidableEq HH']
    (e : HH ≃ HH') : Op HH →ₗ[ℂ] Op HH' where
  toFun M := M.submatrix e.symm e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Kraus operator that writes outcome `x` into a fresh transcript slot. -/
def writeKraus {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (XX : Type) [Fintype XX] [DecidableEq XX] (x : XX) : Matrix (A × XX × B) (A × B) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = x ∧ p.2.2 = q.2 then 1 else 0


end TypedLOCC
