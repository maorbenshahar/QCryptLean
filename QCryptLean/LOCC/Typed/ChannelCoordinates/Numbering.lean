import QCryptLean.LOCC.Typed.ChannelCoordinates.Norm

/-!
# Explicit numeral coordinates for a pair of typed registers

A `Numbering X Y` is the data a typed linear map `Op X →ₗ[ℂ] Op Y` needs in order to be read by
the numeral channel API: a positive dimension and a basis enumeration for each of the two
registers. `QKD.Protocol.NumeralCoordinates` specializes this record to a protocol's input and
heterogeneous output registers.

`Numbering.map` transports a typed map and `Numbering.post` transports an output-register
postprocessor.  The laws below are the whole generic content of a coordinate package:

* transport commutes with **composition** (`map_comp`) and **subtraction** (`map_sub`), and
  cancels an input reindexing entrywise (`map_reindex_apply`);
* the numeral **diamond norm is the coordinate-free one** (`diamondNorm_map`) and in particular
  does not depend on the numbering (`diamondNorm_map_eq`), because two numberings of one map are
  conjugate by basis renumberings (`map_conj_eq`);
* being **CPTP** likewise does not depend on the numbering (`isCPTP_map_congr`,
  `isChannel_iff_map`);
* both registers are **derived** to be nonempty (`nonempty_source`, `nonempty_target`). These facts
  supply the `[Nonempty X]` and `[Nonempty Y]` parameters retained by the norm and channel laws
  from their coordinate-free APIs.

Nothing here knows about programs, layouts, ideal resources or security: a numbering numbers
registers.  Which maps of a concrete protocol get transported, and what holds of them, belongs to
that protocol's own module.
-/

open Quantum.Operators

noncomputable section

namespace TypedLOCC

/-- **Explicit positive numeral coordinates for an ordered pair of typed registers.**

The two equivalences are the only coordinate choices the numeral channel API sees. Positive
dimensions exclude zero-dimensional presentations from this API; an empty register can instead
be numbered by `Fin 0`. -/
structure Numbering (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] where
  /-- Positive input dimension. -/
  inputDim : ℕ
  /-- Positive output dimension. -/
  outputDim : ℕ
  /-- The input coordinate type is nonempty. -/
  [inputDim_neZero : NeZero inputDim]
  /-- The output coordinate type is nonempty. -/
  [outputDim_neZero : NeZero outputDim]
  /-- Input basis numbering. -/
  inputEquiv : X ≃ Fin inputDim
  /-- Output basis numbering. -/
  outputEquiv : Y ≃ Fin outputDim

attribute [instance] Numbering.inputDim_neZero Numbering.outputDim_neZero

namespace Numbering

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Transport -/

/-- **A typed register map read in the numbering.** -/
def map (C : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) :
    Quantum.Operators.Op C.inputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  coordinateLinear C.inputEquiv C.outputEquiv Phi

/-- **An output-register postprocessor read in the same output numbering.**  Composing it with a
transported map is again a transported map (`map_comp`). -/
def post (C : Numbering X Y) (Psi : Op Y →ₗ[ℂ] Op Y) :
    Quantum.Operators.Op C.outputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  coordinateLinear C.outputEquiv C.outputEquiv Psi

/-! ## Derived structural facts

A numbering exhibits a point of each register, supplying nonemptiness when a downstream API
requires it. -/

/-- The input register of a numbering is inhabited. -/
theorem nonempty_source (C : Numbering X Y) : Nonempty X := ⟨C.inputEquiv.symm 0⟩

/-- The output register of a numbering is inhabited. -/
theorem nonempty_target (C : Numbering X Y) : Nonempty Y := ⟨C.outputEquiv.symm 0⟩

/-! ## Composition, subtraction and entries -/

/-- Transport preserves composition with an output postprocessor. -/
theorem map_comp (C : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) (Psi : Op Y →ₗ[ℂ] Op Y) :
    C.map (Psi.comp Phi) = (C.post Psi).comp (C.map Phi) :=
  coordinateLinear_comp C.inputEquiv C.outputEquiv C.outputEquiv Phi Psi

/-- Transport preserves subtraction: a real-minus-ideal map may be formed before or after
numbering. -/
theorem map_sub (C : Numbering X Y) (Phi Psi : Op X →ₗ[ℂ] Op Y) :
    C.map (Phi - Psi) = C.map Phi - C.map Psi :=
  coordinateLinear_sub C.inputEquiv C.outputEquiv Phi Psi

/-- Transport preserves finite sums. -/
theorem map_sum {kappa : Type} [Fintype kappa] (C : Numbering X Y)
    (Phi : kappa → (Op X →ₗ[ℂ] Op Y)) :
    C.map (∑ x, Phi x) = ∑ x, C.map (Phi x) :=
  coordinateLinear_sum C.inputEquiv C.outputEquiv Phi

/-- Transport takes the zero map to the zero map: a real/ideal pair that coincides has numeral
difference zero in every numbering. -/
@[simp] theorem map_zero (C : Numbering X Y) : C.map (0 : Op X →ₗ[ℂ] Op Y) = 0 := by
  apply LinearMap.ext
  intro rho
  ext i j
  simp [map, coordinateLinear]

/-- Entries of a transported map at numbered indices are the entries of the typed map. -/
@[simp] theorem map_reindex_apply (C : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) (rho : Op X)
    (i j : Y) :
    C.map Phi (Matrix.reindex C.inputEquiv C.inputEquiv rho) (C.outputEquiv i)
        (C.outputEquiv j) = Phi rho i j :=
  coordinateLinear_reindex_apply C.inputEquiv C.outputEquiv Phi rho i j

/-! ## Two numberings of one map -/

/-- **Two numberings of one typed map are conjugate by basis renumberings.**  This is the single
structural identity behind the coordinate independence of the diamond norm and of the CPTP
property. -/
theorem map_conj_eq (C D : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) :
    D.map Phi =
      ((Matrix.reindexLinearEquiv ℂ ℂ (C.outputEquiv.symm.trans D.outputEquiv)
              (C.outputEquiv.symm.trans D.outputEquiv)).toLinearMap.comp (C.map Phi)).comp
        (Matrix.reindexLinearEquiv ℂ ℂ (D.inputEquiv.symm.trans C.inputEquiv)
          (D.inputEquiv.symm.trans C.inputEquiv)).toLinearMap :=
  coordinateLinear_conj_eq C.inputEquiv D.inputEquiv C.outputEquiv D.outputEquiv Phi

/-- **The numeral diamond norm does not depend on the numbering.**  Hypothesis-free: only basis
renumberings relate the two presentations. -/
theorem diamondNorm_map_eq (C D : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) :
    Quantum.Channels.diamondNorm (D.map Phi) = Quantum.Channels.diamondNorm (C.map Phi) :=
  diamondNorm_coordinateLinear_eq C.inputEquiv D.inputEquiv C.outputEquiv D.outputEquiv Phi

/-- **Every numbering computes the coordinate-free diamond norm of the typed map.**  So a numeral
estimate is an estimate for the map itself, and conversely. -/
theorem diamondNorm_map [Nonempty X] [Nonempty Y] (C : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y) :
    Quantum.Channels.diamondNorm (C.map Phi) = TypedLOCC.diamondNorm Phi :=
  diamondNorm_coordinateLinear C.inputEquiv C.outputEquiv Phi

/-- **Being CPTP does not depend on the numbering.** -/
theorem isCPTP_map_congr (C D : Numbering X Y) (Phi : Op X →ₗ[ℂ] Op Y)
    (h : Quantum.Channels.IsCPTP ⇑(C.map Phi)) : Quantum.Channels.IsCPTP ⇑(D.map Phi) :=
  isCPTP_coordinateLinear_congr C.inputEquiv D.inputEquiv C.outputEquiv D.outputEquiv Phi h

/-- Being a typed channel is exactly being CPTP in one — hence in every — numbering. -/
theorem isChannel_iff_map [Nonempty X] [Nonempty Y] (C : Numbering X Y)
    (Phi : Op X →ₗ[ℂ] Op Y) :
    IsChannel Phi ↔ Quantum.Channels.IsCPTP ⇑(C.map Phi) :=
  isChannel_iff_coordinateLinear C.inputEquiv C.outputEquiv Phi

end Numbering

end TypedLOCC
