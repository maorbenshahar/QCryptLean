import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.ClassicalContinuation
import QCryptLean.QKD.Protocol

/-!
# The low-level numeral coordinate package of the measure-first BB84 experiment

`coordinates` is the **low-level transport package** of the actual complete measure-first
protocol: the retained factorization, the all-shortage branch and the native comparison are proved
about these explicit numeral maps.  The public real/ideal interface of the configured experiment —
the coordinate bridge, the accepted-key classicality and the full-interface-security criterion —
lives in `QCryptLean.QKD.BB84.RealIdeal`, and
`Parameters.realIdealDistance_eq_coordinates` there transports the estimates about this package to
the coordinate-free distance of the protocol.  Neither package is part of any public security
statement.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84.Engine
open QKD.BB84.Measurement
open QKD.BB84.Sampling

/-- Explicit numeral coordinates for the actual complete measure-first protocol.

The dimensions and equivalences enumerate the source-defined input multipartite system and
heterogeneous complete output boundary. They add no channel, security premise, or protocol choice.
-/
noncomputable def coordinates
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    QKD.Protocol.NumeralCoordinates
      (protocol
        pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q) where
  inputDim := Fintype.card (Measurement.weightedStreamSystem Unit N).total
  outputDim := Fintype.card
    (boundary N nK mZ mX ℓ ℓEV leakEC).space
  inputDim_neZero := Measurement.weightedStreamInputCardNeZero N
  outputDim_neZero :=
    boundaryCardNeZero N nK mZ mX ℓ ℓEV leakEC
  inputEquiv := Fintype.equivFin _
  outputEquiv := Fintype.equivFin _

end QKD.BB84
