import QCryptLean.LOCC.ClassicalInstruments

/-!
# Two-party PE-announcement loop dimension

The transcript dimension contributed by `r` rounds in which each round announces two bits
(Bob's, then Alice's), for use with `LOCC.pinnedReadout`-built announcement programs.

Written with an explicit `match` rather than equation-style alternatives: the Dirac ket
notation in this import closure is a leading term parser and eats a `|` that follows an
applicable term.

## Main definitions

- `QKD.BB84.Model.peLoopDim`: the transcript dimension of `r` announcement pairs.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open LOCC
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-- Dimension of `r` pairs of two-outcome announcements with continuation dimension `D`. -/
def peLoopDim (D : ℕ) (r : ℕ) : ℕ :=
  match r with
  | 0 => D
  | r + 1 => peLoopDim D r * 2 * 2

end QKD.BB84.Model

end
