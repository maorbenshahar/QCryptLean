import QCryptLean.QKD.BB84.Reduction.QuotaShortage
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the all-shortage statement surface

The executable fixtures distinguish the genuine cardinal-shortage case from zero quotas and check
that abort idealization preserves arbitrary entries within one complete public exit.  The test
enforces sorry-freedom for the two proved shortage theorems and the six independent fixtures.
-/

open Quantum.Operators (Op)

noncomputable section

open _root_.LOCC
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Reduction

namespace AllShortageAudit

/-- The canonical empty raw control is quota-sufficient when every requested quota is zero.
This rejects a universal quota-shortage claim without asserting anything about the difference map
at those parameters. -/
theorem zeroRound_zeroQuotas_hasQuotas :
    HasQuotas 0 0 0 (defaultRawControl 0) := by
  decide

/-- A positive retained quota at zero physical rounds is an actual shortage. -/
theorem zeroRound_positiveQuota_hasNoQuotas :
    ¬ HasQuotas 1 0 0 (defaultRawControl 0) := by
  decide

/-- Opposite one-round basis strings with their explicit empty matched-set ordering. -/
def mismatchControl : RawControl 1 :=
  ⟨(fun _ => Basis.z), (fun _ => Basis.x),
    increasingShuffle (fun _ => Basis.z) (fun _ => Basis.x)⟩

/-- The all-mismatched control cannot supply one retained key round. -/
theorem mismatchControl_hasNoQuota :
    ¬ HasQuotas 1 0 0 mismatchControl := by
  decide

/-- The source abort-exit constructor retains both basis strings and the exact sampled shuffle.
The shortage branch therefore does not collapse complete public metadata to a constant exit. -/
theorem mismatchAbortExit_retainsMetadata :
    let e := lateSelectionExit 1 1 0 0 mismatchControl
    e.1 = mismatchControl.a ∧ e.2.1 = mismatchControl.b ∧
      e.2.2.1 = mismatchControl.order := by
  exact ⟨rfl, rfl, rfl⟩

/-- Boundary idealization at an abort exit preserves an arbitrary within-exit row/column entry.
The two local coordinates may differ, so abort does not silently dephase within-exit residual
coherence. -/
theorem abortIdeal_preservesWithinExitEntry
    {P : Type} [Fintype P] [DecidableEq P]
    (A : QKD.Protocol P) (rho : Op A.boundary.space)
    (e : A.boundary.Exit)
    (h : A.layout.disposition e = BoundaryKeyLayout.Disposition.abort)
    (a b : (A.boundary.system e).total) :
    A.resource rho ⟨e, a⟩ ⟨e, b⟩ = rho ⟨e, a⟩ ⟨e, b⟩ := by
  exact A.layout.toBoundaryKeyLayout.ideal_coordinate_abort rho e h a b

end AllShortageAudit
