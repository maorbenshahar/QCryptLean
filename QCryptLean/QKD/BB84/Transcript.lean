import QCryptLean.LOCC.Typed.Transcript.Coordinates
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.Model.PEAnnouncement

/-!
# Typed BB84 transcript coordinates

Pure transcript-word and numeral-coordinate bookkeeping shared by typed BB84 modules.
-/

namespace QKD.BB84.PE
open TypedLOCC

open TypedLOCC.Transcript

/-- The transcript word of `r` parameter-estimation rounds followed by `T`. -/
def transcriptWord (r : ℕ) (T : TList) : TList :=
  match r with
  | 0 => T
  | r + 1 => .cons (Fin 2) (.cons (Fin 2) (transcriptWord r T))

/-- Numeral coordinates for the parameter-estimation transcript word. -/
noncomputable def transcriptEquivFin {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (r : ℕ) :
    Transcript (transcriptWord r T) ≃ Fin (QKD.BB84.Model.peLoopDim D r) :=
  match r with
  | 0 => e
  | r + 1 =>
      consTranscriptEquivFin (Fin 2)
        (consTranscriptEquivFin (Fin 2) (transcriptEquivFin e r))

end QKD.BB84.PE

