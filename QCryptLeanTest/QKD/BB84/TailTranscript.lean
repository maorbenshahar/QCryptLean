import QCryptLean.QKD.BB84.TailTranscript.Raw
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the raw pre-decision decoder

These bounded fixtures unfold `QKD.BB84.preDecisionRawEquiv` directly on the zero-round and
two-round words; they do not invoke `QKD.BB84.preDecisionRawEquiv_succ`.  They pin the literal
Bob-then-Alice chronology of the shared raw record, including the index order of the rounds.
-/

noncomputable section

namespace QCryptLeanTest.BB84.TailTranscript

open TypedLOCC
open QKD.BB84
open QKD.BB84.PE

/-! ## Zero and two-round raw decoding -/

def zeroRoundTranscript (A : ℕ) (z : Fin A) :
    Transcript (transcriptWord 0 (.cons (Fin A) .nil)) :=
  (z, ())

theorem zeroRound_fused (A : ℕ) (z : Fin A) :
    (preDecisionRawEquiv 0 A (zeroRoundTranscript A z)).fusedRaw = z := rfl

theorem zeroRound_roundTrip (A : ℕ)
    (t : Transcript (transcriptWord 0 (.cons (Fin A) .nil))) :
    (preDecisionRawEquiv 0 A).symm (preDecisionRawEquiv 0 A t) = t := by
  exact Equiv.symm_apply_apply _ _

def twoRoundTranscript (A : ℕ) (b0 a0 b1 a1 : Fin 2) (z : Fin A) :
    Transcript (transcriptWord 2 (.cons (Fin A) .nil)) :=
  (b0, (a0, (b1, (a1, (z, ())))))

theorem twoRound_bob_index_zero (A : ℕ) (b0 a0 b1 a1 : Fin 2) (z : Fin A) :
    (preDecisionRawEquiv 2 A (twoRoundTranscript A b0 a0 b1 a1 z)).bobPERaw 0 = b0 := by
  rfl

theorem twoRound_alice_index_zero (A : ℕ) (b0 a0 b1 a1 : Fin 2) (z : Fin A) :
    (preDecisionRawEquiv 2 A
      (twoRoundTranscript A b0 a0 b1 a1 z)).alicePERaw 0 = a0 := by
  rfl

theorem twoRound_bob_tail_succ (A : ℕ) (b0 a0 b1 a1 : Fin 2) (z : Fin A) :
    (preDecisionRawEquiv 2 A (twoRoundTranscript A b0 a0 b1 a1 z)).bobPERaw 1 = b1 := by
  rfl

theorem twoRound_alice_tail_succ (A : ℕ) (b0 a0 b1 a1 : Fin 2) (z : Fin A) :
    (preDecisionRawEquiv 2 A
      (twoRoundTranscript A b0 a0 b1 a1 z)).alicePERaw 1 = a1 := by
  rfl

def chronologyTranscript : Transcript (transcriptWord 2 (.cons (Fin 1) .nil)) :=
  twoRoundTranscript 1 1 0 0 1 0

/-- The deliberately reversed old-to-new indexing is not the actual decoder result. -/
def reversedChronology : PreDecisionRaw 2 1 where
  bobPERaw := Fin.cons 0 (Fin.cons 1 Fin.elim0)
  alicePERaw := Fin.cons 1 (Fin.cons 0 Fin.elim0)
  fusedRaw := 0

theorem decodedChronology_ne_reversed :
    preDecisionRawEquiv 2 1 chronologyTranscript ≠ reversedChronology := by
  intro h
  have h0 := congrArg (fun d => d.bobPERaw 0) h
  change (1 : Fin 2) = 0 at h0
  exact (by decide : (1 : Fin 2) ≠ 0) h0

end QCryptLeanTest.BB84.TailTranscript
