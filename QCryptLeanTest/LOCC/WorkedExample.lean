import QCryptLean.QKD.Protocol
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.LOCC.Instrument.Classical

/-!
# A two-way protocol with residual data

Alice announces her key bit as a query, using a swapped wire encoding. Bob announces whether his
bit matches the interpreted query. On a positive reply Alice privately appends the query to her
local residual data and both parties retain their key factors. On a negative reply they stop
immediately, retaining their registers as residual data but declaring no keys. The construction
has no authored boundary, cast, exit decoder, or parallel layout tree.
-/

noncomputable section

open Quantum.Operators (Op)

namespace LOCC.WorkedExample
open TwoParty QKD

/-- The public encoding of the query bit. -/
private def queryWire : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

section Actions

variable {A B : Type}
variable [Nonempty A] [Fintype A] [DecidableEq A]
variable [Nonempty B] [Fintype B] [DecidableEq B]

/-- Alice announces her bit through a swapped wire cell, retaining her bit and local data. -/
@[implicit_reducible] def query :=
  AnnouncedAction.ofInstrument (R := system ((Fin 1 → Fin 2) × Fin 3) B) .alice
    (Instrument.nondemolitionReadout (fun a : (Fin 1 → Fin 2) × Fin 3 => a.1 0)) queryWire

/-- Bob announces whether his bit matches the query, retaining his bit and local data. -/
@[implicit_reducible] def reply (q : Fin 2) :=
  AnnouncedAction.ofInstrument (R := system A ((Fin 1 → Fin 2) × Fin 5)) .bob
    (Instrument.nondemolitionReadout (fun b : (Fin 1 → Fin 2) × Fin 5 => decide (b.1 0 = q))) id

/-- Alice privately appends the accepted query to her local residual data. -/
@[implicit_reducible] def remember (q : Fin 2) :=
  PrivateAction.ofInstrument (R := system ((Fin 1 → Fin 2) × Fin 3) B) .alice
    (Instrument.functionAndForget (fun a : (Fin 1 → Fin 2) × Fin 3 => (a.1, (a.2, q))))

end Actions

/-- Query, reply, then retain owned keys with residual data or stop immediately without keys. -/
def conversation : Program (system ((Fin 1 → Fin 2) × Fin 3) ((Fin 1 → Fin 2) × Fin 5))
    (KeyEnd Party.alice Party.bob) :=
  query.then fun cell =>
    let q := queryWire.symm cell
    (reply q).then fun ok =>
      if ok then
        (remember q).then (.done (KeyEnd.keysWithResidual 1))
      else .done (KeyEnd.abortRetaining
        (A := (Fin 1 → Fin 2) × Fin 3) (B := (Fin 1 → Fin 2) × Fin 5))

/-- Package the same readable construction and its computed terminal ownership. -/
def protocol : QKD.Protocol Party := conversation.toProtocol (by decide)

/-- The query's semantic view inverts its wire encoding without replacing the wire action. -/
theorem query_read_announce (bit : Fin 2) :
    queryWire.symm ((query (B := Unit)).announce bit) = bit := by
  exact Equiv.swap_apply_self 0 1 bit

/-- The inferred boundary has precisely two cells and value-dependent terminal systems. -/
theorem conversation_boundary : conversation.boundary =
    .announce (Fin 2) (fun _ => .announce Bool fun ok =>
      if ok = true then .leaf (system ((Fin 1 → Fin 2) × (Fin 3 × Fin 2)) ((Fin 1 → Fin 2) × Fin 5))
      else .leaf (system ((Fin 1 → Fin 2) × Fin 3) ((Fin 1 → Fin 2) × Fin 5))) := by
  change Boundary.announce (Fin 2) _ = _
  congr 1
  funext q
  change Boundary.announce Bool _ = _
  congr 1
  funext ok
  cases ok <;> rfl

/-- A positive reply yields an accepted one-bit key owned by each actual laboratory. -/
example : protocol.layout.disposition ⟨(0 : Fin 2), true, ()⟩ = .accept 1 := rfl

/-- Terminal ownership at a concrete exit reduces directly through the action chain. -/
example : (conversation.terminal ⟨(0 : Fin 2), true, ()⟩).disposition = .accept 1 := rfl

/-- A concrete exit selects its natural final system by definitional equality. -/
example : conversation.boundary.system ⟨(0 : Fin 2), true, ()⟩ =
    system ((Fin 1 → Fin 2) × (Fin 3 × Fin 2)) ((Fin 1 → Fin 2) × Fin 5) := rfl

/-- Reading terminal ownership as a layout preserves direct computation at a concrete exit. -/
example : (conversation.outputLayout (by decide)).disposition
    ⟨(0 : Fin 2), true, ()⟩ = .accept 1 := rfl

/-- Alice's accepted residual retains her old data and the interpreted query. -/
example : protocol.layout.AliceResidual ⟨(0 : Fin 2), true, ()⟩ = (Fin 3 × Fin 2) := rfl

/-- Bob's accepted residual is retained unchanged. -/
example : protocol.layout.BobResidual ⟨(0 : Fin 2), true, ()⟩ = Fin 5 := rfl

/-- The local splitting equivalence extracts Alice's key without consuming her residual data. -/
example (k : Fin 1 → Fin 2) (r : Fin 3 × Fin 2) :
    protocol.layout.aliceSplit ⟨(0 : Fin 2), true, ()⟩ (k, r) = (k, r) := rfl

/-- Negative replies terminate with no key disposition. -/
example : protocol.layout.disposition ⟨(1 : Fin 2), false, ()⟩ = .abort := rfl

/-- An early abort retains Alice's entire local register as residual information. -/
example : protocol.layout.AliceResidual ⟨(1 : Fin 2), false, ()⟩ = ((Fin 1 → Fin 2) × Fin 3) := rfl

/-- Accepted zero-bit keys remain distinguishable from abort. -/
example : ((Program.done (KeyEnd.keys 0)).terminal ()).disposition = .accept 0 := rfl

/-- The fully discarded convenience has exactly the key-free terminal system. -/
example : (Program.done KeyEnd.abort).boundary = .leaf (system Unit Unit) := rfl

/-- Classicality is a separate certificate obtained from the actions' preservation laws. -/
theorem conversation_isHonestClassical : conversation.IsHonestClassical := by
  unfold conversation
  refine .announced _ _ ?_ (fun cell => ?_)
  · exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
      (Instrument.nondemolitionReadout_preservesDiagonalBranches _)
  · refine .announced _ _ ?_ (fun ok => ?_)
    · exact AnnouncedAction.ofInstrument_preservesHonestRegistersDiagonal _ _ _
        (Instrument.nondemolitionReadout_preservesDiagonalBranches _)
    · cases ok
      · exact .done _
      · exact .priv _ _
          (PrivateAction.ofInstrument_preservesHonestRegistersDiagonal _ _
            (Instrument.functionAndForget_preservesDiagonalBranches _)) (.done _)

end LOCC.WorkedExample
