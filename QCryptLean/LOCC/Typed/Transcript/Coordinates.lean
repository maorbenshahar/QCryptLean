import QCryptLean.LOCC.Typed.Transcript

/-!
# Transcript numeral coordinates

These coordinates use `Fintype.equivFin` and place the leading transcript cell in the low digit.
-/

namespace TypedLOCC.Transcript

/-- The empty typed transcript in the numeral coordinate `Fin 1`. -/
noncomputable def nilTranscriptEquivFin : Transcript .nil ≃ Fin 1 :=
  Fintype.equivFin Unit

/-- A typed cons transcript uses continuation-first numeral order. -/
noncomputable def consTranscriptEquivFin (Outcome : Type) [Fintype Outcome]
    [DecidableEq Outcome] {T : TList} {D : ℕ} (e : Transcript T ≃ Fin D) :
    Transcript (.cons Outcome T) ≃ Fin (D * Fintype.card Outcome) :=
  (Equiv.prodComm Outcome (Transcript T)).trans
    ((Equiv.prodCongr e (Fintype.equivFin Outcome)).trans finProdFinEquiv)

/-- The numeral encoder for a nonempty transcript uses the leading cell as its low digit. -/
theorem consTranscriptEquivFin_val
    (Outcome : Type) [Fintype Outcome] [DecidableEq Outcome]
    {T : TList} {D : ℕ} (e : Equiv (Transcript T) (Fin D))
    (x : Outcome) (t : Transcript T) :
    ((consTranscriptEquivFin Outcome e) (x, t)).val =
      (Fintype.equivFin Outcome x).val + Fintype.card Outcome * (e t).val := by
  simp only [consTranscriptEquivFin]
  rfl

/-- The empty transcript has numeral coordinate zero. -/
theorem nilTranscriptEquivFin_val (u : Transcript .nil) :
    (nilTranscriptEquivFin u).val = 0 := by
  omega

/-- A tail-coordinate displacement is multiplied by the sizes of two leading alphabets. -/
theorem twoConsEquivFin_delta
    (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {Tf Tp : TList} {Df Dp : ℕ}
    (ef : Equiv (Transcript Tf) (Fin Df))
    (ep : Equiv (Transcript Tp) (Fin Dp))
    (x : α) (y : β) (tf : Transcript Tf) (tp : Transcript Tp)
    (c : ℕ) (h : (ef tf).val = (ep tp).val + c) :
    ((consTranscriptEquivFin α (consTranscriptEquivFin β ef))
      (x, (y, tf))).val =
      ((consTranscriptEquivFin α (consTranscriptEquivFin β ep))
        (x, (y, tp))).val + Fintype.card α * Fintype.card β * c := by
  have hfo := consTranscriptEquivFin_val α (consTranscriptEquivFin β ef) x (y, tf)
  have hfi := consTranscriptEquivFin_val β ef y tf
  have hpo := consTranscriptEquivFin_val α (consTranscriptEquivFin β ep) x (y, tp)
  have hpi := consTranscriptEquivFin_val β ep y tp
  calc
    _ = (Fintype.equivFin α x).val + Fintype.card α *
          ((consTranscriptEquivFin β ef) (y, tf)).val := hfo
    _ = (Fintype.equivFin α x).val + Fintype.card α *
          ((Fintype.equivFin β y).val + Fintype.card β * (ef tf).val) := by
      exact congrArg (fun z => (Fintype.equivFin α x).val + Fintype.card α * z) hfi
    _ = (Fintype.equivFin α x).val + Fintype.card α *
          ((Fintype.equivFin β y).val + Fintype.card β * ((ep tp).val + c)) := by
      exact congrArg (fun z => (Fintype.equivFin α x).val + Fintype.card α *
        ((Fintype.equivFin β y).val + Fintype.card β * z)) h
    _ = ((Fintype.equivFin α x).val + Fintype.card α *
          ((Fintype.equivFin β y).val + Fintype.card β * (ep tp).val)) +
          Fintype.card α * Fintype.card β * c := by ring
    _ = ((Fintype.equivFin α x).val + Fintype.card α *
          ((consTranscriptEquivFin β ep) (y, tp)).val) +
          Fintype.card α * Fintype.card β * c := by
      exact congrArg (fun z => (Fintype.equivFin α x).val + Fintype.card α * z +
        Fintype.card α * Fintype.card β * c) hpi.symm
    _ = _ := by
      exact congrArg (fun z => z + Fintype.card α * Fintype.card β * c) hpo.symm

end TypedLOCC.Transcript
