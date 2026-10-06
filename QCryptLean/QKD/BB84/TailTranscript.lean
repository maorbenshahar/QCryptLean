import QCryptLean.QKD.BB84.SeedTagSyndrome
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.TailTranscript.Raw
import QCryptLean.LOCC.Typed.Boundary.Uniform

/-!
# The classical tail's public transcript, and how to read it

After sifting, each party holds `n = nK + mZ + mX` selected outcome bits and every later action is
classical.  This module fixes the *numbering* of the public cells that the classical tail writes,
and decodes them back into the physical values the final decision consumes.  It contains no program
and no security statement; the stage that announces these cells is defined in
`QCryptLean.QKD.BB84.Program`.

## The register the tail works on

`selectedBitsToRaw` packs a party's `n` selected outcome bits into the single `2 ^ n`-element
classical register `FinalStage.rawSystem` expects, and `registerBit_selectedBitsToRaw` reads an
individual bit back out.  The complete private basis string is deliberately **not** part of the
packed register: it is erased when the tail begins.

## The public cells, in the order they are written

`classicalTailWord` is that chronological announcement word:

1. `n - bb84KeyRoundCount n m` disclosed test rounds, each written as one Bob cell and then one
   Alice cell (`PE.transcriptWord`);
2. one fused cell carrying the privacy-amplification seed index, the verification tag and the
   error-correction syndrome (`QKD.BB84.FusedPublic`).

`classicalPreDecisionBoundary` is the uniform boundary of that word over the raw multipartite
system: after all of it, both parties still hold their raw registers and the final decision has not
yet been announced.

## Reading the cells back

The raw record `PreDecisionRaw` and its decoder `preDecisionRawEquiv`, which the analytical
pre-decision prefix shares, are in `QCryptLean.QKD.BB84.TailTranscript.Raw`.
`ClassicalTailData` is the semantic content of one complete pre-decision transcript: the two
announced PE bit strings in Alice/Bob order, the seed pair, the verification tag and the syndrome.
`classicalTailRawDataEquiv`, `classicalTailDataEquiv` and `classicalTailExitEquiv` are the
*equivalences* — not lossy projections — from raw coordinates, from a transcript, and from a
complete public exit respectively.  Being equivalences is what makes the announced values sufficient
to select the real continuation: the final decision is a function of exactly this data.

Note the one ordering subtlety the decoders record: the announcement chronology is Bob's PE cell
before Alice's, while `ClassicalTailData` presents the strings in the Alice/Bob order the final
stage reads.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## The packed classical register of selected bits -/

/-- Encode the selected local outcome bits as the raw classical register expected by the classical
tail.  The complete private basis string is deliberately absent from the output. -/
def selectedBitsToRaw {N n : ℕ}
    (q : Measurement.SelectedLocalRecord N n) : Fin (2 ^ n) :=
  finFunctionFinEquiv q.2

/-- Register-bit lookup recovers the corresponding selected outcome bit. -/
theorem registerBit_selectedBitsToRaw {N n : ℕ}
    (q : Measurement.SelectedLocalRecord N n) (i : Fin n) :
    LOCC.registerBit n i (selectedBitsToRaw q) = q.2 i := by
  change (@finFunctionFinEquiv 2 n).symm
      (@finFunctionFinEquiv 2 n q.2) i = q.2 i
  rw [Equiv.symm_apply_apply]

/-! ## The chronological announcement word of the classical tail -/

/-- Chronological transcript word for Bob/Alice PE cells followed by the fused seed, tag, and
syndrome announcement. -/
def classicalTailWord (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) : TList :=
  PE.transcriptWord (n - bb84KeyRoundCount n m)
    (.cons (FusedPublic n ℓ ℓEV peSel leakEC) .nil)

/-- Uniform pre-decision boundary reached after all PE and fused public cells. -/
abbrev classicalPreDecisionBoundary (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) : Boundary Party :=
  Boundary.uniform (FinalStage.rawSystem n)
    (classicalTailWord n m ℓ ℓEV peSel leakEC)

/-! ## The semantic data those cells carry -/

/-- Semantic values supplied to the final decision, in Alice/Bob PE order despite the physical
Bob-then-Alice announcement chronology. -/
structure ClassicalTailData (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) where
  alicePE : Fin (n - bb84KeyRoundCount n m) → Fin 2
  bobPE : Fin (n - bb84KeyRoundCount n m) → Fin 2
  seedPair : KeyHashSeedPairEV n ℓ ℓEV peSel
  evTag : Fin (2 ^ ℓEV)
  syndrome : Fin (2 ^ leakEC)

/-- Decode the raw Bob-then-Alice PE coordinates and fused public coordinate into the semantic
data consumed by `FinalStage.program`. -/
noncomputable def classicalTailRawDataEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    PreDecisionRaw (n - bb84KeyRoundCount n m)
        (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC) ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC where
  toFun raw :=
    let fused := (fusedPublicEquiv
      n ℓ ℓEV peSel leakEC).symm raw.fusedRaw
    let tagSyn := finProdFinEquiv.symm fused.2
    { alicePE := fun j => LOCC.outcomeDigit 2 (raw.alicePERaw j)
      bobPE := fun j => LOCC.outcomeDigit 2 (raw.bobPERaw j)
      seedPair := QKD.BB84.Model.announcedSeed n ℓ ℓEV peSel fused.1
      evTag := tagSyn.1
      syndrome := tagSyn.2 }
  invFun d :=
    { bobPERaw := fun j => (LOCC.outcomeDigit 2).symm (d.bobPE j)
      alicePERaw := fun j => (LOCC.outcomeDigit 2).symm (d.alicePE j)
      fusedRaw := fusedPublicEquiv
        n ℓ ℓEV peSel leakEC
        (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) d.seedPair,
          finProdFinEquiv (d.evTag, d.syndrome)) }
  left_inv raw := by
    rcases raw with ⟨bobPE, alicePE, fusedRaw⟩
    dsimp only
    simp only [QKD.BB84.Model.announcedSeed, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
    let f := fusedPublicEquiv n ℓ ℓEV peSel leakEC
    let z := f.symm fusedRaw
    have hpair :
        (z.1, finProdFinEquiv (finProdFinEquiv.symm z.2)) = z := by
      rw [Equiv.apply_symm_apply]
    have hfused : f (z.1, finProdFinEquiv (finProdFinEquiv.symm z.2)) = fusedRaw := by
      rw [hpair]
      exact f.apply_symm_apply fusedRaw
    change PreDecisionRaw.mk (fun j => bobPE j) (fun j => alicePE j)
      (f (z.1, finProdFinEquiv (finProdFinEquiv.symm z.2))) =
        PreDecisionRaw.mk bobPE alicePE fusedRaw
    rw [hfused]
  right_inv d := by
    rcases d with ⟨alicePE, bobPE, seedPair, evTag, syndrome⟩
    simp [QKD.BB84.Model.announcedSeed]

/-- Decode the literal Bob-then-Alice PE cells and fused public cell into the exact semantic data
consumed by `FinalStage.program`.

At each PE cell, `LOCC.outcomeDigit 2` decodes the observed value.  The fused cell is decoded by
`QKD.BB84.fusedPublicEquiv.symm`, its seed index by `QKD.BB84.Model.announcedSeed`, and its value by
`finProdFinEquiv.symm`. -/
noncomputable def classicalTailDataEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    Transcript (classicalTailWord n m ℓ ℓEV peSel leakEC) ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC :=
  (preDecisionRawEquiv
    (n - bb84KeyRoundCount n m)
    (QKD.BB84.Model.bb84AnnounceCard n ℓ ℓEV peSel leakEC)).trans
      (classicalTailRawDataEquiv n m ℓ ℓEV peSel leakEC)

/-- Decode a complete pre-decision public exit into the semantic data supplied to the final
stage. -/
noncomputable def classicalTailExitEquiv (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) :
    (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC :=
  (Boundary.uniformExitEquiv (FinalStage.rawSystem n)
    (classicalTailWord n m ℓ ℓEV peSel leakEC)).trans
      (classicalTailDataEquiv n m ℓ ℓEV peSel leakEC)

end QKD.BB84
