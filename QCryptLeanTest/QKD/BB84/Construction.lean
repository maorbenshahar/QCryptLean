import QCryptLean.QKD.BB84.Measurement.Schedule

/-!
# Shapes of the readable BB84 construction

These checks exercise the construction directly: the symbolic completed-record handoff,
physical action order, natural public values,
chronological test collection, quota-shortage leaves, the empty-test tail, and key ownership.
-/

noncomputable section

namespace QKD.BB84.ConstructionTest
open LOCC LOCC.TwoParty Measurement FiniteKey

/-- A symbolic measurement count feeds the actual completed-record basis readouts directly. -/
def measurementThenBases (pA pB : PMF Basis) (N : ℕ) :
    Program (system (streamRegister Unit N) (streamRegister Unit N)) :=
  measureRounds pA pB Unit N <|
    (announceAliceBases N).then fun _ =>
      (announceBobBases N).then fun _ =>
        (Program.done (R := system (CompletedLocalRecord N) (CompletedLocalRecord N)) PUnit.unit)

/-- At symbolic counts the measurement endpoint is exactly the existing completed local record. -/
example (pA pB : PMF Basis) (N : ℕ) : (measurementThenBases pA pB N).boundary =
    .announce (Fin N → Basis) (fun _ => .announce (Fin N → Basis) (fun _ =>
      .leaf (system (CompletedLocalRecord N) (CompletedLocalRecord N)))) :=
  measureRounds_boundary pA pB Unit N _

/-- A zero-round measurement prefix contains no physical action or public cell. -/
example (pA pB : PMF Basis) (k : Program (weightedStreamSystem Unit 0)) :
    measureRounds pA pB Unit 0 k = k := rfl

/-- One round executes Alice's measurement and then Bob's, before either basis announcement. -/
example (pA pB : PMF Basis) : measurementThenBases pA pB 1 =
    (measureAlice pA Unit 0).then ((measureBob pB Unit 0).then <|
      (announceAliceBases 1).then fun _ =>
        (announceBobBases 1).then fun _ => Program.done PUnit.unit) := rfl

/-- Empty test blocks add no announcement. -/
example (n : ℕ) (k : (Fin 0 → Fin 2 × Fin 2) →
    Program (system (Bits n) (Bits n))) :
    announceTests 0 Fin.elim0 k = k Fin.elim0 := rfl

/-- Test positions are visited in their listed order, with Bob before Alice at each position. -/
example : announceTests 2 ![(2 : Fin 3), 0]
    (fun _ => Program.done (End := fun _ => PUnit) PUnit.unit) =
      (announceBobTest (2 : Fin 3)).then (fun _ =>
        (announceAliceTest (2 : Fin 3)).then fun _ =>
          (announceBobTest (0 : Fin 3)).then fun _ =>
            (announceAliceTest (0 : Fin 3)).then fun _ => Program.done PUnit.unit) := rfl

/-- The discussion returns chronological Alice/Bob pairs from the Bob/Alice announcements. -/
example (b₀ a₀ b₁ a₁ : Fin 2) :
    (announceTests 2 ![(2 : Fin 3), 0]
      (fun tests => Program.done (End := fun _ => ULift (Fin 2 → Fin 2 × Fin 2)) ⟨tests⟩)).terminal
        ⟨b₀, a₀, b₁, a₁, ()⟩ =
      ⟨![(a₀, b₀),
        (a₁, b₁)]⟩ := rfl

/-- A public test cell is the bit that the local instrument reads. -/
example (i : Fin 3) : (announceBobTest (A := Unit) i).announce = id := rfl

/-- The seed announcement exposes the seed pair, tag and syndrome directly. -/
example (n ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) :
    (announceSeedTagSyndrome (B := Unit) ℓ ℓEV ec).announce = id := rfl

/-- A zero-round quota shortage retains all three public control cells and then aborts. -/
example (pA pB : PMF Basis) (ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme 1 (@Sampling.packedPESel 1 0 0) leakEC) (δ Q : ℝ) :
    (construction pA pB 0 1 0 0 ℓ ℓEV leakEC ec δ Q).boundary =
      .announce (Fin 0 → Basis) (fun a => .announce (Fin 0 → Basis) (fun b =>
        .announce (Sampling.Shuffle a b) (fun _ => .leaf (system Unit Unit)))) := rfl

/-- Quota shortage executes two private discards, Alice first, with no extra public cell. -/
example (pA pB : PMF Basis) (ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme 1 (@Sampling.packedPESel 1 0 0) leakEC) (δ Q : ℝ) :
    (construction pA pB 0 1 0 0 ℓ ℓEV leakEC ec δ Q) =
      ((announceAliceBases 0).then fun a =>
        (announceBobBases 0).then fun b =>
          (announceShuffle a b).then fun _ =>
            discardAlice.then (discardBob.then (.done KeyEnd.abort))) := rfl

/-- A quota-shortage layout declares no keys. -/
example (pA pB : PMF Basis) (ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme 1 (@Sampling.packedPESel 1 0 0) leakEC) (δ Q : ℝ)
    (a b : Fin 0 → Basis) (order : Sampling.Shuffle a b) :
    ((construction pA pB 0 1 0 0 ℓ ℓEV leakEC ec δ Q).outputLayout (by decide)).disposition
      ⟨a, b, order, ()⟩ = .abort := rfl

/-- Empty tests still leave exactly one tuple followed by Bob's Boolean decision. -/
example (ℓ ℓEV leakEC : ℕ) (peSel xSel : Fin 0 → Bool)
    (ec : ECScheme 0 peSel leakEC) (δ Q : ℝ) :
    (classicalTail 0 0 ℓ ℓEV peSel xSel leakEC ec δ Q).boundary =
      .announce ((KeyHashSeedPairEV 0 ℓ ℓEV peSel × Bits ℓEV × Bits leakEC)) (fun _ =>
        .announce Bool fun flag => if flag then
          .leaf (system (Bits ℓ) (Bits ℓ)) else .leaf (system Unit Unit)) := by
  change Boundary.announce ((KeyHashSeedPairEV 0 ℓ ℓEV peSel × Bits ℓEV × Bits leakEC)) _ = _
  congr 1
  funext cell
  change Boundary.announce Bool _ = _
  congr 1
  funext flag
  cases flag <;> rfl

/-- A true flag declares the two local output registers as accepted keys. -/
example (ℓ ℓEV leakEC : ℕ) (peSel xSel : Fin 0 → Bool)
    (ec : ECScheme 0 peSel leakEC) (δ Q : ℝ)
    (cell : (KeyHashSeedPairEV 0 ℓ ℓEV peSel × Bits ℓEV × Bits leakEC)) :
    ((classicalTail 0 0 ℓ ℓEV peSel xSel leakEC ec δ Q).outputLayout (by decide)).disposition
      ⟨cell, true, ()⟩ = .accept ℓ := rfl

/-- A false flag declares an abort even when the requested key length is zero. -/
example (ℓEV leakEC : ℕ) (peSel xSel : Fin 0 → Bool)
    (ec : ECScheme 0 peSel leakEC) (δ Q : ℝ)
    (cell : (KeyHashSeedPairEV 0 0 ℓEV peSel × Bits ℓEV × Bits leakEC)) :
    ((classicalTail 0 0 0 ℓEV peSel xSel leakEC ec δ Q).outputLayout (by decide)).disposition
      ⟨cell, false, ()⟩ = .abort := rfl

/-- A one-bit accepted key is owned locally with exactly a Unit residual. -/
example (ec : ECScheme 0 Fin.elim0 0) (δ Q : ℝ)
    (cell : (KeyHashSeedPairEV 0 1 0 Fin.elim0 × Bits 0 × Bits 0)) :
    ((classicalTail 0 0 1 0 Fin.elim0 Fin.elim0 0 ec δ Q).outputLayout
      (by decide)).AliceResidual ⟨cell, true, ()⟩ = Unit := rfl

/-- With zero quotas the complete zero-round program reaches its empty-test classical tail. -/
example (pA pB : PMF Basis) (ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme 0 (@Sampling.packedPESel 0 0 0) leakEC) (δ Q : ℝ) :
    (construction pA pB 0 0 0 0 ℓ ℓEV leakEC ec δ Q).boundary =
      .announce (Fin 0 → Basis) (fun a => .announce (Fin 0 → Basis) (fun b =>
        .announce (Sampling.Shuffle a b) (fun _ =>
          (classicalTail 0 0 ℓ ℓEV (@Sampling.packedPESel 0 0 0)
            (@Sampling.packedXSel 0 0 0) leakEC ec δ Q).boundary))) :=
  rfl

end QKD.BB84.ConstructionTest
