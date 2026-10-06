import QCryptLean.LOCC.Typed.Program.Classical
import QCryptLean.LOCC.Typed.TwoParty
import QCryptLean.QKD.Protocol
import QCryptLean.QKD.BB84.ClassicalData

/-!
# Direct general-`m` BB84 final stage

Bob nondestructively announces the semantic acceptance flag. On acceptance, Alice and Bob
privately compute and retain their respective keys; on abort, both raw registers are discarded
without creating key registers. The construction is a typed finite-round LOCC instrument tree
in the sense of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II.

The public decision follows the classical discussion of Christandl--König--Renner,
arXiv:0809.3019, lines 447--455. The reconciliation and privacy-amplification functions are the
ones described by Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, lines 908--919.
The heterogeneous output retains both local keys on acceptance and no key register on abort.
-/

open Quantum.Operators

noncomputable section

namespace QKD.BB84.FinalStage
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## Laboratory multipartite systems -/

/-- The two raw `2 ^ n`-element classical registers entering the final decision stage. -/
@[reducible] def rawSystem (n : ℕ) : MultipartiteSystem Party :=
  TwoParty.system (Fin (2 ^ n)) (Fin (2 ^ n))

/-- The accepted output multipartite system containing Alice's and Bob's `2 ^ ℓ`-element key
registers. -/
@[reducible] def keySystem (ℓ : ℕ) : MultipartiteSystem Party :=
  TwoParty.system (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))

/-- The abort output multipartite system, containing no Alice or Bob key register. -/
@[reducible] def abortSystem : MultipartiteSystem Party :=
  TwoParty.system Unit Unit

/-! ## Direct decision and accepting continuation -/

/-- Bob nondestructively reads and publicly announces the semantic general-`m` acceptance flag.

The observed outcome type is already `Fin 2`, and `id` is the actual public announcement map.
Consequently the continuation receives `QKD.BB84.Model.acceptFlagOf ... y`, rather than the old
instrument's internal coordinate for that value.  This is the final decision described by the
public classical processing in arXiv:2403.11851, `main.tex:908-919`. -/
def decisionAnnouncement
    (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (evSeed : KeyHashSeed n ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) :
    AnnouncedAction (rawSystem n) (Fin 2) :=
  AnnouncedAction.ofInstrument .bob
    (Instrument.nondemolitionReadout
      (QKD.BB84.Model.acceptFlagOf n m ℓEV peSel xSel leakEC ec δ Q
        as bs evSeed evTag syn)) id

/-- The direct decision action publishes its observed semantic flag without another encoding. -/
@[simp] theorem decisionAnnouncement_announce
    (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (evSeed : KeyHashSeed n ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (flag : Fin 2) :
    (decisionAnnouncement n m ℓEV peSel xSel leakEC ec δ Q
      as bs evSeed evTag syn).announce flag = flag :=
  rfl

/-- Alice privately computes her accepted key and forgets her raw register.

The local function is the existing `QKD.BB84.Model.aliceKeySlotOf`, applied directly.  It is the
Alice-side privacy-amplification computation in arXiv:2403.11851, `main.tex:914-919`. -/
def aliceKeyAction
    (n ℓ : ℕ) (peSel : Fin n → Bool)
    (seed : KeyHashSeed n ℓ peSel) (flag : Fin 2) :
    PrivateAction (rawSystem n) :=
  PrivateAction.ofInstrument .alice
    (Instrument.functionAndForget
      (QKD.BB84.Model.aliceKeySlotOf n ℓ peSel seed flag))

/-- Bob privately reconciles, computes his accepted key, and forgets his raw register.

The syndrome is the already announced Alice syndrome, exactly as in
`QKD.BB84.Model.bobKeySlotOf`.  This realizes the Bob-side reconciliation and common-hash
computation of arXiv:2403.11851, `main.tex:908-919`. -/
def bobKeyAction
    (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ℓ peSel) (syn : Fin (2 ^ leakEC))
    (flag : Fin 2) : PrivateAction (aliceKeyAction n ℓ peSel seed flag).out :=
  PrivateAction.ofInstrument .bob
    (Instrument.functionAndForget
      (QKD.BB84.Model.bobKeySlotOf n ℓ peSel leakEC ec seed syn flag))

/-- The accepting continuation creates Alice's and Bob's keys by two private local functions. -/
def acceptContinuation
    (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ℓ peSel) (syn : Fin (2 ^ leakEC))
    (flag : Fin 2) : Program (rawSystem n) (.leaf (keySystem ℓ)) :=
  cast (by
    apply congrArg (fun R => Program (rawSystem n) (.leaf R))
    change ((system (Fin (2 ^ n)) (Fin (2 ^ n))).set .alice (Fin (2 ^ ℓ))).set
      .bob (Fin (2 ^ ℓ)) = keySystem ℓ
    rw [TwoParty.set_alice, TwoParty.set_bob])
    ((aliceKeyAction n ℓ peSel seed flag).then
      (bobKeyAction n ℓ peSel leakEC ec seed syn flag).run)

/-! ## Direct raw-register abort -/

/-- Alice privately discards her raw `2 ^ n`-element register on abort. -/
def discardAliceRaw (n : ℕ) :
    PrivateAction (rawSystem n) :=
  PrivateAction.ofInstrument .alice
    (Instrument.discardToUnit (Fin (2 ^ n)))

/-- Bob privately discards his raw `2 ^ n`-element register on abort. -/
def discardBobRaw (n : ℕ) :
    PrivateAction (discardAliceRaw n).out :=
  PrivateAction.ofInstrument .bob
    (Instrument.discardToUnit (Fin (2 ^ n)))

/-- Abort both raw registers directly, without first manufacturing zero-valued key registers. -/
def discardKeys (n : ℕ) : Program (rawSystem n) (.leaf abortSystem) :=
  cast (by
    apply congrArg (fun R => Program (rawSystem n) (.leaf R))
    change ((system (Fin (2 ^ n)) (Fin (2 ^ n))).set .alice Unit).set .bob Unit = abortSystem
    rw [TwoParty.set_alice, TwoParty.set_bob])
    ((discardAliceRaw n).then (discardBobRaw n).run)

/-! ## Heterogeneous final stage -/

/-- The branch selected by the semantic flag: digit zero accepts and digit one aborts. -/
def flagBoundary (ℓ : ℕ) (flag : Fin 2) : Boundary Party :=
  if flag = 0 then .leaf (keySystem ℓ) else .leaf abortSystem

/-- The branch-dependent continuation after Bob's semantic decision.

The accepting branch alone evaluates the key functions.  The aborting branch invokes `discardKeys n`
on the raw multipartite system directly. -/
def continuation
    (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ℓ peSel) (syn : Fin (2 ^ leakEC))
    (flag : Fin 2) : Program (rawSystem n) (flagBoundary ℓ flag) := by
  by_cases hflag : flag = 0
  · simpa [flagBoundary, hflag] using
      acceptContinuation n ℓ peSel leakEC ec seed syn flag
  · simpa [flagBoundary, hflag] using discardKeys n

/-- The public boundary of the direct final stage, indexed by the semantic decision flag. -/
def boundary (ℓ : ℕ) : Boundary Party :=
  .announce (Fin 2) (flagBoundary ℓ)

/-- The direct general-`m` final-stage program.

It starts immediately before Bob's final decision and therefore has no permutation, measurement,
parameter-estimation, or fused-announcement prefix.  Those earlier public values occur as explicit
parameters to the decision and key functions. -/
def program
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) : Program (rawSystem n) (boundary ℓ) :=
  (decisionAnnouncement n m ℓEV peSel xSel leakEC ec δ Q
      as bs st.2 evTag syn).then
    fun flag =>
      cast (by
        simp only [decisionAnnouncement, AnnouncedAction.out_ofInstrument, rawSystem,
          TwoParty.set_bob]
        rfl) (continuation n ℓ peSel leakEC ec st.1 syn flag)

/-! ## Reading one complete public exit of the final stage -/

/-- Each branch of the semantic decision is a completed leaf, so it declares exactly one complete
public exit. -/
instance flagBoundaryExitUnique (ℓ : ℕ) (flag : Fin 2) :
    Unique (flagBoundary ℓ flag).Exit := by
  unfold flagBoundary
  split <;> exact inferInstance

/-- **A complete public exit of the final stage is exactly the announced decision flag.**

The branch selected by the flag is a completed leaf, so the flag is this stage's entire public
record: there is no further announcement to read, and no exit is lost. -/
def exitEquiv (ℓ : ℕ) : (boundary ℓ).Exit ≃ Fin 2 where
  toFun e := e.1
  invFun flag := ⟨flag, default⟩
  left_inv e := by
    obtain ⟨flag, leaf⟩ := e
    exact congrArg (Sigma.mk flag) (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- **What survives the final stage.**  When the announced flag accepts, both parties hold a
`2 ^ ℓ`-element key register; when it aborts, neither holds a key register at all — the raw data
was discarded rather than replaced by a zero key. -/
theorem system_eq (ℓ : ℕ) (e : (boundary ℓ).Exit) :
    (boundary ℓ).system e = if e.1 = 0 then keySystem ℓ else abortSystem := by
  obtain ⟨flag, leaf⟩ := e
  change (flagBoundary ℓ flag).system leaf = if flag = 0 then keySystem ℓ else abortSystem
  revert leaf
  unfold flagBoundary
  split
  · rename_i h
    rw [ite_eq_left h]
    intro leaf
    rfl
  · rename_i h
    rw [ite_eq_right h]
    intro leaf
    rfl

/-- Convert the semantic final flag into the key disposition of the heterogeneous output. -/
def disposition (ℓ : ℕ) (flag : Fin 2) : BoundaryKeyLayout.Disposition :=
  if flag = 0 then .accept ℓ else .abort

/-- Local ownership of the accepted keys and the key-free abort output. -/
def outputLayout (ℓ : ℕ) : QKD.OutputLayout (boundary ℓ) where
  alice := .alice
  bob := .bob
  alice_ne_bob := by decide
  disposition e := disposition ℓ e.1
  AliceResidual _ := Unit
  BobResidual _ := Unit
  finAliceResidual _ := inferInstance
  decAliceResidual _ := inferInstance
  nonemptyAliceResidual _ := inferInstance
  finBobResidual _ := inferInstance
  decBobResidual _ := inferInstance
  nonemptyBobResidual _ := inferInstance
  aliceSplit e := by
    rcases e with ⟨flag, e⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at e
      cases e
      change Fin (2 ^ ℓ) ≃ Fin (2 ^ ℓ) × Unit
      exact (Equiv.prodPUnit (Fin (2 ^ ℓ))).symm
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at e
      cases e
      change Unit ≃ Unit × Unit
      exact (Equiv.prodPUnit Unit).symm
  bobSplit e := by
    rcases e with ⟨flag, e⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at e
      cases e
      change Fin (2 ^ ℓ) ≃ Fin (2 ^ ℓ) × Unit
      exact (Equiv.prodPUnit (Fin (2 ^ ℓ))).symm
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at e
      cases e
      change Unit ≃ Unit × Unit
      exact (Equiv.prodPUnit Unit).symm

/-- The heterogeneous output's key disposition at a complete exit is the disposition of the flag
that exit announced. -/
@[simp] theorem outputLayout_disposition (ℓ : ℕ) (e : (boundary ℓ).Exit) :
    (outputLayout ℓ).disposition e = disposition ℓ e.1 := rfl

end QKD.BB84.FinalStage

