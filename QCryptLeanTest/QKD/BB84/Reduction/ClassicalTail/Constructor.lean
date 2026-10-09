import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.TailOutput
import Mathlib.Util.AssertNoSorry

/-!
# Constructor tests for the direct retained BB84 tail

This test decodes the actual final-point constructor independently of the tail-kernel
theorem.  The calculation is structural bookkeeping for the retained classical program motivated
by Renner, arXiv:quant-ph/0512258v2, Section 6.5, and Nahar et al., arXiv:2403.11851, Section V.C;
it is not a security theorem from either paper.
-/

noncomputable section

namespace QKD.BB84.Reduction.ClassicalTailConstructorTests
open _root_.LOCC

open _root_.LOCC.TwoParty
open QKD.BB84.FiniteKey
open QKD.BB84

/-- Decoding the actual final-point constructor returns the ordered Alice/Bob key slots when its
actual flag is true, and returns the key-free `Unit` abort payload when that flag is false. -/
theorem rawClassicalTailFinalPoint_decoder
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) :
    let flag := QKD.BB84.acceptFlag n m ellEV peSel xSel leakEC ec delta Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)
    FinalStage.outputEquiv ell
        (rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x) =
      if flag then
        Sum.inl
          (QKD.BB84.aliceKey n ell peSel d.seedPair.1 (x .alice),
           QKD.BB84.bobKey n ell peSel leakEC ec d.seedPair.1 d.syndrome
             (x .bob))
      else Sum.inr () := by
  dsimp only
  generalize hflag : QKD.BB84.acceptFlag n m ellEV peSel xSel leakEC ec delta Q
    d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = flag
  cases flag <;> simp [rawClassicalTailFinalPoint, hflag, finalStagePoint, finTwoEquiv] <;> rfl

end QKD.BB84.Reduction.ClassicalTailConstructorTests
