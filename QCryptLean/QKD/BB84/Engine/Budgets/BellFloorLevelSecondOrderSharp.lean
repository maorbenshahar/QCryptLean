import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.Engine.Budgets.SecondOrderSharpPenalty
import QCryptLean.QKD.BB84.Engine.Budgets.BellPolyDimTight
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy

/-!
# The Bell carried floor level at the sharp-cap Cor IV.2 penalty and a general PE test-set size `m`

`bb84BellFloorLevelSecondOrderSharp` is the carried floor level of the Bell `C(n+3,3)` row at the
Dupuis–Fawzi Cor IV.2 penalty with the sharp variance cap `bb84SharpVarianceCap = log₂²(1+√2)`
(the bound `V(X|B) ≤ log₂²(1+√2)`, `condDivergenceVariance_le_logb_one_add_sqrt_two`), at a general
test-set split point `m` (key-round count `bb84KeyRoundCount n m = n − m`). Pure scalar definition;
no quantum content.

## Two different words spelled "sharp"

`sharpCharge` (in the security-cell names elsewhere) is the Bell `C(n+3,3)` de Finetti
**charge**, against the CKR `C(n+15,15)`.  The suffix *SecondOrderSharp* denotes the Dupuis–Fawzi
Cor IV.2 **penalty** at the sharp variance cap `bb84SharpVarianceCap = log₂²(1+√2)`
(`condDivergenceVariance_le_logb_one_add_sqrt_two`).  The two are independent axes and the names
are not to be unified.

## Magnitude

At `n = 6·10⁶`, `m = 200 000` (so `n_K = 5 800 000`) and `ε_AEP = 2⁻⁴³¹` the naive (Bennett-style)
finite-size penalty is `193 993.66` bits against
`finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap ≈ 110 340` bits — a factor `≈ 1.758`.
Read as admissible key length on the Bell tight-rate row that is `≈ 83 653` bits of `ℓ` out of
`4 708 755`, i.e. `+1.78 %`.

## Window and deviation

Alongside the free-β axis, `bb84BellFloorLevelSecondOrderSharpAtDev` moves the entropy edge of the
rate factor from the doubled window edge `Q + 2·δ` to the deviation edge `Q + δ + dev`: the window
`δ` keeps only its protocol role (accept-test half-width), the **deviation** `dev` is where the
floor is charged, and `dev = δ` gives the doubled-window level
(`bb84BellFloorLevelSecondOrderSharpAtDev_eq`).  This is the separation of Nahar et al. 2024
(arXiv:2403.11851) Lemma 9 Eq. 44 with §V.C.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`), `\label{lem:divergence-variance-general-bounds}` (`:394`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), `\label{lem:groupPurification}`
(`main.tex:354`), §V.C (`main.tex:909` — the general test-set size `m`; `main.tex:913` —
`n_key = n − m`).
-/

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.Engine

/-- **The Bell carried floor level at the sharp-cap Cor IV.2 penalty and a general test-set
size `m`.**

The rate factor
`(n_K/log 2)·(log 2 − h₂(Q+2δ))` at `n_K = bb84KeyRoundCount n m = n − m`, minus the Cor IV.2
sharp-variance-cap finite-size penalty
`finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap n_K εTensor`. The reference is
the component’s own quantum marginal.

The later purifying-register extension charges `2·log₂ C(n+3,3)` at the full `n`.
The component floor defined here has no de Finetti charge.

**The penalty's copy count IS the key-round count** `bb84KeyRoundCount n m`: the AEP lift is
taken over the `n_K` key rounds, and that is the same `n_K` the rate factor scopes.  A copy count
larger than the rate scope would fund a penalty the entropy does not pay for.

**No hypothesis relating `m` and `n` appears.**  The split point enters only through the key-round
count, so `m = 0` (no test rounds, `n_K = n`) and `m ≥ n` (`n_K = 0`, the level collapses to
`−P_sharp 0 ε`) are both covered and both degenerate.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`)
`\label{cor:continuity-bound-halpha_new}` (`:784`), `\label{eq_eathmin_halpha}` (`:1053`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), §V.C (`main.tex:909`, `:913`). -/
noncomputable def bb84BellFloorLevelSecondOrderSharp (n m : ℕ) (Q δ εTensor : ℝ) : ℝ :=
  (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap (bb84KeyRoundCount n m) εTensor

/-- A positive Bell floor after postselection, error-correction and verification charges
requires the test-set size to be strictly below the total round count. -/
lemma lt_of_bb84BellFloorLevelSecondOrderSharp_charged_pos
    {n m ℓEV leakEC : ℕ} {Q δ εTensor : ℝ}
    (hkEVpos : 0 < bb84BellFloorLevelSecondOrderSharp n m Q δ εTensor -
      2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) :
    m < n := by
  have hpen := finiteSizePenaltySecondOrderSharp_nonneg bb84SharpVarianceCap
    bb84SharpVarianceCap_pos.le (bb84KeyRoundCount n m) εTensor
  have hlog : 0 ≤ Real.log (bb84PolyDimTight n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (bb84PolyDimTight_pos n).ne')
  have hcharge : 0 ≤ 2 * Real.log (bb84PolyDimTight n : ℝ) / Real.log 2 :=
    div_nonneg (by linarith) (Real.log_pos one_lt_two).le
  by_contra hmn
  have hzero : bb84KeyRoundCount n m = 0 := Nat.sub_eq_zero_of_le (by omega)
  rw [bb84BellFloorLevelSecondOrderSharp, hzero, Nat.cast_zero, zero_div, zero_mul] at hkEVpos
  rw [hzero] at hpen
  have hleak : (0 : ℝ) ≤ leakEC := Nat.cast_nonneg _
  have hEV : (0 : ℝ) ≤ ℓEV := Nat.cast_nonneg _
  linarith

/-- **The Bell carried floor level at the sharp-cap Cor IV.2 penalty charged at a free
Rényi offset `β`, and a general test-set size `m`.**

Same expression as `bb84BellFloorLevelSecondOrderSharp` with the Dupuis–Fawzi Cor IV.2 penalty
evaluated at an arbitrary admissible `β ∈ (0, 1)` (`finiteSizePenaltySecondOrderSharpAt`)
instead of at the clamped optimiser `secondOrderSharpBeta`.  The free-β version lets the improved
BB84 row pick any admissible offset.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`)
`\label{cor:continuity-bound-halpha_new}` (`:784`), `\label{eq_eathmin_halpha}` (`:1053`);
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`). -/
noncomputable def bb84BellFloorLevelSecondOrderSharpAt (n m : ℕ) (Q δ εTensor β : ℝ) : ℝ :=
  (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap (bb84KeyRoundCount n m) εTensor β

/-- The fixed-β⋆ floor level is the free-β floor level at `β = secondOrderSharpBeta …`. -/
lemma bb84BellFloorLevelSecondOrderSharp_eq (n m : ℕ) (Q δ εTensor : ℝ) :
    bb84BellFloorLevelSecondOrderSharp n m Q δ εTensor
      = bb84BellFloorLevelSecondOrderSharpAt n m Q δ εTensor
          (secondOrderSharpBeta bb84SharpVarianceCap (bb84KeyRoundCount n m) εTensor) :=
  rfl

/-- **The Bell carried floor level at the sharp-cap Cor IV.2 penalty charged at a free
Rényi offset `β`, a general test-set size `m`, and a free phase-error deviation.**

The same two terms as `bb84BellFloorLevelSecondOrderSharpAt`, with the entropy argument of the
key-scoped phase-only AEP rate moved from the window edge `Q + 2·δ` (where the window half-width
`δ` is charged twice: once as the accept-test window, once as the deviation between the window
edge and the phase-error rate the floor is charged at) to the general deviation edge `Q + δ + dev`.
Here `δ = p.tolerance` keeps only its protocol role — the accept-test window — and `dev` is the
phase-error **deviation**; `dev = δ` gives the doubled-window level up to the arithmetic rewrite
`δ + δ = 2 * δ`.

This is the separation of Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44 with §V.C: the entropy floor is charged at the soundness edge, not at the
completeness window. -/
noncomputable def bb84BellFloorLevelSecondOrderSharpAtDev
    (n m : ℕ) (Q δ dev εTensor β : ℝ) : ℝ :=
  (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + δ + dev)) -
    finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap (bb84KeyRoundCount n m) εTensor β

/-- The doubled-window free-β level is the Dev level at `dev = δ` (up to `δ + δ = 2 * δ`). -/
lemma bb84BellFloorLevelSecondOrderSharpAtDev_eq (n m : ℕ) (Q δ εTensor β : ℝ) :
    bb84BellFloorLevelSecondOrderSharpAtDev n m Q δ δ εTensor β
      = bb84BellFloorLevelSecondOrderSharpAt n m Q δ εTensor β := by
  unfold bb84BellFloorLevelSecondOrderSharpAtDev bb84BellFloorLevelSecondOrderSharpAt
  rw [add_assoc, two_mul]

end QKD.BB84.Engine

end -- noncomputable section
