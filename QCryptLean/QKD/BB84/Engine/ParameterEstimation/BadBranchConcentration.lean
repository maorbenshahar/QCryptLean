import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.PEConcentration
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.Math.Concentration.SelectedBinomialPassSum
import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialKLChernoff

/-!
# Split-test bad-branch concentration: the per-round sift Born weight and accept mass

The local `H ⊗ H` sift on X-designated parameter-estimation rounds turns the announced two-basis
test into a fail-closed **split test**: the Z-subsample (size `m_Z`) carries the bit statistic
and the disjoint X-subsample (size `m_X`) carries the phase statistic, each earning its own
accept-mass concentration bound at the subsample rate `exp(−2·m·δ²)`.

## Main definitions

- `bb84SiftedBorn`: the per-round sift Born weight.  Every round is read in the computational
  basis; an X-designated PE round is read *after* the local `H ⊗ H`, so its weight is the
  computational diagonal of `bb84XBasisConjugate σ`, while Z-designated PE rounds and key rounds
  carry the unrotated diagonal of `σ`.
- `bb84SiftedLocalAcceptProbabilityOnComponent`: the accept mass of a de Finetti component `σ` —
  the total Born weight of the outcome strings that pass `bb84SiftedLocalPETestPassed`.

## Main results

- `bb84_siftedLocal_le_phaseBinomialPassSum`: dropping the Z-subsample conjunct and marginalising
  every round the X-test does not read, the accept mass is bounded by the binomial PE-pass mass
  of `σ`'s phase marginal over the `m_X` X-test rounds.

Each arm drops the other conjunct of the two-basis test
(`Math.Concentration.SelectedBinomialPassSum.passSum_mono_of_imp`) and then marginalises the
unselected rounds
(`Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`
).
The per-round form of the marginalisation is needed because on the Z arm the unselected rounds are
of two kinds — X-PE rounds carrying the `H⊗H`-rotated Born vector and key rounds carrying the
unrotated one — so a single unselected weight vector cannot express them.

References: Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan
(2024), `arXiv:2403.11851`, Lemma 9 Eq.44; Shor–Preskill (2000) for the `Z ↔ X` duality carried by
`bb84_xBasisConjugate_bitRate_eq_phaseRate`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Basis.BellStates InfoTheory.DeFinetti MeasureTheory
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. The per-round V2 Born weight -/

/-- The computational diagonal of a density operator is nonnegative. -/
private lemma densityOp_diag_re_nonneg (ρ : DensityOp signalDim) (k : Fin signalDim) :
    0 ≤ (ρ.toOp k k).re := by
  have h : (0 : ℂ) ≤ ρ.toOp k k :=
    (Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp).diag_nonneg
  exact (Complex.le_def.mp h).1

/-- The computational diagonal of a density operator sums to one (`Tr ρ = 1`). -/
private lemma densityOp_diag_re_sum (ρ : DensityOp signalDim) :
    (∑ k : Fin signalDim, (ρ.toOp k k).re) = 1 := by
  rw [← Complex.re_sum,
    show (∑ k : Fin signalDim, ρ.toOp k k) = (1 : ℂ) from ρ.trace_one, Complex.one_re]

/-- **The per-round sift Born weight.**

Every round is measured in the computational basis; the only rotation is the local `H ⊗ H`
applied on rounds that are both PE-designated and X-designated (`bb84SiftedSinglePairOp`).  So
the round weight is the computational diagonal of the `H⊗H`-conjugate `bb84XBasisConjugate σ` on
an X-test round and the computational diagonal of `σ` itself on a Z-test round or a key round.
Explicit; no `Classical.choose`. -/
def bb84SiftedBorn (peSel xSel : Bool) (σ : DensityOp signalDim) (k : Fin signalDim) :
    ℝ :=
  if peSel && xSel then ((bb84XBasisConjugate σ).toOp k k).re else (σ.toOp k k).re

/-- Each per-round sift Born weight is nonnegative. -/
theorem bb84SiftedBorn_nonneg (peSel xSel : Bool) (σ : DensityOp signalDim)
    (k : Fin signalDim) : 0 ≤ bb84SiftedBorn peSel xSel σ k := by
  unfold bb84SiftedBorn
  split_ifs
  · exact densityOp_diag_re_nonneg _ k
  · exact densityOp_diag_re_nonneg _ k

/-- The per-round sift Born weights sum to one (`Tr σ = Tr (H⊗H · σ · H⊗H) = 1`). -/
theorem bb84SiftedBorn_sum (peSel xSel : Bool) (σ : DensityOp signalDim) :
    (∑ k : Fin signalDim, bb84SiftedBorn peSel xSel σ k) = 1 := by
  unfold bb84SiftedBorn
  split_ifs
  · exact densityOp_diag_re_sum _
  · exact densityOp_diag_re_sum _

/-- The per-round sift Born weight is continuous in the component `σ`. -/
theorem bb84SiftedBorn_continuous (peSel xSel : Bool) (k : Fin signalDim) :
    Continuous (fun σ : DensityOp signalDim => bb84SiftedBorn peSel xSel σ k) := by
  unfold bb84SiftedBorn
  have hbase : Continuous (fun ρ : DensityOp signalDim => (ρ.toOp k k).re) :=
    Complex.continuous_re.comp
      ((continuous_apply k).comp ((continuous_apply k).comp continuous_induced_dom))
  split_ifs
  · exact hbase.comp bb84XBasisConjugate_continuous
  · exact hbase

/-! ## 2. The accept mass of a de Finetti component -/

/-- **The split-test accept mass of a de Finetti component.**

`∑_{ω accepted} ∏_i bb84SiftedBorn (peSel i) (xSel i) σ (ω i)`: the per-component mass of the
outcome strings that pass the fail-closed LOCC two-basis test `bb84SiftedLocalPETestPassed`, with
each round contributing its computational Born weight after the local sift. Explicit finite sum;
no `Classical.choose`. -/
def bb84SiftedLocalAcceptProbabilityOnComponent
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) : ℝ :=
  ∑ ω : Fin n → Fin signalDim,
    if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
      ∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i) else 0

/-- The accept mass is nonnegative. -/
theorem bb84SiftedLocalAcceptProbabilityOnComponent_nonneg
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) :
    0 ≤ bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ := by
  unfold bb84SiftedLocalAcceptProbabilityOnComponent
  refine Finset.sum_nonneg (fun ω _ => ?_)
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => bb84SiftedBorn_nonneg (peSel i) (xSel i) σ (ω i))
  · exact le_refl 0

/-- The accept mass is at most one: dropping the accept filter, the full sum factorises over
the rounds to `∏_i (∑_k bb84SiftedBorn (peSel i) (xSel i) σ k) = ∏_i 1 = 1`. -/
theorem bb84SiftedLocalAcceptProbabilityOnComponent_le_one
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) :
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤ 1 := by
  unfold bb84SiftedLocalAcceptProbabilityOnComponent
  have hfull :
      (∑ ω : Fin n → Fin signalDim,
        ∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) = 1 := by
    rw [← Fintype.prod_sum
      (f := fun (i : Fin n) (k : Fin signalDim) => bb84SiftedBorn (peSel i) (xSel i) σ k)]
    simp_rw [bb84SiftedBorn_sum]
    simp
  calc
    (∑ ω : Fin n → Fin signalDim,
        if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
          ∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i) else 0)
        ≤ ∑ ω : Fin n → Fin signalDim,
            ∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i) := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          split_ifs
          · exact le_refl _
          · exact Finset.prod_nonneg
              (fun i _ => bb84SiftedBorn_nonneg (peSel i) (xSel i) σ (ω i))
    _ = 1 := hfull

/-- The accept mass is continuous in the component `σ`. -/
theorem bb84SiftedLocalAcceptProbabilityOnComponent_continuous
    (n : ℕ) (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    Continuous (bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ) := by
  unfold bb84SiftedLocalAcceptProbabilityOnComponent
  refine continuous_finsetSum _ (fun ω _ => ?_)
  split_ifs
  · exact continuous_finsetProd _
      (fun i _ => bb84SiftedBorn_continuous (peSel i) (xSel i) (ω i))
  · exact continuous_const

/-! ## 3. The phase-arm accept-mass reduction

The accept mass is reduced by dropping the Z-subsample conjunct (`passSum_mono_of_imp`) and
marginalising out the rounds the X-test does not read
(`selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`). No non-degeneracy hypothesis is
needed: the test is fail-closed, so a degenerate subsample gives accept mass `0`.
-/

/-- The `{1,2}` computational-diagonal mass of `σ` is its bit-flip error rate:
`bitFlipProjector = diag(0,1,1,0)` (`bitFlipProjector_eq_matrix`), so
`Tr(Π_bit · σ) = σ₁₁ + σ₂₂`. -/
private lemma bb84_bitRate_eq_diag_flag_sum (σ : DensityOp signalDim) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin signalDim => j = 1 ∨ j = 2), (σ.toOp j j).re) =
      QKD.BB84.Model.bitFlipErrorRate_single σ := by
  rw [show (Finset.univ.filter (fun j : Fin signalDim => j = 1 ∨ j = 2)) =
        ({1, 2} : Finset (Fin signalDim)) from by decide,
      Finset.sum_pair (by decide : (1 : Fin signalDim) ≠ 2)]
  rw [QKD.BB84.Model.bitFlipErrorRate_single, bitFlipProjector_eq_matrix]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]

open QKD.BB84.Engine in
/-- **X-subsample domination of the accept mass.**

Dropping the Z-subsample condition and marginalising every round the X-test does not read, the
accept mass is bounded by the binomial PE-pass mass of `σ`'s **phase** marginal over the `m_X`
X-test rounds.

The phase identification is exactly the X-test soundness of the sift: an X-designated PE round is
read in the computational basis *after* the local `H ⊗ H`, so its `{1,2}` disagreement rate is
`bitFlipErrorRate_single (bb84XBasisConjugate σ)`, which is `phaseFlipErrorRate_single σ` by
`bb84_xBasisConjugate_bitRate_eq_phaseRate`.

No `m_X ≠ 0` hypothesis: at `m_X = 0` the test is fail-closed. -/
theorem bb84_siftedLocal_le_phaseBinomialPassSum {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) :
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤
      Math.Concentration.BinomialPassSum.binomialPassSum
        (bb84SiftedXTestSampleSize peSel xSel) Q δ (phaseFlipErrorRate_single σ) := by
  classical
  set sel : Fin n → Bool := fun i => peSel i && xSel i with hsel
  have hcard : Fintype.card {i // sel i = true} = bb84SiftedXTestSampleSize peSel xSel := by
    rw [Fintype.card_subtype]
    unfold bb84SiftedXTestSampleSize
    congr 1
    ext i
    simp [hsel]
  have hcount : ∀ ω : Fin n → Fin signalDim,
      (Finset.univ.filter
        (fun i => sel i = true ∧ (fun j : Fin signalDim => j = 1 ∨ j = 2) (ω i))).card =
          bb84SiftedXTestErrorCount peSel xSel ω := by
    intro ω
    unfold bb84SiftedXTestErrorCount
    congr 1
    ext i
    simp [hsel, and_assoc]
  -- On an X-test round the V2 Born weight is the computational diagonal of the `H⊗H`-conjugate.
  have hprodeq : ∀ ω : Fin n → Fin signalDim,
      (∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) =
        ∏ i : Fin n, (if sel i then ((bb84XBasisConjugate σ).toOp (ω i) (ω i)).re
          else bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) := by
    intro ω
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : sel i = true
    · rw [ite_eq_left hi]
      have hx : (peSel i && xSel i) = true := by simpa [hsel] using hi
      simp [bb84SiftedBorn, hx]
    · rw [ite_eq_right hi]
  calc bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
         = ∑ ω : Fin n → Fin signalDim,
          if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
            ∏ i : Fin n, (if sel i then ((bb84XBasisConjugate σ).toOp (ω i) (ω i)).re
              else bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) else 0 := by
        unfold bb84SiftedLocalAcceptProbabilityOnComponent
        exact Finset.sum_congr rfl (fun ω _ => by split_ifs with h; exacts [hprodeq ω, rfl])
    _ ≤ ∑ ω : Fin n → Fin signalDim,
          if |((Finset.univ.filter (fun i => sel i = true ∧
                  (fun j : Fin signalDim => j = 1 ∨ j = 2) (ω i))).card : ℝ) /
                Fintype.card {i // sel i = true} - Q| ≤ δ then
            ∏ i : Fin n, (if sel i then ((bb84XBasisConjugate σ).toOp (ω i) (ω i)).re
              else bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) else 0 := by
        refine Math.Concentration.SelectedBinomialPassSum.passSum_mono_of_imp _ _ _ ?_ ?_
        · intro ω
          refine Finset.prod_nonneg (fun i _ => ?_)
          by_cases hi : sel i = true
          · rw [ite_eq_left hi]; exact densityOp_diag_re_nonneg _ (ω i)
          · rw [ite_eq_right hi]; exact bb84SiftedBorn_nonneg (peSel i) (xSel i) σ (ω i)
        · intro ω hω
          rw [hcount ω, hcard]
          simp only [bb84SiftedLocalPETestPassed, Bool.and_eq_true, decide_eq_true_eq] at hω
          exact hω.2.2
    _ = Math.Concentration.BinomialPassSum.binomialPassSum
          (Fintype.card {i // sel i = true}) Q δ
          (∑ j ∈ Finset.univ.filter (fun j : Fin signalDim => j = 1 ∨ j = 2),
            ((bb84XBasisConjugate σ).toOp j j).re) :=
   Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum_perRound
          (sel := sel) (flag := fun j : Fin signalDim => j = 1 ∨ j = 2)
          (g := fun k => ((bb84XBasisConjugate σ).toOp k k).re)
          (h := fun i k => bb84SiftedBorn (peSel i) (xSel i) σ k)
          (densityOp_diag_re_sum _) (fun i => bb84SiftedBorn_sum (peSel i) (xSel i) σ) Q δ
    _ = Math.Concentration.BinomialPassSum.binomialPassSum
          (bb84SiftedXTestSampleSize peSel xSel) Q δ (phaseFlipErrorRate_single σ) := by
        rw [hcard, bb84_bitRate_eq_diag_flag_sum (bb84XBasisConjugate σ),
          bb84_xBasisConjugate_bitRate_eq_phaseRate σ]

end QKD.BB84.Engine

end
