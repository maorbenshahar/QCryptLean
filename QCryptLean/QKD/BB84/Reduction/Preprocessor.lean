import QCryptLean.QKD.BB84.Program.Coordinates
import QCryptLean.QKD.BB84.Measurement.QuantumBridge
import QCryptLean.QKD.BB84.Sampling.TotalKernels
import QCryptLean.LOCC.Typed.ChannelCoordinates
import QCryptLean.LOCC.Typed.Instrument.Classical
import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import QCryptLean.LOCC.Typed.Instrument.WeightedChoice

/-!
# Ambient comparison preprocessor for memory-free BB84

This module constructs the finite channel that feeds either an explicitly selected input
marginal or a shortage input into the native general-`m` comparison.  Its control register covers
every fixed-cardinality retained subset and every shortage label, including coordinates that have
zero probability in a particular parameter regime.

The construction implements equations (14)--(16) and API item 4 of the memory-free real/ideal
comparison.  Christandl--Koenig--Renner, arXiv:0809.3019, source lines 268--301 and
423--455 motivates the ambient channel comparison.  Renner, arXiv:quant-ph/0512258v2, source
lines 673--736, and Pfister et al., arXiv:1506.07502v3, Sections IV--V and Eq. (35), motivate the
fixed-batch schedule.  The exact finite preprocessor is an explicit construction, not a theorem
quoted from those papers.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction
open TypedLOCC

open Measurement Sampling

/-- Ambient classical control for a retained subset or a shortage label. -/
def ComparisonControl (N n : ℕ) : Type :=
  Set.powersetCard (Fin N) n ⊕ Fin n

deriving instance Fintype, DecidableEq for ComparisonControl

/-- The initial retained subset, used only to exhibit that the success control sector is
inhabited. -/
def comparisonInitialSubset {N n : ℕ} (hN : n ≤ N) :
    Set.powersetCard (Fin N) n :=
  Set.powersetCard.ofFinEmb n (Fin N) (Fin.castLEEmb hN)

/-- The ambient comparison control is inhabited for every `N,n`: use the empty retained subset
when `n = 0`, and the first shortage label when `n` is positive. -/
@[implicit_reducible] def comparisonControlNonempty (N n : ℕ) :
    Nonempty (ComparisonControl N n) :=
  match n with
  | 0 => ⟨Sum.inl (comparisonInitialSubset (N := N) (n := 0) (Nat.zero_le N))⟩
  | k + 1 => ⟨Sum.inr (0 : Fin (k + 1))⟩

attribute [local instance] comparisonControlNonempty

/-- Physical two-party bit-string input on `N` measured signal pairs. -/
abbrev ComparisonPreInput (N : ℕ) :=
  (Fin N → Bit) × (Fin N → Bit)

/-- Numeral native input together with the full ambient comparison control. -/
abbrev ComparisonPreOutput (N n : ℕ) :=
  Fin (2 ^ n * 2 ^ n) × ComparisonControl N n

/-- Numeral coordinates for the selected Alice/Bob bit-string pair. -/
def selectedPairNumeralEquiv (n : ℕ) :
    ((Fin n → Bit) × (Fin n → Bit)) ≃ Fin (2 ^ n * 2 ^ n) :=
  (Equiv.prodCongr (retainedBitCoordinateEquiv n)
      (retainedBitCoordinateEquiv n)).trans finProdFinEquiv

/-- The all-zero native general-`m` input basis coordinate. -/
def comparisonZeroNativeInput (n : ℕ) : Fin (2 ^ n * 2 ^ n) :=
  selectedPairNumeralEquiv n
    ((fun _ => (0 : Bit)), (fun _ => (0 : Bit)))

/-- The actual physical schedule input expressed in its two bit-string coordinates. -/
def comparisonPreInputEquiv (N : ℕ) :
    ComparisonPreInput N ≃
      Fin (Fintype.card (Measurement.weightedStreamSystem Unit N).total) :=
  (weightedScheduleUnitInputEquiv N).symm.trans (Fintype.equivFin _)

/-- Product coordinates for the native input and the complete ambient control register. -/
def comparisonPreOutputEquiv (N n : ℕ) :
    ComparisonPreOutput N n ≃
      Fin ((2 ^ n * 2 ^ n) * Fintype.card (ComparisonControl N n)) :=
  (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv

/-- The actual physical input coordinate dimension is nonzero. -/
@[implicit_reducible] def comparisonPreInputDimNeZero (N : ℕ) :
    NeZero (Fintype.card (Measurement.weightedStreamSystem Unit N).total) :=
  Measurement.weightedStreamInputCardNeZero N

/-- The native-input-times-control output coordinate dimension is nonzero. -/
@[implicit_reducible] def comparisonPreOutputDimNeZero (N n : ℕ) :
    NeZero ((2 ^ n * 2 ^ n) * Fintype.card (ComparisonControl N n)) :=
  ⟨Nat.mul_ne_zero
    (Nat.mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))
    Fintype.card_ne_zero⟩

attribute [local instance] comparisonPreInputDimNeZero
attribute [local instance] comparisonPreOutputDimNeZero

/-- Hidden success branch: a retained subset and one hidden representative of its actual
selected-input marginal instrument. -/
abbrev ComparisonPreSuccessIndex (N n : ℕ) :=
  Σ S : Set.powersetCard (Fin N) n,
    (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).krausIndex ()

/-- Hidden preprocessor branch.  The failure summand is empty when `n = 0`; for positive `n`,
only its label-zero slice has nonzero Kraus matrices. -/
abbrev ComparisonPreKrausIndex (N n : ℕ) :=
  ComparisonPreSuccessIndex N n ⊕ (Fin n × ComparisonPreInput N)

/-- Square-root amplitude for a successful retained-subset branch. -/
def comparisonPreSuccessScale
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  Instrument.weightedChoiceScale
      (selectionStatusLaw N nK mZ mX pA pB) true *
    Instrument.uniformChoiceScale
      (R := Set.powersetCard (Fin N) (nK + mZ + mX))

/-- Kraus matrix for one success subset and one hidden selected-marginal representative. -/
def comparisonPreSuccessKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (t : (selectedInputMarginalInstrument
      (increasingSubsetEmbedding S)).krausIndex ()) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  fun q a =>
    if q.2 = Sum.inl S then
      comparisonPreSuccessScale N nK mZ mX pA pB *
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).kraus () t
            ((selectedPairNumeralEquiv (nK + mZ + mX)).symm q.1) a
    else 0

/-- Square-root amplitude of the shortage branch. -/
def comparisonPreFailureScale
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  Instrument.weightedChoiceScale
    (selectionStatusLaw N nK mZ mX pA pB) false

/-- Kraus matrix for one shortage label and one physical input basis coordinate.

Only label zero is active.  Since the label type is `Fin (nK + mZ + mX)`, the entire family is
empty at zero total quota. -/
def comparisonPreFailureKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (a : ComparisonPreInput N) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  if j.val = 0 then
    comparisonPreFailureScale N nK mZ mX pA pB •
      Matrix.single
        (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) a 1
  else 0

/-- Complete success-or-shortage Kraus family on the full ambient comparison output. -/
def comparisonPreKraus
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (r : ComparisonPreKrausIndex N (nK + mZ + mX)) :
    Matrix (ComparisonPreOutput N (nK + mZ + mX))
      (ComparisonPreInput N) ℂ :=
  match r with
  | Sum.inl ⟨S, t⟩ => comparisonPreSuccessKraus N nK mZ mX pA pB S t
  | Sum.inr ⟨j, a⟩ => comparisonPreFailureKraus N nK mZ mX pA pB j a

/-- The ambient success and shortage Kraus blocks resolve the physical input identity.

The hypothesis supplies the finite success-sector inhabitant; no positivity, support, or
normalization premise on an input operator is used. -/
theorem comparisonPreKraus_complete
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    ∑ r : ComparisonPreKrausIndex N (nK + mZ + mX),
        (comparisonPreKraus N nK mZ mX pA pB r)ᴴ *
          comparisonPreKraus N nK mZ mX pA pB r = 1 := by
  classical
  letI : Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
    ⟨comparisonInitialSubset hN⟩
  have hsuccessS
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (a b : ComparisonPreInput N) :
      ∑ t : (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).krausIndex (),
        ((comparisonPreSuccessKraus N nK mZ mX pA pB S t)ᴴ *
          comparisonPreSuccessKraus N nK mZ mX pA pB S t) a b =
        (star (comparisonPreSuccessScale N nK mZ mX pA pB) *
          comparisonPreSuccessScale N nK mZ mX pA pB) *
            (if a = b then 1 else 0) := by
    simp only [comparisonPreSuccessKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def,
      Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    let I := selectedInputMarginalInstrument (increasingSubsetEmbedding S)
    let s := comparisonPreSuccessScale N nK mZ mX pA pB
    let e := (selectedPairNumeralEquiv (nK + mZ + mX)).symm
    change
      ∑ t : I.krausIndex (), ∑ x,
        star (s * I.kraus () t (e x) a) *
          (s * I.kraus () t (e x) b) =
          if a = b then star s * s else 0
    have hcomplete := congrFun (congrFun I.complete a) b
    simp only [Fintype.sum_unique, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply] at hcomplete
    have hcomplete' :
        (∑ t : I.krausIndex (), ∑ x,
          star (I.kraus () t (e x) a) * I.kraus () t (e x) b) =
            if a = b then 1 else 0 := by
      calc
        _ = ∑ t : I.krausIndex (), ∑ x,
            star (I.kraus () t x a) * I.kraus () t x b := by
          apply Finset.sum_congr rfl
          intro t _
          exact e.sum_comp (fun x =>
            star (I.kraus () t x a) * I.kraus () t x b)
        _ = _ := hcomplete
    simp_rw [show ∀ (t : I.krausIndex ()) (x),
        star (s * I.kraus () t (e x) a) *
            (s * I.kraus () t (e x) b) =
          (star s * s) *
            (star (I.kraus () t (e x) a) * I.kraus () t (e x) b) by
            intros
            rw [star_mul']
            ac_rfl]
    calc
      _ = (star s * s) *
          (∑ t : I.krausIndex (), ∑ x,
            star (I.kraus () t (e x) a) * I.kraus () t (e x) b) := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
      _ = _ := by
        rw [hcomplete', mul_ite, mul_one, mul_zero]
  have hfailure (a b : ComparisonPreInput N) :
      ∑ x : Fin (nK + mZ + mX) × ComparisonPreInput N,
        ((comparisonPreFailureKraus N nK mZ mX pA pB x.1 x.2)ᴴ *
          comparisonPreFailureKraus N nK mZ mX pA pB x.1 x.2) a b =
        (star (comparisonPreFailureScale N nK mZ mX pA pB) *
          comparisonPreFailureScale N nK mZ mX pA pB) *
            (if a = b then 1 else 0) := by
    let s := comparisonPreFailureScale N nK mZ mX pA pB
    have hactive (j : Fin (nK + mZ + mX)) (x : ComparisonPreInput N) :
        (comparisonPreFailureKraus N nK mZ mX pA pB j x)ᴴ *
            comparisonPreFailureKraus N nK mZ mX pA pB j x =
          if j.val = 0 then
            (star s * s) • Matrix.single x x (1 : ℂ)
          else 0 := by
      by_cases hj : j.val = 0
      · simp only [comparisonPreFailureKraus, hj, if_pos]
        dsimp only [ComparisonPreOutput, ComparisonControl]
        rw [Matrix.conjTranspose_smul]
        conv_lhs => tactic => exact Matrix.smul_mul _ _ _
        conv_lhs => arg 2; tactic => exact Matrix.mul_smul _ _ _
        rw [smul_smul, Matrix.conjTranspose_single, star_one,
          Matrix.single_mul_single_same, one_mul]
      · simp [comparisonPreFailureKraus, hj]
    simp_rw [hactive]
    rw [Fintype.sum_prod_type]
    by_cases hn : nK + mZ + mX = 0
    · have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      simp [s, comparisonPreFailureScale,
        Instrument.weightedChoiceScale,
        selectionStatusLaw_apply, selectionStatusWeight,
        selectionFailureMass_zero_quotas]
    · let j : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
      rw [Fintype.sum_eq_single j]
      · by_cases hab : a = b
        · subst b
          simp [j, s, Matrix.single_apply]
        · have hj : j.val = 0 := rfl
          rw [if_neg hab]
          simp only [hj, if_true, smul_single, smul_eq_mul, mul_one]
          simp only [mul_zero]
          apply Finset.sum_eq_zero
          intro x _
          simp only [Matrix.single_apply]
          split
          · rename_i hx
            exact (hab (hx.1.symm.trans hx.2)).elim
          · rfl
      · intro k hk
        have hkval : k.val ≠ 0 := by
          intro hzero
          apply hk
          apply Fin.ext
          simpa [j] using hzero
        simp [hkval]
  rw [Fintype.sum_sum_type]
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.one_apply]
  rw [Fintype.sum_sigma]
  simp only [comparisonPreKraus]
  simp_rw [hsuccessS]
  rw [hfailure]
  by_cases hab : a = b
  · subst b
    simp only [if_true, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [comparisonPreSuccessScale, comparisonPreFailureScale]
    rw [show
        star (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true *
            Instrument.uniformChoiceScale) *
            (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true *
            Instrument.uniformChoiceScale) =
          (star (Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true) *
            Instrument.weightedChoiceScale
              (selectionStatusLaw N nK mZ mX pA pB) true) *
          (star (Instrument.uniformChoiceScale
              (R := Set.powersetCard (Fin N) (nK + mZ + mX))) *
            Instrument.uniformChoiceScale) by
              rw [star_mul']
              ring]
    rw [Instrument.weightedChoiceScale_star_mul,
      Instrument.uniformChoiceScale_star_mul,
      Instrument.weightedChoiceScale_star_mul]
    rw [show (Fintype.card
          (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ) *
          (((selectionStatusLaw N nK mZ mX pA pB true).toReal : ℂ) *
            (Fintype.card
              (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ)⁻¹) =
          ((selectionStatusLaw N nK mZ mX pA pB true).toReal : ℂ) by
            rw [mul_left_comm, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
              mul_one]]
    have hprob := Instrument.weightedChoiceProbability_sum
      (selectionStatusLaw N nK mZ mX pA pB)
    rw [Fintype.sum_bool] at hprob
    simpa only [add_comm] using hprob
  · simp [hab]

/-- Certified one-outcome preprocessor instrument on the complete ambient output space. -/
def comparisonPreInstrument
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    Instrument (ComparisonPreInput N)
      (ComparisonPreOutput N (nK + mZ + mX)) Unit where
  krausIndex _ := ComparisonPreKrausIndex N (nK + mZ + mX)
  kraus _ r := comparisonPreKraus N nK mZ mX pA pB r
  complete := by
    simpa only [Fintype.sum_unique] using
      comparisonPreKraus_complete N nK mZ mX pA pB hN

/-- Complex success coefficient, including the uniform retained-subset probability. -/
def comparisonPreSuccessCoefficient
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  ((selectionSuccessMass N nK mZ mX pA pB).toReal : ℂ) *
    (Fintype.card
      (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℂ)⁻¹

/-- Complex shortage coefficient. -/
def comparisonPreFailureCoefficient
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℂ :=
  ((selectionFailureMass N nK mZ mX pA pB).toReal : ℂ)

/-- The squared modulus of the success amplitude is the success coefficient: the selection-status
weight of success times the uniform retained-subset probability. -/
private lemma comparisonPreSuccessScale_mul_star
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) [Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX))] :
    comparisonPreSuccessScale N nK mZ mX pA pB *
        star (comparisonPreSuccessScale N nK mZ mX pA pB) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB := by
  calc comparisonPreSuccessScale N nK mZ mX pA pB *
          star (comparisonPreSuccessScale N nK mZ mX pA pB)
      = (star (Instrument.weightedChoiceScale (selectionStatusLaw N nK mZ mX pA pB) true) *
            Instrument.weightedChoiceScale (selectionStatusLaw N nK mZ mX pA pB) true) *
          (star (Instrument.uniformChoiceScale (R := Set.powersetCard (Fin N) (nK + mZ + mX))) *
            Instrument.uniformChoiceScale) := by
        rw [comparisonPreSuccessScale, star_mul']; ring
    _ = _ := by
        rw [Instrument.weightedChoiceScale_star_mul, Instrument.uniformChoiceScale_star_mul,
          selectionStatusLaw_apply]
        rfl

/-- Exact ambient entry formula for the comparison preprocessor.

Success keeps the subset-dependent selected marginal.  Shortage writes only the zero native input
and label zero.  Distinct success subsets, distinct shortage labels, and success/shortage cross
blocks are zero. -/
def comparisonPreEntry
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (rho : Op (ComparisonPreInput N))
    (q q' : ComparisonPreOutput N (nK + mZ + mX)) : ℂ :=
  match q.2, q'.2 with
  | Sum.inl S, Sum.inl S' =>
      if S = S' then
        comparisonPreSuccessCoefficient N nK mZ mX pA pB *
          (selectedInputMarginalInstrument
            (increasingSubsetEmbedding S)).channel rho
              ((selectedPairNumeralEquiv (nK + mZ + mX)).symm q.1)
              ((selectedPairNumeralEquiv (nK + mZ + mX)).symm q'.1)
      else 0
  | Sum.inr j, Sum.inr j' =>
      if j.val = 0 ∧ j'.val = 0 ∧
          q.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧
          q'.1 = comparisonZeroNativeInput (nK + mZ + mX) then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- Exact evaluation of the certified preprocessor on every complex operator and every pair of
ambient output coordinates. -/
theorem comparisonPreInstrument_channel_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N)
    (rho : Op (ComparisonPreInput N))
    (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
    (comparisonPreInstrument N nK mZ mX pA pB hN).channel rho q q' =
      comparisonPreEntry N nK mZ mX pA pB rho q q' := by
  classical
  letI : Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
    ⟨comparisonInitialSubset hN⟩
  have hsuccess
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
      ∑ t : (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).krausIndex (),
        (comparisonPreSuccessKraus N nK mZ mX pA pB S t * rho *
          (comparisonPreSuccessKraus N nK mZ mX pA pB S t)ᴴ) q q' =
        if q.2 = Sum.inl S ∧ q'.2 = Sum.inl S then
          comparisonPreSuccessCoefficient N nK mZ mX pA pB *
            (selectedInputMarginalInstrument
              (increasingSubsetEmbedding S)).channel rho
                ((selectedPairNumeralEquiv (nK + mZ + mX)).symm q.1)
                ((selectedPairNumeralEquiv (nK + mZ + mX)).symm q'.1)
        else 0 := by
    rcases q with ⟨x, c⟩
    rcases q' with ⟨x', c'⟩
    by_cases hc : c = Sum.inl S
    · subst c
      by_cases hc' : c' = Sum.inl S
      · subst c'
        -- both output blocks are the `S` block: the entry is `s s̄` times the selected-marginal
        -- channel entry, term by term in the Kraus index and the two contracted input indices
        simp only [comparisonPreSuccessKraus, if_pos, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Instrument.channel, Fintype.sum_unique,
          Instrument.operation, LinearMap.sum_apply, matrixConjLinear,
          LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, and_self, star_mul',
          ← comparisonPreSuccessScale_mul_star, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => by ring
      · simp only [mul_apply, comparisonPreSuccessKraus, ↓reduceIte, conjTranspose_apply, hc',
          star_zero, mul_zero, Finset.sum_const_zero, and_false]
    · simp only [mul_apply, comparisonPreSuccessKraus, hc, ↓reduceIte, zero_mul,
        Finset.sum_const_zero, false_and]
  have hfailure
      (j : Fin (nK + mZ + mX)) (a : ComparisonPreInput N)
      (q q' : ComparisonPreOutput N (nK + mZ + mX)) :
      (comparisonPreFailureKraus N nK mZ mX pA pB j a * rho *
        (comparisonPreFailureKraus N nK mZ mX pA pB j a)ᴴ) q q' =
        if j.val = 0 ∧
            (q.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q.2 = Sum.inr j) ∧
            (q'.1 = comparisonZeroNativeInput (nK + mZ + mX) ∧ q'.2 = Sum.inr j) then
          comparisonPreFailureCoefficient N nK mZ mX pA pB * rho a a
        else 0 := by
    have hscale :
        comparisonPreFailureScale N nK mZ mX pA pB *
            star (comparisonPreFailureScale N nK mZ mX pA pB) =
          comparisonPreFailureCoefficient N nK mZ mX pA pB := by
      rw [comparisonPreFailureScale]
      rw [mul_comm, Instrument.weightedChoiceScale_star_mul,
        selectionStatusLaw_apply]
      rfl
    by_cases hj : j.val = 0
    · -- `(c E_{ia}) ρ (c E_{ia})ᴴ = E_{ii} (c ρ_aa c̄)` with `i = (0, inr j)`
      dsimp only [ComparisonPreOutput, ComparisonControl] at q q' ⊢
      rw [comparisonPreFailureKraus, if_pos hj]
      have hsingle := Matrix.smul_single (comparisonPreFailureScale N nK mZ mX pA pB)
        (comparisonZeroNativeInput (nK + mZ + mX), (Sum.inr j : ComparisonControl N _)) a (1 : ℂ)
      simp only [smul_eq_mul, mul_one] at hsingle
      refine (congrArg (fun K : Matrix (ComparisonPreOutput N (nK + mZ + mX))
          (ComparisonPreInput N) ℂ => (K * rho * Kᴴ) q q') hsingle).trans ?_
      refine (congrArg (fun M : Matrix (ComparisonPreInput N)
          (ComparisonPreOutput N (nK + mZ + mX)) ℂ =>
          (Matrix.single (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) a
            (comparisonPreFailureScale N nK mZ mX pA pB) * rho * M) q q')
          (Matrix.conjTranspose_single _ _ _)).trans ?_
      refine (congrFun (congrFun (Matrix.single_mul_mul_single _ _ _ _ _ rho _) q) q').trans ?_
      rw [Matrix.single_apply, ← hscale]
      apply if_congr _ (mul_right_comm _ _ _) rfl
      constructor
      · rintro ⟨hq, hq'⟩
        exact ⟨hj, Prod.mk.inj hq.symm, Prod.mk.inj hq'.symm⟩
      · rintro ⟨_, hq, hq'⟩
        exact ⟨(Prod.ext hq.1 hq.2).symm, (Prod.ext hq'.1 hq'.2).symm⟩
    · simp only [comparisonPreFailureKraus, hj, ↓reduceIte, Matrix.zero_mul, conjTranspose_zero,
        Matrix.mul_zero, zero_apply, false_and]
  rw [Instrument.channel, Fintype.sum_unique, Instrument.operation]
  simp only [LinearMap.sum_apply, matrixConjLinear, LinearMap.coe_mk,
    AddHom.coe_mk]
  change
    (∑ r : ComparisonPreKrausIndex N (nK + mZ + mX),
      comparisonPreKraus N nK mZ mX pA pB r * rho *
        (comparisonPreKraus N nK mZ mX pA pB r)ᴴ) q q' = _
  rw [Matrix.sum_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [comparisonPreKraus]
  simp_rw [hsuccess]
  rw [Fintype.sum_prod_type]
  simp_rw [hfailure]
  rcases q with ⟨x, c⟩
  rcases q' with ⟨x', c'⟩
  cases c <;> cases c'
  all_goals simp only [comparisonPreEntry]
  case inl.inl S S' =>
    simp only [reduceCtorEq, and_false, and_self, ↓reduceIte,
      Finset.sum_const_zero, add_zero]
    by_cases hSS : S = S'
    · subst S'
      rw [if_pos rfl]
      rw [Fintype.sum_eq_single S]
      · simp
      · intro S hS
        simp only [ite_eq_right_iff]
        intro h
        exfalso
        exact hS (Sum.inl.inj h.1).symm
    · rw [if_neg hSS]
      apply Finset.sum_eq_zero
      intro S _
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hSS
      exact (Sum.inl.inj h.1).trans (Sum.inl.inj h.2).symm
  case inl.inr => simp
  case inr.inl => simp
  case inr.inr j j' =>
    simp only [reduceCtorEq, and_self, ↓reduceIte, Finset.sum_const_zero,
      Finset.sum_ite_irrel, zero_add]
    by_cases hcond :
        j.val = 0 ∧ j'.val = 0 ∧
          x = comparisonZeroNativeInput (nK + mZ + mX) ∧
          x' = comparisonZeroNativeInput (nK + mZ + mX)
    · rw [if_pos hcond]
      have hj : j = j' := by
        apply Fin.ext
        exact hcond.1.trans hcond.2.1.symm
      subst j'
      rw [Fintype.sum_eq_single j]
      · have hbranch :
            j.val = 0 ∧
              (x = comparisonZeroNativeInput (nK + mZ + mX) ∧
                (Sum.inr j : ComparisonControl N (nK + mZ + mX)) = Sum.inr j) ∧
              x' = comparisonZeroNativeInput (nK + mZ + mX) ∧
                (Sum.inr j : ComparisonControl N (nK + mZ + mX)) = Sum.inr j :=
          ⟨hcond.1, ⟨hcond.2.2.1, rfl⟩, hcond.2.2.2, rfl⟩
        refine (if_pos hbranch).trans ?_
        rw [Finset.mul_sum]
      · intro k hne
        simp only [ite_eq_right_iff]
        intro h
        exact (hne (Sum.inr.inj h.2.1.2).symm).elim
    · rw [if_neg hcond]
      apply Finset.sum_eq_zero
      intro k _
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hcond
      refine ⟨?_, ?_, h.2.1.1, h.2.2.1⟩
      · rw [Sum.inr.inj h.2.1.2]
        exact h.1
      · rw [Sum.inr.inj h.2.2.2]
        exact h.1

/-- Success-block evaluation, with the selected marginal depending on the retained subset. -/
theorem comparisonPreInstrument_success_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N)
    (rho : Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (x x' : Fin (2 ^ (nK + mZ + mX) * 2 ^ (nK + mZ + mX))) :
    (comparisonPreInstrument N nK mZ mX pA pB hN).channel rho
        (x, Sum.inl S) (x', Sum.inl S) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB *
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            ((selectedPairNumeralEquiv (nK + mZ + mX)).symm x)
            ((selectedPairNumeralEquiv (nK + mZ + mX)).symm x') := by
  rw [comparisonPreInstrument_channel_apply]
  simp [comparisonPreEntry]

/-- Coordinate-linear ambient comparison preprocessor. -/
def comparisonPre
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    Quantum.Operators.Op
        (Fintype.card (Measurement.weightedStreamSystem Unit N).total) →ₗ[ℂ]
      Quantum.Operators.Op
        ((2 ^ (nK + mZ + mX) * 2 ^ (nK + mZ + mX)) *
          Fintype.card (ComparisonControl N (nK + mZ + mX))) :=
  coordinateLinear (comparisonPreInputEquiv N)
    (comparisonPreOutputEquiv N (nK + mZ + mX))
    (comparisonPreInstrument N nK mZ mX pA pB hN).channel

/-- The explicit ambient comparison preprocessor is completely positive and trace preserving. -/
theorem comparisonPre_isCPTP
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    Quantum.Channels.IsCPTP
      ⇑(comparisonPre N nK mZ mX pA pB hN) := by
  exact (comparisonPreInstrument N nK mZ mX pA pB hN).coordinateChannel_isCPTP
    (comparisonPreInputEquiv N)
    (comparisonPreOutputEquiv N (nK + mZ + mX))

end QKD.BB84.Reduction
