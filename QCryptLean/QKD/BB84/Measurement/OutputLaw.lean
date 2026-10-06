import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Sampling.Basic

/-!
# Exact output law for the weighted BB84 measurement schedule

This module identifies every terminal record block of the actual finite
destructive measurement schedule with the corresponding rank-one product measurement row.  Alice
and Bob use separate fixed basis PMFs, and the four accumulator row and column coordinates remain
independent.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates measuring each signal before
classical basis announcement and sifting.  Nahar et al., arXiv:2403.11851, source lines 1239--1257
motivate the later permutation/measurement comparison but do not supply an IID input premise here.
The exact rectangular Kraus row and arbitrary-operator coordinate identity are explicit finite
constructions in this library.  No selected-record trace, batch equivalence, classical
continuation, or security claim is included.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- Read the local basis choice from every chronological stored record. -/
def storedBasisString {N : ℕ}
    (r : Fin N → StoredRecord) : Fin N → Basis :=
  fun i => (r i).2.1

/-- The rectangular rank-one row for fixed Alice and Bob chronological records.

Its columns are pairs of input bit strings.  The coefficient is the chronological product of the
two local BB84 basis-unitary entries, with Alice's and Bob's records kept separate.
-/
def fixedBasisPairKraus {N : ℕ}
    (rA rB : Fin N → StoredRecord) :
    Matrix Unit ((Fin N → Bit) × (Fin N → Bit)) ℂ :=
  fun _ x =>
    ∏ i : Fin N,
      basisUnitary (rA i).2.1 (rA i).2.2 (x.1 i) *
      basisUnitary (rB i).2.1 (rB i).2.2 (x.2 i)

/-- The arbitrary input-operator block between four fixed accumulator coordinates.

The Alice and Bob input bit strings remain independent coordinates.  This is only a structural
submatrix of the actual schedule input and assumes no positivity, trace, or Hermiticity.
-/
def weightedScheduleInputBlock
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F]
    (N : ℕ) (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F) :
    Op ((Fin N → Bit) × (Fin N → Bit)) :=
  (reindexOp (weightedStreamPairEquiv F N) rho).submatrix
    (fun x => ((fA, x.1), (fB, x.2)))
    (fun x => ((fA', x.1), (fB', x.2)))

/-- Exact terminal-coordinate law for the auxiliary weighted destructive schedule.

Equal record vectors have the two independent basis-string probabilities times the rank-one
fixed-record measurement of the corresponding arbitrary accumulator block.  Unequal Alice or
Bob record vectors have zero entry.  The statement has no PSD, trace, IID-input, support,
shared-basis, or equal-accumulator-coordinate premise.
-/
theorem weightedMeasurementScheduleAux_output_apply
    (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F]
    (N : ℕ) (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    (reindexOp (weightedScheduleOutputEquiv F N)
      ((weightedMeasurementScheduleAux pA pB F N).denote rho))
        ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) =
      if rA = rA' ∧ rB = rB' then
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (matrixConjLinear (fixedBasisPairKraus rA rB)
          (weightedScheduleInputBlock F N rho fA fA' fB fB')) () ()
      else 0 := by
  have weightedOperationApply (p : PMF Basis) (observed : Record)
      (sigma : Op Bit) (stored stored' : StoredRecord) :
      (weightedMeasureAndRecord p).operation observed sigma stored stored' =
        if stored.2 = observed ∧ stored'.2 = observed then
          ((p observed.1).toReal : ℂ) *
            ∑ j : Bit, ∑ k : Bit,
              basisUnitary observed.1 observed.2 j * sigma j k *
                star (basisUnitary observed.1 observed.2 k)
        else 0 := by
    obtain ⟨θ, x⟩ := observed
    -- The fixed-basis branch is conjugation by the single row `basisUnitary θ x`.
    have hbranch :
        (fixedBasisMeasurement θ).operation x = matrixConjLinear (fixedBasisKraus θ x) := by
      simp only [Instrument.operation, fixedBasisMeasurement, Instrument.ofFine,
        Finset.univ_unique, Finset.sum_singleton]
    have hentry : (matrixConjLinear (fixedBasisKraus θ x) sigma) () () =
        ∑ j : Bit, ∑ k : Bit, basisUnitary θ x j * sigma j k * star (basisUnitary θ x k) := by
      rw [matrixConjLinear_apply, Finset.sum_comm]
      rfl
    rw [weightedMeasureAndRecord, Instrument.keeping_operation_apply,
      Instrument.weightedChoice_operation, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
      hbranch, hentry]
  by_cases hrecords : rA = rA' ∧ rB = rB'
  · rcases hrecords with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    induction N generalizing F with
    | zero =>
        -- No rounds: the only input coordinate is the pair of empty strings `Fin.elim0`, the one
        -- the empty remaining stream carries.
        have hempty (x : Fin 0 → Bit) : x = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
        letI : Unique ((Fin 0 → Bit) × (Fin 0 → Bit)) :=
          { default := ((fun i => Fin.elim0 i), fun i => Fin.elim0 i)
            uniq := fun x => Prod.ext (hempty x.1) (hempty x.2) }
        -- Both laws and the Kraus row are empty products, and the conjugation reads the single
        -- entry of the input block, which `done` returns unchanged.
        rw [matrixConjLinear_apply, Fintype.sum_unique, Fintype.sum_unique]
        simp only [Sampling.basisStringLaw_apply, fixedBasisPairKraus, Fin.prod_univ_zero,
          ENNReal.toReal_one, Complex.ofReal_one, one_mul, mul_one, star_one]
        rw [weightedMeasurementScheduleAux_zero]
        have hdone := LinearMap.congr_fun
          (Program.denote_done (R := weightedStreamSystem F 0)) rho
        exact congrArg (fun M => reindexOp (weightedScheduleOutputEquiv F 0) M
          ((fA, rA), (fB, rB)) ((fA', rA), (fB', rB))) hdone
    | succ n ih =>
        have hout := weightedStreamBobAction_out pA pB F n
        let sigma (observedA observedB : Record) :=
          ((weightedStreamBobAction pA pB F n).liftedOperation observedB
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho)).submatrix
              (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
              (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
        change ((weightedMeasurementScheduleAux pA pB F (n + 1)).denote rho)
          ((weightedScheduleOutputEquiv F (n + 1)).symm
            ((fA, rA), (fB, rB)))
          ((weightedScheduleOutputEquiv F (n + 1)).symm
            ((fA', rA), (fB', rB))) = _
        rw [weightedMeasurementScheduleAux_succ,
          Program.denote_priv_eq_sum_liftedOperation]
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
        conv_lhs =>
          arg 2
          ext observedA
          tactic =>
            exact congrFun (congrFun (LinearMap.congr_fun
              (Program.denote_priv_eq_sum_liftedOperation
                (weightedStreamBobAction pA pB F n) _) _) _) _
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
        conv_lhs =>
          arg 2
          ext observedA
          arg 2
          ext observedB
          tactic => exact Program.denote_cast_apply hout rfl _ _ _ _
        have hrec (observedA observedB : Record) :
            (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n).denote
                (sigma observedA observedB)
                ((weightedScheduleOutputEquiv F (n + 1)).symm
                  ((fA, rA), (fB, rB)))
                ((weightedScheduleOutputEquiv F (n + 1)).symm
                  ((fA', rA), (fB', rB))) =
              ((Sampling.basisStringLaw n pA
                (storedBasisString (Fin.tail rA))).toReal : ℂ) *
              ((Sampling.basisStringLaw n pB
                (storedBasisString (Fin.tail rB))).toReal : ℂ) *
              (matrixConjLinear
                (fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB))
                (weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0)
                  (fB, rB 0) (fB', rB 0))) () () := by
          have h := ih (F := F × StoredRecord)
            (rho := sigma observedA observedB)
            (fA := (fA, rA 0)) (fA' := (fA', rA 0))
            (fB := (fB, rB 0)) (fB' := (fB', rB 0))
            (Fin.tail rA) (Fin.tail rB)
          exact h
        have hstep (observedA observedB : Record)
            (tailA tailA' tailB tailB' : Fin n → Bit) :
            weightedScheduleInputBlock (F × StoredRecord) n
                (sigma observedA observedB)
                (fA, rA 0) (fA', rA 0) (fB, rB 0) (fB', rB 0)
                (tailA, tailB) (tailA', tailB') =
              ((weightedMeasureAndRecord pB).operation observedB
                (fun j k =>
                  ((weightedMeasureAndRecord pA).operation observedA
                    (fun l m => rho
                      ((MultipartiteSystem.pairEquiv _).symm
                        ((fA, Fin.cons l tailA), (fB, Fin.cons j tailB)))
                      ((MultipartiteSystem.pairEquiv _).symm
                        ((fA', Fin.cons m tailA'), (fB', Fin.cons k tailB'))))
                    (rA 0) (rA 0)))
                (rB 0) (rB 0)) := by
          change ((weightedStreamBobAction pA pB F n).liftedOperation observedB
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho))
              ((Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
                ((TwoParty.pairEquiv _ _).symm (((fA, rA 0), tailA), ((fB, rB 0), tailB))))
              ((Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
                ((TwoParty.pairEquiv _ _).symm (((fA', rA 0), tailA'), ((fB', rB 0), tailB')))) = _
          simp only [← Equiv.cast_symm, Equiv.cast_apply,
            weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n]
          rw [weightedStreamBobAction_liftedOperation_apply pA pB F n,
            weightedStreamStep_operation_apply]
          apply congrArg (fun sigma : Op Bit =>
            ((weightedMeasureAndRecord pB).operation observedB sigma)
              (rB 0) (rB 0))
          funext j k
          change
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho)
                ((MultipartiteSystem.pairEquiv _).symm
                  (((fA, rA 0), tailA), (fB, Fin.cons j tailB)))
                ((MultipartiteSystem.pairEquiv _).symm
                  (((fA', rA 0), tailA'), (fB', Fin.cons k tailB'))) = _
          rw [weightedStreamAliceAction_liftedOperation_apply pA F n,
            weightedStreamStep_operation_apply]
          apply congrArg (fun sigma : Op Bit =>
            ((weightedMeasureAndRecord pA).operation observedA sigma)
              (rA 0) (rA 0))
          rfl
        let allCons :
            (((Fin n → Bit) × (Fin n → Bit)) ×
              (((Fin n → Bit) × (Fin n → Bit)) ×
                (Bit × (Bit × (Bit × Bit))))) ≃
              (((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) ×
                ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit))) :=
          { toFun := fun q =>
              ((Fin.cons q.2.2.2.2.2 q.1.1,
                  Fin.cons q.2.2.2.1 q.1.2),
                (Fin.cons q.2.2.2.2.1 q.2.1.1,
                  Fin.cons q.2.2.1 q.2.1.2))
            invFun := fun q =>
              ((Fin.tail q.1.1, Fin.tail q.1.2),
                ((Fin.tail q.2.1, Fin.tail q.2.2),
                  (q.2.2 0, (q.1.2 0, (q.2.1 0, q.1.1 0)))))
            left_inv := by
              intro q
              rcases q with ⟨tc, tr, br, bc, ar, ac⟩
              simp [Fin.tail_cons]
            right_inv := by
              intro q
              rcases q with ⟨⟨cA, cB⟩, ⟨uA, uB⟩⟩
              simp [Fin.cons_self_tail] }
        have sumAll
            (g : ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) →
              ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) → ℂ) :
            (∑ col, ∑ row, g col row) =
              ∑ tailCol : (Fin n → Bit) × (Fin n → Bit),
              ∑ tailRow : (Fin n → Bit) × (Fin n → Bit),
              ∑ bobRow : Bit, ∑ bobCol : Bit,
              ∑ aliceRow : Bit, ∑ aliceCol : Bit,
                g (Fin.cons aliceCol tailCol.1, Fin.cons bobCol tailCol.2)
                  (Fin.cons aliceRow tailRow.1, Fin.cons bobRow tailRow.2) := by
          calc
            _ = ∑ q :
                (((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) ×
                  ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit))),
                g q.1 q.2 := by
              exact (Fintype.sum_prod_type (f := fun q => g q.1 q.2)).symm
            _ = ∑ q, g (allCons q).1 (allCons q).2 := by
              exact (Equiv.sum_comp allCons (fun q => g q.1 q.2)).symm
            _ = _ := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro tailCol _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro tailRow _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro bobRow _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro bobCol _
              rw [Fintype.sum_prod_type]
              rfl
        calc
          _ = ∑ observedA : Record, ∑ observedB : Record,
              ((Sampling.basisStringLaw n pA
                (storedBasisString (Fin.tail rA))).toReal : ℂ) *
              ((Sampling.basisStringLaw n pB
                (storedBasisString (Fin.tail rB))).toReal : ℂ) *
              (matrixConjLinear
                (fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB))
                (weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0)
                  (fB, rB 0) (fB', rB 0))) () () := by
            apply Finset.sum_congr rfl
            intro observedA _
            apply Finset.sum_congr rfl
            intro observedB _
            exact hrec observedA observedB
          _ = _ := by
            -- The head coefficients split off the `n + 1` laws and Kraus row, and the `n + 1`
            -- input block is `rho` read at the consed coordinates.
            have hlaw (p : PMF Basis) (r : Fin (n + 1) → StoredRecord) :
                ((Sampling.basisStringLaw (n + 1) p (storedBasisString r)).toReal : ℂ) =
                  ((p (r 0).2.1).toReal : ℂ) *
                    ((Sampling.basisStringLaw n p (storedBasisString (Fin.tail r))).toReal :
                      ℂ) := by
              rw [Sampling.basisStringLaw_apply, Sampling.basisStringLaw_apply,
                Fin.prod_univ_succ, ENNReal.toReal_mul, Complex.ofReal_mul]
              rfl
            have hK (a b : Bit) (x y : Fin n → Bit) :
                fixedBasisPairKraus rA rB () (Fin.cons a x, Fin.cons b y) =
                  basisUnitary (rA 0).2.1 (rA 0).2.2 a * basisUnitary (rB 0).2.1 (rB 0).2.2 b *
                    fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB) () (x, y) := by
              simp only [fixedBasisPairKraus, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
              rfl
            have hblk (P Q : (Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) :
                weightedScheduleInputBlock F (n + 1) rho fA fA' fB fB' P Q =
                  rho ((MultipartiteSystem.pairEquiv _).symm ((fA, P.1), (fB, P.2)))
                    ((MultipartiteSystem.pairEquiv _).symm ((fA', Q.1), (fB', Q.2))) :=
              rfl
            -- Off the recorded head branches the head operation, hence the tail block, vanishes.
            have hblk_zero (observedA observedB : Record)
                (hne : observedA ≠ (rA 0).2 ∨ observedB ≠ (rB 0).2) :
                weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0) (fB, rB 0) (fB', rB 0) = 0 := by
              ext ⟨tailA, tailB⟩ ⟨tailA', tailB'⟩
              rw [hstep, Matrix.zero_apply]
              rcases hne with hne | hne <;> simp [weightedOperationApply, Ne.symm hne]
            rw [Fintype.sum_eq_single (rA 0).2 fun observedA hne =>
                Fintype.sum_eq_zero _ fun observedB => by
                  rw [hblk_zero observedA observedB (Or.inl hne), map_zero, Matrix.zero_apply,
                    mul_zero],
              Fintype.sum_eq_single (rB 0).2 fun observedB hne => by
                rw [hblk_zero _ observedB (Or.inr hne), map_zero, Matrix.zero_apply, mul_zero]]
            -- The surviving branch entrywise: both sides are the same sum, over the two tails and
            -- the four head bits, of head amplitudes times tail amplitudes times `rho`.
            rw [matrixConjLinear_apply, matrixConjLinear_apply, sumAll, hlaw, hlaw,
              Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun tailCol _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun tailRow _ => ?_
            -- Evaluate Bob's and then Alice's head measurement at the recorded branch,
            rw [hstep, weightedOperationApply, if_pos ⟨rfl, rfl⟩]
            simp only [weightedOperationApply, and_self, ite_true]
            -- split the head factors off the `n + 1` Kraus row and read the `n + 1` block,
            simp only [hK, hblk, star_mul']
            -- and distribute both sides into sums over the four head bits.
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun bobRow _ => Finset.sum_congr rfl fun bobCol _ =>
              Finset.sum_congr rfl fun aliceRow _ => Finset.sum_congr rfl fun aliceCol _ => ?_
            ring
  · rw [if_neg hrecords]
    exact weightedMeasurementScheduleAux_recordsDiagonal pA pB F N rho
      fA fA' fB fB' rA rA' rB rB' (not_and_or.mp hrecords)

/-- Exact terminal-coordinate law for the physical Unit-accumulator schedule.

This is the direct physical specialization of `weightedMeasurementScheduleAux_output_apply`; its
left side contains `weightedMeasurementSchedule` itself rather than an auxiliary alias.
-/
theorem weightedMeasurementSchedule_output_apply
    (pA pB : PMF Basis) (N : ℕ)
    (rho : Op (weightedStreamSystem Unit N).total)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    (reindexOp (weightedScheduleOutputEquiv Unit N)
      ((weightedMeasurementSchedule pA pB N).denote rho))
        (((), rA), ((), rB)) (((), rA'), ((), rB')) =
      if rA = rA' ∧ rB = rB' then
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (matrixConjLinear (fixedBasisPairKraus rA rB)
          (weightedScheduleInputBlock Unit N rho () () () ())) () ()
      else 0 := by
  simpa [weightedMeasurementSchedule] using
    weightedMeasurementScheduleAux_output_apply pA pB Unit N rho
      () () () () rA rA' rB rB'

/-- **Summing a round-wise product over two strings factors round by round.** -/
theorem sum_sum_prod {R : Type*} [CommSemiring R] {ι α : Type} [Fintype ι]
    [DecidableEq ι] [Fintype α] (g : ι → α → α → R) :
    (∑ u : ι → α, ∑ v : ι → α, ∏ r, g r (u r) (v r)) = ∏ r, ∑ x, ∑ y, g r x y := by
  symm
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end QKD.BB84.Measurement
