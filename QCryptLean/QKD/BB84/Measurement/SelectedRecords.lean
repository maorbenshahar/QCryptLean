import QCryptLean.QKD.BB84.Measurement.OutputLaw
import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import QCryptLean.LOCC.Typed.Program.Classical
import QCryptLean.LOCC.Typed.Program.GraftDenotation

/-!
# Selected-record continuation for the weighted BB84 schedule

This module projects each completed local measurement record to its full basis string and the
bits selected by a fixed embedding, packages the two local projections as private classical
actions, and grafts them onto the physical weighted measurement schedule.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates immediate measurement followed
by basis announcement and classical sifting.  Nahar et al., arXiv:2403.11851, source lines
1239--1257 motivates the later permutation/measurement comparison.  The exact arbitrary-operator
identity below is instead a finite coordinate consequence of the library's schedule output law
and selected-input marginal instrument.  The embedding is fixed: this module makes no physical
selector or security claim.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

local instance (N : ℕ) : DecidableEq (Fin N → Basis) :=
  Fintype.decidablePiFintype

local instance (N : ℕ) : DecidableEq (Fin N → Bit) :=
  Fintype.decidablePiFintype

/-- A local record retaining every basis choice and only the outcome bits selected by a fixed
embedding. -/
abbrev SelectedLocalRecord (N n : ℕ) :=
  (Fin N → Basis) × (Fin n → Bit)

/-- Project a completed local chronological record to all bases and the embedded bit substring. -/
def selectedLocalRecord {n N : ℕ} (f : Fin n ↪ Fin N)
    (q : streamRegister (finishAcc Unit N) 0) : SelectedLocalRecord N n :=
  let r := (finishedStreamEquiv Unit N q).2
  (storedBasisString r, fun i => (r (f i)).2.2)

/-- Reassemble the stored records at selected positions from a full basis string and selected
bit string. -/
def selectedStoredRecords {n N : ℕ} (f : Fin n ↪ Fin N)
    (a : Fin N → Basis) (u : Fin n → Bit) : Fin n → StoredRecord :=
  fun i => ((), (a (f i), u i))

/-- Two-party multipartite system after both laboratories retain their selected classical records.
-/
def weightedSelectedRecordSystem (N n : ℕ) : MultipartiteSystem Party :=
  system (SelectedLocalRecord N n) (SelectedLocalRecord N n)

/-- Alice's private deterministic projection of a complete local record. -/
def selectedRecordAliceAction {n N : ℕ} (f : Fin n ↪ Fin N) :
    PrivateAction (weightedStreamSystem (finishAcc Unit N) 0) :=
  PrivateAction.ofInstrument .alice
    (Instrument.functionAndForget (selectedLocalRecord f))

/-- Bob's private deterministic projection of a complete local record. -/
def selectedRecordBobAction {n N : ℕ} (f : Fin n ↪ Fin N) :
    PrivateAction (selectedRecordAliceAction f).out :=
  PrivateAction.ofInstrument .bob
    (Instrument.functionAndForget (selectedLocalRecord f))

/-- Sequential local continuation: Alice projects and erases her full record, then Bob does the
same, without a public control-flow node. -/
def selectedRecordContinuation {n N : ℕ} (f : Fin n ↪ Fin N) :
    Program (weightedStreamSystem (finishAcc Unit N) 0)
      (.leaf (weightedSelectedRecordSystem N n)) :=
  cast (by
    simp only [selectedRecordAliceAction, selectedRecordBobAction,
      PrivateAction.out_ofInstrument, weightedStreamSystem, weightedSelectedRecordSystem,
      TwoParty.set_alice, TwoParty.set_bob])
    ((selectedRecordAliceAction f).then (selectedRecordBobAction f).run)

/-- The actual physical weighted measurement schedule followed by the two local selected-record
projections at its unique exit. -/
def weightedSelectedMeasurementProgram
    (pA pB : PMF Basis) {n : ℕ} (N : ℕ) (f : Fin n ↪ Fin N) :
    Program (weightedStreamSystem Unit N)
      (.leaf (weightedSelectedRecordSystem N n)) :=
  (weightedMeasurementSchedule pA pB N).graft
    (fun _ => selectedRecordContinuation f)

/-- Physical Unit-accumulator input coordinates as Alice and Bob bit strings. -/
def weightedScheduleUnitInputEquiv (N : ℕ) :
    (weightedStreamSystem Unit N).total ≃
      (Fin N → Bit) × (Fin N → Bit) :=
  (weightedStreamPairEquiv Unit N).trans
    (Equiv.prodCongr (unitProdEquiv _) (unitProdEquiv _))

/-- Terminal selected-record coordinates as Alice's and Bob's local records. -/
def selectedRecordOutputEquiv (N n : ℕ) :
    (Boundary.leaf (weightedSelectedRecordSystem N n)).space ≃
      SelectedLocalRecord N n × SelectedLocalRecord N n :=
  (Boundary.leafSpaceEquiv _).trans
    (TwoParty.pairEquiv (SelectedLocalRecord N n) (SelectedLocalRecord N n))

/-- The Unit-accumulator input block is exactly input reindexing by the explicit physical input
equivalence. -/
theorem weightedScheduleInputBlock_unit_eq_reindex (N : ℕ)
    (rho : Op (weightedStreamSystem Unit N).total) :
    weightedScheduleInputBlock Unit N rho () () () () =
      reindexOp (weightedScheduleUnitInputEquiv N) rho := by
  rfl

/-- Explicit selected-record comparison law.  It samples independent basis strings from the two
fixed PMFs, applies the selected-input marginal, and then evaluates the corresponding fixed-basis
measurement row.  Its output matrix is diagonal in both complete selected local records. -/
def selectedMeasurementLaw (pA pB : PMF Basis) {n N : ℕ}
    (f : Fin n ↪ Fin N) :
    Op ((Fin N → Bit) × (Fin N → Bit)) →ₗ[ℂ]
      Op (SelectedLocalRecord N n × SelectedLocalRecord N n) where
  toFun rho q q' :=
    if q.1 = q'.1 ∧ q.2 = q'.2 then
      ((Sampling.basisStringLaw N pA q.1.1).toReal : ℂ) *
      ((Sampling.basisStringLaw N pB q.2.1).toReal : ℂ) *
      (matrixConjLinear
        (fixedBasisPairKraus
          (selectedStoredRecords f q.1.1 q.1.2)
          (selectedStoredRecords f q.2.1 q.2.2))
        ((selectedInputMarginalInstrument f).channel rho)) () ()
    else 0
  map_add' rho sigma := by
    ext q q'
    by_cases h : q.1 = q'.1 ∧ q.2 = q'.2
    · have hqq : q = q' := Prod.ext h.1 h.2
      subst q'
      simp [map_add, mul_add]
    · simp [h]
  map_smul' c rho := by
    ext q q'
    by_cases h : q.1 = q'.1 ∧ q.2 = q'.2
    · have hqq : q = q' := Prod.ext h.1 h.2
      subst q'
      simp [map_smul]
      ring
    · simp [h]

/-- Defining entry formula for the selected-record comparison law. -/
theorem selectedMeasurementLaw_apply (pA pB : PMF Basis) {n N : ℕ}
    (f : Fin n ↪ Fin N)
    (rho : Op ((Fin N → Bit) × (Fin N → Bit)))
    (a a' b b' : Fin N → Basis) (uA uA' uB uB' : Fin n → Bit) :
    selectedMeasurementLaw pA pB f rho
        ((a, uA), (b, uB)) ((a', uA'), (b', uB')) =
      if (a, uA) = (a', uA') ∧ (b, uB) = (b', uB') then
        ((Sampling.basisStringLaw N pA a).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB b).toReal : ℂ) *
        (matrixConjLinear
          (fixedBasisPairKraus
            (selectedStoredRecords f a uA)
            (selectedStoredRecords f b uB))
          ((selectedInputMarginalInstrument f).channel rho)) () ()
      else 0 := by
  rfl

/-! ### Selected and complementary bit coordinates -/

/-- Reading a recombined bit string at an embedded position returns the selected bit. -/
private theorem selectedBitSplit_symm_apply_embedding {n N : ℕ} (f : Fin n ↪ Fin N)
    (u : Fin n → Bit) (v : Fin (N - n) → Bit) (i : Fin n) :
    (selectedBitSplit f).symm (u, v) (f i) = u i :=
  congrFun (congrArg Prod.fst ((selectedBitSplit f).apply_symm_apply (u, v))) i

/-- Reading a recombined bit string at a complementary position returns the complementary bit. -/
private theorem selectedBitSplit_symm_apply_complement {n N : ℕ} (f : Fin n ↪ Fin N)
    (u : Fin n → Bit) (v : Fin (N - n) → Bit) (j : Fin (N - n)) :
    (selectedBitSplit f).symm (u, v) (Math.FiniteEmbedding.embeddingComplementEquiv f j) = v j :=
  congrFun (congrArg Prod.snd ((selectedBitSplit f).apply_symm_apply (u, v))) j

/-- The pair split recombines Alice's and Bob's strings separately. -/
private theorem selectedPairBitSplit_symm_apply {n N : ℕ} (f : Fin n ↪ Fin N)
    (q : ((Fin n → Bit) × (Fin n → Bit)) × ((Fin (N - n) → Bit) × (Fin (N - n) → Bit))) :
    (selectedPairBitSplit f).symm q =
      ((selectedBitSplit f).symm (q.1.1, q.2.1), (selectedBitSplit f).symm (q.1.2, q.2.2)) :=
  rfl

/-- A product over `Fin N` splits into the embedded positions and their complement. -/
private theorem prod_eq_prod_embedding_mul_prod_complement {n N : ℕ} (f : Fin n ↪ Fin N)
    (g : Fin N → ℂ) :
    (∏ i, g i) =
      (∏ i : Fin n, g (f i)) *
        ∏ j : Fin (N - n), g (Math.FiniteEmbedding.embeddingComplementEquiv f j) := by
  rw [← Equiv.prod_comp (Math.FiniteEmbedding.embeddingSplitEquiv f) g, Fintype.prod_sum_type]
  simp only [Math.FiniteEmbedding.embeddingSplitEquiv_apply_range,
    Math.FiniteEmbedding.embeddingSplitEquiv_apply_complement]

/-- The pair Kraus row of complete records whose bits are recombined from selected and
complementary parts factors into the selected-record row and a complementary product. -/
private theorem fixedBasisPairKraus_selectedBitSplit {n N : ℕ} (f : Fin n ↪ Fin N)
    (thetaA thetaB : Fin N → Basis) (uA uB : Fin n → Bit) (vA vB : Fin (N - n) → Bit)
    (q : ((Fin n → Bit) × (Fin n → Bit)) × ((Fin (N - n) → Bit) × (Fin (N - n) → Bit))) :
    fixedBasisPairKraus
        (fun i ↦ ((), (thetaA i, ((selectedBitSplit f).symm (uA, vA)) i)))
        (fun i ↦ ((), (thetaB i, ((selectedBitSplit f).symm (uB, vB)) i)))
        () ((selectedPairBitSplit f).symm q) =
      fixedBasisPairKraus
          (selectedStoredRecords f thetaA uA) (selectedStoredRecords f thetaB uB) () q.1 *
        ∏ j : Fin (N - n),
          basisUnitary (thetaA (Math.FiniteEmbedding.embeddingComplementEquiv f j))
              (vA j) (q.2.1 j) *
            basisUnitary (thetaB (Math.FiniteEmbedding.embeddingComplementEquiv f j))
              (vB j) (q.2.2 j) := by
  simp only [fixedBasisPairKraus]
  rw [prod_eq_prod_embedding_mul_prod_complement f, selectedPairBitSplit_symm_apply]
  simp only [selectedStoredRecords, selectedBitSplit_symm_apply_embedding,
    selectedBitSplit_symm_apply_complement]

/-- Summing over the bit strings with a prescribed selected part is summing over the
complementary part. -/
private theorem sum_ite_selected_eq {n N : ℕ} (f : Fin n ↪ Fin N) (u : Fin n → Bit)
    (g : (Fin N → Bit) → ℂ) :
    (∑ x, if u = (fun i ↦ x (f i)) then g x else 0) =
      ∑ v : Fin (N - n) → Bit, g ((selectedBitSplit f).symm (u, v)) := by
  rw [← (selectedBitSplit f).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_eq_single u fun u' hu' => Finset.sum_eq_zero fun v _ => if_neg fun h =>
      hu' (h.trans (funext (selectedBitSplit_symm_apply_embedding f u' v))).symm]
  exact Finset.sum_congr rfl fun v _ =>
    if_pos (funext (selectedBitSplit_symm_apply_embedding f u v)).symm

/-! ### Completeness of the complementary fixed-basis measurements -/

/-- Row completeness of one fixed-basis measurement: `∑ₒ U(o, x) · conj U(o, x') = δ(x, x')`. -/
private theorem sum_basisUnitary_mul_star (theta : Basis) (x x' : Bit) :
    (∑ observed : Bit,
      basisUnitary theta observed x * star (basisUnitary theta observed x')) =
      if x = x' then 1 else 0 := by
  have h := congrFun (congrFun (fixedBasisKraus_complete theta) x') x
  simpa [fixedBasisKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm, eq_comm] using h

/-- Row completeness of a product of fixed-basis measurements on a finite family of qubits. -/
private theorem sum_prod_basisUnitary_mul_star {ι : Type} [Fintype ι] [DecidableEq ι]
    (theta : ι → Basis) (x x' : ι → Bit) :
    (∑ observed : ι → Bit,
      (∏ i, basisUnitary (theta i) (observed i) (x i)) *
        star (∏ i, basisUnitary (theta i) (observed i) (x' i))) =
      if x = x' then 1 else 0 := by
  calc
    _ = ∑ observed : ι → Bit, ∏ i,
          basisUnitary (theta i) (observed i) (x i) *
            star (basisUnitary (theta i) (observed i) (x' i)) :=
        Finset.sum_congr rfl fun observed _ => by
          rw [star_prod, ← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ observed : Bit,
          basisUnitary (theta i) observed (x i) *
            star (basisUnitary (theta i) observed (x' i)) :=
        (Fintype.prod_sum fun i observed ↦
          basisUnitary (theta i) observed (x i) *
            star (basisUnitary (theta i) observed (x' i))).symm
    _ = ∏ i, if x i = x' i then (1 : ℂ) else 0 :=
        Finset.prod_congr rfl fun i _ => sum_basisUnitary_mul_star (theta i) (x i) (x' i)
    _ = if x = x' then 1 else 0 := by
        rw [Fintype.prod_boole]
        exact if_congr funext_iff.symm rfl rfl

/-- Row completeness of Alice's and Bob's product measurements on the same finite family. -/
private theorem sum_sum_prod_pair_basisUnitary_mul_star {ι : Type} [Fintype ι] [DecidableEq ι]
    (thetaA thetaB : ι → Basis) (x x' : (ι → Bit) × (ι → Bit)) :
    (∑ observedB : ι → Bit, ∑ observedA : ι → Bit,
      (∏ i, basisUnitary (thetaA i) (observedA i) (x.1 i) *
          basisUnitary (thetaB i) (observedB i) (x.2 i)) *
        star (∏ i, basisUnitary (thetaA i) (observedA i) (x'.1 i) *
          basisUnitary (thetaB i) (observedB i) (x'.2 i))) =
      if x = x' then 1 else 0 := by
  calc
    _ = (∑ observedA : ι → Bit,
          (∏ i, basisUnitary (thetaA i) (observedA i) (x.1 i)) *
            star (∏ i, basisUnitary (thetaA i) (observedA i) (x'.1 i))) *
        (∑ observedB : ι → Bit,
          (∏ i, basisUnitary (thetaB i) (observedB i) (x.2 i)) *
            star (∏ i, basisUnitary (thetaB i) (observedB i) (x'.2 i))) := by
        -- Swap the two observation sums and separate Alice's and Bob's factors.
        rw [Fintype.sum_mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun observedA _ => Finset.sum_congr rfl fun observedB _ => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, star_mul']
        ring
    _ = (if x.1 = x'.1 then 1 else 0) * (if x.2 = x'.2 then 1 else 0) := by
        rw [sum_prod_basisUnitary_mul_star, sum_prod_basisUnitary_mul_star]
    _ = if x = x' then 1 else 0 := by
        rw [ite_zero_mul_ite_zero, one_mul]
        exact if_congr Prod.ext_iff.symm rfl rfl

/-! ### Tracing out the complementary bits -/

/-- Four finite sums can be interchanged in pairs. -/
private theorem sum_sum_sum_sum_comm {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] (g : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, g a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, g a b c d :=
  calc
    _ = ∑ a, ∑ c, ∑ d, ∑ b, g a b c d :=
      Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ d, ∑ b, g a b c d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Tracing out through complete product rows.**  Conjugating by the rows `a(x) · b_o(y)` and
summing over a family of rows with `∑ₒ b_o(y) · conj b_o(y') = δ(y, y')` traces out `y`. -/
private theorem sum_sum_conj_mul_row_eq {α β ω₁ ω₂ : Type} [Fintype α] [Fintype β]
    [DecidableEq β] [Fintype ω₁] [Fintype ω₂] (a : α → ℂ) (b : ω₂ → ω₁ → β → ℂ)
    (hb : ∀ y y', (∑ o₁, ∑ o₂, b o₂ o₁ y * star (b o₂ o₁ y')) = if y = y' then 1 else 0)
    (r : Matrix (α × β) (α × β) ℂ) :
    (∑ o₁, ∑ o₂, ∑ col : α × β, ∑ row : α × β,
        a row.1 * b o₂ o₁ row.2 * r row col * star (a col.1 * b o₂ o₁ col.2)) =
      ∑ col : α, ∑ row : α, a row * (∑ y, r (row, y) (col, y)) * star (a col) := by
  rw [sum_sum_sum_sum_comm]
  calc
    _ = ∑ col : α × β, ∑ row : α × β,
          a row.1 * r row col * star (a col.1) * (if row.2 = col.2 then 1 else 0) :=
        Finset.sum_congr rfl fun col _ => Finset.sum_congr rfl fun row _ => by
          rw [← hb, Finset.mul_sum]
          refine Finset.sum_congr rfl fun o₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun o₂ _ => ?_
          rw [star_mul']
          ring
    _ = ∑ col : α × β, ∑ row : α, a row * r (row, col.2) col * star (a col.1) :=
        Finset.sum_congr rfl fun col _ => by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun row _ => ?_
          rw [Fintype.sum_eq_single col.2 fun y hy => by rw [if_neg hy, mul_zero], if_pos rfl,
            mul_one]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun col _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun row _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- **Discarding the complementary bits.**  Summing the complete-record measurement over both
parties' complementary observed bits measures the selected records on the selected-input
marginal. -/
private theorem sum_matrixConjLinear_fixedBasisPairKraus_selectedBitSplit {n N : ℕ}
    (f : Fin n ↪ Fin N) (thetaA thetaB : Fin N → Basis) (uA uB : Fin n → Bit)
    (r : Op ((Fin N → Bit) × (Fin N → Bit))) :
    (∑ observedB : Fin (N - n) → Bit, ∑ observedA : Fin (N - n) → Bit,
      matrixConjLinear
        (fixedBasisPairKraus
          (fun i ↦ ((), (thetaA i, ((selectedBitSplit f).symm (uA, observedA)) i)))
          (fun i ↦ ((), (thetaB i, ((selectedBitSplit f).symm (uB, observedB)) i))))
        r () ()) =
      matrixConjLinear
        (fixedBasisPairKraus
          (selectedStoredRecords f thetaA uA) (selectedStoredRecords f thetaB uB))
        ((selectedInputMarginalInstrument f).channel r) () () := by
  -- The selected row, the complementary rows and the input in split coordinates.
  let kSelected : (Fin n → Bit) × (Fin n → Bit) → ℂ :=
    fixedBasisPairKraus (selectedStoredRecords f thetaA uA) (selectedStoredRecords f thetaB uB) ()
  let kComplement : (Fin (N - n) → Bit) → (Fin (N - n) → Bit) →
      (Fin (N - n) → Bit) × (Fin (N - n) → Bit) → ℂ := fun observedA observedB y ↦
    ∏ j, basisUnitary (thetaA (Math.FiniteEmbedding.embeddingComplementEquiv f j))
        (observedA j) (y.1 j) *
      basisUnitary (thetaB (Math.FiniteEmbedding.embeddingComplementEquiv f j))
        (observedB j) (y.2 j)
  let rSplit := reindexOp (selectedPairBitSplit f) r
  calc
    _ = ∑ observedB, ∑ observedA, ∑ col, ∑ row,
          kSelected row.1 * kComplement observedA observedB row.2 * rSplit row col *
            star (kSelected col.1 * kComplement observedA observedB col.2) :=
        Finset.sum_congr rfl fun observedB _ => Finset.sum_congr rfl fun observedA _ => by
          rw [matrixConjLinear_apply, ← (selectedPairBitSplit f).symm.sum_comp]
          refine Finset.sum_congr rfl fun col _ => ?_
          rw [← (selectedPairBitSplit f).symm.sum_comp]
          refine Finset.sum_congr rfl fun row _ => ?_
          rw [fixedBasisPairKraus_selectedBitSplit, fixedBasisPairKraus_selectedBitSplit]
          rfl
    _ = ∑ col, ∑ row, kSelected row * (∑ y, rSplit (row, y) (col, y)) * star (kSelected col) :=
        sum_sum_conj_mul_row_eq kSelected kComplement
          (fun y y' => sum_sum_prod_pair_basisUnitary_mul_star _ _ y y') rSplit
    _ = _ := by
        rw [matrixConjLinear_apply]
        simp only [selectedInputMarginalInstrument_channel_apply]
        rfl

/-! ### Complete local records -/

/-- Complete local records of the finished schedule as their basis and bit strings. -/
private def finishedRecordEquiv (N : ℕ) :
    streamRegister (finishAcc Unit N) 0 ≃ (Fin N → Basis) × (Fin N → Bit) :=
  ((finishedStreamEquiv Unit N).trans (unitProdEquiv _)).trans
    { toFun := fun r ↦ (storedBasisString r, fun i ↦ (r i).2.2)
      invFun := fun p i ↦ ((), (p.1 i, p.2 i))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The complete record with basis string `p.1` and bit string `p.2` has these records. -/
private theorem finishedStreamEquiv_finishedRecordEquiv_symm (N : ℕ)
    (p : (Fin N → Basis) × (Fin N → Bit)) :
    finishedStreamEquiv Unit N ((finishedRecordEquiv N).symm p) =
      ((), fun i ↦ ((), (p.1 i, p.2 i))) :=
  (finishedStreamEquiv Unit N).apply_symm_apply _

/-- The selected record of the complete record `(θ, x)` is `(θ, x ∘ f)`. -/
private theorem selectedLocalRecord_finishedRecordEquiv_symm {n N : ℕ} (f : Fin n ↪ Fin N)
    (p : (Fin N → Basis) × (Fin N → Bit)) :
    selectedLocalRecord f ((finishedRecordEquiv N).symm p) = (p.1, fun i ↦ p.2 (f i)) := by
  simp only [selectedLocalRecord, finishedStreamEquiv_finishedRecordEquiv_symm]
  rfl

/-- **Summing over the complete records with a prescribed selected record.**  Only the basis
string `theta` contributes, and the bits outside the embedding stay free. -/
private theorem sum_ite_selectedLocalRecord_eq {n N : ℕ} (f : Fin n ↪ Fin N)
    (theta : Fin N → Basis) (u : Fin n → Bit) (g : streamRegister (finishAcc Unit N) 0 → ℂ) :
    (∑ r, if (theta, u) = selectedLocalRecord f r then g r else 0) =
      ∑ v : Fin (N - n) → Bit,
        g ((finishedRecordEquiv N).symm (theta, (selectedBitSplit f).symm (u, v))) := by
  rw [← (finishedRecordEquiv N).symm.sum_comp, Fintype.sum_prod_type]
  simp only [selectedLocalRecord_finishedRecordEquiv_symm, Prod.mk.injEq]
  rw [Fintype.sum_eq_single theta fun theta' h => Finset.sum_eq_zero fun x _ =>
    if_neg fun hx => h hx.1.symm]
  exact (Finset.sum_congr rfl fun x _ => if_congr (and_iff_right rfl) rfl rfl).trans
    (sum_ite_selected_eq f u _)

/-- Diagonal schedule-output entries at two complete records: the two basis-string weights times
the fixed-record measurement of the input. -/
private theorem weightedMeasurementSchedule_output_finishedRecordEquiv_symm
    (pA pB : PMF Basis) (N : ℕ) (rho : Op (weightedStreamSystem Unit N).total)
    (p q : (Fin N → Basis) × (Fin N → Bit)) :
    reindexOp (Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc Unit N) 0))
        ((weightedMeasurementSchedule pA pB N).denote rho)
        ((TwoParty.pairEquiv _ _).symm ((finishedRecordEquiv N).symm p,
          (finishedRecordEquiv N).symm q))
        ((TwoParty.pairEquiv _ _).symm ((finishedRecordEquiv N).symm p,
          (finishedRecordEquiv N).symm q)) =
      ((Sampling.basisStringLaw N pA p.1).toReal : ℂ) *
      ((Sampling.basisStringLaw N pB q.1).toReal : ℂ) *
      (matrixConjLinear
        (fixedBasisPairKraus (fun i ↦ ((), (p.1 i, p.2 i))) (fun i ↦ ((), (q.1 i, q.2 i))))
        (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () :=
  (weightedMeasurementSchedule_output_apply pA pB N rho _ _ _ _).trans (if_pos ⟨rfl, rfl⟩)

/-! ### The grafted program -/

/-- **Entry of the selected-record continuation.** Alice and then Bob replace their complete local
record by its selected projection `selectedLocalRecord f`, so the entry at a pair of selected
records sums the diagonal input entries over the complete records projecting onto them. -/
theorem selectedRecordContinuation_denote_apply {n N : ℕ} (f : Fin n ↪ Fin N)
    (xi : Op (weightedStreamSystem (finishAcc Unit N) 0).total)
    (q q' : SelectedLocalRecord N n × SelectedLocalRecord N n) :
    (selectedRecordContinuation f).denote xi
        ((Boundary.leafSpaceEquiv
          (weightedSelectedRecordSystem N n)).symm
            ((TwoParty.pairEquiv _ _).symm q))
        ((Boundary.leafSpaceEquiv
          (weightedSelectedRecordSystem N n)).symm
            ((TwoParty.pairEquiv _ _).symm q')) =
      ∑ rB : streamRegister (finishAcc Unit N) 0,
        if q.2 = selectedLocalRecord f rB ∧
            q'.2 = selectedLocalRecord f rB then
          ∑ rA : streamRegister (finishAcc Unit N) 0,
            if q.1 = selectedLocalRecord f rA ∧
                q'.1 = selectedLocalRecord f rA then
              xi ((TwoParty.pairEquiv _ _).symm (rA, rB))
                ((TwoParty.pairEquiv _ _).symm (rA, rB))
            else 0
        else 0 := by
  rcases q with ⟨qA, qB⟩
  rcases q' with ⟨qA', qB'⟩
  have hout : (selectedRecordBobAction f).out = weightedSelectedRecordSystem N n := by
    simp only [selectedRecordBobAction, selectedRecordAliceAction,
      PrivateAction.out_ofInstrument, weightedStreamSystem, weightedSelectedRecordSystem,
      TwoParty.set_alice, TwoParty.set_bob]
  have hcoord (a b : SelectedLocalRecord N n) :
      (Equiv.cast (congrArg Boundary.space (congrArg Boundary.leaf hout.symm)))
          ((Boundary.leafSpaceEquiv (weightedSelectedRecordSystem N n)).symm
            ((TwoParty.pairEquiv _ _).symm (a, b))) =
        (Boundary.leafSpaceEquiv (selectedRecordBobAction f).out).symm
          ((selectedRecordBobAction f).out.pairEquiv.symm (a, b)) := by
    change cast (congrArg (fun T => (Boundary.leaf T).space) hout.symm)
      ((Boundary.leafSpaceEquiv (weightedSelectedRecordSystem N n)).symm
        ((weightedSelectedRecordSystem N n).pairEquiv.symm (a, b))) = _
    rw [Boundary.cast_leafSpaceEquiv_symm hout.symm,
      MultipartiteSystem.cast_pairEquiv_symm hout.symm]
    rfl
  change (selectedRecordContinuation f).denote xi
    ((Boundary.leafSpaceEquiv (weightedSelectedRecordSystem N n)).symm
      ((TwoParty.pairEquiv _ _).symm (qA, qB)))
    ((Boundary.leafSpaceEquiv (weightedSelectedRecordSystem N n)).symm
      ((TwoParty.pairEquiv _ _).symm (qA', qB'))) = _
  unfold selectedRecordContinuation
  rw [Program.denote_cast_apply rfl (congrArg Boundary.leaf hout.symm), hcoord, hcoord]
  change ((selectedRecordAliceAction f).then (selectedRecordBobAction f).run).denote xi
    ((Boundary.leafSpaceEquiv (selectedRecordBobAction f).out).symm
      ((selectedRecordBobAction f).out.pairEquiv.symm (qA, qB)))
    ((Boundary.leafSpaceEquiv (selectedRecordBobAction f).out).symm
      ((selectedRecordBobAction f).out.pairEquiv.symm (qA', qB'))) = _
  unfold PrivateAction.then PrivateAction.run
  rw [Program.denote_priv_eq_sum_liftedOperation]
  change ((∑ o : Unit, ((selectedRecordBobAction f).then Program.done).denote ∘ₗ
    (selectedRecordAliceAction f).liftedOperation o) xi) _ _ = _
  rw [Fintype.sum_unique]
  simp only [LinearMap.comp_apply]
  unfold PrivateAction.then
  rw [Program.denote_priv_eq_sum_liftedOperation]
  change ((∑ o : Unit, Program.done.denote ∘ₗ (selectedRecordBobAction f).liftedOperation o)
    ((selectedRecordAliceAction f).liftedOperation () xi)) _ _ = _
  rw [Fintype.sum_unique]
  simp only [LinearMap.comp_apply, Program.denote_done]
  change ((selectedRecordBobAction f).liftedOperation ()
    ((selectedRecordAliceAction f).liftedOperation () xi))
      ((selectedRecordBobAction f).out.pairEquiv.symm (qA, qB))
      ((selectedRecordBobAction f).out.pairEquiv.symm (qA', qB')) = _
  change (((Instrument.functionAndForget (selectedLocalRecord f)).liftAt
    (selectedRecordAliceAction f).out .bob).operation ()
      ((selectedRecordAliceAction f).liftedOperation () xi))
        (((selectedRecordAliceAction f).out.set .bob (SelectedLocalRecord N n)).pairEquiv.symm
          (qA, qB))
        (((selectedRecordAliceAction f).out.set .bob (SelectedLocalRecord N n)).pairEquiv.symm
          (qA', qB')) = _
  rw [Instrument.liftAt_bob_operation_apply, Instrument.functionAndForget_operation_apply]
  have hAliceApply (a a' : SelectedLocalRecord N n)
      (rB : streamRegister (finishAcc Unit N) 0) :
      ((selectedRecordAliceAction f).liftedOperation () xi)
          ((selectedRecordAliceAction f).out.pairEquiv.symm (a, rB))
          ((selectedRecordAliceAction f).out.pairEquiv.symm (a', rB)) =
        ∑ rA : streamRegister (finishAcc Unit N) 0,
          if a = selectedLocalRecord f rA ∧ a' = selectedLocalRecord f rA then
            xi ((TwoParty.pairEquiv _ _).symm (rA, rB))
              ((TwoParty.pairEquiv _ _).symm (rA, rB))
          else 0 := by
    change (((Instrument.functionAndForget (selectedLocalRecord f)).liftAt
      (weightedStreamSystem (finishAcc Unit N) 0) .alice).operation () xi)
        (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
          (SelectedLocalRecord N n)).pairEquiv.symm (a, rB))
        (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
          (SelectedLocalRecord N n)).pairEquiv.symm (a', rB)) = _
    rw [Instrument.liftAt_alice_operation_apply, Instrument.functionAndForget_operation_apply]
    rfl
  simp_rw [Matrix.submatrix_apply, hAliceApply]
  rfl

/-- **Entry law of the grafted program.**  An output entry of the selected-record program sums
the diagonal entries of the schedule output over the complete local records that project to the
given selected records. -/
private theorem weightedSelectedMeasurementProgram_denote_apply
    (pA pB : PMF Basis) {n : ℕ} (N : ℕ) (f : Fin n ↪ Fin N)
    (rho : Op (weightedStreamSystem Unit N).total) (qA qB qA' qB' : SelectedLocalRecord N n) :
    reindexOp (selectedRecordOutputEquiv N n)
        ((weightedSelectedMeasurementProgram pA pB N f).denote rho) (qA, qB) (qA', qB') =
      ∑ rB : streamRegister (finishAcc Unit N) 0,
        if qB = selectedLocalRecord f rB ∧ qB' = selectedLocalRecord f rB then
          ∑ rA : streamRegister (finishAcc Unit N) 0,
            if qA = selectedLocalRecord f rA ∧ qA' = selectedLocalRecord f rA then
              reindexOp (Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc Unit N) 0))
                  ((weightedMeasurementSchedule pA pB N).denote rho)
                ((TwoParty.pairEquiv _ _).symm (rA, rB))
                ((TwoParty.pairEquiv _ _).symm (rA, rB))
            else 0
        else 0 := by
  -- The schedule output on the leaf's register coordinates.
  set sigma : Op (weightedStreamSystem (finishAcc Unit N) 0).total :=
    reindexOp (Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc Unit N) 0))
      ((weightedMeasurementSchedule pA pB N).denote rho)
  have hsigma :
      (Program.done : Program (weightedStreamSystem (finishAcc Unit N) 0)
        (.leaf (weightedStreamSystem (finishAcc Unit N) 0))).denote sigma =
        (weightedMeasurementSchedule pA pB N).denote rho := by
    ext q q'
    simp [sigma, Program.denote_done, reindexOp,
      Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply]
  -- The grafted continuation runs the selected-record continuation on `sigma`.
  have hgraft :
      (weightedSelectedMeasurementProgram pA pB N f).denote rho =
        (selectedRecordContinuation f).denote sigma := by
    have hdone := LinearMap.congr_fun (Program.controlledContinuation_comp_denote_done
      (weightedStreamSystem (finishAcc Unit N) 0) (fun _ => selectedRecordContinuation f)) sigma
    rw [LinearMap.comp_apply, hsigma] at hdone
    exact (LinearMap.congr_fun (Program.denote_graft (weightedMeasurementSchedule pA pB N)
      (fun _ => selectedRecordContinuation f)) rho).trans hdone
  rw [hgraft]
  exact selectedRecordContinuation_denote_apply f sigma (qA, qB) (qA', qB')

/-- Exact arbitrary-operator identity between the grafted physical selected-record program and
the explicit selected-input-marginal comparison law.

This finite coordinate statement specializes the destructive measurement schedule motivated by
Renner, arXiv:quant-ph/0512258v2, source lines 673--736.  It introduces no IID, positivity,
normalization, full-support, or selection-success premise; the later physical selector and
security transfer are outside this statement.
-/
theorem weightedSelectedMeasurementProgram_denote_eq
    (pA pB : PMF Basis) {n : ℕ} (N : ℕ) (f : Fin n ↪ Fin N) :
    (reindexOp (selectedRecordOutputEquiv N n)).comp
        (weightedSelectedMeasurementProgram pA pB N f).denote =
      (selectedMeasurementLaw pA pB f).comp
        (reindexOp (weightedScheduleUnitInputEquiv N)) := by
  apply LinearMap.ext
  intro rho
  ext ⟨⟨a, uA⟩, ⟨b, uB⟩⟩ ⟨⟨a', uA'⟩, ⟨b', uB'⟩⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, weightedSelectedMeasurementProgram_denote_apply,
    selectedMeasurementLaw_apply]
  by_cases hdiag : (a, uA) = (a', uA') ∧ (b, uB) = (b', uB')
  · -- Diagonal entries: both record sums run over the complementary bits only.
    obtain ⟨⟨⟩, ⟨⟩⟩ := hdiag
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [and_self, sum_ite_selectedLocalRecord_eq,
      weightedMeasurementSchedule_output_finishedRecordEquiv_symm]
    -- Pull out the basis-string weights and discard the complementary bits.
    rw [← sum_matrixConjLinear_fixedBasisPairKraus_selectedBitSplit, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
  · -- Off-diagonal entries vanish: a complete record has a single selected record.
    rw [if_neg hdiag]
    refine Finset.sum_eq_zero fun rB _ => ?_
    by_cases hB : (b, uB) = selectedLocalRecord f rB ∧ (b', uB') = selectedLocalRecord f rB
    · rw [if_pos hB]
      exact Finset.sum_eq_zero fun rA _ => if_neg fun hA =>
        hdiag ⟨hA.1.trans hA.2.symm, hB.1.trans hB.2.symm⟩
    · exact if_neg hB

end QKD.BB84.Measurement
