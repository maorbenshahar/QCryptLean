import QCryptLean.QKD.BB84.Measurement.ProductInput
import QCryptLean.QKD.BB84.Completeness

/-!
# The honest BB84 source on the physical input

The canonical source identities hold for every real `q`; this particular source is positive exactly
on `0 ≤ q ≤ 1/2`. The broader `HonestPairLaw` requires positivity, trace one, and the prescribed
matched Z–Z and X–X Born tables. `HonestOperation` consists of tensor powers of such pairs, and its
`rate_nonneg`, `rate_le_one`, and `trace_eq_one` lemmas derive the physical bounds. Equal matched
tables do not characterize invariance under `H ⊗ H`; the canonical pair has both properties, while
invariance alone need not give these tables or uniform marginals.

The library's honest source is `bb84HonestSource N q`: `N` independent EPR pairs, each with Bob's
half sent through the Pauli channel `ρ ↦ (1 - 2q) ρ + q X_B ρ X_B + q Z_B ρ Z_B`
(`bb84HonestPauliChannel`).  One pair is the Bell-diagonal operator with weights `1 - 2q, q, q, 0`
on `Φ⁺, Ψ⁺, Φ⁻, Ψ⁻`: a bit flip with probability `q`, a phase flip with probability `q`, and never
both.  The two errors are mutually exclusive, not independent — independent bit and phase flips at
rate `q` would put weight `q²` on `Ψ⁻` — but in both models the bit and the phase error rates equal
`q`, and those two rates are all that a matched-basis measurement reads.  For `0 ≤ q ≤ 1/2` the pair
is a density operator; outside that range it has a negative eigenvalue.

`honestSource N q` is exactly that operator on the input multipartite system of the measure-first
program, round `i` of the transmitted stream carrying the `i`-th pair
(`honestSource_eq_productSource`).  It is prepared before the program runs, so it does not depend on
the basis strings, the matched-round shuffle or the selection, which the program itself draws
afterwards.  It is also the honest input of the fixed-count robustness layer, read in these
coordinates.

On one honest pair, a measurement in bases `θA, θB` reads the outcome pair `(x, y)` with probability
`honestRoundLaw q θA θB x y`: for equal bases the bits agree with probability `1 - q`, each agreeing
or disagreeing pair being equally likely, and for different bases every pair has probability `1/4`
(`pairBornWeight_honestPair`).  Consequently

* the measurement schedule records independent basis strings and, given them, independent rounds
  with that law (`weightedMeasurementSchedule_honestSource_apply`);
* at every quota-feasible public control, the selected records carry the raw-control mass times
  `honestPairWeight q` on every selected round, whatever its role — the matched Z and X rounds read
  the same law because the honest pair has equal bit and phase error rates
  (`weightedLatePublicSelectionProgram_honestSource_success_apply`).

Portmann--Renner parametrize robustness by a channel noise model `𝒬_q`, naming a depolarizing
channel as an example (arXiv:2102.00021, `qkd.tex:845`--`:848`); the model used here is the Y-free
equal-rate Pauli channel above, not a depolarizing channel.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open QKD.BB84.Sampling
open QKD.BB84.Engine

attribute [local instance] storedRecordVectorDecidableEq

/-! ## The honest source -/

/-- **One honest pair in Alice/Bob bit coordinates**: `bb84HonestSourceSingle q`, whose index
`finProdFinEquiv (x, y)` carries Alice's bit `x` as the high digit and Bob's bit `y` as the low
digit. -/
def honestPair (q : ℝ) : Op (Bit × Bit) :=
  (bb84HonestSourceSingle q).submatrix finProdFinEquiv finProdFinEquiv

/-- Round-grouped coordinates of the physical input multipartite system: digit `i` of the
`4 ^ N`-valued index is `finProdFinEquiv (xA i, xB i)` for Alice's and Bob's input bits of round
`i`, the convention of `bb84HonestSource`. -/
def honestRoundEquiv (N : ℕ) : (weightedStreamSystem Unit N).total ≃ Fin (signalDim ^ N) :=
  (weightedScheduleUnitInputEquiv N).trans <|
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bit) (fun _ => Bit)).symm.trans <|
      (Equiv.piCongrRight fun _ => (finProdFinEquiv : Bit × Bit ≃ Fin signalDim)).trans
        finFunctionFinEquiv

/-- **The honest source on the physical input multipartite system**: `bb84HonestSource N q` read in
the program's input coordinates, round `i` of the transmitted stream carrying the `i`-th honest
pair. -/
def honestSource (N : ℕ) (q : ℝ) : Op (weightedStreamSystem Unit N).total :=
  Matrix.reindex (honestRoundEquiv N).symm (honestRoundEquiv N).symm (bb84HonestSource N q)

/-- **The honest source is the i.i.d. product of the honest pair.** -/
theorem honestSource_eq_productSource (N : ℕ) (q : ℝ) :
    honestSource N q = productSource N (honestPair q) := by
  ext s s'
  simp [honestSource, productSource, bb84HonestSource, honestRoundEquiv, honestPair,
    roundProductOp, reindexOp]

/-- One honest pair has unit trace, for every `q`. -/
theorem honestPair_trace (q : ℝ) : (honestPair q).trace = 1 := by
  rw [← bb84_honestSourceSingle_trace_one q]
  exact Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl

/-- The honest source has unit trace, for every `q`. -/
theorem honestSource_trace (N : ℕ) (q : ℝ) : (honestSource N q).trace = 1 := by
  rw [honestSource_eq_productSource, trace_productSource, honestPair_trace, one_pow]

/-! ## The honest one-round law -/

/-- **The honest law of one matched round's two bits**: agreement with probability `1 - q`,
disagreement with probability `q`, each ordered bit pair equally likely within either case. -/
def honestPairWeight (q : ℝ) (x y : Bit) : ℝ := if x = y then (1 - q) / 2 else q / 2

/-- **The honest law of one round's two recorded bits given both bases**: `honestPairWeight q` for
equal bases and uniform `1/4` for different bases. -/
def honestRoundLaw (q : ℝ) (θA θB : Basis) (x y : Bit) : ℝ :=
  if θA = θB then honestPairWeight q x y else 1 / 4

/-- For equal bases the honest round law is the matched-round law. -/
@[simp] theorem honestRoundLaw_self (q : ℝ) (θ : Basis) (x y : Bit) :
    honestRoundLaw q θ θ x y = honestPairWeight q x y := by
  simp [honestRoundLaw]

/-- The four honest matched-round weights add up to one. -/
theorem sum_honestPairWeight (q : ℝ) : ∑ x : Bit, ∑ y : Bit, honestPairWeight q x y = 1 := by
  simp [honestPairWeight, Fin.sum_univ_two]
  ring

/-- The honest matched-round weights are nonnegative on `0 ≤ q ≤ 1`. -/
theorem honestPairWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x y : Bit) :
    0 ≤ honestPairWeight q x y := by
  unfold honestPairWeight
  split_ifs <;> linarith

/-- Entries of one honest pair in bit coordinates: diagonal `(1 - q)/2` on agreeing and `q/2` on
disagreeing pairs, coherence `(1 - 3q)/2` between the two agreeing pairs and `q/2` between the two
disagreeing pairs. -/
theorem honestPair_apply (q : ℝ) (a b a' b' : Bit) :
    honestPair q (a, b) (a', b') =
      if (a, b) = (a', b') then (if a = b then ((1 - q : ℝ) : ℂ) / 2 else ((q : ℝ) : ℂ) / 2)
      else if a = b ∧ a' = b' then ((1 - 3 * q : ℝ) : ℂ) / 2
      else if a ≠ b ∧ a' ≠ b' then ((q : ℝ) : ℂ) / 2
      else 0 := by
  rw [honestPair, Matrix.submatrix_apply, bb84HonestSourceSingle_eq_matrix, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> simp [finProdFinEquiv]

/-- In Alice/Bob bit coordinates the honest pair is invariant under `H ⊗ H`: this is
`hadamardPair_honestSourceSingle_conj` read through `finProdFinEquiv`. -/
private theorem hadamard_kronecker_conj_honestPair (q : ℝ) :
    (Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard) * honestPair q *
      (Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard) = honestPair q := by
  -- `H ⊗ₖ H` is `bb84HadamardPair = H ⊗ H` read through `finProdFinEquiv`
  have hK : (Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard : Op (Bit × Bit)) =
      QKD.BB84.Model.bb84HadamardPair.submatrix finProdFinEquiv finProdFinEquiv := by
    ext c c'
    simp only [QKD.BB84.Model.bb84HadamardPair, Quantum.TensorProducts.Op.tensor, reindex_apply,
      submatrix_apply, Equiv.symm_apply_apply]
  rw [hK, honestPair, submatrix_mul_equiv, submatrix_mul_equiv,
    QKD.BB84.hadamardPair_honestSourceSingle_conj]

/-- Measuring both halves in the X basis reads the diagonal of the `H ⊗ H`-rotated operator. -/
private theorem pairBornWeight_x_x (σ : Op (Bit × Bit)) (x y : Bit) :
    pairBornWeight σ .x .x x y =
      ((Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard) * σ *
        (Quantum.Gates.hadamard ⊗ₖ Quantum.Gates.hadamard)) (x, y) (x, y) := by
  -- `H` is Hermitian: `star (H i j) = H j i`
  have hH : ∀ i j : Bit, star (Quantum.Gates.hadamard i j) = Quantum.Gates.hadamard j i :=
    fun i j => by rw [← conjTranspose_apply, Quantum.Gates.hadamard_hermitian]
  simp only [pairBornWeight, basisUnitary, mul_apply, kroneckerMap_apply, Finset.sum_mul,
    star_mul', hH]
  exact Finset.sum_comm

/-- A Z-basis measurement of Alice's half selects her bit-`x` block of `σ`. -/
private theorem pairBornWeight_z_left (σ : Op (Bit × Bit)) (θB : Basis) (x y : Bit) :
    pairBornWeight σ .z θB x y = ∑ j : Bit, ∑ j' : Bit,
      basisUnitary θB y j * σ (x, j) (x, j') * star (basisUnitary θB y j') := by
  -- the Z-basis row of Alice's outcome `x` is the indicator of `x`; collapse its two sums
  simp only [pairBornWeight, Fintype.sum_prod_type, basisUnitary_z_apply, apply_ite star,
    star_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]

/-- A Z-basis measurement of Bob's half selects his bit-`y` block of `σ`. -/
private theorem pairBornWeight_z_right (σ : Op (Bit × Bit)) (θA : Basis) (x y : Bit) :
    pairBornWeight σ θA .z x y = ∑ i : Bit, ∑ i' : Bit,
      basisUnitary θA x i * σ (i, y) (i', y) * star (basisUnitary θA x i') := by
  -- the Z-basis row of Bob's outcome `y` is the indicator of `y`; collapse its two sums
  simp only [pairBornWeight, Fintype.sum_prod_type, basisUnitary_z_apply, apply_ite star,
    star_zero, ite_mul, mul_ite, zero_mul, mul_zero, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]

/-- Every X-basis amplitude has modulus squared `1/2`. -/
private theorem basisUnitary_x_mul_mul_star (x j : Bit) (c : ℂ) :
    basisUnitary .x x j * c * star (basisUnitary .x x j) = c / 2 := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hstar : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [basisUnitary_x_apply, star_mul', hstar]
  split_ifs
  · rw [star_neg, star_one]; linear_combination c * hs
  · rw [star_one]; linear_combination c * hs

/-- **The Born table of one honest pair.**  Measuring Alice's half in basis `θA` and Bob's in basis
`θB` yields `(x, y)` with probability `honestRoundLaw q θA θB x y`.  The Z–Z entries are the
computational diagonal; the X–X entries coincide with them because the honest pair is invariant
under `H ⊗ H` (`hadamardPair_honestSourceSingle_conj`); mixed bases give `1/4`. -/
theorem pairBornWeight_honestPair (q : ℝ) (θA θB : Basis) (x y : Bit) :
    pairBornWeight (honestPair q) θA θB x y = (honestRoundLaw q θA θB x y : ℂ) := by
  -- Z–Z: the computational diagonal of the honest pair
  have hzz : pairBornWeight (honestPair q) .z .z x y = (honestPairWeight q x y : ℂ) := by
    rw [pairBornWeight_z_z, honestPair_apply, if_pos rfl, honestPairWeight]
    split_ifs <;> push_cast <;> rfl
  cases θA <;> cases θB
  · rw [hzz, honestRoundLaw_self]
  · -- Z–X: Alice's outcome selects her bit-`x` block, which is diagonal with trace `1/2`
    have h01 : honestPair q (x, 0) (x, 1) = 0 ∧ honestPair q (x, 1) (x, 0) = 0 := by
      fin_cases x <;> simp [honestPair_apply]
    have hdiag : honestPair q (x, 0) (x, 0) + honestPair q (x, 1) (x, 1) = 1 / 2 := by
      fin_cases x <;> simp [honestPair_apply] <;> ring
    rw [pairBornWeight_z_left]
    simp only [Fin.sum_univ_two, h01.1, h01.2, mul_zero, zero_mul, add_zero, zero_add,
      basisUnitary_x_mul_mul_star, honestRoundLaw, reduceCtorEq, if_false]
    push_cast
    linear_combination hdiag / 2
  · -- X–Z: Bob's outcome selects his bit-`y` block, which is diagonal with trace `1/2`
    have h01 : honestPair q (0, y) (1, y) = 0 ∧ honestPair q (1, y) (0, y) = 0 := by
      fin_cases y <;> simp [honestPair_apply]
    have hdiag : honestPair q (0, y) (0, y) + honestPair q (1, y) (1, y) = 1 / 2 := by
      fin_cases y <;> simp [honestPair_apply] <;> ring
    rw [pairBornWeight_z_right]
    simp only [Fin.sum_univ_two, h01.1, h01.2, mul_zero, zero_mul, add_zero, zero_add,
      basisUnitary_x_mul_mul_star, honestRoundLaw, reduceCtorEq, if_false]
    push_cast
    linear_combination hdiag / 2
  · -- X–X: `H ⊗ H` fixes the honest pair, so the X–X weights are the Z–Z weights
    rw [pairBornWeight_x_x, hadamard_kronecker_conj_honestPair,
      ← pairBornWeight_z_z (honestPair q), hzz, honestRoundLaw_self]

/-! ## The first two stages on the honest source -/

/-- **The recorded bases and outcomes of the honest run.**  The measurement schedule's record
block is diagonal; its diagonal entry is the product of both parties' basis-string masses and of
the honest round law at every round's recorded bases and outcomes. -/
theorem weightedMeasurementSchedule_honestSource_apply (pA pB : PMF Basis) (N : ℕ) (q : ℝ)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    (reindexOp (weightedScheduleOutputEquiv Unit N)
      ((weightedMeasurementSchedule pA pB N).denote (honestSource N q)))
        (((), rA), ((), rB)) (((), rA'), ((), rB')) =
      if rA = rA' ∧ rB = rB' then
        ((basisStringLaw N pA (storedBasisString rA)).toReal : ℂ) *
        ((basisStringLaw N pB (storedBasisString rB)).toReal : ℂ) *
        ∏ i, (honestRoundLaw q (rA i).2.1 (rB i).2.1 (rA i).2.2 (rB i).2.2 : ℂ)
      else 0 := by
  rw [honestSource_eq_productSource, weightedMeasurementSchedule_productSource_apply]
  simp_rw [pairBornWeight_honestPair]

/-- **The selected data of the honest run, at every quota-feasible control.**

The selected-record entry between `r` and `r'` is zero unless `r = r'` and both records carry the
announced basis strings; then it is the raw-control mass of `ω` times the honest matched-round law
of every selected round's two bits.  This holds for every control meeting the quotas, including
controls of zero mass; the selected law is the same for all of them. -/
theorem weightedLatePublicSelectionProgram_honestSource_success_apply
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) (q : ℝ) (ω : RawControl N)
    (h : HasQuotas nK mZ mX ω)
    (r r' : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
    (weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote (honestSource N q)
        (lateSelectionSuccessAt N nK mZ mX ω h r) (lateSelectionSuccessAt N nK mZ mX ω h r') =
      if r = r' ∧ r.1.1 = ω.a ∧ r.2.1 = ω.b then
        ((rawControlLaw N pA pB ω).toReal : ℂ) *
          ∏ k, (honestPairWeight q (r.1.2 k) (r.2.2 k) : ℂ)
      else 0 := by
  rw [honestSource_eq_productSource,
    weightedLatePublicSelectionProgram_productSource_success_apply, honestPair_trace, one_pow,
    mul_one]
  simp_rw [pairBornWeight_honestPair, honestRoundLaw_self]

/-! ## Physical inputs with the symmetric matched-basis law -/

/-- A physical pair with uniform matched-basis marginals and disagreement rate `q` in both
Z and X bases. Equal matched tables do not characterize invariance under `H ⊗ H`.
Mixed-basis tables are unconstrained because unmatched rounds are discarded. -/
structure HonestPairLaw (q : ℝ) (σ : Op (Bit × Bit)) : Prop where
  /-- The pair has unit trace. -/
  trace_eq_one : σ.trace = 1
  /-- The pair is a positive semidefinite operator. -/
  posSemidef : σ.PosSemidef
  /-- Both matched measurement bases have the symmetric binary error law. -/
  pairBornWeight_self : ∀ θ x y,
    pairBornWeight σ θ θ x y = (honestPairWeight q x y : ℂ)

/-- Independent identical physical pairs with the prescribed matched-basis law.
This shares the IID input form of Renner, quant-ph/0512258, main.tex:1655–1660; Renner's
class Γ there is defined by non-abortion, rather than by this specific Born table. -/
def HonestOperation (N : ℕ) (q : ℝ) (ρ : Op (weightedStreamSystem Unit N).total) : Prop :=
  ∃ σ : Op (Bit × Bit), HonestPairLaw q σ ∧ ρ = productSource N σ

/-- Positivity of a disagreeing Z-basis outcome implies a nonnegative error rate. -/
lemma HonestPairLaw.rate_nonneg {q : ℝ} {σ : Op (Bit × Bit)} (h : HonestPairLaw q σ) :
    0 ≤ q := by
  have hd := h.posSemidef.diag_nonneg (i := ((0 : Bit), (1 : Bit)))
  rw [← pairBornWeight_z_z σ 0 1, h.pairBornWeight_self] at hd
  have hr := (Complex.nonneg_iff.mp hd).1
  norm_num [honestPairWeight] at hr
  linarith

/-- Positivity of an agreeing Z-basis outcome bounds the error rate by one. -/
lemma HonestPairLaw.rate_le_one {q : ℝ} {σ : Op (Bit × Bit)} (h : HonestPairLaw q σ) :
    q ≤ 1 := by
  have hd := h.posSemidef.diag_nonneg (i := ((0 : Bit), (0 : Bit)))
  rw [← pairBornWeight_z_z σ 0 0, h.pairBornWeight_self] at hd
  have hr := (Complex.nonneg_iff.mp hd).1
  norm_num [honestPairWeight] at hr
  linarith

/-- A physical honest operation has nonnegative error rate. -/
lemma HonestOperation.rate_nonneg {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : 0 ≤ q := by
  obtain ⟨σ, hσ, -⟩ := h
  exact hσ.rate_nonneg

/-- A physical honest operation has error rate at most one. -/
lemma HonestOperation.rate_le_one {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : q ≤ 1 := by
  obtain ⟨σ, hσ, -⟩ := h
  exact hσ.rate_le_one

/-- A product of unit-trace honest pairs has unit trace. -/
lemma HonestOperation.trace_eq_one {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : ρ.trace = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := h
  rw [trace_productSource, hσ.trace_eq_one, one_pow]

/-- The library's Bell-diagonal pair is positive semidefinite for `0 ≤ q ≤ 1/2`. -/
theorem honestPair_posSemidef (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (honestPair q).PosSemidef :=
  (bb84HonestSourceSingle_posSemidef q hq0 hq).submatrix
    (finProdFinEquiv : Bit × Bit ≃ Fin signalDim)

/-- The library's Bell-diagonal pair has the physical honest law for `0 ≤ q ≤ 1/2`. -/
theorem honestPairLaw_honestPair (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    HonestPairLaw q (honestPair q) :=
  ⟨honestPair_trace q, honestPair_posSemidef q hq0 hq, fun θ x y => by
    rw [pairBornWeight_honestPair, honestRoundLaw_self]⟩

/-- The product of the library's honest pairs is an honest operation for `0 ≤ q ≤ 1/2`. -/
theorem honestOperation_honestSource (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    HonestOperation N q (honestSource N q) :=
  ⟨honestPair q, honestPairLaw_honestPair q hq0 hq, honestSource_eq_productSource N q⟩

end QKD.BB84.Measurement
