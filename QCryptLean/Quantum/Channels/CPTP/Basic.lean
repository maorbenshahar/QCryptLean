import Mathlib.LinearAlgebra.Complex.Module
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Metrics.TraceNorm.Jordan
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# CPTP Maps — Kraus representation, Choi matrix, Stinespring dilation

Completely positive trace-preserving (CPTP) maps representing the most general
quantum operations on density operators.

## Main definitions
- `KrausRepresentation`: Kraus operator representation of quantum channels
- `KrausRepresentation.castOutput`: casts a Kraus representation along an
  output-dimension equality
- `ChoiMatrix`: Choi-Jamiołkowski matrix of a quantum operation
- `IsCompletelyPositive`: Predicate for completely positive maps (Choi matrix PSD)
- `IsTracePreserving`: Predicate for trace-preserving maps
- `IsCPTP`: Predicate for completely positive trace-preserving maps
- `DilationRecovers`: Stinespring recovery predicate Φ(A) = Tr_E(V A V†)

## Main statements
- `KrausRepresentation.is_cptp`: Kraus channels are CPTP
- `choi_jamiolkowski`: CPTP iff positive Choi matrix with partial trace = identity (given linearity)
- `stinespring_dilation`: Stinespring dilation theorem
- `id_is_cptp`: Identity map is CPTP
- `isCompletelyPositive_comp`: Composition of completely positive maps is completely positive
- `cptp_comp`: Composition of CPTP maps is CPTP
- `cptp_contracts_trace_distance`: CPTP maps are trace distance contractions
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Agreement on density operators determines a complex-linear operator map. -/
lemma linearMap_eq_of_densityOp {a : ℕ} [NeZero a]
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : Op a →ₗ[ℂ] E) (h : ∀ ρ : DensityOp a, F ρ.toOp = G ρ.toOp) : F = G := by
  have hpsd (A : Op a) (hA : A.PosSemidef) : F A = G A := by
    by_cases hz : A.trace = 0
    · rw [hA.trace_eq_zero_iff.mp hz, map_zero, map_zero]
    · have hpos : 0 < A.trace.re := by
        have hn := Complex.nonneg_iff.mp hA.trace_nonneg
        refine lt_of_le_of_ne hn.1 ?_
        intro heq
        apply hz
        exact Complex.ext heq.symm hn.2.symm
      have hscaled : ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A).PosSemidef :=
        hA.smul (by exact_mod_cast inv_nonneg.mpr hpos.le)
      let ρ : DensityOp a :=
        { toOp := (((A.trace.re)⁻¹ : ℝ) : ℂ) • A
          isHermitian := hscaled.isHermitian
          pos_semidef := posSemidef_re_quadraticForm_nonneg hscaled
          trace_one := by
            have hreal : A.trace = (A.trace.re : ℂ) :=
              Complex.ext rfl (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
            rw [Matrix.trace_smul, smul_eq_mul, hreal, Complex.ofReal_re, ← Complex.ofReal_mul,
              inv_mul_cancel₀ hpos.ne', Complex.ofReal_one] }
      have hn := h ρ
      change F ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A) =
        G ((((A.trace.re)⁻¹ : ℝ) : ℂ) • A) at hn
      rw [map_smul, map_smul] at hn
      exact (smul_right_injective E (by exact_mod_cast inv_ne_zero hpos.ne')) hn
  apply LinearMap.ext_on (span_selfAdjoint (A := Op a))
  intro A hA
  obtain ⟨P, N, hP, hN, hPN, _⟩ :=
    Quantum.Metrics.traceNormHermitian_eq_trace_pos_neg A hA
  rw [hPN, map_sub, map_sub, hpsd P hP, hpsd N hN]

/-!
## Kraus Representation

The Kraus representation theorem states that any quantum channel Φ can be
written as Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ† where the Kraus operators satisfy Σᵢ Kᵢ†Kᵢ = I.
-/

/-- Kraus operator representation of a quantum channel.

    A quantum channel Φ: L(H_in) → L(H_out) is specified by a set of
    Kraus operators {Kᵢ} satisfying the completeness relation Σᵢ Kᵢ†Kᵢ = I.

    The channel action is: Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ† -/
structure KrausRepresentation (n m : ℕ) where
  /-- Number of Kraus operators. -/
  numOps : ℕ
  /-- The Kraus operators Kᵢ: H_in → H_out. -/
  operators : Fin numOps → Matrix (Fin m) (Fin n) ℂ
  /-- Completeness relation: Σᵢ Kᵢ† Kᵢ = I.
      This ensures trace preservation. -/
  completeness : ∑ i, (operators i)† * (operators i) = 1

/-- Reinterpret a `KrausRepresentation n m` as a `KrausRepresentation n m'` when
`m = m'`.  Operators and completeness are transported along `h`. -/
def KrausRepresentation.castOutput {n m m' : ℕ}
    (h : m = m') (kr : KrausRepresentation n m) :
    KrausRepresentation n m' where
  numOps := kr.numOps
  operators := fun i => h ▸ kr.operators i
  completeness := by
    subst h
    exact kr.completeness

@[simp] lemma KrausRepresentation.castOutput_numOps {n m m' : ℕ}
    (h : m = m') (kr : KrausRepresentation n m) :
    (kr.castOutput h).numOps = kr.numOps := rfl

lemma KrausRepresentation.castOutput_operators_heq {n m m' : ℕ}
    (h : m = m') (kr : KrausRepresentation n m) :
    HEq (kr.castOutput h).operators kr.operators := by
  subst h
  rfl

/-- Apply a Kraus representation to a general operator (Op-level).

    Φ(A) = Σᵢ Kᵢ A Kᵢ†

    This is the fundamental definition on all operators, needed for the
    Choi matrix construction and CPTP characterization. -/
def KrausRepresentation.applyOp {n m : ℕ}
    (K : KrausRepresentation n m) (A : Op n) : Op m :=
  ∑ i, K.operators i * A * (K.operators i)†

/-- Apply a Kraus representation to a density operator.

    Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ† -/
def KrausRepresentation.apply {n m : ℕ} [NeZero n] [NeZero m]
    (K : KrausRepresentation n m) (ρ : DensityOp n) : DensityOp m :=
  ⟨⟨⟨K.applyOp ρ.toOp, by
    -- Hermiticity: (Σᵢ Kᵢ ρ Kᵢ†)† = Σᵢ Kᵢ ρ Kᵢ†
    unfold IsHermitian
    simp only [KrausRepresentation.applyOp]
    rw [conjTranspose_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose,
        ρ.toPosSemidefOp.toHermitianOp.isHermitian,
        Matrix.mul_assoc]⟩, by
    -- PSD: ∀ x, ⟨x|Σᵢ Kᵢ ρ Kᵢ†|x⟩ = Σᵢ ⟨Kᵢ†x|ρ|Kᵢ†x⟩ ≥ 0
    intro x
    unfold quadraticForm
    simp only [KrausRepresentation.applyOp]
    rw [sum_mulVec, dotProduct_sum]
    exact Finset.sum_induction _ (fun z : ℂ => (0 : ℝ) ≤ z.re)
      (fun a b ha hb => by simp [Complex.add_re]; linarith)
      (by simp) fun i _ => by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
        have : vecMul (star x) (K.operators i) =
            star ((K.operators i)† *ᵥ x) := by
          rw [star_mulVec, conjTranspose_conjTranspose]
        rw [this]
        exact ρ.toPosSemidefOp.pos_semidef _⟩, by
    -- Trace: Tr(Σᵢ Kᵢ ρ Kᵢ†) = Σᵢ Tr(Kᵢ†Kᵢ ρ) = Tr((Σᵢ Kᵢ†Kᵢ) ρ) = Tr(ρ) = 1
    change (K.applyOp ρ.toOp).trace = 1
    simp only [KrausRepresentation.applyOp]
    rw [Matrix.trace_sum Finset.univ]
    have h_cyc : ∀ i, (K.operators i * ρ.toOp * (K.operators i)†).trace =
        ((K.operators i)† * K.operators i * ρ.toOp).trace := by
      intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp_rw [h_cyc, ← Matrix.trace_sum Finset.univ, ← Finset.sum_mul,
        K.completeness, Matrix.one_mul]
    exact ρ.trace_one⟩

/-- The output of a Kraus representation is a valid density operator.

    **Proof sketch**:
    - Hermiticity: (Σᵢ Kᵢ ρ Kᵢ†)† = Σᵢ Kᵢ ρ† Kᵢ† = Σᵢ Kᵢ ρ Kᵢ†
    - PSD: For any |ψ⟩, ⟨ψ|Σᵢ Kᵢ ρ Kᵢ†|ψ⟩ = Σᵢ ⟨Kᵢ†ψ|ρ|Kᵢ†ψ⟩ ≥ 0
    - Trace: Tr(Σᵢ Kᵢ ρ Kᵢ†) = Σᵢ Tr(Kᵢ† Kᵢ ρ) = Tr((Σᵢ Kᵢ† Kᵢ) ρ) = Tr(ρ) = 1 -/
theorem KrausRepresentation.apply_is_density {n m : ℕ} [NeZero n] [NeZero m]
    (K : KrausRepresentation n m) (ρ : DensityOp n) :
    let ρ_out := K.apply ρ
    ρ_out.toOp.trace = 1 ∧ ρ_out.toOp.PosSemidef := by
  exact ⟨(K.apply ρ).trace_one, posSemidefOp_implies_mathlib (K.apply ρ).toPosSemidefOp⟩

/-!
## Complete Positivity

A map Φ is completely positive if (id_k ⊗ Φ) is positive for all k.
This is stronger than just being positive, and is necessary for
physical quantum operations.
-/

/-- The Choi matrix of a linear map Φ: L(H_in) → L(H_out).

    C_Φ = Σᵢⱼ |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)

    This uses the **unnormalized** convention: the corresponding maximally
    entangled state is |Ω⟩ = Σᵢ |i⟩⊗|i⟩ (without the 1/√n factor).
    With the normalized convention C would differ by a factor of 1/n.

    The Choi matrix encodes all information about the map Φ.
    The input must be a linear map on all operators `Op n → Op m`,
    since the construction applies Φ to matrix units |i⟩⟨j| which
    need not be positive semidefinite or trace-one. -/
def ChoiMatrix (n m : ℕ) [NeZero n] [NeZero m]
    (Φ : Op n → Op m) : Op (n * m) :=
  -- C_Φ = Σᵢⱼ |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)
  -- In index notation: C_{(i,a),(j,b)} = Φ(E_{ij})_{a,b}
  -- where E_{ij} is the matrix unit with 1 at (i,j) and 0 elsewhere.
  Matrix.of fun α β =>
    let (i, a) := finProdFinEquiv.symm α
    let (j, b) := finProdFinEquiv.symm β
    Φ (Matrix.of fun r c => if r = i ∧ c = j then 1 else 0) a b

/-- A map is completely positive iff its Choi matrix is positive semidefinite.

    This is one direction of the Choi-Jamiołkowski theorem.

    **Linearity caveat**: This definition is meaningful only for linear maps.
    `choi_jamiolkowski` and `IsCPTP` both require linearity separately. -/
def IsCompletelyPositive {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) : Prop :=
  (ChoiMatrix n m Φ).PosSemidef

/-- A map Φ: L(H_in) → L(H_out) is trace-preserving iff Tr(Φ(A)) = Tr(A)
    for all operators A.

    This is now a non-trivial condition since Φ operates on general operators,
    not just density operators. -/
def IsTracePreserving {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) : Prop :=
  ∀ A : Op n, (Φ A).trace = A.trace

/-- A map Φ: L(H_in) → L(H_out) is CPTP (completely positive trace-preserving)
    iff it is linear, completely positive, and trace-preserving.

    CPTP maps are exactly the physically realizable quantum channels.
    Linearity is included in the definition as it is part of the standard
    mathematical definition of a quantum channel. -/
def IsCPTP {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) : Prop :=
  IsLinearMap ℂ Φ ∧ IsCompletelyPositive Φ ∧ IsTracePreserving Φ

/-- Entry of a matrix sandwiched with a matrix unit:
    `(M * E_{ij} * M†)(a,b) = M(a,i) * star(M(b,j))`.
    Used in Kraus and Choi matrix proofs. -/
lemma mul_unitMatrix_conjTranspose_apply {n m : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) (a b : Fin m) :
    (M * (Matrix.of fun r c => if r = i ∧ c = j then (1:ℂ) else 0) * M†) a b =
    M a i * star (M b j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
             Matrix.of_apply, mul_ite, mul_one, mul_zero]
  have h_inner : ∀ c, (∑ d, if d = i ∧ c = j then M a d else 0) =
      if c = j then M a i else 0 := by
    intro c; by_cases hc : c = j
    · subst hc; simp only [and_true]
      have := Finset.sum_ite_eq' Finset.univ i (fun d => M a d)
      simp only [Finset.mem_univ, ite_true] at this; exact this
    · rw [ite_eq_right hc]
      exact Finset.sum_eq_zero (fun d _ =>
        ite_eq_right (show ¬(d = i ∧ c = j) from fun h => hc h.2))
  simp_rw [h_inner, ite_mul, zero_mul]
  have := Finset.sum_ite_eq' Finset.univ j (fun c => M a i * star (M b c))
  simp only [Finset.mem_univ, ite_true] at this; exact this

/-- Any Kraus representation defines a CPTP map.

    **Proof sketch**:
    - Complete positivity: The Kraus form Σᵢ Kᵢ ρ Kᵢ† is manifestly CP
    - Trace preservation: Follows from Σᵢ Kᵢ†Kᵢ = I -/
theorem KrausRepresentation.is_cptp {n m : ℕ} [NeZero n] [NeZero m]
    (K : KrausRepresentation n m) : IsCPTP K.applyOp := by
  refine ⟨?_, ?_, ?_⟩
  · -- Linearity: applyOp is linear (sum of conjugation maps)
    constructor
    · intro x y; simp only [applyOp]; rw [← Finset.sum_add_distrib]
      congr 1; ext i; rw [Matrix.mul_add, Matrix.add_mul]
    · intro c x; simp only [applyOp]
      simp_rw [Matrix.mul_smul, Matrix.smul_mul]
      exact (Finset.smul_sum ..).symm
  · -- Complete positivity: Choi matrix = ∑ₖ wₖ wₖ† is PSD
    unfold IsCompletelyPositive
    -- Helper: distribute sum of matrices over entries
    have h_sum_entry : ∀ (f : Fin K.numOps → Op m) (a b : Fin m),
        (∑ k, f k) a b = ∑ k, f k a b := by
      intro f a b
      rw [show (∑ k, f k) a = ∑ k, (f k) a from Finset.sum_apply a Finset.univ f]
      exact Finset.sum_apply b Finset.univ _
    -- (M * E_{ij} * M†)(a,b) = M(a,i) * star(M(b,j))
    -- Define w_k(α) = K_k(a, i) where (i,a) = finProdFinEquiv.symm(α)
    let w : Fin K.numOps → Fin (n * m) → ℂ := fun k α =>
      K.operators k (finProdFinEquiv.symm α).2 (finProdFinEquiv.symm α).1
    -- Choi matrix = ∑_k vecMulVec w_k (star w_k) → PSD by sum of PSD
    suffices h_eq : ChoiMatrix n m K.applyOp =
        ∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k)) by
      rw [h_eq]
      exact posSemidef_sum Finset.univ (fun k _ => posSemidef_vecMulVec_self_star (w k))
    ext α β
    -- Unfold ChoiMatrix and applyOp
    simp only [ChoiMatrix, Matrix.of_apply, applyOp]
    -- Distribute LHS sum over matrix entries (∑ k, f k)(a)(b) = ∑ k, f k a b
    rw [h_sum_entry]
    -- Distribute RHS sum over matrix entries
    have h_rhs : (∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k))) α β =
        ∑ k, w k α * star (w k β) := by
      rw [show (∑ k ∈ Finset.univ, vecMulVec (w k) (star (w k))) α =
          ∑ k, vecMulVec (w k) (star (w k)) α from
        Finset.sum_apply α Finset.univ _]
      rw [show (∑ k, vecMulVec (w k) (star (w k)) α) β =
          ∑ k, vecMulVec (w k) (star (w k)) α β from
        Finset.sum_apply β Finset.univ _]
      simp only [vecMulVec, Matrix.of_apply, Pi.star_apply]
    rw [h_rhs]
    -- Both sides: ∑ k, (...)  — match per-summand
    apply Finset.sum_congr rfl
    intro k _
    simp only [w]
    exact mul_unitMatrix_conjTranspose_apply (K.operators k) _ _ _ _
  · -- Trace preservation: Tr(Σᵢ Kᵢ A Kᵢ†) = Tr(A) using Σᵢ Kᵢ†Kᵢ = I
    intro A
    simp only [applyOp]
    -- Distribute trace over sum (use `exact` to handle ∑ i, vs ∑ i ∈ s, defeq)
    have h_dist : trace (∑ i, K.operators i * A * (K.operators i)ᴴ) =
        ∑ i, trace (K.operators i * A * (K.operators i)ᴴ) :=
      Matrix.trace_sum Finset.univ _
    rw [h_dist]
    -- Rewrite each term: Tr(Kᵢ A Kᵢ†) = Tr(Kᵢ† Kᵢ A) by trace cyclicity
    rw [Finset.sum_congr rfl (fun i _ => show
        trace (K.operators i * A * (K.operators i)ᴴ) =
        trace ((K.operators i)ᴴ * K.operators i * A) by
      rw [Matrix.trace_mul_comm (K.operators i * A), Matrix.mul_assoc])]
    -- Re-aggregate: ∑ᵢ Tr(Kᵢ†Kᵢ A) = Tr((∑ᵢ Kᵢ†Kᵢ) A)
    have h_agg : (∑ i, trace ((K.operators i)ᴴ * K.operators i * A)) =
        trace ((∑ i, (K.operators i)ᴴ * K.operators i) * A) := by
      rw [Finset.sum_mul]
      exact (Matrix.trace_sum Finset.univ _).symm
    rw [h_agg, K.completeness, one_mul]

/-!
## Choi-Jamiołkowski Isomorphism

The Choi-Jamiołkowski theorem establishes a 1-1 correspondence between
CPTP maps and certain positive semidefinite matrices.
-/

/-- Diagonal entry of the Choi matrix at index `(i,a)`:
    `C_Φ((i,a),(i,a)) = Φ(E_{ii})(a,a)` where `E_{ii}` is the matrix unit.
    Used in `choi_jamiolkowski`. -/
lemma choiMatrix_diag_eq_apply {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (i : Fin n) (a : Fin m) :
    ChoiMatrix n m Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (i, a)) =
    (Φ (Matrix.of fun r c => if r = i ∧ c = i then (1:ℂ) else 0)) a a := by
  change (Φ (Matrix.of fun r c =>
    if r = (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1 ∧
      c = (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
    then (1:ℂ) else 0))
    (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2
    (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2 = _
  rw [finProdFinEquiv.symm_apply_apply]

/-- Entry (i,j) of `partialTraceB (ChoiMatrix n m Φ)` equals the trace of `Φ(E_{ij})`. -/
lemma partialTraceB_choiMatrix_eq {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (i j : Fin n) :
    partialTraceB (ChoiMatrix n m Φ) i j =
    (Φ (Matrix.of fun r c => if r = i ∧ c = j then (1:ℂ) else 0)).trace := by
  simp only [partialTraceB, ChoiMatrix, Matrix.of_apply, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Equiv.symm_apply_apply]

/-- The trace of the matrix unit E_{ij} is δ_{ij}. -/
lemma trace_matrixUnit {n : ℕ} [NeZero n] (i j : Fin n) :
    (Matrix.of fun r c => if r = i ∧ c = j then (1:ℂ) else 0).trace =
    if i = j then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp only [and_self, ite_true]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℂ))]
    simp
  · simp only [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    simp only [ite_eq_right_iff, one_ne_zero]
    intro ⟨hk, _⟩
    exact absurd (hk.symm ▸ ‹_›) hij

/-- **Choi-Jamiołkowski theorem**: A linear map Φ is CPTP if and only if
    its Choi matrix is PSD with partial trace equal to the identity.

    - Φ is CP  ↔  C_Φ ≥ 0 (Choi matrix is positive semidefinite)
    - Φ is TP  ↔  Tr_B(C_Φ) = I_n (partial trace over output system is identity)

    Linearity is a precondition: the Choi matrix only captures Φ's values on
    matrix units E_{ij}, so the RHS conditions cannot detect non-linearity.

    **Reference**: Choi (1975), Jamiołkowski (1972). -/
theorem choi_jamiolkowski {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hlin : IsLinearMap ℂ Φ) :
    IsCPTP Φ ↔
      (ChoiMatrix n m Φ).PosSemidef ∧ partialTraceB (ChoiMatrix n m Φ) = (1 : Op n) := by
  constructor
  · -- Forward: IsCPTP Φ → PSD ∧ partialTraceB = 1
    intro ⟨_, hcp, htp⟩
    exact ⟨hcp, by
      ext i j
      rw [partialTraceB_choiMatrix_eq, htp, trace_matrixUnit]
      simp [Matrix.one_apply]⟩
  · -- Backward: PSD ∧ partialTraceB = 1 → IsCPTP Φ
    intro ⟨hpsd, hptrace⟩
    refine ⟨hlin, hpsd, ?_⟩
    -- Trace preservation: ∀ A, (Φ A).trace = A.trace
    intro A
    -- Decompose A = ∑_{i,j} A(i,j) • E_{ij}
    -- Each (Φ(E_{ij})).trace = δ_{ij} from hptrace
    have htr : ∀ i j : Fin n,
        (Φ (Matrix.of fun r c => if r = i ∧ c = j then (1:ℂ) else 0)).trace =
        if i = j then 1 else 0 := by
      intro i j
      have h := congr_fun (congr_fun hptrace i) j
      rw [partialTraceB_choiMatrix_eq] at h
      simp only [Matrix.one_apply] at h
      exact h
    -- Decompose A via single: A = ∑_{i,j} A(i,j) • single i j 1
    have hA_single : A = ∑ i : Fin n, ∑ j : Fin n, A i j • single i j (1 : ℂ) :=
      (matrix_eq_sum_single A).trans (Finset.sum_congr rfl (fun c _ =>
        Finset.sum_congr rfl (fun d _ => by ext i j; simp [single_apply, smul_eq_mul])))
    -- Relate single to our matrix unit notation
    have h_single_eq : ∀ i j : Fin n,
        single i j (1 : ℂ) = Matrix.of fun r c => if r = i ∧ c = j then (1:ℂ) else 0 := by
      intro i j; ext r c; simp [single_apply, eq_comm]
    -- Use linearity
    set hL := IsLinearMap.mk' Φ hlin
    conv_lhs => rw [hA_single, show Φ = hL from rfl, map_sum hL]
    simp_rw [map_sum hL, hL.map_smul, show ∀ x, (hL x : Op m) = Φ x from fun _ => rfl]
    rw [Matrix.trace_sum Finset.univ]
    simp_rw [Matrix.trace_sum Finset.univ, Matrix.trace_smul, h_single_eq, htr]
    -- Now: ∑_i ∑_j A(i,j) • δ_{ij} = ∑_i A(i,i) = trace A
    simp only [Matrix.trace, Matrix.diag, smul_eq_mul, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl; intro i _
    rw [show ∑ x, (if i = x then A i x else 0) =
        if i ∈ Finset.univ then A i i else 0
      from Finset.sum_ite_eq Finset.univ i _]
    simp

/-- Every CPTP map admits a Kraus decomposition: Φ(A) = ∑_k K_k A K_k† for some operators K_k.
    Proof: decompose the PSD Choi matrix as ∑ vecMulVec and extract Kraus operators. -/
lemma cptp_eq_kraus_sum {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin m) (Fin n) ℂ),
      ∀ A, Φ A = ∑ k, K k * A * (K k)† := by
  -- Decompose PSD Choi matrix
  have hcp := hΦ.2.1
  unfold IsCompletelyPositive at hcp
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hcp
  obtain ⟨r, v, hv⟩ := hcp
  -- Define Kraus operators K_k(a, i) = v_k(finProdFinEquiv(i, a))
  set K : Fin r → Matrix (Fin m) (Fin n) ℂ :=
    fun k => Matrix.of fun a i => v k (finProdFinEquiv (i, a))
  refine ⟨r, K, ?_⟩
  intro A; ext a b
  -- Both sides boil down to ∑_k ∑_i ∑_j v_k(i,a) * A(i,j) * star(v_k(j,b))
  -- LHS via linearity + Choi, RHS via matrix multiplication definition
  -- Step 1: Expand RHS using matrix multiplication
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K, Matrix.of_apply]
  -- Step 2: Expand LHS using linearity + Choi matrix
  -- Φ(A)(a,b) = ∑_{i,j} A(i,j) * C_Φ((i,a),(j,b)) by linearity
  set E := fun i j : Fin n => Matrix.of fun r c =>
    if r = i ∧ c = j then (1:ℂ) else 0 with hE_def
  set hL := IsLinearMap.mk' Φ hΦ.1
  -- Decompose A
  have hA_decomp : A = ∑ i, ∑ j, A i j • E i j := by
    ext r c; simp only [E, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact ite_eq_right (fun ⟨h1, _⟩ => hi h1.symm)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => ite_eq_right (fun ⟨_, h2⟩ => hj h2.symm))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  -- Apply linearity to get entry-wise sum
  have hΦ_entry : Φ A a b = ∑ i, ∑ j, A i j *
      ChoiMatrix n m Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
    conv_lhs => rw [hA_decomp, show Φ = hL from rfl, map_sum hL]
    simp_rw [map_sum hL, hL.map_smul, show ∀ x, (hL x : Op m) = Φ x from fun _ => rfl,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext i; congr 1; ext j
    congr 1
    simp only [E, ChoiMatrix, Matrix.of_apply, Equiv.symm_apply_apply]
  rw [hΦ_entry, hv]
  -- Simplify LHS: push sum application inside
  simp only [vecMulVec, Pi.star_apply]
  have h_push : ∀ i j : Fin n,
      (∑ k, Matrix.of fun x_2 y => v k x_2 * star (v k y))
        (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      ∑ k, v k (finProdFinEquiv (i, a)) * star (v k (finProdFinEquiv (j, b))) :=
    fun i j => Matrix.sum_apply _ _ Finset.univ _
  simp_rw [h_push]
  -- Now both sides are pure sums; reorder and use commutativity
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  -- LHS: ∑_a:Fn ∑_b:Fn ∑_k:Fr f(a,b,k)
  -- RHS: ∑_k:Fr ∑_b:Fn ∑_a:Fn g(a,b,k) with f ~ g by ring
  have reorder : ∀ (f : Fin n → Fin n → Fin r → ℂ),
      ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ b, ∑ a, f a b k := by
    intro f
    calc ∑ a, ∑ b, ∑ k, f a b k
        = ∑ a, ∑ k, ∑ b, f a b k := by
          congr 1; ext a; exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, f a b k := Finset.sum_comm
      _ = ∑ k, ∑ b, ∑ a, f a b k := by
          congr 1; ext k; exact Finset.sum_comm
  rw [reorder]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- If `∀ A, (∑ k, K k * A * (K k)†).trace = A.trace`, then `∑ k, (K k)† * K k = 1`.
    Uses the fact that `Tr(M * A) = Tr(A)` for all A implies `M = 1`. -/
lemma kraus_sum_completeness {n m r : ℕ} [NeZero n] [NeZero m]
    (K : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (htp : ∀ A : Op n, (∑ k, K k * A * (K k)†).trace = A.trace) :
    ∑ k, (K k)† * K k = 1 := by
  set M := ∑ k, (K k)† * K k
  -- It suffices to show M = 1, i.e., M i j = (1 : Op n) i j
  suffices h : ∀ A : Op n, (M * A).trace = A.trace by
    ext i j
    -- Test with A = E_{ji} (matrix unit with 1 at position (j,i))
    set Eji := Matrix.of fun r c => if r = j ∧ c = i then (1 : ℂ) else 0
    have hME := h Eji
    -- Tr(M * E_{ji}) = M(i,j) and Tr(E_{ji}) = δ_{ji}
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Eji, Matrix.of_apply] at hME
    simp only [mul_ite, mul_one, mul_zero] at hME
    -- Simplify LHS: ∑_r ∑_c M(r,c) * (if c = j ∧ r = i then 1 else 0)
    --             = ∑_r (if r = i then M(r,j) else 0) = M(i,j)
    conv_lhs at hME =>
      arg 2; ext r
      rw [show (∑ c, if c = j ∧ r = i then M r c else 0) =
          if r = i then M r j else 0 by
        by_cases hr : r = i
        · subst hr
          simp only [and_true]
          rw [Finset.sum_ite_eq' Finset.univ j]; simp
        · simp only [hr, and_false, ite_false, Finset.sum_const_zero]]
    rw [Finset.sum_ite_eq' Finset.univ i (fun r => M r j)] at hME
    simp only [Finset.mem_univ, ite_true] at hME
    -- Simplify RHS: Tr(E_{ji}) = δ_{ji}
    rw [hME]; simp only [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Finset.sum_ite_eq' Finset.univ]
    · rw [ite_eq_right hij]
      apply Finset.sum_eq_zero; intro x _
      exact ite_eq_right (fun ⟨h1, h2⟩ => hij (h2 ▸ h1))
  -- Now prove ∀ A, Tr(M * A) = Tr(A)
  intro A
  have htp' := htp A
  -- Tr(∑_k K_k * A * (K_k)†) = ∑_k Tr(K_k * A * (K_k)†) = ∑_k Tr((K_k)† * K_k * A)
  rw [Matrix.trace_sum Finset.univ] at htp'
  conv at htp' =>
    lhs; arg 2; ext k
    rw [Matrix.trace_mul_comm (K k * A), ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum Finset.univ, ← Finset.sum_mul] at htp'
  exact htp'

/-!
## Stinespring Dilation

Every CPTP map has a unitary dilation: Φ(ρ) = Tr_E(U(ρ ⊗ |0⟩⟨0|)U†)
for some unitary U and environment state |0⟩.
-/

/-- Predicate asserting that an isometry recovers the original channel.

    This captures: Φ(A) = Tr_E(V A V†) for all operators A.

    The channel Φ is recovered by:
    1. Applying the isometry V : ℂⁿ → ℂ^(m·envDim)
    2. Tracing out the environment subsystem via `partialTraceB`

    V maps into ℂ^(m·envDim) ≅ ℂ^m ⊗ ℂ^envDim (output first, environment second),
    matching `partialTraceB` which traces out the second tensor factor.

    Quantifies over all `Op n` (not just density operators), matching the
    standard Stinespring dilation theorem. -/
def DilationRecovers {n m envDim : ℕ} [NeZero n] [NeZero m] [NeZero envDim]
    [NeZero (m * envDim)]
    (Φ : Op n → Op m)
    (V : Matrix (Fin (m * envDim)) (Fin n) ℂ) : Prop :=
  ∀ A : Op n,
    Φ A = Quantum.TensorProducts.partialTraceB (V * A * V†)

/-- **Stinespring dilation theorem**: Every CPTP map admits an isometric dilation.

    Given a quantum channel Φ : L(ℂⁿ) → L(ℂᵐ), there exists an environment
    space ℂ^envDim and an isometry V : ℂⁿ → ℂᵐ ⊗ ℂ^envDim such that:
      Φ(A) = Tr_E(V A V†) for all A

    **In plain language**: Every quantum channel can be realized by embedding the
    input into a larger system (via an isometry V), then discarding the environment.
    This is the quantum analog of every stochastic map being a marginal of a
    deterministic map.

    **Reference**: Stinespring (1955). -/
theorem stinespring_dilation {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (_hΦ : IsCPTP Φ) :
    ∃ (envDim : ℕ) (henv : NeZero envDim)
      (hme : NeZero (m * envDim))
      (V : Matrix (Fin (m * envDim)) (Fin n) ℂ),
      -- V is an isometry (V†V = I on input space ℂⁿ)
      V† * V = 1 ∧
      @DilationRecovers n m envDim ‹NeZero n› ‹NeZero m› henv hme Φ V := by
  -- Step 1: Get Kraus operators
  obtain ⟨r, K, hK⟩ := cptp_eq_kraus_sum Φ _hΦ
  -- Step 2: Show r ≠ 0 (otherwise Φ = 0, contradicting trace preservation)
  have hr : r ≠ 0 := by
    intro hr0; subst hr0
    have h0 : ∀ A : Op n, Φ A = 0 := fun A => by
      rw [hK A]; exact Finset.sum_empty
    have htp := _hΦ.2.2 1
    rw [h0 1, Matrix.trace_zero] at htp
    have hne : (1 : Op n).trace ≠ 0 := by
      simp only [Matrix.trace_one, Fintype.card_fin]
      exact Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact hne htp.symm
  have : NeZero r := ⟨hr⟩
  have : NeZero (m * r) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos m) (NeZero.pos r))⟩
  -- Step 3: Build V by stacking Kraus operators
  let V : Matrix (Fin (m * r)) (Fin n) ℂ :=
    Matrix.of fun α i =>
      let ak := finProdFinEquiv.symm α
      K ak.2 ak.1 i
  refine ⟨r, ⟨hr⟩, ‹NeZero (m * r)›, V, ?_, ?_⟩
  · -- V†V = 1
    -- First establish Kraus completeness: ∑ k, (K k)† * K k = 1
    have hcomp : ∑ k, (K k)† * K k = 1 := by
      apply kraus_sum_completeness K
      intro A
      rw [← hK A]
      exact _hΦ.2.2 A
    -- Now show V†V = 1 by expanding matrix entries
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply, V,
      Matrix.of_apply]
    -- (V†V)(i,j) = ∑_α star(V(α,i)) * V(α,j)
    -- = ∑_{(a,k)} star(K k a i) * K k a j
    -- = ∑_k ∑_a star(K k a i) * K k a j
    -- = ∑_k ((K k)† * K k)(i,j) = 1(i,j)
    -- Reindex: sum over Fin(m*r) → double sum over Fin m × Fin r
    -- Then recognize as ∑ k, ((K k)† * K k) i j = 1 i j
    -- Convert single sum over Fin(m*r) to ∑ k, (K k)†*(K k) then use hcomp
    trans (∑ k : Fin r, ((K k)† * K k) i j)
    · -- Reindex
      trans (∑ p : Fin m × Fin r, star (K p.2 p.1 i) * K p.2 p.1 j)
      · exact Fintype.sum_equiv finProdFinEquiv.symm _ _
          (fun x => by simp)
      · rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
    · rw [← Matrix.sum_apply, hcomp, Matrix.one_apply]
  · -- DilationRecovers: ∀ A, Φ A = partialTraceB (V * A * V†)
    intro A; ext a b
    rw [hK A]
    simp only [Quantum.TensorProducts.partialTraceB, Matrix.of_apply]
    -- RHS: ∑_k (V * A * V†)(finProdFinEquiv(a,k), finProdFinEquiv(b,k))
    -- LHS: ∑_k (K k * A * (K k)†)(a,b)
    -- Expand both as triple sums and show equality
    simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, V, Matrix.of_apply]
    -- Both sides should match after expanding V entries
    apply Finset.sum_congr rfl; intro k _
    -- (K k * A * (K k)†)(a,b) = ∑_i (K k * A)(a,i) * star(K k b i)
    --   = ∑_i (∑_j K k a j * A j i) * star(K k b i)
    -- RHS term = ∑_i (∑_j V(finProdFinEquiv(a,k),j) * A(j,i)) * star(V(finProdFinEquiv(b,k),i))
    -- V(finProdFinEquiv(a,k), j) = K (finProdFinEquiv.symm(finProdFinEquiv(a,k))).2
    --   (finProdFinEquiv.symm(finProdFinEquiv(a,k))).1 j = K k a j
    apply Finset.sum_congr rfl; intro i _
    congr 1
    · apply Finset.sum_congr rfl; intro j _
      simp [finProdFinEquiv.symm_apply_apply]
    · simp [finProdFinEquiv.symm_apply_apply]

/-!
## Composition and Identity

CPTP maps form a category with composition and identity.
-/

/-- The identity map is CPTP. -/
theorem id_is_cptp (n : ℕ) [NeZero n] : IsCPTP (id : Op n → Op n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Linearity: id is linear
    exact LinearMap.id.isLinear
  · -- Complete positivity: Choi matrix of id is PSD
    -- C_id_{(i,a),(j,b)} = δ_{ia}δ_{jb} = v_α * conj(v_β)
    -- C_id = vecMulVec v (star v) which is PSD by Mathlib
    unfold IsCompletelyPositive
    let v : Fin (n * n) → ℂ := fun α =>
      if α.divNat = α.modNat then 1 else 0
    suffices h_eq : ChoiMatrix n n id = vecMulVec v (star v) by
      exact h_eq ▸ Matrix.posSemidef_vecMulVec_self_star v
    ext α β
    simp only [ChoiMatrix, Matrix.of_apply, id, vecMulVec, Pi.star_apply, v]
    split_ifs <;> simp_all
  · -- Trace preservation: Tr(id(A)) = Tr(A)
    intro A; rfl

private lemma finProdFinEquiv_fst {m n : ℕ} [NeZero n] (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j)).divNat = i := by
  have := finProdFinEquiv.symm_apply_apply (i, j)
  rw [finProdFinEquiv_symm_apply] at this; exact congr_arg Prod.fst this

private lemma finProdFinEquiv_snd {m n : ℕ} [NeZero n] (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i, j)).modNat = j := by
  have := finProdFinEquiv.symm_apply_apply (i, j)
  rw [finProdFinEquiv_symm_apply] at this; exact congr_arg Prod.snd this

private lemma choi_entry_Ψ {n m : ℕ} [NeZero n] [NeZero m]
    (Ψ : Op n → Op m) {rΨ : ℕ} (vΨ : Fin rΨ → Fin (n * m) → ℂ)
    (hvΨ : ChoiMatrix n m Ψ = ∑ t, vecMulVec (vΨ t) (star (vΨ t)))
    (i j : Fin n) (c d : Fin m) :
    (Ψ (of fun r c₁ => if r = i ∧ c₁ = j then 1 else 0)) c d =
    ∑ t : Fin rΨ, vΨ t (finProdFinEquiv (i, c)) *
      starRingEnd ℂ (vΨ t (finProdFinEquiv (j, d))) := by
  have h1 : ChoiMatrix n m Ψ (finProdFinEquiv (i, c)) (finProdFinEquiv (j, d)) =
      Ψ (of fun r c₁ => if r = i ∧ c₁ = j then 1 else 0) c d := by
    dsimp only [ChoiMatrix]
    simp [of_apply, finProdFinEquiv_fst, finProdFinEquiv_snd]
  rw [← h1, hvΨ]
  simp [Matrix.sum_apply, vecMulVec, Pi.star_apply, of_apply]

private lemma choi_entry_Φ {m k : ℕ} [NeZero m] [NeZero k]
    (Φ : Op m → Op k) {rΦ : ℕ} (vΦ : Fin rΦ → Fin (m * k) → ℂ)
    (hvΦ : ChoiMatrix m k Φ = ∑ s, vecMulVec (vΦ s) (star (vΦ s)))
    (c d : Fin m) (a b : Fin k) :
    Φ (single c d 1) a b =
    ∑ s : Fin rΦ, vΦ s (finProdFinEquiv (c, a)) *
      starRingEnd ℂ (vΦ s (finProdFinEquiv (d, b))) := by
  have h1 : ChoiMatrix m k Φ (finProdFinEquiv (c, a)) (finProdFinEquiv (d, b)) =
      Φ (single c d 1) a b := by
    dsimp only [ChoiMatrix]
    simp only [of_apply, Equiv.symm_apply_apply]
    congr 1; ext r c₁; simp [single_apply, eq_comm]
  rw [← h1, hvΦ]
  simp [Matrix.sum_apply, vecMulVec, Pi.star_apply, of_apply]

private lemma sum_reorder_four {α₁ α₂ α₃ α₄ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype α₃] [Fintype α₄]
    (f : α₁ → α₂ → α₃ → α₄ → ℂ) :
    ∑ c, ∑ d, ∑ t, ∑ s, f c d t s = ∑ s, ∑ t, ∑ c, ∑ d, f c d t s := by
  calc ∑ c, ∑ d, ∑ t, ∑ s, f c d t s
      = ∑ c, ∑ t, ∑ d, ∑ s, f c d t s := by congr 1; ext c; exact Finset.sum_comm
    _ = ∑ t, ∑ c, ∑ d, ∑ s, f c d t s := Finset.sum_comm
    _ = ∑ t, ∑ c, ∑ s, ∑ d, f c d t s := by
          congr 1; ext t; congr 1; ext c; exact Finset.sum_comm
    _ = ∑ t, ∑ s, ∑ c, ∑ d, f c d t s := by congr 1; ext t; exact Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ c, ∑ d, f c d t s := Finset.sum_comm

-- Choi matrix decomposition requires 4-fold sum reordering over Fin indices.
/-- Composition of completely positive maps is completely positive,
    assuming the outer map is linear.

    The proof decomposes both Choi matrices as Σ vecMulVec(v)(star v) and
    constructs composition vectors w_{s,t}(i,a) = Σ_c vΨ_t(i,c) * vΦ_s(c,a),
    showing the composed Choi matrix equals Σ_{s,t} vecMulVec(w_{s,t})(star w_{s,t}). -/
theorem isCompletelyPositive_comp {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op m → Op k) (Ψ : Op n → Op m)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ)
    (hlin : IsLinearMap ℂ Φ) :
    IsCompletelyPositive (Φ ∘ Ψ) := by
  unfold IsCompletelyPositive at *
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hΦ hΨ
  obtain ⟨rΦ, vΦ, hvΦ⟩ := hΦ
  obtain ⟨rΨ, vΨ, hvΨ⟩ := hΨ
  set w : Fin rΦ × Fin rΨ → Fin (n * k) → ℂ := fun ⟨s, t⟩ α =>
    let ⟨i, a⟩ := finProdFinEquiv.symm α
    ∑ c : Fin m, vΨ t (finProdFinEquiv (i, c)) * vΦ s (finProdFinEquiv (c, a))
    with hw_def
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec]
  refine ⟨rΦ * rΨ, fun p => w (finProdFinEquiv.symm p), ?_⟩
  suffices key : ∀ α β, ChoiMatrix n k (Φ ∘ Ψ) α β =
      ∑ s : Fin rΦ, ∑ t : Fin rΨ, w (s, t) α * starRingEnd ℂ (w (s, t) β) by
    ext α β
    simp only [Matrix.sum_apply, vecMulVec, of_apply, Pi.star_apply, key]
    rw [← Finset.sum_product']
    exact (Equiv.sum_comp finProdFinEquiv.symm _).symm
  intro α β
  let hL := IsLinearMap.mk' Φ hlin
  have hChoi : ChoiMatrix n k (Φ ∘ Ψ) α β =
      Φ (Ψ (of fun r c => if r = α.divNat ∧ c = β.divNat then 1 else 0))
        α.modNat β.modNat := by
    simp only [ChoiMatrix, of_apply, Function.comp_apply]; rfl
  rw [hChoi]
  -- Decompose Ψ output as ∑ A_{c,d} • E_{c,d} to apply Φ's linearity
  set A := Ψ (of fun r c => if r = α.divNat ∧ c = β.divNat then 1 else 0) with hA_def
  have hA_decomp : A = ∑ c : Fin m, ∑ d : Fin m, A c d • single c d (1 : ℂ) :=
    (matrix_eq_sum_single A).trans (Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => by ext i j; simp [single_apply, smul_eq_mul])))
  have hΦ_eq : ∀ x, Φ x = hL x := fun _ => rfl
  rw [hA_decomp, hΦ_eq, map_sum hL]
  simp_rw [map_sum hL, hL.map_smul]
  simp_rw [show ∀ x, (hL x : Op k) = Φ x from fun _ => rfl]
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  -- Use extracted helper lemmas for Choi entry decompositions
  simp_rw [hA_def, choi_entry_Ψ Ψ vΨ hvΨ α.divNat β.divNat,
    choi_entry_Φ Φ vΦ hvΦ _ _ α.modNat β.modNat, Finset.sum_mul, Finset.mul_sum]
  rw [sum_reorder_four]
  congr 1; ext s; congr 1; ext t
  simp only [hw_def, finProdFinEquiv_symm_apply]
  rw [map_sum (starRingEnd ℂ)]
  simp_rw [map_mul (starRingEnd ℂ)]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  congr 1; ext c; congr 1; ext d; ring

/-- **Composition of CPTP maps is CPTP.**

    If Φ and Ψ are both completely positive trace-preserving maps, then
    Φ ∘ Ψ is also CPTP. This means quantum channels form a category.

    **Proof** (fully formalized): Linearity by composition, complete positivity
    by `isCompletelyPositive_comp`, trace preservation by transitivity. -/
theorem cptp_comp {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op m → Op k) (Ψ : Op n → Op m)
    (hΦ : IsCPTP Φ) (hΨ : IsCPTP Ψ) :
    IsCPTP (Φ ∘ Ψ) := by
  exact ⟨(hΦ.1.mk'.comp hΨ.1.mk').isLinear,
         isCompletelyPositive_comp Φ Ψ hΦ.2.1 hΨ.2.1 hΦ.1,
         fun A => (hΦ.2.2 (Ψ A)).trans (hΨ.2.2 A)⟩

/-!
## CPTP Maps Contract Trace Distance

A fundamental property of CPTP maps is that they cannot increase
distinguishability between states.
-/

/-- CPTP maps preserve the adjoint: (Φ A)† = Φ(A†) for any CPTP map Φ. -/
lemma cptp_preserves_conjTranspose {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) (A : Op n) :
    (Φ A)† = Φ (A†) := by
  obtain ⟨r, K, hK⟩ := cptp_eq_kraus_sum Φ hΦ
  rw [hK A, hK (A†)]
  rw [conjTranspose_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- CPTP maps preserve Hermiticity: if A is Hermitian and Φ is CPTP, then Φ(A) is Hermitian.
    This follows from complete positivity: CP maps preserve the PSD cone,
    and every Hermitian operator decomposes as A = A₊ - A₋ with A₊, A₋ ∈ PSD. -/
lemma IsCPTP.preserves_hermitian {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (_hΦ : IsCPTP Φ) (A : Op n) (_hA : A.IsHermitian) :
    (Φ A).IsHermitian := by
  unfold IsHermitian
  rw [cptp_preserves_conjTranspose Φ _hΦ A, _hA]

/-- CPTP maps preserve positive semidefiniteness. -/
lemma cptp_preserves_posSemidef {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ) (P : Op n) (hP : P.PosSemidef) :
    (Φ P).PosSemidef := by
  obtain ⟨r, K, hK⟩ := cptp_eq_kraus_sum Φ hΦ
  rw [hK P]
  apply Matrix.posSemidef_sum
  intro k _
  have := hP.conjTranspose_mul_mul_same (K k)ᴴ
  simp only [conjTranspose_conjTranspose] at this
  exact this

/-- CPTP maps contract trace norm: ‖Φ(ρ) - Φ(σ)‖₁ ≤ ‖ρ - σ‖₁.

    This is a consequence of the data processing inequality and is
    essential for security proofs where we need to show that
    post-processing cannot help an adversary distinguish states.

    Stated at the `Op` level using trace norm. For density operators
    ρ, σ, trace distance D(ρ,σ) = (1/2)‖ρ - σ‖₁, so this implies
    the standard trace distance contraction.

    **Reference**: Ruskai (1994). -/
theorem cptp_contracts_trace_distance {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ)
    (ρ σ : DensityOp n) :
    Quantum.Metrics.traceNorm (Φ ρ.toOp - Φ σ.toOp) ≤
    Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) := by
  have hΔ : (ρ.toOp - σ.toOp).IsHermitian :=
    Quantum.Metrics.densityOp_sub_isHermitian ρ σ
  -- Jordan decomposition of ρ - σ
  obtain ⟨Dp, Dm, hDp, hDm, hDecomp, hNorm⟩ :=
    Quantum.Metrics.traceNormHermitian_eq_trace_pos_neg
      (ρ.toOp - σ.toOp) hΔ
  -- Rewrite LHS using linearity
  have hLinSub : Φ ρ.toOp - Φ σ.toOp = Φ Dp - Φ Dm := by
    rw [← hΦ.1.map_sub, hDecomp, hΦ.1.map_sub]
  have hPhiDiff_herm : (Φ Dp - Φ Dm).IsHermitian := by
    rw [← hΦ.1.map_sub]
    exact IsCPTP.preserves_hermitian Φ hΦ _ (hDecomp ▸ hΔ)
  calc Quantum.Metrics.traceNorm (Φ ρ.toOp - Φ σ.toOp)
      = Quantum.Metrics.traceNorm (Φ Dp - Φ Dm) := by rw [hLinSub]
    _ = Quantum.Metrics.traceNormHermitian (Φ Dp - Φ Dm) hPhiDiff_herm := by
          rw [Quantum.Metrics.traceNorm_hermitian_eq]
    _ ≤ ((Φ Dp).trace + (Φ Dm).trace).re := by
          open Quantum.Metrics in
          exact traceNormHermitian_le_trace_posSemidef_sub
            _ _ _ hPhiDiff_herm
            (cptp_preserves_posSemidef Φ hΦ Dp hDp)
            (cptp_preserves_posSemidef Φ hΦ Dm hDm) rfl
    _ = (Dp.trace + Dm.trace).re := by rw [hΦ.2.2 Dp, hΦ.2.2 Dm]
    _ = Quantum.Metrics.traceNormHermitian (ρ.toOp - σ.toOp) hΔ := hNorm.symm
    _ = Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) := by
          rw [Quantum.Metrics.traceNorm_hermitian_eq]

/-- **CPTP contractivity for Hermitian operators**:
    For any CPTP map Φ and Hermitian operator A, ‖Φ(A)‖₁ ≤ ‖A‖₁.

    The proof uses the Jordan decomposition A = A₊ - A₋, then CPTP preserves
    PSD and trace, and the trace norm of a Hermitian equals Tr(A₊) + Tr(A₋).

    Reference: Ruskai (1994), Watrous Theorem 3.33. -/
theorem traceNorm_cptp_contractive_hermitian {n m : ℕ}
    [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : IsCPTP Φ)
    (A : Op n) (hA : A.IsHermitian) :
    Quantum.Metrics.traceNorm (Φ A) ≤ Quantum.Metrics.traceNorm A := by
  open Quantum.Metrics in
  obtain ⟨Dp, Dm, hDp, hDm, hDecomp, hNorm⟩ :=
    traceNormHermitian_eq_trace_pos_neg A hA
  have hLinSub : Φ A = Φ Dp - Φ Dm := by
    rw [hDecomp, hΦ.1.map_sub]
  have hPhiHerm : (Φ Dp - Φ Dm).IsHermitian := by
    rw [← hΦ.1.map_sub]
    exact IsCPTP.preserves_hermitian Φ hΦ _ (hDecomp ▸ hA)
  calc Quantum.Metrics.traceNorm (Φ A)
      = Quantum.Metrics.traceNorm (Φ Dp - Φ Dm) := by rw [hLinSub]
    _ = Quantum.Metrics.traceNormHermitian (Φ Dp - Φ Dm) hPhiHerm := by
          rw [Quantum.Metrics.traceNorm_hermitian_eq]
    _ ≤ ((Φ Dp).trace + (Φ Dm).trace).re := by
          exact traceNormHermitian_le_trace_posSemidef_sub
            _ _ _ hPhiHerm
            (cptp_preserves_posSemidef Φ hΦ Dp hDp)
            (cptp_preserves_posSemidef Φ hΦ Dm hDm) rfl
    _ = (Dp.trace + Dm.trace).re := by
          rw [hΦ.2.2 Dp, hΦ.2.2 Dm]
    _ = Quantum.Metrics.traceNormHermitian A hA := hNorm.symm
    _ = Quantum.Metrics.traceNorm A := by
          rw [Quantum.Metrics.traceNorm_hermitian_eq]

end Quantum.Channels
