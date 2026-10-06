import QCryptLean.Quantum.Symmetry.FiniteGroupCommutant
import QCryptLean.Quantum.Symmetry.UnitaryCentralizerTensorPowers
import QCryptLean.Quantum.Symmetry.LocalCommutantTwirl
import QCryptLean.Quantum.TensorProducts.PairedTensorCommutant
import Mathlib.GroupTheory.SemidirectProduct
import QCryptLean.Math.Probability.HaarMeasure

/-!
# Schur–Weyl commutants relative to a finite group

Independent finite-group actions and permutations of the tensor factors form a
semidirect-product representation. Averaging the ordinary polarization theorem
identifies its commutant with the span of tensor powers of the one-round commutant.
Taking the double commutant gives the relative Schur–Weyl theorem.
-/

open Matrix Quantum.Operators Quantum.TensorProducts
open Math.RepresentationTheory
open scoped BigOperators

noncomputable section

namespace Quantum.Symmetry

/-- Permutations act on group-valued words by permuting their positions. -/
def wordPermutationAction (G : Type*) [Group G] (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Fin n → G) where
  toFun σ :=
    { toFun := fun v => v ∘ σ.symm
      invFun := fun v => v ∘ σ
      left_inv v := by funext k; simp
      right_inv v := by funext k; simp
      map_mul' v w := rfl }
  map_one' := by ext v k; rfl
  map_mul' σ τ := by ext v k; rfl

/-- Independent actions of a matrix representation on the tensor factors. -/
def tensorFamilyRep {G : Type*} [Group G] {d : ℕ} (ρ : G →* Op d) (n : ℕ) :
    (Fin n → G) →* Op (d ^ n) where
  toFun v := tensorFamily fun k => ρ (v k)
  map_one' := by simp only [Pi.one_apply, map_one, tensorFamily_one]
  map_mul' v w := by simp only [Pi.mul_apply, map_mul, tensorFamily_mul]

/-- The joint representation of independent group actions and tensor-factor permutations. -/
def tensorWreathRep {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (ρ : G →* Op d) (n : ℕ) :
    SemidirectProduct (Fin n → G) (Equiv.Perm (Fin n)) (wordPermutationAction G n) →*
      Op (d ^ n) where
  toFun x := tensorFamilyRep ρ n x.left * permutationRepresentation d n x.right
  map_one' := by
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one,
      permutationRepresentation_one, one_mul]
  map_mul' x y := by
    change tensorFamilyRep ρ n (x.left * wordPermutationAction G n x.right y.left) *
        permutationRepresentation d n (x.right * y.right) = _
    rw [map_mul, ← permutationRepresentation_mul]
    change tensorFamily (fun k => ρ (x.left k)) *
        tensorFamily (fun k => ρ (y.left (x.right.symm k))) *
        (permutationRepresentation d n x.right * permutationRepresentation d n y.right) = _
    simp only [tensorFamilyRep, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc]
    rw [← mul_assoc (permutationRepresentation d n x.right),
      permutationRepresentation_mul_tensorFamily]
    simp only [mul_assoc]

/-- Independent conjugation averages commute with forming a tensor power. -/
lemma finiteGroupMatrixAverage_tensorPow {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : G →* Op d) (A : Op d) (n : ℕ) :
    finiteGroupMatrixAverage (tensorFamilyRep ρ n) (Op.tensorPow A n) =
      Op.tensorPow (finiteGroupMatrixAverage ρ A) n := by
  simp only [finiteGroupMatrixAverage, Op.tensorPow_eq_tensorFamily,
    tensorFamily_const_smul, tensorFamily_sum, tensorFamilyRep, MonoidHom.coe_mk,
    OneHom.coe_mk, Pi.inv_apply, ← tensorFamily_mul, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, inv_pow]

/-- Commuting with the joint action means commuting with its two constituent actions. -/
lemma mem_tensorWreathRep_commutant_iff {G : Type*} [Group G] {d n : ℕ} [NeZero d]
    (ρ : G →* Op d) (T : Op (d ^ n)) :
    T ∈ commutant (d ^ n) (Set.range (tensorWreathRep ρ n)) ↔
      (∀ v, Commute (tensorFamilyRep ρ n v) T) ∧ T ∈ permCommutant d n := by
  constructor
  · intro h
    constructor
    · intro v
      have hv := h _ ⟨⟨v, 1⟩, rfl⟩
      simpa only [Commute, SemiconjBy, tensorWreathRep, MonoidHom.coe_mk, OneHom.coe_mk,
        permutationRepresentation_one, mul_one] using hv
    · intro σ
      have hσ := h _ ⟨⟨1, σ⟩, rfl⟩
      simpa only [tensorWreathRep, MonoidHom.coe_mk, OneHom.coe_mk,
        tensorFamilyRep, Pi.one_apply, map_one, tensorFamily_one, one_mul] using hσ
  · rintro ⟨hG, hP⟩ M ⟨x, rfl⟩
    exact ((hG x.left).mul_left (hP x.right)).eq

/-- Tensor powers of the one-round commutant span the commutant of the joint finite action. -/
theorem span_centralizer_tensorPow_eq {G : Type*} [Group G] [Finite G]
    {d n : ℕ} [NeZero d] [NeZero n] (ρ : G →* Op d) :
    Submodule.span ℂ (Set.range fun A : commutant d (Set.range ρ) =>
      Op.tensorPow (A : Op d) n) = commutant (d ^ n) (Set.range (tensorWreathRep ρ n)) := by
  let := Fintype.ofFinite G
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨A, rfl⟩
    apply (mem_tensorWreathRep_commutant_iff ρ _).mpr
    constructor
    · intro v
      change tensorFamily (fun k => ρ (v k)) * Op.tensorPow (A : Op d) n =
        Op.tensorPow (A : Op d) n * tensorFamily (fun k => ρ (v k))
      simp only [Op.tensorPow_eq_tensorFamily, tensorFamily_mul]
      congr 1
      funext k
      exact A.property _ ⟨v k, rfl⟩
    · intro σ
      exact (Op.commute_tensorPow_permutationRepresentation (A : Op d) σ).symm.eq
  · intro T hT
    obtain ⟨hG, hP⟩ := (mem_tensorWreathRep_commutant_iff ρ T).mp hT
    rw [← span_tensorPow_eq_permCommutant] at hP
    let L := finiteGroupMatrixAverageLinear (tensorFamilyRep ρ n)
    have hLT : L T = T := finiteGroupMatrixAverage_eq_self _ _ hG
    rw [← hLT]
    clear hT hG hLT
    induction hP using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨A, rfl⟩ := hM
        change finiteGroupMatrixAverage _ _ ∈ _
        rw [finiteGroupMatrixAverage_tensorPow]
        apply Submodule.subset_span
        refine ⟨⟨finiteGroupMatrixAverage ρ A, ?_⟩, rfl⟩
        rintro M ⟨g, rfl⟩
        exact (finiteGroupMatrixAverage_commute ρ A g).eq
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [map_add]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => rw [map_smul]; exact Submodule.smul_mem _ c hA

/-- The commutant of constrained matrix tensor powers is the span of the joint finite action. -/
theorem commutant_centralizer_tensorPow_eq {G : Type*} [Group G] [Finite G]
    {d n : ℕ} [NeZero d] [NeZero n] (ρ : G →* Op d) :
    commutant (d ^ n) (Set.range fun A : commutant d (Set.range ρ) =>
      Op.tensorPow (A : Op d) n) = Submodule.span ℂ (Set.range (tensorWreathRep ρ n)) := by
  have : Finite (SemidirectProduct (Fin n → G) (Equiv.Perm (Fin n))
      (wordPermutationAction G n)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  rw [commutant_span, span_centralizer_tensorPow_eq, finiteGroup_bicommutant]

/-- Restricted Schur–Weyl duality for unitaries commuting with a finite-group action. -/
theorem commutant_unitaryCentralizer_tensorPow_eq {G : Type*} [Group G] [Finite G]
    {d n : ℕ} [NeZero d] [NeZero n] (ρ : G →* Op d)
    (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹) :
    commutant (d ^ n)
      (Set.range fun U : {U : Matrix.unitaryGroup (Fin d) ℂ // ∀ g, Commute (ρ g) (U : Op d)} =>
        Op.tensorPow (U.val : Op d) n) = Submodule.span ℂ (Set.range (tensorWreathRep ρ n)) := by
  rw [← commutant_centralizer_tensorPow_eq ρ]
  ext T
  constructor
  · intro hT A hA
    obtain ⟨A, rfl⟩ := hA
    refine commute_tensorPow_of_unitaryCentralizer (Set.range ρ) ?_ T ?_ (A : Op d) ?_
    · rintro M ⟨g, rfl⟩
      exact ⟨g⁻¹, (hρ g).symm⟩
    · intro U hU
      exact hT _ ⟨⟨U, fun g => hU _ ⟨g, rfl⟩⟩, rfl⟩
    · rintro M ⟨g, rfl⟩
      exact A.property _ ⟨g, rfl⟩
  · rintro hT A ⟨U, rfl⟩
    apply hT
    refine ⟨⟨(U.val : Op d), ?_⟩, rfl⟩
    rintro M ⟨g, rfl⟩
    exact (U.property g).eq

/-- Local action of the finite-group generators implies local compression of the Haar commutant. -/
theorem hasLocalCommutant_unitaryCentralizer_tensorPow {G : Type*} [Group G] [Finite G]
    {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n] (ρ : G →* Op b)
    (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹) (Q : Op (a ^ n * b ^ n))
    (hgen : ∀ x, ∃ X : Op (a ^ n),
      Op.tensor (1 : Op (a ^ n)) (tensorWreathRep ρ n x) * Q =
        Op.tensor X (1 : Op (b ^ n)) * Q) :
    HasLocalCommutant
      (fun U : {U : Matrix.unitaryGroup (Fin b) ℂ // ∀ g, Commute (ρ g) (U : Op b)} =>
        Op.tensorPow (U.val : Op b) n) Q := by
  let R := Set.range fun U :
    {U : Matrix.unitaryGroup (Fin b) ℂ // ∀ g, Commute (ρ g) (U : Op b)} =>
      Op.tensorPow (U.val : Op b) n
  apply hasLocalCommutant_of_span _ Q
    (Set.ofPred fun T => ∃ (X : Op (a ^ n)) (M : Op (b ^ n)),
      (∀ Y ∈ R, Commute Y M) ∧ T = Op.tensor X M)
  · intro T hT
    apply (Set.ext_iff.mp (commutant_pairedTensorFamily_eq_tensorCommutantSpan
      (dA := a) (dR := b) (n := n) R) T).mp
    rintro M ⟨U, rfl⟩
    exact hT U
  · rintro T ⟨X, M, hM, rfl⟩
    have hspan : M ∈ Submodule.span ℂ (Set.range (tensorWreathRep ρ n)) := by
      rw [← commutant_unitaryCentralizer_tensorPow_eq ρ hρ]
      exact hM
    clear hM
    induction hspan using Submodule.span_induction with
    | mem M hM =>
        obtain ⟨x, rfl⟩ := hM
        obtain ⟨Y, hY⟩ := hgen x
        refine ⟨X * Y, ?_⟩
        calc
          Op.tensor X (tensorWreathRep ρ n x) * Q =
              Op.tensor X (1 : Op (b ^ n)) *
                (Op.tensor (1 : Op (a ^ n)) (tensorWreathRep ρ n x) * Q) := by
            rw [← mul_assoc, Op.tensor_mul, mul_one, one_mul]
          _ = Op.tensor (X * Y) (1 : Op (b ^ n)) * Q := by
            rw [hY, ← mul_assoc, Op.tensor_mul, mul_one]
    | zero =>
        refine ⟨0, ?_⟩
        simp only [Op.tensor, Matrix.kronecker_zero, Matrix.zero_kronecker]
    | add M N _ _ hM hN =>
        obtain ⟨Y, hY⟩ := hM
        obtain ⟨Z, hZ⟩ := hN
        exact ⟨Y + Z, by rw [Op.tensor_add_right, add_mul, hY, hZ,
          Op.tensor_add_left, add_mul]⟩
    | smul c M _ hM =>
        obtain ⟨Y, hY⟩ := hM
        exact ⟨c • Y, by rw [Op.tensor_smul_right, smul_mul_assoc, hY,
          Op.tensor_smul_left, smul_mul_assoc]⟩

/-- Unitaries commuting with a matrix representation form its unitary centralizer. -/
def unitaryCentralizer {G : Type*} [Group G] {d : ℕ} (ρ : G →* Op d) :
    Subgroup (Matrix.unitaryGroup (Fin d) ℂ) where
  carrier := {U | ∀ g, Commute (ρ g) (U : Op d)}
  one_mem' := fun _ => Commute.one_right _
  mul_mem' hU hV g := (hU g).mul_right (hV g)
  inv_mem' {U} hU g := (hU g).units_inv_right (u := Unitary.toUnits U)

/-- The unitary centralizer is a closed subgroup. -/
lemma isClosed_unitaryCentralizer {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Op d) : IsClosed (unitaryCentralizer ρ : Set (Matrix.unitaryGroup (Fin d) ℂ)) := by
  change IsClosed (Set.ofPred fun U : Matrix.unitaryGroup (Fin d) ℂ => ∀ g,
    ρ g * (U : Op d) = (U : Op d) * ρ g)
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.matrix_mul continuous_subtype_val)
      (continuous_subtype_val.matrix_mul continuous_const)

/-- The unitary centralizer is compact. -/
instance unitaryCentralizer_compactSpace {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (ρ : G →* Op d) : CompactSpace (unitaryCentralizer ρ) :=
  isCompact_iff_compactSpace.mp (isClosed_unitaryCentralizer ρ).isCompact

/-- Haar probability measure on the unitary centralizer of a representation. -/
def unitaryCentralizerHaar {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (ρ : G →* Op d) : MeasureTheory.Measure (unitaryCentralizer ρ) :=
  ((MeasureTheory.Measure.haar : MeasureTheory.Measure (unitaryCentralizer ρ)) Set.univ)⁻¹ •
    MeasureTheory.Measure.haar

/-- The normalized Haar measure of the centralizer is a probability measure. -/
instance unitaryCentralizerHaar_isProbability {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (ρ : G →* Op d) : MeasureTheory.IsProbabilityMeasure (unitaryCentralizerHaar ρ) := by
  constructor
  simp only [unitaryCentralizerHaar, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (MeasureTheory.Measure.IsOpenPosMeasure.open_pos
    _ isOpen_univ Set.univ_nonempty) (ne_of_lt (IsCompact.measure_lt_top isCompact_univ))

/-- Normalization preserves left invariance of the centralizer Haar measure. -/
instance unitaryCentralizerHaar_isMulLeftInvariant {G : Type*} [Group G] {d : ℕ}
    [NeZero d] (ρ : G →* Op d) : (unitaryCentralizerHaar ρ).IsMulLeftInvariant := by
  unfold unitaryCentralizerHaar
  infer_instance

/-- Tensor powers of the defining unitary centralizer representation. -/
def unitaryCentralizerTensorPower {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Op d) (n : ℕ) :
    unitaryCentralizer ρ →* Matrix.unitaryGroup (Fin (d ^ n)) ℂ where
  toFun U := ⟨Op.tensorPow (U.val : Op d) n, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    exact Op.conjTranspose_tensorPow_mul_self (Matrix.mem_unitaryGroup_iff'.mp U.val.prop) n⟩
  map_one' := Subtype.ext (Op.one_tensorPow n)
  map_mul' U V := Subtype.ext (Op.mul_tensorPow (U.val : Op d) (V.val : Op d) n)

/-- The tensor-power centralizer action is continuous. -/
lemma continuous_unitaryCentralizerTensorPower {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Op d) (n : ℕ) : Continuous (unitaryCentralizerTensorPower ρ n) := by
  apply Continuous.subtype_mk
  exact (Op.continuous_tensorPow n).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- A fixed joint action transfers its reference action to the inverse system action. -/
lemma reference_action_eq_local_of_joint_fixed {a b : ℕ} (A A' : Op a)
    (B : Op b) (Q : Op (a * b)) (hA : A' * A = 1)
    (hfix : Op.tensor A B * Q = Q) :
    Op.tensor (1 : Op a) B * Q = Op.tensor A' (1 : Op b) * Q := by
  have h := congrArg (fun T => Op.tensor A' (1 : Op b) * T) hfix
  simpa only [← mul_assoc, Op.tensor_mul, hA, one_mul] using h

/-- Joint group and permutation support implies local compression of the centralizer commutant. -/
theorem hasLocalCommutant_unitaryCentralizer_of_joint_fixed
    {G : Type*} [Group G] [Finite G] {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n]
    (α : G →* Op a) (ρ : G →* Op b) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (Q : Op (a ^ n * b ^ n))
    (hG : ∀ v, Op.tensor (tensorFamilyRep α n v) (tensorFamilyRep ρ n v) * Q = Q)
    (hP : ∀ σ, Op.tensor (permutationRepresentation a n σ)
      (permutationRepresentation b n σ) * Q = Q) :
    HasLocalCommutant (fun U : unitaryCentralizer ρ =>
      (unitaryCentralizerTensorPower ρ n U : Op (b ^ n))) Q := by
  apply hasLocalCommutant_unitaryCentralizer_tensorPow ρ hρ Q
  intro x
  refine ⟨tensorWreathRep α n x⁻¹, reference_action_eq_local_of_joint_fixed
    (tensorWreathRep α n x) (tensorWreathRep α n x⁻¹) _ Q ?_ ?_⟩
  · rw [← map_mul, inv_mul_cancel, map_one]
  · change Op.tensor (tensorFamilyRep α n x.left * permutationRepresentation a n x.right)
      (tensorFamilyRep ρ n x.left * permutationRepresentation b n x.right) * Q = Q
    rw [← Op.tensor_mul, mul_assoc, hP, hG]

/-- The restricted Haar tensor moment is the inverse-marginal normalization of its support. -/
theorem unitaryCentralizerHaar_moment_eq_inverse_marginal
    {G : Type*} [Group G] [Finite G] {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n]
    (α : G →* Op a) (ρ : G →* Op b) (hρ : ∀ g, (ρ g)ᴴ = ρ g⁻¹)
    (T Q : Op (a ^ n * b ^ n)) (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hG : ∀ v, Op.tensor (tensorFamilyRep α n v) (tensorFamilyRep ρ n v) * Q = Q)
    (hP : ∀ σ, Op.tensor (permutationRepresentation a n σ)
      (permutationRepresentation b n σ) * Q = Q)
    (hcomm : ∀ U : unitaryCentralizer ρ,
      Commute (Op.tensor (1 : Op (a ^ n))
        (unitaryCentralizerTensorPower ρ n U : Op (b ^ n))) Q)
    (hΩ : IsUnit (partialTraceB Q)) (hT : partialTraceB T = 1) :
    referenceTwirl (unitaryCentralizerHaar ρ) (unitaryCentralizerTensorPower ρ n) T =
      Op.tensor (partialTraceB Q)⁻¹ (1 : Op (b ^ n)) * Q := by
  exact referenceTwirl_eq_inverse_marginal_mul _ _ T Q
    (referenceTwirl_integrable _ _ (continuous_unitaryCentralizerTensorPower ρ n) T)
    hQ hTQ hcomm (hasLocalCommutant_unitaryCentralizer_of_joint_fixed α ρ hρ Q hG hP) hΩ hT

end Quantum.Symmetry
