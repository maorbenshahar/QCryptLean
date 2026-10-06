import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.Quantum.Symmetry.FiniteGroupTensorCommutant
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirl
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.InfoTheory.Postselection.GroupPurification
import QCryptLean.InfoTheory.Postselection.GroupInvariantStates

/-!
# The blocked group twirl

The paired product-group twirl regrouped onto the blocked registers
`Aⁿ ⊗ (BE)ⁿ`, the reference representation on Bob and the purification
reference, and the commutation lemmas that make the blocked group twirl
compatible with the fixed-marginal de Finetti reduction.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ### The blocked group twirl -/

/-- The paired product-group twirl regrouped onto `Aⁿ ⊗ (BE)ⁿ`. -/
def groupBlockedTwirlProjector {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A]
    [Fintype G_B] {dA dB n : ℕ} (πA : G_A → Op dA) (πB : G_B → Op dB) :
    Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
  Matrix.reindex (pairedToBlockedEquiv dA dB n) (pairedToBlockedEquiv dA dB n)
    (groupPairedTwirlProjector n (prodRep πA πB))

/-- The product-group action on Bob and the purification reference, with Alice separated. -/
def groupReferenceRep {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB : ℕ}
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    G_A × G_B →* Op (dA * dB ^ 2) where
  toFun g := Matrix.reindex (finCongr (show dB * (dA * dB) = dA * dB ^ 2 by ring))
    (finCongr (show dB * (dA * dB) = dA * dB ^ 2 by ring))
    (Op.tensor (πB g.2) (entryConj (prodRep πA πB g)))
  map_one' := by
    simp only [Prod.snd_one, hπB.one, (prodRep_isUnitaryRep πA hπA πB hπB).one,
      entryConj_one, Op.tensor_one]
    simp
  map_mul' g h := by
    simp only [Prod.snd_mul, hπB.1, (prodRep_isUnitaryRep πA hπA πB hπB).1,
      entryConj_mul, ← Op.tensor_mul, Matrix.reindex_mul]

/-- The reference representation sends inversion to conjugate transpose. -/
lemma groupReferenceRep_conjTranspose
    {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB : ℕ}
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) (g : G_A × G_B) :
    (groupReferenceRep πA hπA πB hπB g)ᴴ = groupReferenceRep πA hπA πB hπB g⁻¹ := by
  simp only [groupReferenceRep, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.conjTranspose_reindex, Op.tensor_conjTranspose, entryConj_conjTranspose,
    ← hπB.inv, ← (prodRep_isUnitaryRep πA hπA πB hπB).inv, Prod.snd_inv]

/-- Paired group actions regroup into Alice and reference tensor-family actions. -/
lemma pairedToBlockedEquiv_groupAction
    {G_A G_B : Type*} [Group G_A] [Group G_B] {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) (v : Fin n → G_A × G_B) :
    Matrix.reindex (pairedToBlockedEquiv dA dB n) (pairedToBlockedEquiv dA dB n)
      (Op.tensor (tensorFamily fun k => prodRep πA πB (v k))
        (tensorFamily fun k => entryConj (prodRep πA πB (v k)))) =
      Op.tensor (tensorFamily fun k => πA (v k).1)
        (tensorFamilyRep (groupReferenceRep πA hπA πB hπB) n v) :=
  pairedToBlockedEquiv_tensorFamily _ _ _

/-- Every joint Alice-reference group action fixes the blocked twirl range. -/
lemma jointGroupAction_mul_groupBlockedTwirlProjector
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) (v : Fin n → G_A × G_B) :
    Op.tensor (tensorFamily fun k => πA (v k).1)
      (tensorFamilyRep (groupReferenceRep πA hπA πB hπB) n v) *
      groupBlockedTwirlProjector πA πB = groupBlockedTwirlProjector πA πB := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (pairedToBlockedEquiv dA dB n))
    (pairedGroupAction_mul_groupPairedTwirlProjector
      (prodRep πA πB) (prodRep_isUnitaryRep πA hπA πB hπB) v)
  simp only [map_mul, Matrix.coe_reindexAlgEquiv, pairedToBlockedEquiv_groupAction
    πA hπA πB hπB] at h
  exact h

/-- The blocked group twirl is an orthogonal projection. -/
lemma groupBlockedTwirlProjector_isOrthogonalProjection
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    let Q : Op (dA ^ n * (dA * dB ^ 2) ^ n) := groupBlockedTwirlProjector πA πB
    Q.IsHermitian ∧ Q * Q = Q := by
  dsimp only
  have hπ := prodRep_isUnitaryRep πA hπA πB hπB
  constructor
  · unfold groupBlockedTwirlProjector Matrix.IsHermitian
    rw [Matrix.conjTranspose_reindex, groupPairedTwirlProjector_isHermitian _ hπ]
  · unfold groupBlockedTwirlProjector
    rw [← Matrix.reindex_mul, groupPairedTwirlProjector_isProjection _ hπ]

/-- Regrouping preserves commutation of the group twirl with the round symmetrizer. -/
lemma groupBlockedTwirlProjector_commute_symmetricProjectorPairedGen
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (πB : G_B → Op dB) :
    Commute (groupBlockedTwirlProjector πA πB)
      (symmetricProjectorPairedGen dA (dA * dB ^ 2) n) := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (pairedToBlockedEquiv dA dB n))
    (groupPairedTwirlProjector_commute_symmetricProjectorPaired (n := n) (prodRep πA πB))
  simp only [map_mul, Matrix.coe_reindexAlgEquiv,
    pairedToBlockedEquiv_conjugates_projector] at h
  exact h

/-- The reference centralizer acts locally on the group-symmetric commutant. -/
lemma groupBlockedSymmetric_hasLocalCommutant
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    HasLocalCommutant (fun U : unitaryCentralizer (groupReferenceRep πA hπA πB hπB) =>
      (unitaryCentralizerTensorPower (groupReferenceRep πA hπA πB hπB) n U :
        Op ((dA * dB ^ 2) ^ n)))
      (groupBlockedTwirlProjector πA πB * symmetricProjectorPairedGen dA (dA * dB ^ 2) n) := by
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  apply hasLocalCommutant_unitaryCentralizer_of_joint_fixed
    -- the representation `πA`, viewed as a homomorphism into the matrix monoid
    ((⟨⟨πA, hπA.one⟩, hπA.1⟩ : G_A →* Op dA).comp (MonoidHom.fst G_A G_B)) _
    (groupReferenceRep_conjTranspose πA hπA πB hπB)
  · intro v
    rw [← mul_assoc]
    change (Op.tensor (tensorFamily fun k => πA (v k).1)
      (tensorFamilyRep (groupReferenceRep πA hπA πB hπB) n v) * _) * _ = _
    rw [jointGroupAction_mul_groupBlockedTwirlProjector πA hπA πB hπB]
  · intro σ
    rw [(groupBlockedTwirlProjector_commute_symmetricProjectorPairedGen πA πB).eq,
      ← mul_assoc, pairedPermutation_mul_symmetricProjectorPairedGen]

/-- Reference unitaries in the centralizer commute with the blocked group twirl. -/
lemma unitaryCentralizer_commute_groupBlockedTwirlProjector
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (U : unitaryCentralizer (groupReferenceRep πA hπA πB hπB)) :
    Commute (Op.tensor (1 : Op (dA ^ n))
      (unitaryCentralizerTensorPower (groupReferenceRep πA hπA πB hπB) n U :
        Op ((dA * dB ^ 2) ^ n))) (groupBlockedTwirlProjector πA πB) := by
  have hρU (v : Fin n → G_A × G_B) :
      Commute (Op.tensorPow (U.val : Op (dA * dB ^ 2)) n)
        (tensorFamilyRep (groupReferenceRep πA hπA πB hπB) n v) := by
    change Op.tensorPow _ _ * tensorFamily _ = tensorFamily _ * Op.tensorPow _ _
    simp only [Op.tensorPow_eq_tensorFamily, tensorFamily_mul]
    congr 1
    funext k
    exact (U.property (v k)).symm.eq
  unfold groupBlockedTwirlProjector
  rw [groupPairedTwirlProjector_eq_sum, Matrix.reindex_smul, Matrix.reindex_sum]
  apply Commute.smul_right
  apply Commute.sum_right
  intro v _
  rw [pairedToBlockedEquiv_groupAction πA hπA πB hπB]
  change Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U.val : Op (dA * dB ^ 2)) n) * _ = _
  rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, (hρU v).eq]
  rfl

/-- Lifting an Alice operator that commutes with every round-family group action
preserves commutation with the blocked group twirl. -/
lemma tensor_one_commute_groupBlockedTwirlProjector
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (πB : G_B → Op dB) (A : Op (dA ^ n))
    (hA : ∀ v : Fin n → G_A, A * tensorFamily (fun k => πA (v k)) =
      tensorFamily (fun k => πA (v k)) * A) :
    Commute (Op.tensor A (1 : Op ((dA * dB ^ 2) ^ n)))
      (groupBlockedTwirlProjector πA πB) := by
  let e := roundGroupEquiv dA dB n
  let M := Matrix.reindex e.symm e.symm (Op.tensor A (1 : Op (dB ^ n)))
  have hcomm : ∀ v : Fin n → G_A × G_B,
      M * tensorFamily (fun k => prodRep πA πB (v k)) =
        tensorFamily (fun k => prodRep πA πB (v k)) * M := by
    intro v
    have hAU := hA (fun k => (v k).1)
    apply (Matrix.reindexAlgEquiv ℂ ℂ e).injective
    simp only [map_mul, Matrix.coe_reindexAlgEquiv]
    rw [show Matrix.reindex e e M = Op.tensor A (1 : Op (dB ^ n)) from
      Matrix.reindex_reindex_symm e e _]
    have hfamily : Matrix.reindex e e (tensorFamily (fun k => prodRep πA πB (v k))) =
        Op.tensor (tensorFamily (fun k => πA ((v k).1)))
          (tensorFamily (fun k => πB ((v k).2))) := by
      rw [show e = (interleavingEquivGen dA dB n).symm from
        roundGroupEquiv_eq_interleavingEquivGen_symm dA dB n]
      exact tensorFamily_tensor_interleaving _ _
    rw [hfamily, Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, hAU]
  have hpaired : Commute (Op.tensor M (1 : Op ((dA * dB) ^ n)))
      (groupPairedTwirlProjector n (prodRep πA πB)) := by
    rw [groupPairedTwirlProjector_eq_sum]
    apply Commute.smul_right
    apply Commute.sum_right
    intro v _
    change _ * _ = _ * _
    rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, hcomm]
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (pairedToBlockedEquiv dA dB n)) hpaired.eq
  simp only [map_mul, Matrix.coe_reindexAlgEquiv] at h
  rw [show Matrix.reindex (pairedToBlockedEquiv dA dB n) (pairedToBlockedEquiv dA dB n)
      (Op.tensor M (1 : Op ((dA * dB) ^ n))) =
      Op.tensor A (1 : Op ((dA * dB ^ 2) ^ n)) from
        pairedToBlockedEquiv_tensor_one dA dB n A] at h
  exact h

/-- The lifted Alice marginal of a Hermitian operator supported on the blocked
group-twirl range commutes with that group twirl. -/
lemma partialTraceB_groupBlockedTwirl_supported_commute
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (X : Op (dA ^ n * (dA * dB ^ 2) ^ n)) (hX : X.IsHermitian)
    (hsupp : groupBlockedTwirlProjector πA πB * X = X) :
    Commute (Op.tensor (partialTraceB X) (1 : Op ((dA * dB ^ 2) ^ n)))
      (groupBlockedTwirlProjector πA πB) := by
  haveI : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  let e := pairedToBlockedEquiv dA dB n
  let Y := Matrix.reindex e.symm e.symm X
  have hY : Y.IsHermitian := hX.submatrix e
  have hGY : groupPairedTwirlProjector n (prodRep πA πB) * Y = Y := by
    have h := congrArg (Matrix.reindex e.symm e.symm) hsupp
    simpa only [Y, e, groupBlockedTwirlProjector, Matrix.reindex_mul,
      Matrix.reindex_symm_reindex] using h
  have hmarg : partialTraceB X = partialTraceB
      (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (partialTraceB Y)) := by
    have h := pairedToBlockedEquiv_partialTraceB_eq_roundGroup dA dB n Y
    simpa only [Y, e, Matrix.reindex_reindex_symm] using h
  apply tensor_one_commute_groupBlockedTwirlProjector
  intro v
  have hinv := partialTraceB_groupPairedTwirl_supported_invariant
    (prodRep πA πB) (prodRep_isUnitaryRep πA hπA πB hπB) Y hY hGY
    (fun k => (v k, 1))
  have htrans := roundwiseAliceMarginal_conj (fun k => πA (v k)) (fun _ => πB 1)
    (fun _ => hπB.2 1) (partialTraceB Y)
  dsimp only [prodRep] at hinv
  rw [hinv, ← hmarg] at htrans
  have h := congrArg (fun M => M * tensorFamily (fun k => πA (v k))) htrans
  have hU := conjTranspose_tensorFamily_mul_self (fun k => hπA.2 (v k))
  simpa only [mul_assoc, hU, mul_one] using h

/-- The prescribed Alice marginal, lifted to the blocked register, commutes with
the group-twirl projector. -/
lemma sigmaA_tensorPowGen_commute_groupBlockedTwirlProjector
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n) :
    Commute (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
      (groupBlockedTwirlProjector πA πB) := by
  apply tensor_one_commute_groupBlockedTwirlProjector
  intro v
  have hA := sigmaA_tensorPowGen_invariant πA πB hπB σA ρ hiid hmarg v
  have hU := conjTranspose_tensorFamily_mul_self (fun k => hπA.2 (v k))
  have h := congrArg (fun X => X * tensorFamily (fun k => πA (v k))) hA
  simpa only [mul_assoc, hU, mul_one] using h.symm

end InfoTheory.Postselection
