import QCryptLean.QKD.BB84.Reduction.RetainedBlocks
import QCryptLean.QKD.BB84.Model.IdealChannelKeyReplace
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Engine.Postselection.AnnounceOrthogonalSectors
import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp

/-!
# The retained experiment is a classical post-processing of the analytical model

The retained experiment (`QKD.BB84.Reduction.retainedAnalysisProgram`) announces a uniform
inner permutation, applies both parties' local sift-after-permutation operators, measures both
raw registers and runs the literal classical tail: parameter-estimation announcements, the fused
seed/tag/syndrome announcement, the accept decision, and the two private key computations or the
key-free abort.  The analytical model (`QKD.BB84.Model.bb84SymRealChannel`,
the classical part of the protocol of Nahar, Tupkary, Zhao, Lütkenhaus and Tan, arXiv:2403.11851,
Section V.C, `main.tex:906-919`) averages over the same permutations,
applies the same sift conjugation and joint measurement, and writes the same announcements, the
accept flag, and both hashed keys, with both key registers set to zero on abort.

Both outputs are therefore classical mixtures over the permutation, the raw outcome and the seed
pair, and each model output coordinate names one retained output point.  This module makes that
correspondence a channel and proves the two identities of the real/ideal interface of
Christandl--König--Renner, arXiv:0809.3019, Theorem 1 and Lemma 1, on the retained block
`n = nK + mZ + mX` with test-set size `mZ + mX` and the packed selectors:

* **N1** `retainedAnalysisReal_eq_modelPostprocess_comp`:
  `retainedAnalysisReal = modelPostprocess ∘ bb84SymRealChannel`.
* **N2** `retainedAnalysisIdeal_eq_modelPostprocess_comp`:
  `retainedAnalysisIdeal = modelPostprocess ∘ bb84SymIdealChannel`.
* **N3** `retainedAnalysisDifference_diamondNorm_le_model`: the diamond norm of the retained
  real-minus-ideal map is at most that of the model's.

`modelPostprocess` is the classical channel with Kraus operators `|modelOutputPoint j⟩⟨j|`: it reads
the model output in its computational basis and writes the retained output point that the read
coordinate names.  The announced permutation and every announcement are relabelled into the
retained complete output (`modelOutputDecode`, `modelTailData`), and on the abort flag the two key
registers are discarded, since the retained abort leaf holds no key register.  No input relabelling
occurs: `retainedAnalysisReal` already contains the round-grouped-to-Alice/Bob regrouping, so both
maps read the same `4 ^ n`-dimensional register.

N1 is proved entrywise.  The retained program is a classical mixture
(`retainedAnalysisProgram_denote_eq_sum`); so is the model (`bb84SymRealChannel_eq_sum`).  The two
local sift operators in Alice/Bob block coordinates are the model's sift-after-permutation in the
interleaved coordinates (`reindex_retainedAnalysisSiftedState`,
`QKD.BB84.Model.siftPermHalf_pair_conj_reindex`), and the model output coordinate of a raw outcome
names the retained output point of that outcome (`modelOutputPoint_modelOutputIndex`).  The last
step uses that the announced parameter-estimation test is the model's accept gate, which holds
because the packed selector marks exactly the announced test rounds
(`QKD.BB84.Reduction.packedPESel_keyCount`, through `QKD.BB84.Model.acceptFlagOf_eq`).

N2 follows from N1, the key-replacement law of the model
(`QKD.BB84.Model.bb84SymIdealChannel_eq_keyReplace_real`) and the intertwining of the two key
resources on the model's diagonal output (`retainedAnalysisResource_modelPostprocess_single`): an
accepting model coordinate names an accepting retained leaf holding its two keys, where both
resources replace the keys by one uniform shared key, and an aborting coordinate names the key-free
abort leaf, which both resources fix.  The retained side is computed through the key-layout
morphism of one final-stage leaf into the retained output (`retainedFinalStageHom`).
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace TypedLOCC.BoundaryKeyLayout

variable {P : Type} [Fintype P] [DecidableEq P]

/-- **The ideal key resource on a diagonal matrix unit.**  At a complete exit `e`, the ideal sends
the rank-one projector onto the output with key coordinates `(a, b)` and retained coordinate `u`
to the uniform mixture, over the shared key `k`, of the projectors onto the output with key
coordinates `(k, k)` and the same retained coordinate. -/
theorem ideal_single_coordinates {B : Boundary P} (L : BoundaryKeyLayout B) (e : B.Exit)
    (a b : (L.disposition e).Key) (u : L.Residual e) :
    L.ideal (Matrix.single (⟨e, (L.coordinates e).symm (a, b, u)⟩ : B.space)
        ⟨e, (L.coordinates e).symm (a, b, u)⟩ (1 : ℂ)) =
      ((((Fintype.card (L.disposition e).Key : ℝ))⁻¹ : ℝ) : ℂ) •
        ∑ k, Matrix.single (⟨e, (L.coordinates e).symm (k, k, u)⟩ : B.space)
          ⟨e, (L.coordinates e).symm (k, k, u)⟩ (1 : ℂ) := by
  classical
  ext ⟨f, p⟩ ⟨g, q⟩
  by_cases hfg : f = g
  · subst hfg
    rcases hp : L.coordinates f p with ⟨a₁, b₁, u₁⟩
    rcases hq : L.coordinates f q with ⟨a₂, b₂, u₂⟩
    obtain rfl : p = (L.coordinates f).symm (a₁, b₁, u₁) := by
      rw [← hp, Equiv.symm_apply_apply]
    obtain rfl : q = (L.coordinates f).symm (a₂, b₂, u₂) := by
      rw [← hq, Equiv.symm_apply_apply]
    rw [L.ideal_coordinate_entry]
    by_cases hfe : f = e
    · subst hfe
      simp only [Matrix.single_apply, Matrix.smul_apply, Matrix.sum_apply, Sigma.mk.inj_iff,
        heq_eq_eq, true_and, Equiv.apply_eq_iff_eq, Prod.mk.injEq, smul_eq_mul]
      by_cases hk : a₁ = b₁ ∧ a₂ = b₂ ∧ a₁ = a₂
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        rw [if_pos ⟨rfl, rfl, rfl⟩]
        simp [Finset.sum_ite_eq, ite_and, eq_comm]
      · rw [if_neg hk]
        symm
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => if_neg ?_)
        rintro ⟨⟨rfl, rfl, -⟩, ⟨h₂, h₂', -⟩⟩
        exact hk ⟨rfl, h₂.symm.trans h₂', h₂⟩
    · have hne : ∀ (r r' : (L.disposition e).Key × (L.disposition e).Key × L.Residual e)
          (s s' : (L.disposition f).Key × (L.disposition f).Key × L.Residual f),
          Matrix.single (⟨e, (L.coordinates e).symm r⟩ : B.space)
            ⟨e, (L.coordinates e).symm r'⟩ (1 : ℂ)
            (⟨f, (L.coordinates f).symm s⟩ : B.space)
            (⟨f, (L.coordinates f).symm s'⟩ : B.space) = 0 := by
        intro r r' s s'
        rw [Matrix.single_apply, if_neg]
        rintro ⟨h, -⟩
        exact hfe (congrArg Sigma.fst h).symm
      simp only [hne, Finset.sum_const_zero, mul_zero, ite_self, Matrix.smul_apply,
        Matrix.sum_apply, smul_zero]
  · rw [L.ideal_crossExit_zero _ hfg]
    symm
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => if_neg ?_)
    rintro ⟨h, h'⟩
    exact hfg ((congrArg Sigma.fst h).symm.trans (congrArg Sigma.fst h'))

namespace Hom

/-- **The ideal key resource transports diagonal matrix units along an injective morphism.** If
the source ideal sends the projector onto `x` to a weighted sum of projectors, the target ideal
sends the projector onto the image of `x` to the same weighted sum of the image projectors. -/
theorem ideal_single_of_injective {B₂ B₁ : Boundary P} {L₂ : BoundaryKeyLayout B₂}
    {L₁ : BoundaryKeyLayout B₁} (φ : Hom L₂ L₁) (hφ : Function.Injective φ)
    {ι : Type} [Fintype ι] (x : B₂.space) (c : ℂ) (y : ι → B₂.space)
    (h : L₂.ideal (Matrix.single x x (1 : ℂ)) =
      c • ∑ i, Matrix.single (y i) (y i) (1 : ℂ)) :
    L₁.ideal (Matrix.single (φ x) (φ x) (1 : ℂ)) =
      c • ∑ i, Matrix.single (φ (y i)) (φ (y i)) (1 : ℂ) := by
  classical
  have hM : ∀ z w, (z ∉ Set.range φ ∨ w ∉ Set.range φ) →
      Matrix.single (φ x) (φ x) (1 : ℂ) z w = 0 := by
    rintro z w (hz | hw)
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hz ⟨x, rfl⟩
    · rw [Matrix.single_apply, if_neg]
      rintro ⟨-, rfl⟩
      exact hw ⟨x, rfl⟩
  have hM' : ∀ z w, (z ∉ Set.range φ ∨ w ∉ Set.range φ) →
      (c • ∑ i, Matrix.single (φ (y i)) (φ (y i)) (1 : ℂ)) z w = 0 := by
    rintro z w hzw
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => if_neg ?_)
    rintro ⟨rfl, rfl⟩
    rcases hzw with hz | hw
    · exact hz ⟨y i, rfl⟩
    · exact hw ⟨y i, rfl⟩
  rw [φ.ideal_eq_iff hM hM']
  have hsub : ∀ z : B₂.space,
      (Matrix.single (φ z) (φ z) (1 : ℂ)).submatrix φ φ = Matrix.single z z 1 := by
    intro z
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.single_apply, hφ.eq_iff]
  rw [hsub, h]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply,
    hφ.eq_iff]

end Hom

end TypedLOCC.BoundaryKeyLayout

namespace QKD

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

/-- Conjugating a diagonal matrix unit by a Kraus operator whose column at the unit's index is a
single scaled basis vector. -/
theorem conj_single_of_mul_single {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (i : Fin p)
    (i' : Fin q) (μ : ℂ) (h : K * Matrix.single i i (1 : ℂ) = Matrix.single i' i μ) :
    K * Matrix.single i i (1 : ℂ) * Kᴴ = Matrix.single i' i' (μ * star μ) := by
  have hS : Matrix.single i i (1 : ℂ) * (Matrix.single i i (1 : ℂ))ᴴ =
      Matrix.single i i (1 : ℂ) := by
    rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one]
  calc K * Matrix.single i i (1 : ℂ) * Kᴴ
         = K * (Matrix.single i i (1 : ℂ) * (Matrix.single i i (1 : ℂ))ᴴ) * Kᴴ := by rw [hS]
    _ = (K * Matrix.single i i (1 : ℂ)) * (K * Matrix.single i i (1 : ℂ))ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Matrix.single i' i' (μ * star μ) := by
        rw [h, Matrix.conjTranspose_single, Matrix.single_mul_single_same]

/-- **Key replacement fixes an abort matrix unit.** -/
theorem keyReplace_single_abort (ℓ D : ℕ) (kp : Fin (2 ^ ℓ * 2 ^ ℓ)) (r : Fin D) :
    keyReplace ℓ D
        (Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r)))
          (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) (1 : ℂ)) =
      Matrix.single (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r)))
        (finProdFinEquiv (kp, finProdFinEquiv ((1 : Fin 2), r))) (1 : ℂ) := by
  classical
  obtain ⟨⟨kA, kB⟩, rfl⟩ := finProdFinEquiv.surjective kp
  rw [keyReplace_eq_krausMapFintype]
  change ∑ o, keyReplaceKraus ℓ D o * _ * (keyReplaceKraus ℓ D o)ᴴ = _
  rw [Fintype.sum_option]
  have hnone := conj_single_of_mul_single (abortProjOp ℓ D) _ _ _
    (QKD.BB84.Model.abortProjOp_mul_single (finProdFinEquiv (kA, kB)) (1 : Fin 2) r
      (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((1 : Fin 2), r))))
  have hsome : ∀ o : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
      keyReplaceKraus ℓ D (some o) *
          Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
            finProdFinEquiv ((1 : Fin 2), r)))
            (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((1 : Fin 2), r)))
            (1 : ℂ) *
          (keyReplaceKraus ℓ D (some o))ᴴ = 0 := by
    rintro ⟨k, a, b⟩
    rw [keyReplaceKraus_some, conj_single_of_mul_single _ _ _ _
      (QKD.BB84.Model.freshKeyKraus_mul_single k a b kA kB (1 : Fin 2) r _)]
    simp
  rw [keyReplaceKraus_none, hnone, Finset.sum_eq_zero fun o _ => hsome o, add_zero]
  simp

/-- **Key replacement on an accept matrix unit**: both keys are replaced by one uniform shared
key, and the flag and the remaining transcript are kept. -/
theorem keyReplace_single_accept (ℓ D : ℕ) (kA kB : Fin (2 ^ ℓ)) (r : Fin D) :
    keyReplace ℓ D
        (Matrix.single
          (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r)))
          (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r))) (1 : ℂ)) =
      ((2 : ℂ) ^ ℓ)⁻¹ • ∑ k : Fin (2 ^ ℓ),
        Matrix.single (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r)))
          (finProdFinEquiv (finProdFinEquiv (k, k), finProdFinEquiv ((0 : Fin 2), r))) (1 : ℂ) := by
  classical
  rw [keyReplace_eq_krausMapFintype]
  change ∑ o, keyReplaceKraus ℓ D o * _ * (keyReplaceKraus ℓ D o)ᴴ = _
  rw [Fintype.sum_option]
  have hnone := conj_single_of_mul_single (abortProjOp ℓ D) _ _ _
    (QKD.BB84.Model.abortProjOp_mul_single (finProdFinEquiv (kA, kB)) (0 : Fin 2) r
      (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r))))
  have hc : ((Real.sqrt ((2 : ℝ) ^ ℓ) : ℂ))⁻¹ * ((Real.sqrt ((2 : ℝ) ^ ℓ) : ℂ))⁻¹ =
      ((2 : ℂ) ^ ℓ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hsome : ∀ o : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
      keyReplaceKraus ℓ D (some o) *
          Matrix.single (finProdFinEquiv (finProdFinEquiv (kA, kB),
            finProdFinEquiv ((0 : Fin 2), r)))
            (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv ((0 : Fin 2), r)))
            (1 : ℂ) *
          (keyReplaceKraus ℓ D (some o))ᴴ =
        if o.2.1 = kA ∧ o.2.2 = kB then
          ((2 : ℂ) ^ ℓ)⁻¹ • Matrix.single
            (finProdFinEquiv (finProdFinEquiv (o.1, o.1), finProdFinEquiv ((0 : Fin 2), r)))
            (finProdFinEquiv (finProdFinEquiv (o.1, o.1), finProdFinEquiv ((0 : Fin 2), r)))
            (1 : ℂ)
        else 0 := by
    rintro ⟨k, a, b⟩
    rw [keyReplaceKraus_some, conj_single_of_mul_single _ _ _ _
      (QKD.BB84.Model.freshKeyKraus_mul_single k a b kA kB (0 : Fin 2) r _)]
    by_cases ha : a = kA <;> by_cases hb : b = kB <;>
      simp [ha, hb, hc, Matrix.smul_single]
  rw [keyReplaceKraus_none, hnone, Finset.sum_congr rfl fun o _ => hsome o]
  simp only [Fintype.sum_prod_type, ite_and]
  simp [Finset.smul_sum]

end QKD

namespace QKD.BB84.Reduction

open TypedLOCC TypedLOCC.TwoParty QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Engine
open QKD.BB84.Model

/-! ## The analytical model as a classical mixture -/

section Model

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

/-- A tensor product distributes over a finite sum in its left factor. -/
theorem op_tensor_sum_left {n m : ℕ} {ι : Type*} [Fintype ι] (f : ι → Op n) (B : Op m) :
    Op.tensor (∑ i, f i) B = ∑ i, Op.tensor (f i) B := by
  ext a b
  simp only [Op_tensor_apply_finProd, Matrix.sum_apply, Finset.sum_mul]

/-- **The output index of the analytical model**: at an announced permutation `pi`, a seed pair
`st` and a joint round outcome `ω`, the classical post-processing index
`QKD.BB84.Model.bb84OutIndex` with the announced permutation appended as the last register. -/
def modelOutputIndex (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ) (pi : Equiv.Perm (Fin n))
    (st : KeyHashSeedPairEV n ell ellEV peSel) (ω : Fin n → Fin signalDim) :
    Fin (bb84EveVisiblePEAnnounceSymOutputDim n m ell ellEV peSel leakEC 1) :=
  Fin.cast (QKD.BB84.Model.symOutDimPad n m ell ellEV peSel leakEC)
    (finProdFinEquiv
      (QKD.BB84.Model.bb84OutIndex n m ell ellEV peSel xSel leakEC ec delta Q st ω,
        permAnnounceIndexEquiv n pi))

/-- The classical layer of the model on an arbitrary operator: the diagonal entry at each joint
outcome, spread uniformly over the announced seed pairs. -/
theorem bb84RealProtocolMapBare_eq_sum (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (delta Q : ℝ) (A : Op (4 ^ n)) :
    QKD.BB84.Model.bb84RealProtocolMapBare n m ell ellEV peSel xSel leakEC ec delta Q A =
      ∑ c : Fin (4 ^ n), ∑ st : KeyHashSeedPairEV n ell ellEV peSel,
        (A c c * ((Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ))⁻¹) •
          Matrix.single
            (QKD.BB84.Model.bb84OutIndex n m ell ellEV peSel xSel leakEC ec delta Q st
              (finFunctionFinEquiv.symm c))
            (QKD.BB84.Model.bb84OutIndex n m ell ellEV peSel xSel leakEC ec delta Q st
              (finFunctionFinEquiv.symm c)) (1 : ℂ) := by
  rw [QKD.BB84.Model.bb84RealProtocolMapBare, LinearMap.comp_apply,
    QKD.BB84.Model.bb84MeasureBare_apply,
    Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => QKD.BB84.Model.single_conj_general c A,
    map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, QKD.BB84.Model.classicalPostBare_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [smul_smul]

/-- **The real map of the analytical model as a classical mixture.**

`bb84SymRealChannel` sends an arbitrary input operator to the sum, over the announced
permutation `pi`, the joint round outcome `c` and the announced seed pair `st`, of the projector
onto `modelOutputIndex pi st c`, weighted by `1 / n!`, the diagonal entry at `c` of the sifted and
permuted input and the uniform seed weight. -/
theorem bb84SymRealChannel_eq_sum (n m ell ellEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q delta : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (rho : Op (4 ^ n)) :
    bb84SymRealChannel n m ell ellEV Q delta peSel xSel leakEC ec rho =
      ∑ pi : Equiv.Perm (Fin n), ∑ c : Fin (4 ^ n),
        ∑ st : KeyHashSeedPairEV n ell ellEV peSel,
          ((n.factorial : ℂ)⁻¹ *
              ((bb84SiftedRotation n peSel xSel * permuteSignalLinear n pi rho *
                  (bb84SiftedRotation n peSel xSel)ᴴ) c c *
                ((Fintype.card (KeyHashSeedPairEV n ell ellEV peSel) : ℂ))⁻¹)) •
            Matrix.single
              (modelOutputIndex n m ell ellEV peSel xSel leakEC ec delta Q pi st
                (finFunctionFinEquiv.symm c))
              (modelOutputIndex n m ell ellEV peSel xSel leakEC ec delta Q pi st
                (finFunctionFinEquiv.symm c)) (1 : ℂ) := by
  rw [QKD.BB84.Model.bb84SymRealChannel_apply_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [bb84RealProtocolMapBare_eq_sum, op_tensor_sum_left, Op.castDim_sum_univ,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [op_tensor_sum_left, Op.castDim_sum_univ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [Op.tensor_smul_left, Op.castDim_smul, smul_smul,
    QKD.BB84.Engine.permAnnounceProjector_eq_single',
    Op.single_tensor_single_diag, Op.castDim_single, one_div]
  rfl

end Model

/-! ## Final-stage output points -/

/-- **The final-stage output point written by an announced decision flag and two key values.**
On flag `0` it is the accepting leaf in which Alice holds `a` and Bob holds `b`; on every other flag
it is the key-free abort leaf, which does not depend on `a` and `b`. -/
noncomputable def finalStagePoint (ell : ℕ) (flag : Fin 2) (a b : Fin (2 ^ ell)) :
    (FinalStage.boundary ell).space := by
  by_cases hflag : flag = 0
  · refine (Boundary.publicSpaceEquiv (FinalStage.flagBoundary ell)).symm
      ⟨flag, ?_⟩
    simpa [FinalStage.flagBoundary, hflag] using
      (Boundary.leafSpaceEquiv (FinalStage.keySystem ell)).symm
        ((TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell))).symm (a, b))
  · refine (Boundary.publicSpaceEquiv (FinalStage.flagBoundary ell)).symm
      ⟨flag, ?_⟩
    simpa [FinalStage.flagBoundary, hflag] using
      (Boundary.leafSpaceEquiv FinalStage.abortSystem).symm
        ((TwoParty.pairEquiv Unit Unit).symm ((), ()))

/-- The retained classical tail's final point is the final-stage point of its semantic decision flag
and its two key slots. -/
theorem rawClassicalTailFinalPoint_eq_finalStagePoint
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) :
    rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x =
      finalStagePoint ell
        (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
          d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob))
        (QKD.BB84.Model.aliceKeySlotOf n ell peSel d.seedPair.1
          (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
            d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)) (x .alice))
        (QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec d.seedPair.1 d.syndrome
          (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
            d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)) (x .bob)) :=
  rfl


/-! ## The classical post-processing from the model output to the retained output -/

section PostProcessing

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

attribute [local instance] retainedAnalysisOutputDimNeZero

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- The output dimension of the analytical model on the retained block of `nK + mZ + mX` sifted
rounds with `mZ + mX` test rounds and the packed selectors. -/
abbrev ModelOutputDim : ℕ :=
  bb84EveVisiblePEAnnounceSymOutputDim (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC 1

/-- The inner transcript dimension of the model: seed pair, verification tag, syndrome and
parameter-estimation block. -/
abbrev ModelInnerDim : ℕ :=
  bb84PEAnnounceInnerTranscriptDim (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC

/-- **The public data recorded by an inner transcript coordinate of the model.**  The coordinate
is read as the announced seed pair, verification tag, syndrome and parameter-estimation block;
each announced test-round outcome is read as Alice's bit (high digit) and Bob's bit (low digit),
the digit convention of `QKD.BB84.Model.jointOutcome`. -/
noncomputable def modelTailData (t : Fin (ModelInnerDim nK mZ mX ell ellEV leakEC)) :
    QKD.BB84.ClassicalTailData (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC :=
  let tp := finProdFinEquiv.symm t
  let us := finProdFinEquiv.symm tp.1
  let se := finProdFinEquiv.symm us.1
  let pe := finFunctionFinEquiv.symm tp.2
  { alicePE := fun i => ((finProdFinEquiv (m := 2) (n := 2)).symm (pe i)).1
    bobPE := fun i => ((finProdFinEquiv (m := 2) (n := 2)).symm (pe i)).2
    seedPair := (Fintype.equivFin _).symm se.1
    evTag := se.2
    syndrome := us.2 }

/-- **The data recorded by a model output coordinate**: the announced permutation, the two key
registers, the decision flag and the inner transcript coordinate. -/
noncomputable def modelOutputDecode (j : Fin (ModelOutputDim nK mZ mX ell ellEV leakEC)) :
    Equiv.Perm (Fin (nK + mZ + mX)) × (Fin (2 ^ ell) × Fin (2 ^ ell)) × Fin 2 ×
      Fin (ModelInnerDim nK mZ mX ell ellEV leakEC) :=
  let jp := finProdFinEquiv.symm
    (Fin.cast (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).symm j)
  let base := finProdFinEquiv.symm jp.1
  let rest := finProdFinEquiv.symm base.2
  ((permAnnounceIndexEquiv (nK + mZ + mX)).symm jp.2, finProdFinEquiv.symm base.1, rest.1, rest.2)

/-- **The retained output point named by a model output coordinate.**

The announced permutation, the public tail data of `modelTailData`, and the final-stage point of
the recorded decision flag: on flag `0` the accepting leaf holding the two recorded keys, on flag
`1` the key-free abort leaf.  The two key registers of an aborting model output are discarded. -/
noncomputable def modelOutputPoint (j : Fin (ModelOutputDim nK mZ mX ell ellEV leakEC)) :
    (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space :=
  let D := modelOutputDecode nK mZ mX ell ellEV leakEC j
  (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
    (D.1, (Boundary.graftSpaceEquiv
        (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)
        (fun _ => FinalStage.boundary ell)).symm
      ⟨(QKD.BB84.classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).symm
          (modelTailData nK mZ mX ell ellEV leakEC D.2.2.2),
        finalStagePoint ell D.2.2.1 D.2.1.1 D.2.1.2⟩)

/-- **The classical post-processing channel from the model output to the retained output.**

It reads the model output register in its computational basis and writes the retained output
point that the read coordinate names (`modelOutputPoint`): the announced permutation and every
announcement are relabelled into the retained experiment's complete output, and on the abort flag
the two key registers are discarded, since the retained experiment's abort leaf holds no key
register.  Its Kraus operators are the matrix units `|modelOutputPoint j⟩⟨j|`. -/
noncomputable def modelPostprocess :
    Op (ModelOutputDim nK mZ mX ell ellEV leakEC) →ₗ[ℂ]
      Op (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  Quantum.Channels.krausMapFintype fun j =>
    Matrix.single
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
        (modelOutputPoint nK mZ mX ell ellEV leakEC j)) j (1 : ℂ)

/-- The classical post-processing is a channel. -/
theorem modelPostprocess_isCPTP :
    Quantum.Channels.IsCPTP ⇑(modelPostprocess nK mZ mX ell ellEV leakEC) := by
  refine Quantum.Channels.krausMapFintype_isCPTP _ ?_
  simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, mul_one]
  exact Matrix.sum_single_one

/-- The classical post-processing sends a diagonal matrix unit to the matrix unit at the named
retained output point. -/
theorem modelPostprocess_single (j : Fin (ModelOutputDim nK mZ mX ell ellEV leakEC)) (c : ℂ) :
    modelPostprocess nK mZ mX ell ellEV leakEC (Matrix.single j j c) =
      Matrix.single
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
          (modelOutputPoint nK mZ mX ell ellEV leakEC j))
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
          (modelOutputPoint nK mZ mX ell ellEV leakEC j)) c := by
  change ∑ i, Matrix.single (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
      (modelOutputPoint nK mZ mX ell ellEV leakEC i)) i (1 : ℂ) * Matrix.single j j c *
      (Matrix.single (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
        (modelOutputPoint nK mZ mX ell ellEV leakEC i)) i (1 : ℂ))ᴴ = _
  rw [Finset.sum_eq_single j]
  · rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same,
      Matrix.single_mul_single_same, one_mul, mul_one]
  · intro i _ hij
    rw [Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Reading a model output coordinate built from its registers returns those registers. -/
theorem modelOutputDecode_cast (kp : Fin (2 ^ ell * 2 ^ ell)) (f : Fin 2)
    (t : Fin (ModelInnerDim nK mZ mX ell ellEV leakEC))
    (p : Fin (nK + mZ + mX).factorial) :
    modelOutputDecode nK mZ mX ell ellEV leakEC
        (Fin.cast (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
            (@Sampling.packedPESel nK mZ mX) leakEC)
          (finProdFinEquiv (finProdFinEquiv (kp, finProdFinEquiv (f, t)), p))) =
      ((permAnnounceIndexEquiv (nK + mZ + mX)).symm p, finProdFinEquiv.symm kp, f, t) := by
  simp [modelOutputDecode]

end PostProcessing


/-! ## The model output of a raw outcome names the retained output of that outcome -/

section Decode

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

/-- `rawClassicalTailDataOf` with its fused announcement decoded: the parameter-estimation bits of
both parties, the seed pair, and Alice's verification tag and syndrome. -/
theorem rawClassicalTailDataOf_eq (n m ell ellEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ell ellEV peSel) :
    rawClassicalTailDataOf n m ell ellEV peSel leakEC ec x st =
      { alicePE := fun j =>
          LOCC.registerBit n (bb84PERoundIdx (m := m) peSel j) (x .alice)
        bobPE := fun j =>
          LOCC.registerBit n (bb84PERoundIdx (m := m) peSel j) (x .bob)
        seedPair := st
        evTag := verificationTag n ellEV peSel st.2 (QKD.BB84.Model.aliceKeyOf n peSel (x .alice))
        syndrome := ec.syndrome (QKD.BB84.Model.aliceKeyOf n peSel (x .alice)) } := by
  simp [rawClassicalTailDataOf, QKD.BB84.Model.evTagSynOf_eq, QKD.BB84.Model.announcedSeed]

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- The inner transcript coordinate the model writes at the seed pair `st` on the joint outcome
of the raw registers `x` records exactly the retained experiment's public tail data. -/
theorem modelTailData_eq_rawClassicalTailDataOf
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total)
    (st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)) :
    modelTailData nK mZ mX ell ellEV leakEC
        (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv
          (Fintype.equivFin (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
            (@Sampling.packedPESel nK mZ mX)) st,
          verificationTag (nK + mZ + mX) ellEV (@Sampling.packedPESel nK mZ mX) st.2
            (aliceKeyString (@Sampling.packedPESel nK mZ mX)
              (QKD.BB84.Model.jointOutcome (nK + mZ + mX) (x .alice) (x .bob)))),
          ec.syndrome (aliceKeyString (@Sampling.packedPESel nK mZ mX)
            (QKD.BB84.Model.jointOutcome (nK + mZ + mX) (x .alice) (x .bob)))),
          finFunctionFinEquiv (bb84PartEquiv (m := mZ + mX) (@Sampling.packedPESel nK mZ mX)
            (QKD.BB84.Model.jointOutcome (nK + mZ + mX) (x .alice) (x .bob))).2)) =
      rawClassicalTailDataOf (nK + mZ + mX) (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
        leakEC ec x st := by
  rw [rawClassicalTailDataOf_eq]
  simp [modelTailData, QKD.BB84.Model.jointOutcome, QKD.BB84.Model.aliceKeyString_jointOutcome]


/-- The abort leaf of the final stage carries no key register: its point does not depend on the
two key values. -/
theorem finalStagePoint_one (ell : ℕ) (a b a' b' : Fin (2 ^ ell)) :
    finalStagePoint ell 1 a b = finalStagePoint ell 1 a' b' :=
  rfl

/-- **A model output of a raw outcome names the retained output of that outcome.**

At the announced permutation `pi`, the seed pair `st` and the raw registers `x`, the model output
coordinate `modelOutputIndex` written on the joint outcome of `x` names, through
`modelOutputPoint`, the retained output point of `pi` and the raw-tail output of `x` and `st`.
The announced parameter-estimation test is the model's accept gate because the packed selector
marks exactly the announced test rounds (`packedPESel_keyCount`). -/
theorem modelOutputPoint_modelOutputIndex
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX))
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
    modelOutputPoint nK mZ mX ell ellEV leakEC
        (modelOutputIndex (nK + mZ + mX) (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q pi st
          (QKD.BB84.Model.jointOutcome (nK + mZ + mX) (x .alice) (x .bob))) =
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
        (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q
          x st) := by
  have hflag := QKD.BB84.Model.acceptFlagOf_eq (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q
    (packedPESel_keyCount nK mZ mX) st.2 (x .alice) (x .bob)
  have hdata := modelTailData_eq_rawClassicalTailDataOf nK mZ mX ell ellEV leakEC ec x st
  simp only [rawClassicalTailOutputPoint]
  rw [rawClassicalTailFinalPoint_eq_finalStagePoint, rawClassicalTailDataOf_eq]
  dsimp only
  rw [hflag]
  unfold modelOutputPoint modelOutputIndex
  rw [QKD.BB84.Model.bb84OutIndex]
  split_ifs with hg
  · simp only [bb84.pePassOutIndex]
    rw [modelOutputDecode_cast]
    dsimp only
    rw [hdata, rawClassicalTailDataOf_eq]
    simp only [Equiv.symm_apply_apply, Fin.zero_eta, QKD.BB84.Model.aliceKeySlotOf,
      QKD.BB84.Model.bobKeySlotOf, ↓reduceIte, QKD.BB84.Model.aliceKeyString_jointOutcome,
      QKD.BB84.Model.bobKeyString_jointOutcome]
  · simp only [bb84.peFailOutIndex]
    rw [modelOutputDecode_cast]
    dsimp only
    rw [hdata, rawClassicalTailDataOf_eq]
    simp only [Equiv.symm_apply_apply]
    rfl

end Decode


/-! ## N1: the retained real map is the post-processed model real map -/

section Real

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

attribute [local instance] retainedAnalysisOutputDimNeZero

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- **The retained real map is the classical post-processing of the model's real map.**

For every complex input operator on the `4 ^ (nK + mZ + mX)`-dimensional round-grouped register,
the retained experiment's real map equals `modelPostprocess` after the analytical model's real
map `bb84SymRealChannel` at sifted block `nK + mZ + mX`, test-set size `mZ + mX` and the
packed selectors.  The two maps read the same input register: the round-grouped-to-Alice/Bob
regrouping `retainedAnalysisRoundToBlock` is part of `retainedAnalysisReal` itself, so no input
relabelling occurs.  The permutation average, the sift conjugation and the joint measurement of
the model are the announced inner permutation, the two local sift operators and the two private
measurements of the retained experiment (`QKD.BB84.Model.siftPermHalf_pair_conj_reindex`,
`reindex_retainedAnalysisSiftedState`), and the model's announcement index names the retained
output point (`modelOutputPoint_modelOutputIndex`). -/
theorem retainedAnalysisReal_eq_modelPostprocess_comp [NeZero (nK + mZ + mX)]
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (bb84SymRealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  classical
  refine LinearMap.ext fun rho => ?_
  have hL : retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q rho =
      Matrix.reindex (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
        ((retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote
          (Matrix.reindex (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
            (Matrix.reindex (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
              (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)) rho))) := by
    rfl
  rw [hL, retainedAnalysisProgram_denote_eq_sum, LinearMap.comp_apply,
    bb84SymRealChannel_eq_sum]
  simp only [Matrix.reindex_sum, Matrix.reindex_smul, Quantum.TensorProducts.reindex_single,
    map_sum, map_smul, modelPostprocess_single]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [← Equiv.sum_comp ((retainedAnalysisBlockInputEquiv (nK + mZ + mX)).trans
    (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)).symm)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun st _ => ?_
  have hc : ((retainedAnalysisBlockInputEquiv (nK + mZ + mX)).trans
      (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)).symm) x =
      finFunctionFinEquiv (QKD.BB84.Model.jointOutcome (nK + mZ + mX) (x .alice) (x .bob)) :=
    QKD.BB84.Model.roundGroupEquiv_symm_finProd (nK + mZ + mX) (x .alice) (x .bob)
  have hstate :
      (bb84SiftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) * permuteSignalLinear (nK + mZ + mX) pi rho *
        (bb84SiftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX))ᴴ)
          (((retainedAnalysisBlockInputEquiv (nK + mZ + mX)).trans
            (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)).symm) x)
          (((retainedAnalysisBlockInputEquiv (nK + mZ + mX)).trans
            (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)).symm) x) =
        retainedAnalysisSiftedState (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi
          (Matrix.reindex (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
            (Matrix.reindex (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
              (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)) rho)) x x := by
    calc _ = Matrix.reindex (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
            (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
            (bb84SiftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) * permuteSignalLinear (nK + mZ + mX) pi rho *
              (bb84SiftedRotation (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX))ᴴ)
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX) x)
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX) x) := rfl
      _ = Matrix.reindex (retainedAnalysisBlockInputEquiv (nK + mZ + mX))
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX))
            (retainedAnalysisSiftedState (@Sampling.packedPESel nK mZ mX)
              (@Sampling.packedXSel nK mZ mX) pi
              (Matrix.reindex (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
                (retainedAnalysisBlockInputEquiv (nK + mZ + mX)).symm
                (Matrix.reindex (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
                  (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX)) rho)))
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX) x)
            (retainedAnalysisBlockInputEquiv (nK + mZ + mX) x) := by
        rw [← QKD.BB84.Model.siftPermHalf_pair_conj_reindex, reindex_retainedAnalysisSiftedState]
      _ = _ := by
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hc, Equiv.symm_apply_apply, modelOutputPoint_modelOutputIndex, ← hc, hstate,
    Fintype.card_perm, Fintype.card_fin]
  congr 1
  ring

end Real


/-! ## N2: the retained ideal map is the post-processed model ideal map -/

section Ideal

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

attribute [local instance] retainedAnalysisOutputDimNeZero

/-- The final-stage ideal fixes the key-free abort leaf. -/
theorem finalStage_ideal_single_abort (ell : ℕ) (a b : Fin (2 ^ ell)) :
    (FinalStage.outputLayout ell).toBoundaryKeyLayout.ideal
        (Matrix.single (finalStagePoint ell 1 a b) (finalStagePoint ell 1 a b) (1 : ℂ)) =
      Matrix.single (finalStagePoint ell 1 a b) (finalStagePoint ell 1 a b) (1 : ℂ) :=
  BoundaryKeyLayout.ideal_single_of_abort _ rfl rfl 1

/-- **The final-stage ideal on the accepting leaf**: the two keys are replaced by one uniform shared
key. -/
theorem finalStage_ideal_single_accept (ell : ℕ) (a b : Fin (2 ^ ell)) :
    (FinalStage.outputLayout ell).toBoundaryKeyLayout.ideal
        (Matrix.single (finalStagePoint ell 0 a b) (finalStagePoint ell 0 a b) (1 : ℂ)) =
      ((2 : ℂ) ^ ell)⁻¹ • ∑ k : Fin (2 ^ ell),
        Matrix.single (finalStagePoint ell 0 k k) (finalStagePoint ell 0 k k) (1 : ℂ) := by
  let L := (FinalStage.outputLayout ell).toBoundaryKeyLayout
  let e0 : (FinalStage.boundary ell).Exit := ⟨0, ()⟩
  haveI : Subsingleton (L.Residual e0) := by
    refine ⟨fun x y => Prod.ext (Prod.ext rfl rfl) (funext fun i => ?_)⟩
    rcases i with ⟨⟨p, hp⟩, hpb⟩
    cases p with
    | alice => exact (hp rfl).elim
    | bob => exact (hpb (Subtype.ext rfl)).elim
  let u := (L.coordinates e0 (finalStagePoint ell 0 a b).2).2.2
  have hpt : ∀ a' b' : Fin (2 ^ ell),
      finalStagePoint ell 0 a' b' = ⟨e0, (L.coordinates e0).symm (a', b', u)⟩ := by
    intro a' b'
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine ((L.coordinates e0).eq_symm_apply).mpr ?_
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))
  have hcard : Fintype.card ((L.disposition e0).Key) = 2 ^ ell := Fintype.card_fin _
  rw [hpt a b, L.ideal_single_coordinates e0 a b u, hcard]
  simp_rw [hpt]
  push_cast
  rfl

/-- The inclusion of one final-stage continuation into the retained output, at the announced
permutation `pi` and the pre-decision public exit `e`, as a morphism of key layouts. -/
noncomputable def retainedFinalStageHom (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    BoundaryKeyLayout.Hom (FinalStage.outputLayout ell).toBoundaryKeyLayout
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout :=
  (retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi).comp
    (QKD.OutputLayout.graftInclHom _ (fun _ => FinalStage.boundary ell)
      (fun _ => FinalStage.outputLayout ell) .alice .bob (by decide) (fun _ => rfl)
      (fun _ => rfl) e)

/-- `retainedFinalStageHom` places a final-stage point at the announced permutation and the
pre-decision exit. -/
theorem retainedFinalStageHom_apply (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit)
    (r : (FinalStage.boundary ell).space) :
    retainedFinalStageHom nK mZ mX ell ellEV leakEC pi e r =
      (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
        (pi, (Boundary.graftSpaceEquiv _ (fun _ => FinalStage.boundary ell)).symm ⟨e, r⟩) :=
  rfl

/-- `retainedFinalStageHom` is injective: the retained output decomposition is a bijection and the
graft decomposition of the raw-tail output is a bijection. -/
theorem retainedFinalStageHom_injective (nK mZ mX ell ellEV leakEC : ℕ)
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (e : (QKD.BB84.classicalPreDecisionBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).Exit) :
    Function.Injective (retainedFinalStageHom nK mZ mX ell ellEV leakEC pi e) := by
  intro r r' h
  rw [retainedFinalStageHom_apply, retainedFinalStageHom_apply] at h
  have h1 := congrArg Prod.snd
    ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm.injective h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp
    ((Boundary.graftSpaceEquiv _ (fun _ => FinalStage.boundary ell)).symm.injective h1)).2

/-- The retained resource on a diagonal matrix unit is the retained ideal in the numbered output
coordinates. -/
theorem retainedAnalysisResource_single (nK mZ mX ell ellEV leakEC : ℕ)
    (u : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC
        (Matrix.single (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC u)
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC u) (1 : ℂ)) =
      Matrix.reindex (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
        ((retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
          (Matrix.single u u (1 : ℂ))) := by
  rw [retainedAnalysisResource, ← Quantum.TensorProducts.reindex_single, coordinateLinear_reindex]

end Ideal


section KeyReplacement

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry

attribute [local instance] retainedAnalysisOutputDimNeZero

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- The model output coordinate of the registers `(kp, f, t, p)` is, in the flagged two-key
register of `QKD.keyReplace`, the coordinate of the keys `kp`, the flag `f` and the inner
transcript `(t, p)`: the announced permutation is the last digit of the inner transcript. -/
theorem modelOutputIndex_regroup (kp : Fin (2 ^ ell * 2 ^ ell)) (f : Fin 2)
    (t : Fin (ModelInnerDim nK mZ mX ell ellEV leakEC))
    (p : Fin (nK + mZ + mX).factorial) :
    Fin.cast (Nat.mul_one (QKD.keyedFlagOutDim ell
        (bb84SymPEAnnounceTranscriptInnerDim (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)))
      (Fin.cast (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)
        (finProdFinEquiv (finProdFinEquiv (kp, finProdFinEquiv (f, t)), p))) =
      finProdFinEquiv (kp, finProdFinEquiv (f, finProdFinEquiv (t, p))) := by
  apply Fin.ext
  simp only [Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-- The inverse reading of `modelOutputIndex_regroup`. -/
theorem modelOutputIndex_regroup_symm (kp : Fin (2 ^ ell * 2 ^ ell)) (f : Fin 2)
    (t : Fin (ModelInnerDim nK mZ mX ell ellEV leakEC))
    (p : Fin (nK + mZ + mX).factorial) :
    Fin.cast (Nat.mul_one (QKD.keyedFlagOutDim ell
        (bb84SymPEAnnounceTranscriptInnerDim (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC))).symm
      (finProdFinEquiv (kp, finProdFinEquiv (f, finProdFinEquiv (t, p)))) =
      Fin.cast (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)
        (finProdFinEquiv (finProdFinEquiv (kp, finProdFinEquiv (f, t)), p)) := by
  rw [← modelOutputIndex_regroup]
  rfl

/-- The retained output point named by the model output coordinate of the registers
`(kp, f, t, p)` is the final-stage point of the flag `f` and the keys `kp`, included at the
announced permutation of `p` and the pre-decision exit of `t`. -/
theorem modelOutputPoint_cast (kp : Fin (2 ^ ell * 2 ^ ell)) (f : Fin 2)
    (t : Fin (ModelInnerDim nK mZ mX ell ellEV leakEC))
    (p : Fin (nK + mZ + mX).factorial) :
    modelOutputPoint nK mZ mX ell ellEV leakEC
        (Fin.cast (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
            (@Sampling.packedPESel nK mZ mX) leakEC)
          (finProdFinEquiv (finProdFinEquiv (kp, finProdFinEquiv (f, t)), p))) =
      retainedFinalStageHom nK mZ mX ell ellEV leakEC
        ((permAnnounceIndexEquiv (nK + mZ + mX)).symm p)
        ((QKD.BB84.classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).symm
          (modelTailData nK mZ mX ell ellEV leakEC t))
        (finalStagePoint ell f (finProdFinEquiv.symm kp).1 (finProdFinEquiv.symm kp).2) := by
  unfold modelOutputPoint
  rw [modelOutputDecode_cast]
  rfl

/-- **The retained resource after the post-processing is the post-processing after key
replacement**, on every diagonal matrix unit of the model output.  An accepting model coordinate
names an accepting retained leaf holding its two keys, and both resources replace them by one
uniform shared key; an aborting model coordinate names the key-free abort leaf, which both
resources fix. -/
theorem retainedAnalysisResource_modelPostprocess_single
    (j : Fin (ModelOutputDim nK mZ mX ell ellEV leakEC)) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC
        (modelPostprocess nK mZ mX ell ellEV leakEC (Matrix.single j j (1 : ℂ))) =
      modelPostprocess nK mZ mX ell ellEV leakEC
        (Op.castDim (Nat.mul_one (QKD.keyedFlagOutDim ell
            (bb84SymPEAnnounceTranscriptInnerDim (nK + mZ + mX) (mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX) leakEC))).symm
          (QKD.keyReplace ell
            (bb84SymPEAnnounceTranscriptInnerDim (nK + mZ + mX) (mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX) leakEC)
            (Op.castDim (Nat.mul_one (QKD.keyedFlagOutDim ell
                (bb84SymPEAnnounceTranscriptInnerDim (nK + mZ + mX) (mZ + mX) ell ellEV
                  (@Sampling.packedPESel nK mZ mX) leakEC)))
              (Matrix.single j j (1 : ℂ))))) := by
  obtain ⟨⟨o, p⟩, rfl⟩ := (finProdFinEquiv.trans (finCongr
    (QKD.BB84.Model.symOutDimPad (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC))).surjective j
  obtain ⟨⟨kp, w⟩, rfl⟩ := finProdFinEquiv.surjective o
  obtain ⟨⟨f, t⟩, rfl⟩ := finProdFinEquiv.surjective w
  obtain ⟨⟨kA, kB⟩, rfl⟩ := finProdFinEquiv.surjective kp
  simp only [Equiv.trans_apply, finCongr_apply]
  rw [modelPostprocess_single, modelOutputPoint_cast, Equiv.symm_apply_apply,
    retainedAnalysisResource_single, Op.castDim_single, modelOutputIndex_regroup]
  dsimp only
  have hinj := retainedFinalStageHom_injective nK mZ mX ell ellEV leakEC
    ((permAnnounceIndexEquiv (nK + mZ + mX)).symm p)
    ((QKD.BB84.classicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).symm (modelTailData nK mZ mX ell ellEV leakEC t))
  fin_cases f
  · simp only [Fin.zero_eta]
    rw [QKD.keyReplace_single_accept, Op.castDim_smul, Op.castDim_sum_univ, map_smul, map_sum,
      BoundaryKeyLayout.Hom.ideal_single_of_injective _ hinj _ _ _
        (finalStage_ideal_single_accept ell kA kB),
      Matrix.reindex_smul, Matrix.reindex_sum]
    simp only [Op.castDim_single, modelOutputIndex_regroup_symm, modelPostprocess_single,
      modelOutputPoint_cast, Equiv.symm_apply_apply, Quantum.TensorProducts.reindex_single]
  · simp only [Fin.mk_one]
    have habort := BoundaryKeyLayout.Hom.ideal_single_of_injective _ hinj
      (finalStagePoint ell 1 kA kB) 1 (fun _ : Unit => finalStagePoint ell 1 kA kB)
      (by rw [finalStage_ideal_single_abort, Fintype.sum_unique, one_smul])
    rw [Fintype.sum_unique, one_smul] at habort
    rw [QKD.keyReplace_single_abort, habort, Op.castDim_single,
      modelOutputIndex_regroup_symm, modelPostprocess_single, modelOutputPoint_cast,
      Equiv.symm_apply_apply, Quantum.TensorProducts.reindex_single]

/-- **The retained ideal map is the classical post-processing of the model's ideal map.**

The retained ideal is the retained key resource after the retained real map, and the model's ideal
is the key-replacement channel after the model's real map
(`QKD.BB84.Model.bb84SymIdealChannel_eq_keyReplace_real`).  With the real maps identified by
`retainedAnalysisReal_eq_modelPostprocess_comp`, it remains that the retained resource after the
post-processing is the post-processing after key replacement on the model's output, which is
diagonal (`retainedAnalysisResource_modelPostprocess_single`). -/
theorem retainedAnalysisIdeal_eq_modelPostprocess_comp [NeZero (nK + mZ + mX)]
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (bb84SymIdealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  refine LinearMap.ext fun rho => ?_
  rw [retainedAnalysisIdeal, LinearMap.comp_apply, retainedAnalysisReal_eq_modelPostprocess_comp,
    LinearMap.comp_apply, LinearMap.comp_apply,
    QKD.BB84.Model.bb84SymIdealChannel_eq_keyReplace_real, QKD.BB84.Model.mapTensorId_one,
    bb84SymRealChannel_eq_sum]
  simp only [map_sum, map_smul, Op.castDim_sum_univ, Op.castDim_smul,
    retainedAnalysisResource_modelPostprocess_single]

end KeyReplacement

/-! ## N3: the retained distance is at most the model distance -/

section Distance

open Quantum.Operators

attribute [local instance] retainedAnalysisOutputDimNeZero

variable (nK mZ mX ell ellEV leakEC : ℕ)

/-- **The retained real-minus-ideal map is the post-processed model real-minus-ideal map.** -/
theorem retainedAnalysisDifference_eq_modelPostprocess_comp [NeZero (nK + mZ + mX)]
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q =
      (modelPostprocess nK mZ mX ell ellEV leakEC).comp
        (bb84SymRealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec -
          bb84SymIdealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  rw [retainedAnalysisDifference, retainedAnalysisReal_eq_modelPostprocess_comp,
    retainedAnalysisIdeal_eq_modelPostprocess_comp, LinearMap.comp_sub]

/-- **The retained experiment's real/ideal distance is at most the analytical model's.**

The diamond norm of the retained real-minus-ideal map is at most that of
`bb84SymRealChannel - bb84SymIdealChannel` at sifted block `nK + mZ + mX`, test-set
size `mZ + mX` and the packed selectors: the retained difference is the model difference followed
by the channel `modelPostprocess`, and post-composing a channel does not increase the diamond norm
(`Quantum.Channels.diamondNorm_postcomp_cptp_le`).  No budget, key-rate condition, state
assumption or condition on the error-correction scheme occurs. -/
theorem retainedAnalysisDifference_diamondNorm_le_model [NeZero (nK + mZ + mX)]
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) ≤
      Quantum.Channels.diamondNorm
        (bb84SymRealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec -
          bb84SymIdealChannel (nK + mZ + mX) (mZ + mX) ell ellEV Q delta
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec) := by
  rw [retainedAnalysisDifference_eq_modelPostprocess_comp]
  exact Quantum.Channels.diamondNorm_postcomp_cptp_le _
    (modelPostprocess_isCPTP nK mZ mX ell ellEV leakEC) _

end Distance

end QKD.BB84.Reduction
