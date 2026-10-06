import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.Model.BB84ClassicalProgram
import QCryptLean.QKD.KeyedOutputRegister.KeyReplacement
import QCryptLean.LOCC.Local

-- Several of the module paths in the import closure exceed 100 characters; this is the same
-- suppression `QKD/LOCC/BB84FullBridge.lean` already carries for the same imports.

/-!
# The BB84 computation at a general test-set size `m`

Nine security cells, including the flagship, are stated at a *free* parameter-estimation test-set
size `m` rather than the canonical `m = ⌈n/2⌉ = (n+1)/2`. This module evaluates the general-`m`
stack in explicit coordinates and supplies the register arithmetic the typed BB84
development reads.

## What is proved here

The general-`m` coordinate dictionary and the general-`m` computation:

* the general-`m` count hypothesis and the first-`m`-rounds selector that satisfies it;
* the general-`m` transcript and output dimensions, and the announced output index
  `QKD.BB84.Model.bb84OutIndex`;
* the classical layer on a basis projector, `QKD.BB84.Model.classicalPostBare_single`;
* the identification of the announced parameter-estimation test with the accept gate,
  `QKD.BB84.Model.acceptFlagOf_eq` — the one place `bb84KeyCount n m peSel` is needed;
* the symmetrized channel formula `QKD.BB84.Model.bb84SymRealChannel_apply_eq_sum`;
* the general-`m` flagged two-key output register's transcript-dimension arithmetic.

## The side condition, and what it is NOT

`hcount : bb84KeyCount n m peSel`, i.e. `Fintype.card {i // peSel i = false} = n − m`, is an
**ordinary hypothesis the caller supplies**. It is not hidden and not discharged here.

* it is genuinely needed, because the experiment announces the `n − (n−m)` *sorted* PE rounds
  `bb84PERoundIdx peSel j`, while the accept gate `bb84SiftedLocalPETestPassed`
  filters over **every** round with `peSel i = true`. The two agree iff the sorted PE block
  enumerates exactly the PE rounds, which is what the count hypothesis says.

No relation between `m` and `n` is assumed anywhere in this module.

## What is reused rather than mirrored

The `m`-free half of the canonical development is imported and used directly, not copied: the
register dictionary `jointOutcome`/`aliceKeyOf`/`bobKeyOf`, the fused announcement `evTagSynOf`,
the key slots, the joint measurement `bb84MeasureBare`, and the accept gate
`bb84SiftedLocalPEAndEVPassed` itself (which reads no split point). Only the objects whose *type*
mentions the PE-block size are mirrored.

References: Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024,
arXiv:2403.11851, `main.tex:909` and `:913` (the protocol at a general test-set size `m`,
`\nkey = n - m`). -/
open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Quantum.Channels Matrix
open Math.RepresentationTheory InfoTheory.Postselection QKD.BB84.Engine
open LOCC
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model

/-! ## 1. The general-`m` count hypothesis -/

/-! ## 2. The general-`m` transcript, output dimension and output index -/

/-- **The output index at a general `m`.** Mirror of `bb84OutIndex`. -/
def bb84OutIndex (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim) :
    Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
    bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
      ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
      ((aliceKeyHashFamily n ℓ peSel).hash st.1
        (ec.decode (bobKeyString peSel ω)
          (ec.syndrome (aliceKeyString peSel ω))))
      st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
      (ec.syndrome (aliceKeyString peSel ω))
      (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2)
  else
    bb84.peFailOutIndex n m ℓ ℓEV peSel leakEC st
      (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
      (ec.syndrome (aliceKeyString peSel ω))
      (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2)

/-! ## 3. The classical layer at a general `m`, on a basis projector -/

/-- The general-`m` V2 pass Kraus at the unit Eve slot, in matrix-unit form. Mirror of
`retainedPass_kraus_eq_sum`. -/
theorem retainedPass_kraus_eq_sum (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim) :
    bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
        (st, ω) =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv
              (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
                ((aliceKeyHashFamily n ℓ peSel).hash st.1
                  (aliceKeyString peSel ω))
                ((aliceKeyHashFamily n ℓ peSel).hash st.1
                  (ec.decode (bobKeyString peSel ω)
                    (ec.syndrome (aliceKeyString peSel ω))))
                st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                (ec.syndrome (aliceKeyString peSel ω))
                (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2), r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
      else 0 := by
  classical
  ext a b
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · rw [if_pos h]
    simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, h, Matrix.kroneckerMap,
      Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
      Quantum.TensorProducts.sum_single_finProdFinEquiv_apply]
  · rw [if_neg h]
    simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, h]

/-- The general-`m` V2 fail Kraus at the unit Eve slot, in matrix-unit form. Mirror of
`retainedFail_kraus_eq_sum`. -/
theorem retainedFail_kraus_eq_sum (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim) :
    bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
        (st, ω) =
      if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv
              (bb84.peFailOutIndex n m ℓ ℓEV peSel leakEC st
                (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                (ec.syndrome (aliceKeyString peSel ω))
                (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2), r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
      else 0 := by
  classical
  ext a b
  by_cases h : ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
  · rw [if_pos h]
    simp [bb84.retainedSiftedPEAnnounceFailBranchKraus, h, Matrix.kroneckerMap,
      Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
      Quantum.TensorProducts.sum_single_finProdFinEquiv_apply]
  · rw [if_neg h]
    simp [bb84.retainedSiftedPEAnnounceFailBranchKraus, h]

/-- The general-`m` classical layer with both unit Eve slots stripped. Mirror of
`bb84ClassicalPostBare`. -/
def bb84ClassicalPostBare (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Op (4 ^ n) →ₗ[ℂ] Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  (Op.castDimLinear (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC))).comp
    ((bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV 1 peSel xSel
        leakEC ec δ Q).comp
      (Op.castDimLinear (Nat.mul_one (4 ^ n)).symm))

/-- **The general-`m` classical layer, on a basis projector.** One output index per
announced seed pair, each with the uniform weight `1 / |KeyHashSeedPairEV|`, on the pass *and* the
abort branch. Mirror of `classicalPostBare_single`. -/
theorem classicalPostBare_single (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (c : Fin (4 ^ n)) :
    bb84ClassicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q (Matrix.single c c (1 : ℂ)) =
      ∑ st : KeyHashSeedPairEV n ℓ ℓEV peSel,
        ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ •
          Matrix.single
            (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st (finFunctionFinEquiv.symm c))
            (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st (finFunctionFinEquiv.symm c))
            (1 : ℂ) := by
  classical
  set ST := KeyHashSeedPairEV n ℓ ℓEV peSel with hST
  have hin : Op.castDim (Nat.mul_one (4 ^ n)).symm (Matrix.single c c (1 : ℂ)) =
      Matrix.single (finProdFinEquiv (c, (0 : Fin 1))) (finProdFinEquiv (c, (0 : Fin 1)))
        (1 : ℂ) := by
    rw [Op.castDim_single, castDim_mul_one_symm_eq]
  have hbranch : ∀ (st : ST) (ω : Fin n → Fin signalDim),
      bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            (st, ω) *
          Matrix.single (finProdFinEquiv (c, (0 : Fin 1)))
            (finProdFinEquiv (c, (0 : Fin 1))) (1 : ℂ) *
          (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            (st, ω))ᴴ +
        bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            (st, ω) *
          Matrix.single (finProdFinEquiv (c, (0 : Fin 1)))
            (finProdFinEquiv (c, (0 : Fin 1))) (1 : ℂ) *
          (bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            (st, ω))ᴴ =
      if ω = finFunctionFinEquiv.symm c then
        Matrix.single
          (finProdFinEquiv
            (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st ω, (0 : Fin 1)))
          (finProdFinEquiv
            (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st ω, (0 : Fin 1)))
          (1 : ℂ)
      else 0 := by
    intro st ω
    have hcω : (finProdFinEquiv (c, (0 : Fin 1)) =
        finProdFinEquiv (finFunctionFinEquiv ω, (0 : Fin 1))) ↔ ω = finFunctionFinEquiv.symm c := by
      constructor
      · intro hh
        have hcc : c = finFunctionFinEquiv ω :=
          (Prod.mk.injEq _ _ _ _ ▸ finProdFinEquiv.injective hh).1
        rw [hcc, Equiv.symm_apply_apply]
      · intro hh
        rw [hh, Equiv.apply_symm_apply]
    rw [retainedPass_kraus_eq_sum, retainedFail_kraus_eq_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, bb84OutIndex]
    by_cases hg : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
    · rw [if_pos hg, if_neg (by simpa using hg), if_pos hg]
      rw [singleKraus_conj_single]
      simp only [Matrix.zero_mul, add_zero]
      by_cases hω : ω = finFunctionFinEquiv.symm c
      · rw [if_pos (hcω.mpr hω), if_pos hω]
      · rw [if_neg (fun hh => hω (hcω.mp hh)), if_neg hω]
    · rw [if_neg hg, if_pos (by simpa using hg), if_neg hg]
      rw [singleKraus_conj_single]
      simp only [Matrix.zero_mul, zero_add]
      by_cases hω : ω = finFunctionFinEquiv.symm c
      · rw [if_pos (hcω.mpr hω), if_pos hω]
      · rw [if_neg (fun hh => hω (hcω.mp hh)), if_neg hω]
  have hL : (bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV 1 peSel
        xSel leakEC ec δ Q)
      (Matrix.single (finProdFinEquiv (c, (0 : Fin 1)))
        (finProdFinEquiv (c, (0 : Fin 1))) (1 : ℂ)) =
      (1 / (Fintype.card ST : ℂ)) • ∑ st : ST,
        Matrix.single
          (finProdFinEquiv (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st
            (finFunctionFinEquiv.symm c), (0 : Fin 1)))
          (finProdFinEquiv (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st
            (finFunctionFinEquiv.symm c), (0 : Fin 1))) (1 : ℂ) := by
    simp only [bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap,
      LinearMap.add_apply, LinearMap.smul_apply, krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← smul_add]
    refine congrArg _ ?_
    have hadd := (Finset.sum_add_distrib
      (s := (Finset.univ : Finset (ST × (Fin n → Fin signalDim))))
      (f := fun idx =>
        bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q idx *
          Matrix.single (finProdFinEquiv (c, (0 : Fin 1)))
            (finProdFinEquiv (c, (0 : Fin 1))) (1 : ℂ) *
          (bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            idx)ᴴ)
      (g := fun idx =>
        bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q idx *
          Matrix.single (finProdFinEquiv (c, (0 : Fin 1)))
            (finProdFinEquiv (c, (0 : Fin 1))) (1 : ℂ) *
          (bb84.retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV 1 peSel xSel leakEC ec δ Q
            idx)ᴴ)).symm
    rw [hadd, Fintype.sum_prod_type (α₁ := ST) (α₂ := Fin n → Fin signalDim)]
    refine Finset.sum_congr rfl fun st _ => ?_
    rw [Finset.sum_eq_single (finFunctionFinEquiv.symm c)]
    · rw [hbranch st (finFunctionFinEquiv.symm c), if_pos rfl]
    · intro ω _ hω
      rw [hbranch st ω, if_neg hω]
    · intro h
      exact absurd (Finset.mem_univ (finFunctionFinEquiv.symm c)) h
  simp only [bb84ClassicalPostBare, LinearMap.comp_apply, Op.castDimLinear, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [hin, hL, Op.castDim_smul, Op.castDim_sum_univ, one_div, Finset.smul_sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  refine congrArg _ ?_
  rw [Op.castDim_single]
  have hcast : Fin.cast (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC))
      (finProdFinEquiv (bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st
        (finFunctionFinEquiv.symm c), (0 : Fin 1))) =
      bb84OutIndex n m ℓ ℓEV peSel xSel leakEC ec δ Q st (finFunctionFinEquiv.symm c) :=
    Fin.ext (by simp)
  rw [hcast]

/-! ## 4. The parameter-estimation test at a general `m`, from the announced bits alone

This is the one place `bb84KeyCount n m peSel` is used, and the one place it is needed.
`bb84SiftedLocalPETestPassed` filters over **every** PE round; the announced block carries only the
`n − (n−m)` sorted rounds `bb84PERoundIdx peSel j`. Under the count hypothesis the sorted rounds
are exactly the PE rounds (`bb84PERoundIdx_isPE` one way, `bb84_peRound_eq_peIdx` the
other), so the two agree. Without it a PE round is invisible to every announced digit, and the flag
becomes a function of a bit neither party holds. -/

theorem bb84PERoundIdx_injective (n m : ℕ) (peSel : Fin n → Bool) :
    Function.Injective (bb84PERoundIdx (n := n) (m := m) peSel) := by
  intro j j' h
  have h' : bb84RoundEquiv (m := m) peSel (Sum.inr j) =
      bb84RoundEquiv (m := m) peSel (Sum.inr j') := by
    rw [bb84RoundEquiv_inr, bb84RoundEquiv_inr, h]
  exact Sum.inr_injective ((bb84RoundEquiv (m := m) peSel).injective h')

/-- **The PE error counts at a general `m`, re-indexed onto the announced rounds.** Mirror of
`peErrorCount_eq`. -/
theorem peErrorCount_eq (n m : ℕ) (peSel : Fin n → Bool)
    (hcount : bb84KeyCount n m peSel)
    (pr : Fin n → Prop) [DecidablePred pr] (x y : Fin (2 ^ n)) :
    (Finset.univ.filter fun i : Fin n => peSel i = true ∧ pr i ∧
        (jointOutcome n x y i = 1 ∨ jointOutcome n x y i = 2)).card =
      (Finset.univ.filter fun j : Fin (n - bb84KeyRoundCount n m) =>
        pr (bb84PERoundIdx peSel j) ∧
          registerBit n (bb84PERoundIdx peSel j) x ≠
            registerBit n (bb84PERoundIdx peSel j) y).card := by
  classical
  refine (Finset.card_bij (fun j _ => bb84PERoundIdx peSel j) ?_ ?_ ?_).symm
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, bb84PERoundIdx_isPE peSel hcount j, hj.2.1,
      (jointOutcome_disagree_iff n x y _).mpr hj.2.2⟩
  · intro j _ j' _ h
    exact bb84PERoundIdx_injective n m peSel h
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨j, rfl⟩ := bb84_peRound_eq_peIdx peSel hcount i hi.2.1
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2.2.1, (jointOutcome_disagree_iff n x y _).mp hi.2.2.2⟩

/-- **The accept test at a general `m` is a function of the announced PE bits** — under the count
hypothesis. Mirror of `peTestPassed_eq_of_announced`. -/
theorem peTestPassed_eq_of_announced (n m : ℕ) (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (hcount : bb84KeyCount n m peSel) (x y : Fin (2 ^ n)) :
    bb84SiftedLocalPETestPassed peSel xSel δ Q (jointOutcome n x y) =
      peOKOfAnnounced m peSel xSel δ Q
        (fun j => registerBit n (bb84PERoundIdx peSel j) x)
        (fun j => registerBit n (bb84PERoundIdx peSel j) y) := by
  classical
  have hZ := peErrorCount_eq n m peSel hcount (fun i => xSel i = false) x y
  have hX := peErrorCount_eq n m peSel hcount (fun i => xSel i = true) x y
  simp only [bb84SiftedLocalPETestPassed, bb84SiftedZTestErrorCount, bb84SiftedXTestErrorCount,
    peOKOfAnnounced]
  simp only [hZ, hX]

/-- **The announced accept flag at a general `m` is the gate.** `0` accepts. This is
where `bb84KeyCount` is used. -/
theorem acceptFlagOf_eq (n m _ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (hcount : bb84KeyCount n m peSel)
    (t : KeyHashSeed n ℓEV peSel) (x y : Fin (2 ^ n)) :
    acceptFlagOf n m ℓEV peSel xSel leakEC ec δ Q
        (fun j => registerBit n (bb84PERoundIdx peSel j) x)
        (fun j => registerBit n (bb84PERoundIdx peSel j) y) t
        (verificationTag n ℓEV peSel t (aliceKeyOf n peSel x))
        (ec.syndrome (aliceKeyOf n peSel x)) y =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t (jointOutcome n x y) then 0 else 1 :=
          by
  have hpe := peTestPassed_eq_of_announced n m peSel xSel δ Q hcount x y
  simp only [acceptFlagOf, bb84SiftedLocalPEAndEVPassed, evVerified,
    aliceKeyString_jointOutcome, bobKeyString_jointOutcome, ← hpe, Bool.and_eq_true,
    decide_eq_true_eq]

/-! ## 5. The general-`m` output index, as a value -/

/-! ## 6. The general-`m` channel, computed -/

/-- The `Nat` reconciliation the general-`m` classical post-processing's codomain needs. Mirror of
`symOutDimPad`. -/
theorem symOutDimPad (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial =
      bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC 1 :=
  (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC).trans (Nat.mul_one _).symm

/-- **The general-`m` announcement map at the unit Eve slot, computed.** Mirror of
`announceEveVisible_one_apply`. -/
theorem announceEveVisible_one_apply (n m ℓ ℓEV : ℕ) [NeZero n] (peSel : Fin n → Bool)
    (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (B : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC 1)) :
    bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π B =
      Op.castDim (symOutDimPad n m ℓ ℓEV peSel leakEC)
        (Op.tensor
          (Op.castDim (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) B)
          (permAnnounceProjector n π)) := by
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
    bb84PEAnnounceBaseOutputDim_neZero n m ℓ ℓEV peSel leakEC
  have hB : Op.tensor
      (Op.castDim (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) B)
      (1 : Op 1) = B := by
    rw [← op_castDim_mul_one_eq_tensor_one, Op.castDim_trans]
    rfl
  have hmap : bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π B =
      mapTensorId (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π) B := rfl
  rw [hmap]
  conv_lhs => rw [← hB]
  rw [mapTensorId_tensor]
  change Op.tensor
      (Op.castDim (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC)
        (Op.tensor
          (Op.castDim (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) B)
          (permAnnounceProjector n π)))
      (1 : Op 1) = _
  rw [← op_castDim_mul_one_eq_tensor_one, Op.castDim_trans]

/-- The general-`m` real protocol map — measure, then privacy-amplify-or-abort — with both
unit Eve slots stripped. Mirror of `bb84RealProtocolMapBare`. -/
def bb84RealProtocolMapBare (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Op (4 ^ n) →ₗ[ℂ] Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  (bb84ClassicalPostBare n m ℓ ℓEV peSel xSel leakEC ec δ Q).comp (bb84MeasureBare n)

/-- The de-padded general-`m` real protocol map IS the general-`m` scheme's own `realProtocolMap` at
the unit Eve slot. Mirror of `realProtocolMapBare_apply`. -/
theorem realProtocolMapBare_apply (n m ℓ ℓEV : ℕ) [NeZero n] (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (A : Op (4 ^ n)) :
    bb84RealProtocolMapBare n m ℓ ℓEV peSel xSel leakEC ec δ Q A =
      Op.castDim (Nat.mul_one (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC))
        ((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).realProtocolMap (eveDim := 1) (Op.castDim (Nat.mul_one (4 ^ n)).symm A)) := by
  simp only [bb84RealProtocolMapBare, bb84ClassicalPostBare, LinearMap.comp_apply,
    Op.castDimLinear, LinearMap.coe_mk, AddHom.coe_mk, bb84SiftedPEAnnounceEveVisibleProtocol,
    measurementChannel_one_castDim]

/-- **The general-`m` headline channel, computed.** Writes `bb84SymRealChannel` as the `(1/n!)`
mixture over `π` of "conjugate by the sift-after-permutation, run the measure-and-postprocess
map, append `|π⟩⟨π|` to the transcript". -/
theorem bb84SymRealChannel_apply_eq_sum (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC)
    (ρ : Op (4 ^ n)) :
    bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec ρ =
      (1 / (n.factorial : ℂ)) • ∑ π : Equiv.Perm (Fin n),
        Op.castDim (symOutDimPad n m ℓ ℓEV peSel leakEC)
          (Op.tensor
            (bb84RealProtocolMapBare n m ℓ ℓEV peSel xSel leakEC ec δ Q
              (bb84SiftedRotation n peSel xSel * permuteSignalLinear n π ρ *
                (bb84SiftedRotation n peSel xSel)ᴴ))
            (permAnnounceProjector n π)) := by
  have hchan : bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      (1 / (n.factorial : ℂ)) • ∑ π : Equiv.Perm (Fin n),
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
          (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
                δ).realProtocolMap (eveDim := 1)).comp
            (((bb84SiftedConjChannel n 1 peSel xSel).comp (bb84UnitRegisterEmbed n)).comp
              (permuteSignalLinear n π))) := rfl
  rw [hchan, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
  refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
  change (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π)
      ((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
          δ).realProtocolMap (eveDim := 1)
        (bb84SiftedConjChannel n 1 peSel xSel
          (bb84UnitRegisterEmbed n (permuteSignalLinear n π ρ)))) = _
  rw [siftEmbedPerm_castDim, announceEveVisible_one_apply, ← realProtocolMapBare_apply]

/-! ## The general-`m` flagged two-key output register -/

instance bb84SymPEAnnounceTranscriptInnerDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) : NeZero (bb84SymPEAnnounceTranscriptInnerDim n m ℓ ℓEV peSel leakEC) :=
  ⟨Nat.mul_ne_zero
    (NeZero.ne (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))
    (Nat.factorial_ne_zero n)⟩

end QKD.BB84.Model

end
