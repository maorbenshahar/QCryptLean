import QCryptLean.QKD.BB84.Engine.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorization

/-!
# The genuine-LOCC `Eⁿ⊗V` coarsen-key split and PE-announce object

The genuine-LOCC counterparts of the L2/L3 layer of `EnVDecompositionReferee.lean`: the per-round
factorization of the trivial-attack per-σ family block, its key-first sorted form, the coarsen-key
operation and its product split, and the conditioning-side PE-announce key CQ constructor.

Every declaration here reads the fail-closed LOCC two-basis accept event
`bb84SiftedLocalPETestPassed` applied after the local `H ⊗ H` sift `bb84SiftedRotation` — where
the referee declarations read the Bell-joint test after the non-LOCC Bell rotation.  The referee
declarations are untouched; these are new declarations beside them.

## The general test-set size `m`

The L3 layer is stated at a **general** test-set size `m`, as Nahar, Tupkary, Zhao, Lütkenhaus and
Tan state the protocol (arXiv:2403.11851, `main.tex:909`, `:913`, `\nkey = n - m`): the
`…Param` declarations below carry the split point as a parameter, over the split-point-parametrised
round partition `bb84KeyRoundCount` / `bb84KeyRoundIdx` / `bb84PERoundIdx` / `bb84PartEquiv` /
`bb84KeyCount`.  The closed `m = ⌈n/2⌉` declarations are their instances: `bb84KeyRoundCount n
⌈n/2⌉` is `bb84KeyRoundCountCanonical n` definitionally, so the closed proofs are one-line
applications and no `castDim` transport appears.  `bb84CoarsenKey` keeps its body written out rather
than delegated, so that the consumers which `unfold` it still see `CQState.coarsen`.

## What the sift changes, and what it does not

`bb84SiftedSingleRoundRefBlock_eq_of_not_xTest` says the per-round block on a non-X-test round
**is** the referee key-round block `bb84RefereeSiftedSingleRoundRefBlock ψ false`.  Every key round
(`peSel = false`) is such a round, so the key-side factor of the split is literally the referee key
CQ object `bb84SiftedKeyRoundCQ` and the whole Devetak–Winter / AEP rate layer above it is reused
unchanged.  Only the PE-side factor is new: `bb84SiftedPERoundProd` reads each sorted PE round in
its own frame — the `H ⊗ H`-rotated frame when that round is X-designated, the computational `Z`
frame when it is Z-designated.

The endpoint reference needed for the conditioning-side PE-announce constructor mentions neither
the sift nor the accept predicate nor `ψ` — it is the register re-partition of the CKR calibration
reference — so the referee construction is reused verbatim.

## The accept predicate factors through the PE rounds

The filter carried by `bb84PairedHaarPerSigmaFamily` is
`bb84PostMeasurementCQSiftedLocalPEPassFilter` at the PE-only predicate
`bb84SiftedLocalPETestPassed`, which `bb84SiftedLocalPETestPassed_key_indep` proves is a function of
the PE-round outcomes alone.  The coarsen-key split below consumes exactly that, through
`bb84SiftedLocalPETestPassed_eq_pePass`: the accept `if` commutes out of the key-string fiber sum,
leaving the key factor unfiltered and the PE factor carrying the whole verdict.  A predicate that
coupled the key and PE outcomes would break the split. A key⊗PE product predicate admits a
factorization with the corresponding filter applied to each factor.

The protocol-level gate `bb84SiftedLocalPEAndEVPassed` conjoins error verification, whose two
arguments `aliceKeyString`/`bobKeyString` read the key rounds only; it is therefore a key⊗PE
product predicate. It is not the predicate of the objects in this file, and nothing here covers it.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413); Renner 2005
(arXiv:quant-ph/0512258v2) §5, §6.5. -/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PerSigmaFamily.lean`/`AcceptSplit.lean`, this uses the Frobenius norm on matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## L2 — the trivial-attack per-round factorization of the per-σ family block -/

/-- **L2 — the trivial-attack per-round factorization of the per-σ family block.**

On the PE-pass branch the block of the pure-paired-Haar per-σ family factorizes (after the
eveDim-`1` collapse) into the per-round single-round sifted reference blocks; on the fail branch
it is zero.  The tensor factor at position `a` is the round-`Fin.rev a` block: the source
`tensorPowGen` and the sifting rotation index round-major (`finFunctionFinEquiv`), whereas
`SubDensityOp.tensorFinProd` uses the reversed (`Fin.rev`) convention.

Rests on the per-round factorization `bb84_siftedUnitRegisterEmbed_tauConditioned_eq_tensorFinProd`.
-/
theorem bb84_sifted_unitRegisterEmbed_stateMap_eq_tensorFinProd
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim))
    (ω : Fin n → Fin signalDim) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel
        xSel Q δ ψ).stateMap ω =
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω
       then SubDensityOp.castDim (by rw [Nat.one_mul])
              (SubDensityOp.tensorFinProd n
                (fun a => bb84SiftedSingleRoundRefBlock ψ (peSel (Fin.rev a)) (xSel (Fin.rev a))
                  (ω (Fin.rev a))))
       else 0) := by
  have : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  by_cases hpe : bb84SiftedLocalPETestPassed peSel xSel δ Q ω
  · rw [ite_eq_left hpe]
    have hfam : (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ).stateMap ω =
        bb84SiftedTauEveRefConditioned 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)) ω := by
      change (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
          (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
            (densityOp_reindex (interleavingEquiv signalDim n).symm
              (ψ.tensorPowGen n))).toCQState.stateMap ω
        else (0 : SubDensityOp _)) = _
      rw [ite_eq_left hpe]
      rfl
    rw [hfam, bb84_siftedUnitRegisterEmbed_tauConditioned_eq_tensorFinProd]
  · rw [ite_eq_right hpe]
    change (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then _ else (0 : SubDensityOp _)) = 0
    rw [ite_eq_right hpe]

/-! ## The key-round fibre sum at an arbitrary key-round count

Neither the proof nor the statement below mentions the round partition: it is about a tensor power
of the single-round key CQ state and holds at an arbitrary count `N`, so it covers the fixed count
`N = bb84KeyRoundCountCanonical n` as a special case without further argument. -/

/-- **The `N`-fold key-round bit-CQ tensor power as a key-string fibre sum, at an arbitrary count.**

The `z`-block of `(bb84SiftedKeyRoundCQ ψ)^{⊗N}` is the sum, over the outcome strings `k` whose
Alice-`Z` bit string is `z`, of the `N`-fold tensor product of the per-round `Z`-key reference
blocks.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) App. B, the key-register
fibre decomposition of `\Zkey^{\nkey}` (`main.tex:913`). -/
theorem bb84SiftedKeyRoundCQ_tensorPower_stateMap_eq_fiberSumCount {N : ℕ}
    (ψ : DensityOp (signalDim * signalDim)) (z : Fin N → Fin 2) :
    (((bb84SiftedKeyRoundCQ ψ).tensorPower N).stateMap z).toOp =
      ∑ k : Fin N → Fin signalDim,
        (if (fun i => bb84AliceBitMap (k i)) = z then
          (SubDensityOp.tensorFinProd N
            (fun i => bb84RefereeSiftedSingleRoundRefBlock ψ false (k i))).toOp
        else 0) := by
  have : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have : NeZero (signalDim ^ N) := NeZero.pow
  rw [InfoTheory.SmoothMinEntropy.CQState.tensorPower_stateMap_toOp]
  ext A B
  rw [Matrix.sum_apply]
  set a := (finFunctionFinEquiv.symm A) ∘ Fin.rev with ha
  set b := (finFunctionFinEquiv.symm B) ∘ Fin.rev with hb
  have hrev : (Fin.rev : Fin N → Fin N) ∘ Fin.rev = id := by funext i; simp
  have hAeq : A = finFunctionFinEquiv (a ∘ Fin.rev) := by rw [ha, Function.comp_assoc, hrev]; simp
  have hBeq : B = finFunctionFinEquiv (b ∘ Fin.rev) := by rw [hb, Function.comp_assoc, hrev]; simp
  rw [hAeq, hBeq, SubDensityOp.tensorFinProd_toOp_entry_prod_rev]
  have hkey : ∀ i : Fin N,
      ((bb84SiftedKeyRoundCQ ψ).stateMap (z i)).toOp (a i) (b i)
      = ∑ k' : Fin signalDim,
          if bb84AliceBitMap k' = z i then
            (bb84RefereeSiftedSingleRoundRefBlock ψ false k').toOp (a i) (b i)
          else 0 := by
    intro i
    rw [bb84SiftedKeyRoundCQ, CQState.coarsen_stateMap_toOp, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k' _
    by_cases hk : bb84AliceBitMap k' = z i
    · rw [ite_eq_left hk, ite_eq_left hk]; rfl
    · rw [ite_eq_right hk, ite_eq_right hk, Matrix.zero_apply]
  simp_rw [hkey]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (fun i => bb84AliceBitMap (k i)) = z
  · rw [ite_eq_left hk, SubDensityOp.tensorFinProd_toOp_entry_prod_rev]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun hk i)]
  · rw [ite_eq_right hk, Matrix.zero_apply]
    obtain ⟨i, hi⟩ : ∃ i, bb84AliceBitMap (k i) ≠ z i := by
      by_contra hcon; push Not at hcon; exact hk (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right hi])

/-! ## L3 — the coarsen-key split of the trivial-attack per-σ family block

`bb84SortRoundPerm` (`EnVDecomposition.lean:266`), the quantum register sort that gathers the key
rounds into the leading block, is sift-independent and reused verbatim; it does not mention the
split point at all, so the same permutation serves every test-set size `m`.

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol at a **general** test-set size `m`
(arXiv:2403.11851, `main.tex:909` and `:913`, `\nkey = n - m`, both inside
`\subsection{Classical part}` at `:906`).  The `…Param` declarations below are that general-`m`
layer, over the split-point-parametrised round partition `bb84KeyRoundCount`,
`bb84KeyRoundIdx`, `bb84PERoundIdx`, `bb84PartEquiv`, `bb84KeyCount`; the closed
declarations beside them are their `m = ⌈n/2⌉` instances, definitionally so — no `castDim`
transport, and their proofs are one-line applications.

The general-`m` forms carry **no** constraint relating `m` to `n`: nothing here needs a nonempty key
block or a nonempty test block, so `m = 0` and `m = n` are covered and degenerate rather than
excluded. -/

/-- **Sorted per-block factorization of the trivial-attack per-σ factor, at a general test-set
size `m`.**  Casting away the one-dimensional Eve register and sorting the de-Finetti reference
register by `bb84SortRoundPerm` turns the L2 round-interleaved tensor product into the contiguous
key-block ⊗ PE-block product: the first `n_K = n − m` factors are the **referee** key-round
reference blocks (read in the `Z` basis; the sift is the identity on a key round,
`bb84SiftedSingleRoundRefBlock_eq_of_not_xTest`), the last `m` are the PE-round blocks, each read in
the frame of its own round through `xSel (bb84PERoundIdx peSel j)`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
lemma bb84_sifted_unitRegisterEmbed_reindexBlock {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hcount : bb84KeyCount n m peSel)
    (ψ : DensityOp (signalDim * signalDim))
    (ω : Fin n → Fin signalDim) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    SubDensityOp.reindex (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)
        (SubDensityOp.castDim (by rw [Nat.one_mul])
          ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ).stateMap ω)) =
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
        SubDensityOp.castDim (by rw [← pow_add, bb84KeyRoundCount_add'])
          ((SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
              (fun i =>
                bb84RefereeSiftedSingleRoundRefBlock ψ false (ω (bb84KeyRoundIdx peSel i)))).tensor
            (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
              (fun j => bb84SiftedSingleRoundRefBlock ψ true (xSel (bb84PERoundIdx peSel j))
                (ω (bb84PERoundIdx peSel j)))))
      else 0) := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  rw [bb84_sifted_unitRegisterEmbed_stateMap_eq_tensorFinProd]
  by_cases hpe : bb84SiftedLocalPETestPassed peSel xSel δ Q ω
  · rw [ite_eq_left hpe, ite_eq_left hpe]
    -- Cancel the two register casts (`4ⁿ → eveDim·4ⁿ → 4ⁿ` is the identity).
    rw [SubDensityOp.castDim_cancel,
      SubDensityOp.tensorFinProd_sortSplit (hn := bb84KeyRoundCount_add' n m)]
    -- Identify the sorted key/PE factor families with the per-round reference blocks.
    have hσ : ∀ (r : Fin n),
        bb84SortRoundPerm peSel r = (bb84PeSelSort peSel r).rev := by
      intro r; rw [bb84SortRoundPerm, Equiv.trans_apply, Fin.revPerm_apply]
    have hkey : (fun i => (fun a => bb84SiftedSingleRoundRefBlock ψ (peSel (Fin.rev a))
            (xSel (Fin.rev a)) (ω (Fin.rev a)))
          (bb84SortRoundPerm peSel
            (Fin.cast (bb84KeyRoundCount_add' n m)
              (Fin.castAdd (n - bb84KeyRoundCount n m) i)))) =
        (fun i => bb84RefereeSiftedSingleRoundRefBlock ψ false (ω (bb84KeyRoundIdx peSel i))) := by
      funext i
      rw [hσ]
      simp only [Fin.rev_rev]
      rw [show bb84PeSelSort peSel
            (Fin.cast (bb84KeyRoundCount_add' n m)
              (Fin.castAdd (n - bb84KeyRoundCount n m) i)) =
              bb84KeyRoundIdx peSel i from rfl]
      exact bb84SiftedSingleRoundRefBlock_eq_of_not_xTest ψ _ _
        (by rw [bb84KeyRoundIdx_isKey peSel hcount i]; rfl) _
    have hpeBlk : (fun j => (fun a => bb84SiftedSingleRoundRefBlock ψ (peSel (Fin.rev a))
            (xSel (Fin.rev a)) (ω (Fin.rev a)))
          (bb84SortRoundPerm peSel
            (Fin.cast (bb84KeyRoundCount_add' n m)
              (Fin.natAdd (bb84KeyRoundCount n m) j)))) =
        (fun j => bb84SiftedSingleRoundRefBlock ψ true (xSel (bb84PERoundIdx peSel j))
          (ω (bb84PERoundIdx peSel j))) := by
      funext j
      rw [hσ]
      simp only [Fin.rev_rev]
      rw [show bb84PeSelSort peSel
            (Fin.cast (bb84KeyRoundCount_add' n m)
              (Fin.natAdd (bb84KeyRoundCount n m) j)) =
              bb84PERoundIdx peSel j from rfl,
        bb84PERoundIdx_isPE peSel hcount j]
    rw [hkey, hpeBlk]
  · rw [ite_eq_right hpe, ite_eq_right hpe, SubDensityOp.castDim_zero,
    bb84_subDensityOp_reindex_zero]

/-- **The coarsen-key operation at a general test-set size `m`.**  Cast away the trivial-attack
Eve register, sort the de-Finetti reference register so the key rounds lead (`reindexQ` by the
rev-corrected key-first sort `bb84SortRoundPerm`), then classically coarsen the round-outcome
register into the sorted Alice-`Z` key bits (`n_K = n − m` of them) and the sorted PE outcomes (`m`
of them).  The quantum register stays `4ⁿ` (gathered into key⊗PE blocks by the sort).

The genuine-LOCC counterpart of the referee `bb84CoarsenKey`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
noncomputable def bb84CoarsenKey {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (signalDim * signalDim)) :
    CQState ((Fin (bb84KeyRoundCount n m) → Fin 2) ×
        (Fin (n - bb84KeyRoundCount n m) → Fin signalDim))
      (signalDim ^ n) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  CQState.coarsen
    (fun ω => (fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i),
      (bb84PartEquiv (m := m) peSel ω).2))
    (CQState.reindexQ (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)
      (bb84CastCQState (by rw [Nat.one_mul])
        (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ ψ)))

/-- **L3 — the coarsen-key split of the trivial-attack per-σ family block, at a general
test-set size `m`.**  Coarsening the trivial-attack de-Finetti reference component `f ψ` along the
key/PE round partition factors it as the `n_K = n − m`-fold **referee** key bit-CQ tensor power
`(bb84SiftedKeyRoundCQ ψ)^{⊗n_K}` tensored with the general-`m` PE-round product
`bb84SiftedPERoundProd`.

The key factor is the referee one because the sift is the identity on every key round
(`bb84SiftedSingleRoundRefBlock_eq_of_not_xTest`), so the AEP/Devetak–Winter layer above
`bb84SiftedKeyRoundCQ` transfers unchanged at every `m`.

The accept `if` leaves the key-string fibre sum untouched and lands entirely on the PE factor
because the predicate is a function of the PE-round outcomes alone
(`bb84SiftedLocalPETestPassed_eq_pePass`); a key/PE-coupled predicate would break this
factorization.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
theorem bb84_sifted_unitRegisterEmbed_coarsenKey_eq {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hcount : bb84KeyCount n m peSel)
    (ψ : DensityOp (signalDim * signalDim)) :
    bb84CoarsenKey (m := m) peSel xSel Q δ ψ =
      bb84CastCQState (by rw [← pow_add, bb84KeyRoundCount_add'])
        (CQState.tensor ((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m))
          (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)) := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hd : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  apply CQState.ext_stateMap
  funext zp
  obtain ⟨z, p⟩ := zp
  apply SubDensityOp.ext
  ext i j
  -- The block of the sorted-reindexed cast state, per outcome string (sorted factorization).
  have hPsi : ∀ ω : Fin n → Fin signalDim,
      ((CQState.reindexQ (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)
          (bb84CastCQState (by rw [Nat.one_mul])
            (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ))).stateMap
              ω).toOp =
        (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
          SubDensityOp.castDim (by rw [← pow_add, bb84KeyRoundCount_add'])
            ((SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
                (fun k =>
                  bb84RefereeSiftedSingleRoundRefBlock ψ false
                      (ω (bb84KeyRoundIdx peSel k)))).tensor
              (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
                (fun k => bb84SiftedSingleRoundRefBlock ψ true
                  (xSel (bb84PERoundIdx peSel k)) (ω (bb84PERoundIdx peSel k)))))
          else 0).toOp := by
    intro ω
    rw [CQState.reindexQ_stateMap, bb84CastCQState_stateMap,
      bb84_sifted_unitRegisterEmbed_reindexBlock peSel xSel Q δ hcount ψ ω]
  -- The key fiber-sum identity (E), at arbitrary entries.
  have hEentry : ∀ A B : Fin (signalDim ^ bb84KeyRoundCount n m),
      (∑ kk : Fin (bb84KeyRoundCount n m) → Fin signalDim,
        if (fun k => bb84AliceBitMap (kk k)) = z then
          (SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
            (fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false (kk k))).toOp A B else 0)
        = (((bb84SiftedKeyRoundCQ ψ).tensorPower
            (bb84KeyRoundCount n m)).stateMap z).toOp A B := by
    intro A B
    rw [bb84SiftedKeyRoundCQ_tensorPower_stateMap_eq_fiberSumCount, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro kk _
    split <;> simp
  -- LHS: unfold coarsen, push the entry through, substitute the sorted block, reindex + collapse.
  rw [bb84CoarsenKey, CQState.coarsen_stateMap_toOp, Matrix.sum_apply]
  simp_rw [hPsi, apply_ite (fun M : Op (signalDim ^ n) => M i j),
    apply_ite (fun M : SubDensityOp (signalDim ^ n) => M.toOp i j),
    bb84_subDensityOp_zero_toOp, SubDensityOp.castDim_toOp_cast,
    bb84_subDensityOp_tensor_toOp_apply, Matrix.zero_apply]
  -- Reindex the outcome-string sum by the key/PE partition equivalence.
  rw [← Equiv.sum_comp (bb84PartEquiv (m := m) peSel).symm, Fintype.sum_prod_type]
  simp_rw [bb84SiftedLocalPETestPassed_eq_pePass peSel xSel δ Q hcount,
    Equiv.apply_symm_apply, bb84PartEquiv_symm_apply_keyIdx,
    bb84PartEquiv_symm_apply_peIdx]
  -- Collapse the PE-outcome sum (`q = p` survives; the test factors as `pePassParam p`).
  have hq : ∀ kk : Fin (bb84KeyRoundCount n m) → Fin signalDim,
      (∑ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
        if (fun k => bb84AliceBitMap (kk k), q) = (z, p) then
          (if bb84SiftedPEPass (m := m) peSel xSel δ Q q = true then
            (SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
                (fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false (kk k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).1
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).1 *
            (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
                (fun k => bb84SiftedSingleRoundRefBlock ψ true
                  (xSel (bb84PERoundIdx peSel k)) (q k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).2
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).2
          else 0)
        else 0) =
        if (fun k => bb84AliceBitMap (kk k)) = z then
          (if bb84SiftedPEPass (m := m) peSel xSel δ Q p = true then
            (SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
                (fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false (kk k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).1
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).1 *
            (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
                (fun k => bb84SiftedSingleRoundRefBlock ψ true
                  (xSel (bb84PERoundIdx peSel k)) (p k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).2
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).2
          else 0)
        else 0 := by
    intro kk
    rw [Finset.sum_eq_single p
      (fun q _ hq => ite_eq_right (fun hcon => hq (congrArg Prod.snd hcon)))
      (fun h => absurd (Finset.mem_univ p) h)]
    simp only [Prod.mk.injEq, and_true]
  simp_rw [hq]
  -- Split on the PE-pass verdict; in each case factor and apply (E).
  by_cases hpass : bb84SiftedPEPass (m := m) peSel xSel δ Q p = true
  · -- RHS reduction (accepting).
    rw [bb84CastCQState_stateMap, SubDensityOp.castDim_toOp_cast,
      show (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
            (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).stateMap (z, p) =
          SubDensityOp.tensor
            (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).stateMap z)
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p) from rfl,
      bb84_subDensityOp_tensor_toOp_apply]
    -- The ρ_PE block at `p` is the PE-round tensor product (pass branch).
    rw [show (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p =
          SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
            (fun k => bb84SiftedSingleRoundRefBlock ψ true
              (xSel (bb84PERoundIdx peSel k)) (p k)) from by
        simp only [bb84SiftedPERoundProd, hpass, ite_true]]
    -- LHS: drop the PE-pass `if`, factor out the (kk-independent) PE entry, apply (E).
    simp_rw [ite_eq_left hpass]
    rw [show (∑ kk : Fin (bb84KeyRoundCount n m) → Fin signalDim,
          if (fun k => bb84AliceBitMap (kk k)) = z then
            (SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
                (fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false (kk k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).1
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).1 *
            (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
                (fun k => bb84SiftedSingleRoundRefBlock ψ true
                  (xSel (bb84PERoundIdx peSel k)) (p k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).2
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).2
          else 0) =
        (∑ kk : Fin (bb84KeyRoundCount n m) → Fin signalDim,
          if (fun k => bb84AliceBitMap (kk k)) = z then
            (SubDensityOp.tensorFinProd (bb84KeyRoundCount n m)
                (fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false (kk k))).toOp
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).1
              (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).1
          else 0) *
          (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
              (fun k => bb84SiftedSingleRoundRefBlock ψ true
                (xSel (bb84PERoundIdx peSel k)) (p k))).toOp
            (finProdFinEquiv.symm (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) i)).2
            (finProdFinEquiv.symm
              (Fin.cast (by rw [← pow_add, bb84KeyRoundCount_add']) j)).2 from by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro kk _; split <;> simp]
    rw [hEentry]
  · -- Non-accepting: both sides vanish.
    rw [bb84CastCQState_stateMap, SubDensityOp.castDim_toOp_cast,
      show (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
            (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).stateMap (z, p) =
          SubDensityOp.tensor
            (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).stateMap z)
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p) from rfl,
      bb84_subDensityOp_tensor_toOp_apply]
    rw [show (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p = 0 from by
        simp only [bb84SiftedPERoundProd]; exact ite_eq_right hpass]
    simp only [ite_eq_right hpass, bb84_subDensityOp_zero_toOp, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, ite_self]

/-! ## The conditioning-side PE-announce key CQ constructor

The faithful register move announces the PE-round product block into the **conditioning**
(quantum) register while keeping the key-round bits on the secret (classical) register: kernel
first, coarsen second.  Coarsening an announced register away instead asserts data processing
backwards — the exact counterexample has left-hand side `1`, right-hand side `1/2`.

The announced block is the PE-round product's own quantum marginal, an outcome-independent
sub-normalized operator, so the decoupled-ancilla seam lemma
`smoothMinEntropy_le_condTensor_decoupled_ancilla` applies penalty-free **at each Carathéodory
point** — and only there. A de Finetti mixture need not retain this product structure, so applying
the decoupled-ancilla bound there requires a separate factorization argument.

The product reference tensors the key marginal with the announced PE marginal. The extended
entropy comparison includes a zero PE marginal. -/

/-! ## The protocol-level gate is a key ⊗ PE product predicate

The objects above filter on the PE-only predicate `bb84SiftedLocalPETestPassed`.  The gate the
protocol's channels are actually built on, `bb84SiftedLocalPEAndEVPassed`, conjoins error
verification.  It is a **product** predicate — a function of the sorted PE outcomes times a
function of the sorted key outcomes. For such a predicate, an analogous factorization must also
filter the key factor by the key-dependent verdict.
`bb84_sifted_unitRegisterEmbed_coarsenKey_eq` establishes the PE-only case, whose key factor remains
unfiltered. A key/PE-coupled predicate need not preserve that split.

These statements are about the predicates only.  No object in this file is filtered by the full
gate, and nothing here transports the split to it. -/

end QKD.BB84.Engine

end -- noncomputable section
