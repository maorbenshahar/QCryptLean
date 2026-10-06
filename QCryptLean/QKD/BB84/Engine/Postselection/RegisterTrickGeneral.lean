import QCryptLean.QKD.BB84.Engine.Postselection.RegisterTrick
import QCryptLean.QKD.BB84.Engine.Postselection.PEAnnounceRelabelGeneral

/-!
# The Bell-twirl trace-norm invariance of the genuine-LOCC channels, at a general test-set size `m`

The Bell-twirl trace-norm invariance of the symmetrized channel difference
`bb84SymSiftedRealChannelDirect_withPEAnnounce − bb84SymSiftedIdealChannelDirect_withPEAnnounce`
(`SiftedPEAnnounce.lean`), at a general PE test-set size `m`.

`m` enters this file in exactly one place — the width of the announced PE-outcome register
`Fin (signalDim ^ (n − bb84KeyRoundCount n m))`, a `ℕ` factor of
`bb84PEAnnounceBaseOutputDim`, i.e. a type index of the channels' codomain.  No step reads a
property of `m`, so the family carries no constraint relating `m` to `n`.

Three pieces, then the assembly.

* **The announce-orthogonal sector split**
  (`bb84_announceLinearEveVisible_sum_traceNorm_eq_sum` and its `⊗ id_R`-stabilized form
  `bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum`): the announcement appends
  the rank-one projector `|π⟩⟨π|` on the `n!` public-permutation register, which sits strictly right
  of the `m`-indexed base register, so distinct `π` land in orthogonal sectors and the trace norm is
  additive over them.

* **The per-summand covariance through the pre-channel layer**
  (`bb84PEAnnounceBareSummandInner_bellTwirl_conj`): the per-`π` inner map
  `Δ_proto ∘ (sift ∘ pre) ∘ permuteSignal_π` intertwines the input Bell twirl `U_g` with the
  announced-PE relabel at the string `bb84SiftedTwirlString peSel xSel (g ∘ π⁻¹)`.
  Assembled from `permuteSignalLinear_bellTwirl_conj` (`g ↦ g ∘ π⁻¹`, `m`-free), the pre-channel
  covariance (`IsBellTwirlCovariantPre`, `RegisterTrick.lean`) and the end-to-end base covariance
  `bb84SiftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj` (`PEAnnounceRelabelGeneral.lean`).

* **The stabilized invariance** (`bb84_bellTwirl_traceNorm_invariant_stabilized`), which feeds the
  channel-independent register trick
  `bellRegExt_traceNorm_mapTensorId_referee_of_bellTwirl_invariant` (`RegisterTrick.lean`).

## The pre-channel layer is not free

The twirl reaches the sift only through the pre-channel slot (`bb84SiftedConjAfterPre` is
`bb84SiftedConjChannel ∘ₗ pre`), and `IsCPTP ⇑pre` says nothing about `pre` on twirled inputs.
`bb84_bellTwirl_traceNorm_invariant_stabilized_of_preCov` therefore carries the explicit hypothesis
`IsBellTwirlCovariantPre pre` — consumed at exactly one place — and
`bb84_bellTwirl_traceNorm_invariant_stabilized` is its unit-register instance.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, the
Postselection Theorem `\label{thm:maintheorem}` (`main.tex:481`) and
`main.tex:354` `\label{lem:groupPurification}` at `x = ∑ᵢ mᵢ² = 4`; Christandl–König–Renner (2009),
`arXiv:0809.3019`, `main.tex:268`–`:401` (Main Result: the Post-Selection Theorem
`\label{thm:main}` :291–:301, the substate-extraction Lemma `\label{lem:extractpart}` :319–:328);
Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84

/-! ## The announce-orthogonal sector split -/

/-- **Orthogonal announced-permutation sector additivity at the general-`m` output register.**

The announcement `bb84SiftedPEAnnounceLinearEveVisible … π` appends the orthogonal
rank-one projector `permAnnounceProjector n π = |π⟩⟨π|` on the `Fin n.factorial`
public-permutation register, so for every operator family `F` the trace norm of the announced sum is
additive over `π`.  The announced-PE register `m` widens sits inside
`bb84PEAnnounceBaseOutputDim`, strictly left of the `n!` register this argument reads, so the
port is a pure index swap.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B,
`main.tex:481` `\label{thm:maintheorem}`; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/
theorem bb84_announceLinearEveVisible_sum_traceNorm_eq_sum {n m ℓ ℓEV eveDim : ℕ}
    [NeZero n] [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    traceNorm (∑ π : Equiv.Perm (Fin n),
        bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π (F π)) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
          (F π)) := by
  classical
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  haveI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  haveI hbe : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * eveDim) :=
    bb84EveVisiblePEAnnounceBaseOutputDim_neZero n m ℓ ℓEV peSel leakEC eveDim
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * eveDim * n.factorial) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  set e := permAnnounceIndexEquiv n with he
  set G : Fin n.factorial → Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * eveDim) :=
    fun j => F (e.symm j) with hG
  -- RHS: each term collapses to `‖F π‖₁`.
  have hRHS : ∀ π : Equiv.Perm (Fin n),
      traceNorm (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π (F π)) =
        traceNorm (F π) :=
    fun π => bb84_announceLinearEveVisible_traceNorm_eq peSel leakEC π (F π)
  -- LHS: pull the castDim out of the sum, strip it, then reindex to block-diagonal form.
  have hLHS_sum :
      (∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π (F π)) =
        mapTensorId
          (Op.castDimLinear (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC))
          (∑ π : Equiv.Perm (Fin n),
            mapTensorId
              (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
                (permAnnounceIndexEquiv n π)) (F π)) := by
    rw [show mapTensorId
          (Op.castDimLinear (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC))
          (∑ π : Equiv.Perm (Fin n),
            mapTensorId
              (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
                (permAnnounceIndexEquiv n π)) (F π)) =
        mapTensorIdLinear
          (Op.castDimLinear (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC))
          (∑ π : Equiv.Perm (Fin n),
            mapTensorId
              (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
                (permAnnounceIndexEquiv n π)) (F π)) from rfl, map_sum]
    exact Finset.sum_congr rfl fun π _ =>
      bb84SiftedPEAnnounceLinearEveVisible_eq_mapTensorId_castDim_append peSel leakEC π (F π)
  -- The inner append-sum is a reindex of the block-diagonal normal form.
  have hSumSub :
      (∑ j : Fin n.factorial, G j ⊗ (Matrix.single j j 1 : Op n.factorial)).submatrix
          (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
            n.factorial eveDim)
          (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
            n.factorial eveDim) =
        ∑ j : Fin n.factorial,
          (G j ⊗ (Matrix.single j j 1 : Op n.factorial)).submatrix
            (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              n.factorial eveDim)
            (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              n.factorial eveDim) := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  have hInner :
      (∑ π : Equiv.Perm (Fin n),
          mapTensorId
            (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              (permAnnounceIndexEquiv n π)) (F π)) =
        (∑ j : Fin n.factorial, G j ⊗ (Matrix.single j j 1 : Op n.factorial)).submatrix
          (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
            n.factorial eveDim)
          (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
            n.factorial eveDim) := by
    rw [hSumSub]
    have hterm : ∀ π : Equiv.Perm (Fin n),
        mapTensorId
            (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              (permAnnounceIndexEquiv n π)) (F π) =
          (F π ⊗ (Matrix.single (e π) (e π) 1 : Op n.factorial)).submatrix
            (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              n.factorial eveDim)
            (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
              n.factorial eveDim) := by
      intro π
      rw [mapTensorId_appendSingleLinear]
    rw [Finset.sum_congr rfl (fun π _ => hterm π)]
    rw [← Equiv.sum_comp e (fun j : Fin n.factorial =>
      (G j ⊗ (Matrix.single j j 1 : Op n.factorial)).submatrix
        (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
          n.factorial eveDim)
        (tensorSwapInnerEquiv (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
          n.factorial eveDim))]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [hG, he, Equiv.symm_apply_apply]
  rw [hLHS_sum, traceNorm_mapTensorId_castDimLinear, hInner, traceNorm_submatrix_equiv,
    traceNorm_blockDiagonal_sum]
  rw [Finset.sum_congr rfl (fun π _ => hRHS π)]
  rw [show (∑ j : Fin n.factorial, traceNorm (G j)) =
      ∑ j : Fin n.factorial, traceNorm (F (e.symm j)) from by
        exact Finset.sum_congr rfl fun j _ => by rw [hG]]
  exact Equiv.sum_comp e.symm (fun π => traceNorm (F π))

/-- **Stabilized announce-orthogonal sector split.**  Threading the substate-extraction
register `dimR` through the general-`m` announcement keeps the trace norm additive over the
announced-permutation sectors.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B,
`main.tex:481` `\label{thm:maintheorem}`; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/
theorem bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum
    {n m ℓ ℓEV eveDim dimR : ℕ} [NeZero n] [NeZero eveDim] [NeZero dimR] [NeZero (eveDim * dimR)]
    (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR)) :
    traceNorm (∑ π : Equiv.Perm (Fin n),
        mapTensorId (k := dimR)
          (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) (F π)) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm (mapTensorId (k := dimR)
          (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) (F π)) := by
  classical
  set e := prodAssocFin
    (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) eveDim dimR with he
  have hterm : ∀ π : Equiv.Perm (Fin n),
      mapTensorId (k := dimR)
          (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) (F π) =
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV (eveDim * dimR) peSel leakEC π
          (F π |>.submatrix
            (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim dimR)
            (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim
              dimR))).submatrix e.symm e.symm :=
    fun π => bb84SiftedPEAnnounceLinearEveVisible_mapTensorId_reassoc peSel leakEC π (F π)
  have hLHS :
      (∑ π : Equiv.Perm (Fin n),
          mapTensorId (k := dimR)
            (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) (F π)) =
        (∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV (eveDim * dimR) peSel leakEC π
            (F π |>.submatrix
              (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim dimR)
              (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim
                dimR))).submatrix e.symm e.symm := by
    rw [Finset.sum_congr rfl (fun π _ => hterm π)]
    ext p q
    simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hLHS, traceNorm_submatrix_equiv, bb84_announceLinearEveVisible_sum_traceNorm_eq_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [hterm π, traceNorm_submatrix_equiv]

/-!
## The per-summand inner map and its Bell-twirl covariance

`IsBellTwirlCovariantPre` (`RegisterTrick.lean`) constrains a map
`Op (4^n) →ₗ Op (4^n * eveDim)`, neither of whose dimensions carries a split point, so it is
`m`-free.
-/

/-- The per-`π` bare general-`m` inner summand: the general-`m` real−ideal protocol-map difference
after the sifted pre-channel and the symmetrization permutation, before the public-permutation
announcement. -/
private noncomputable def bb84PEAnnounceBareSummandInner (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (eveDim : ℕ) [NeZero eveDim] (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (π : Equiv.Perm (Fin n)) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q δ).realProtocolMap
        (eveDim := eveDim) -
      (bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
          δ).idealProtocolMap
        (eveDim := eveDim)).comp
    ((bb84SiftedConjAfterPre eveDim pre peSel xSel).comp (permuteSignalLinear n π)))

/-- **The per-summand general-`m` covariance.**  The bare general-`m` inner summand intertwines the
input Bell twirl `U_g` with the general-`m` announced-PE relabel at the sift-relabelled,
`π⁻¹`-transported string `bb84SiftedTwirlString peSel xSel (g ∘ π⁻¹)`.

The three transports: `permuteSignalLinear_bellTwirl_conj` moves the twirl past the symmetrization
permutation (`g ↦ g ∘ π⁻¹`), `hcov` moves it past the pre-channel, and
`bb84SiftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj` moves it through the sift, the
computational measurement and the PA/abort maps onto the output relabel.  The `ec` hypotheses are
stated at the physical string `g ∘ π⁻¹`, which is legitimate because the sift is the identity on key
rounds (`bellTwirlKeyError_siftedTwirlString`). -/
private theorem bb84PEAnnounceBareSummandInner_bellTwirl_conj (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (hcov : IsBellTwirlCovariantPre pre) (π : Equiv.Perm (Fin n)) (g : Fin n → Fin 4)
    (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹)) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹))
          (ec.syndrome (a + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹))) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹))
    (ρ : Op (4 ^ n)) :
    bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π
        (bellTwirlUnitary n g * ρ * (bellTwirlUnitary n g)ᴴ) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
            (bb84SiftedTwirlString peSel xSel (g ∘ ⇑π⁻¹)) πsyn)
          (1 : Op eveDim) *
        bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π ρ *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (bb84SiftedTwirlString peSel xSel (g ∘ ⇑π⁻¹)) πsyn)
          (1 : Op eveDim))ᴴ := by
  -- The inner map, applied, IS the general-`m` real−ideal PA/abort difference after the
  -- measurement, the sift, the pre-channel and the symmetrization permutation (definitional
  -- unfolding of the `comp`s).
  have happly : ∀ A0 : Op (4 ^ n),
      bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π A0 =
        ((retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel
                xSel leakEC ec δ Q -
              retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
                leakEC ec δ Q).comp (measurementChannel n eveDim))
          (bb84SiftedConjChannel n eveDim peSel xSel
            (pre (permuteSignalLinear n π A0))) :=
    fun A0 => rfl
  rw [happly, happly, permuteSignalLinear_bellTwirl_conj n π g ρ,
    hcov (g ∘ ⇑π⁻¹) (permuteSignalLinear n π ρ)]
  exact bb84SiftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj n m ℓ ℓEV eveDim peSel
    xSel leakEC ec δ Q (g ∘ ⇑π⁻¹) πsyn hsyn hdec _

/-! ## The stabilized Bell-twirl trace-norm invariance -/

/-- **The stabilized Bell-twirl trace-norm invariance at a general `m`, at a Bell-twirl covariant
pre-channel.**

For the general-`m` real−ideal symmetrized channel difference `Δ` and every
`X : Op (4^n · dimR)`,

`‖(Δ ⊗ id_R)(U_g ⊗ id_R · X · (U_g ⊗ id_R)†)‖₁ = ‖(Δ ⊗ id_R)(X)‖₁`.

Every step threads `id_R`: the per-summand covariance
(`bb84PEAnnounceBareSummandInner_bellTwirl_conj`) lifts through
`mapTensorIdLinear_left_conj_of_conj`, the per-block relabel `W ⊗ 1_E` stays an isometry under
`⊗ id_R`, and the announce-orthogonal sector split tensorizes
(`bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum`).

`m` enters only as the width of the announced PE-outcome register inside
`bb84PEAnnounceBaseOutputDim`, i.e. as a type index of the output relabel unitary
`bb84PEAnnounceBellRelabelUnitary`; no step reads a property of `m`.

**The `ec` hypothesis is the exact clause pair the proof consumes, not a proof of
`ECScheme.IsTranslationEquivariant` for `ec`.**  The argument reads the syndrome-alphabet relabel
of clause (i) and the decoder covariance of clause (ii) at one error pattern per announced
permutation `π` — `bellTwirlKeyError peSel (g ∘ π⁻¹)` — and at no other.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B,
`main.tex:481` `\label{thm:maintheorem}` and `main.tex:354` `\label{lem:groupPurification}` at
`x = ∑ᵢ mᵢ² = 4`; Christandl–König–Renner (2009), `arXiv:0809.3019`, `main.tex:268`–`:401`;
Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/
theorem bb84_bellTwirl_traceNorm_invariant_stabilized_of_preCov (n m ℓ ℓEV : ℕ)
    [NeZero n] [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (g : Fin n → Fin 4)
    (hec : ∀ π : Equiv.Perm (Fin n),
      (∃ πsyn : Equiv.Perm (Fin (2 ^ leakEC)), ∀ a : KeyBitString n peSel,
          ec.syndrome (a + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹)) = πsyn (ec.syndrome a)) ∧
        (∀ a b : KeyBitString n peSel,
          ec.decode (b + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹))
              (ec.syndrome (a + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹)))
            = ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel (g ∘ ⇑π⁻¹)))
    (eveDim : ℕ) [NeZero eveDim] (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (hcov : IsBellTwirlCovariantPre pre)
    (dimR : ℕ) [NeZero dimR] (M : Op (4 ^ n * dimR)) :
    traceNorm (mapTensorId (k := dimR)
        (bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
            pre -
          bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
              pre)
        (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
      traceNorm (mapTensorId (k := dimR)
        (bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
            pre -
          bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
              pre)
        M) := by
  haveI : NeZero (4 ^ n * eveDim) := instNeZeroNatHMul
  haveI : NeZero (eveDim * dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  set U := bellTwirlUnitary n g with hUdef
  set Mtw := Op.tensor U (1 : Op dimR) * M * (Op.tensor U (1 : Op dimR))ᴴ with hMtwdef
  -- Per-summand trace-norm invariance (stabilized).
  have hsummand : ∀ π : Equiv.Perm (Fin n),
      traceNorm (mapTensorId (k := dimR)
        ((bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
          (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π))
        Mtw) =
      traceNorm (mapTensorId (k := dimR)
        ((bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
          (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π))
        M) := by
    intro π
    obtain ⟨πsyn, hsyn⟩ := (hec π).1
    have hdec := (hec π).2
    rw [← mapTensorId_comp
        (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) Mtw,
      ← mapTensorId_comp
        (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) M,
      bb84_announceLinearEveVisible_mapTensorId_traceNorm_eq,
      bb84_announceLinearEveVisible_mapTensorId_traceNorm_eq]
    set W := bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
      (bb84SiftedTwirlString peSel xSel (g ∘ ⇑π⁻¹)) πsyn with hWdef
    set V := Op.tensor W (1 : Op eveDim) with hVdef
    have hconj := mapTensorIdLinear_left_conj_of_conj (k := dimR)
      (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π) U V
      (fun ρ => bb84PEAnnounceBareSummandInner_bellTwirl_conj n m ℓ ℓEV Q δ peSel xSel leakEC
        ec eveDim pre hcov π g πsyn hsyn hdec ρ) M
    rw [hMtwdef]
    rw [show mapTensorId (k := dimR)
          (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
          (Op.tensor U (1 : Op dimR) * M * (Op.tensor U (1 : Op dimR))ᴴ) =
        mapTensorIdLinear
          (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
          (Op.tensor U (1 : Op dimR) * M * (Op.tensor U (1 : Op dimR))ᴴ) from rfl,
      hconj]
    have hViso : (Op.tensor V (1 : Op dimR))ᴴ * Op.tensor V (1 : Op dimR) = 1 := by
      rw [Op.tensor_conjTranspose, Op.tensor_mul, Matrix.conjTranspose_one, Matrix.one_mul, hVdef,
        bb84PEAnnounceBellRelabelUnitary_tensor_one_unitary, Op.tensor_one]
    exact Quantum.Metrics.TraceNormHoelder.traceNorm_isometry_mul_left _ _ hViso
  -- Assemble: decompose the difference, push `mapTensorId` through the smul-sum, split the sectors.
  have hdecomp :
      (bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre -
          bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
              pre) =
        (1 / (n.factorial : ℂ)) •
          ∑ π : Equiv.Perm (Fin n),
            (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
              (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim
                pre π) := by
    simp only [bb84SymSiftedRealChannelDirect_withPEAnnounce,
      bb84SymSiftedIdealChannelDirect_withPEAnnounce, bb84PEAnnounceBareSummandInner]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun π _ => ?_)
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
  have hcompsplit : ∀ A0 : Op (4 ^ n * dimR),
      (∑ π : Equiv.Perm (Fin n),
        mapTensorId (k := dimR)
          ((bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
            (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π))
          A0) =
      ∑ π : Equiv.Perm (Fin n),
        mapTensorId (k := dimR)
          (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π)
          (mapTensorId (k := dimR)
            (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
            A0) :=
    fun A0 => Finset.sum_congr rfl fun π _ =>
      (mapTensorId_comp
        (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π)
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) A0).symm
  have hsumeq :
      traceNorm (∑ π : Equiv.Perm (Fin n),
          mapTensorId (k := dimR)
            ((bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
              (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π))
            Mtw) =
        traceNorm (∑ π : Equiv.Perm (Fin n),
          mapTensorId (k := dimR)
            ((bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
              (bb84PEAnnounceBareSummandInner n m ℓ ℓEV Q δ peSel xSel leakEC ec eveDim pre π))
            M) := by
    rw [hcompsplit Mtw, hcompsplit M,
      bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum,
      bb84_announceLinearEveVisible_mapTensorId_sum_traceNorm_eq_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [mapTensorId_comp, mapTensorId_comp]
    exact hsummand π
  rw [hdecomp, mapTensorId_linearMap_smul, mapTensorId_linearMap_smul,
    mapTensorId_linearMap_sum, mapTensorId_linearMap_sum,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, hsumeq]

/-- **The stabilized Bell-twirl trace-norm invariance at a general `m`, at the unit register slot.**

The real−ideal symmetrized channel difference at the unit register slot — the slot
`bb84SymRealChannel` / `bb84SymIdealChannel` live at — is trace-norm invariant under the
IID Bell twirl `U_g = bellTwirlUnitary n g` with the substate-extraction ancilla register `R`
present:

`‖(Δ ⊗ id_R)(U_g ⊗ id_R · X · (U_g ⊗ id_R)†)‖₁ = ‖(Δ ⊗ id_R)(X)‖₁`.

The instance of `bb84_bellTwirl_traceNorm_invariant_stabilized_of_preCov` at `eveDim := 1`,
`pre := bb84UnitRegisterEmbed n`, whose covariance side condition is discharged by
`bb84UnitRegisterEmbed_isBellTwirlCovariantPre`.  No attack object is named in the statement or in
the proof.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B,
`main.tex:481` `\label{thm:maintheorem}`; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/
theorem bb84_bellTwirl_traceNorm_invariant_stabilized (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (hec : ec.IsTranslationEquivariant)
    (dimR : ℕ) [NeZero dimR] (g : Fin n → Fin 4) (M : Op (4 ^ n * dimR)) :
    traceNorm (mapTensorId (k := dimR)
        (bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
            1 (bb84UnitRegisterEmbed n) -
          bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
            1 (bb84UnitRegisterEmbed n))
        (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
      traceNorm (mapTensorId (k := dimR)
        (bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
            1 (bb84UnitRegisterEmbed n) -
          bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
            1 (bb84UnitRegisterEmbed n)) M) :=
  bb84_bellTwirl_traceNorm_invariant_stabilized_of_preCov n m ℓ ℓEV Q δ peSel xSel leakEC
    ec g (fun π => hec (bellTwirlKeyError peSel (g ∘ ⇑π⁻¹)))
    1 (bb84UnitRegisterEmbed n)
    (bb84UnitRegisterEmbed_isBellTwirlCovariantPre n) dimR M

/-! ## The general-`m` register trick

`bellRegExt` (`RegisterTrickReferee.lean`) is channel-independent and the generic trace-norm
preservation `bellRegExt_traceNorm_mapTensorId_referee_of_bellTwirl_invariant`
(`RegisterTrickReferee.lean`) is already `{n dimR dimOut}`-generic in the map `Δ`, so nothing here
is re-derived: the general-`m` form is that lemma instantiated at the general-`m` channel difference
and `bb84_bellTwirl_traceNorm_invariant_stabilized`. -/

end QKD.BB84.Engine

end
