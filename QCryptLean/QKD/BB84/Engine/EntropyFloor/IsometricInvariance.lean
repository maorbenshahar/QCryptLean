import QCryptLean.QKD.BB84.Engine.EntropyFloor.IsometricInvarianceReferee
import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecomposition
import QCryptLean.QKD.BB84.Engine.EntropyFloor.ClassicalAnnounceKernel

/-!
# The key-scoped register bridge on Alice's key string

`bb84SortedKeyBitEquiv` identifies the sorted key-bit string `Fin n_K → Fin 2` with the
physical key string `KeyBitString n peSel` hashed by `aliceKeyHashFamily`. The selector identity
`bb84KeyCount n m peSel` supplies the bijection at `n_K = n - m`. Relabelling by this bijection
preserves extended smooth min-entropy through `smoothMinEntropy_relabel`.

The sift is the identity on every key round, so the key factor is `bb84SiftedKeyRoundCQ`.
Its tensor power is normalized. In the key/PE product decomposition, the PE factor therefore
carries exactly the accepted weight of `bb84PairedHaarPerSigmaFamily`. These identities include
zero accepted weight and empty key blocks.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B and §V.C;
Renner 2005, arXiv:quant-ph/0512258v2, §3.1 and §6.5.
-/

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.QuantumLHL
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## The sorted-key-round bijection onto the physical key rounds -/

/-! ## Accept-weight bookkeeping

Each object of the key/PE split carries exactly the accepted weight of the per-σ family
`bb84PairedHaarPerSigmaFamily`, because the key factor is normalized and the split is the
product `bb84_sifted_unitRegisterEmbed_coarsenKey_eq`. -/

/-- **The referee key-round bit-CQ object is normalized.**  Its two Alice-bit blocks are the
`bb84AliceBitMap` coarsening of the single sifted key round, whose four outcome blocks have total
trace `1` (`bb84RefereeSiftedRoundBlock_trace_sum` at the key-round type `b = false`). -/
lemma bb84SiftedKeyRoundCQ_weight (ψ : DensityOp (signalDim * signalDim)) :
    ∑ z : Fin 2, ((bb84SiftedKeyRoundCQ ψ).stateMap z).trace = 1 := by
  change ∑ z : Fin 2,
    ((CQState.coarsen bb84AliceBitMap (bb84SiftedKeyRoundCQRaw ψ)).stateMap z).trace = 1
  rw [CQState.sum_coarsen_stateMap_trace_eq]
  exact bb84RefereeSiftedRoundBlock_trace_sum ψ false

/-! ## The key-scoped register bridge at a general test-set size `m`

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol at a **general** test-set size `m`
(arXiv:2403.11851, `main.tex:909` "a random subset of $m$ signals", `:913`
"the remaining $\nkey = n-m$ signals", both inside `\subsection{Classical part}` at `:906`).  The
declarations below are that general-`m` layer of this file, over the split-point-parametrised round
partition `bb84KeyRoundCount`, `bb84KeyRoundIdx`, `bb84PERoundIdx`,
`bb84PartEquiv`, `bb84KeyCount`, and over the general-`m` objects
`bb84SiftedPERoundProd` and `bb84CoarsenKey`.  At `m = ⌈n/2⌉` they specialise definitionally — no
`castDim` transport.

**The general-`m` forms carry no constraint relating `m` to `n`.**  Every split-point obligation of
this file — the register split `4ⁿ = 4^{n_K}·4^{n − n_K}` used by `SubDensityOp.castDim` and by
`SubDensityOp.tensorFinProd_sortSplit` — is discharged by `bb84KeyRoundCount_add'`, which is
unconditional (`n − m ≤ n` at every `m`).  In particular `hn : 2 ≤ n`, load-bearing on the carried
bridges only to make `n_K = ⌊n/2⌋` nonzero, is **absent** here: no step of the argument reads a
nonempty key block, and `m = 0`, `m ≥ n` come out degenerate rather than excluded.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B main.tex:1341–:1413,
Lemma 14, §V.C (`main.tex:909`, `:913`); Renner 2005 (arXiv:quant-ph/0512258v2) §6.5, Lemma 3.1.10 /
Cor. 3.1.11; Christandl–König–Renner 2009 (PRL 102, 020504). -/

/-- The general-`m` sorted key-round index map is injective: it is the key-first sort
    `bb84PeSelSort`
(an `Equiv`) precomposed with the injections `Fin.castAdd` and `Fin.cast`. -/
lemma bb84KeyRoundIdx_injective {n m : ℕ} (peSel : Fin n → Bool) :
    Function.Injective (bb84KeyRoundIdx (n := n) (m := m) peSel) := by
  intro i j hij
  have h := (bb84PeSelSort peSel).injective hij
  have hv : (i : ℕ) = (j : ℕ) := by
    have := congrArg Fin.val h
    simpa [Fin.castAdd, Fin.castLE] using this
  exact Fin.ext hv

/-- **The general-`m` sorted key rounds are exactly the physical key rounds.**

`bb84KeyRoundIdx peSel` sends the `i`-th slot of the key-first sort to a round with
`peSel = false` (`bb84KeyRoundIdx_isKey`); under the count
hypothesis `hcount : bb84KeyCount n m peSel` it is a bijection onto `{i // peSel i = false}`,
the domain of `KeyBitString`.  Injectivity is `bb84KeyRoundIdx_injective` and surjectivity
follows from the equal cardinalities.

This is the *bijection* that lets a floor on the sorted key-bit register transfer to Alice's key
string; a coarsening would not, since `Hmin(f(X)|E) ≤ Hmin(X|E)`. -/
def bb84KeyRoundSubtypeEquiv {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : bb84KeyCount n m peSel) :
    Fin (bb84KeyRoundCount n m) ≃ {i : Fin n // peSel i = false} :=
  Equiv.ofBijective
    (fun i => ⟨bb84KeyRoundIdx peSel i, bb84KeyRoundIdx_isKey peSel hcount i⟩)
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
      · intro i j hij
        exact bb84KeyRoundIdx_injective peSel (congrArg Subtype.val hij)
      · rw [Fintype.card_fin, hcount])

/-- **Alice's key string, read in general-`m` sorted key-round order.**

The relabelling of the secret register that identifies `KeyBitString n peSel` with the sorted
key-bit register `Fin n_K → Fin 2`, at `n_K = bb84KeyRoundCount n m`.  A bijection, not a
coarsening. -/
def bb84SortedKeyBitEquiv {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : bb84KeyCount n m peSel) :
    KeyBitString n peSel ≃ (Fin (bb84KeyRoundCount n m) → Fin 2) :=
  (Equiv.arrowCongr (bb84KeyRoundSubtypeEquiv peSel hcount) (Equiv.refl (Fin 2))).symm

/-- **The general-`m` relabel is Alice's key string.**  `bb84SortedKeyBitEquiv` carries
`aliceKeyString peSel ω` to the sorted Alice bits
`fun i => bb84AliceBitMap ((bb84PartEquiv peSel ω).1 i)` that the general-`m` coarsen-key
operation `bb84CoarsenKey` reads; this is what makes the register identification the physically
correct one rather than an arbitrary enumeration. -/
lemma bb84SortedKeyBitEquiv_bb84AliceKeyString {n m : ℕ} (peSel : Fin n → Bool)
    (hcount : bb84KeyCount n m peSel) (ω : Fin n → Fin signalDim) :
    bb84SortedKeyBitEquiv peSel hcount (aliceKeyString peSel ω) =
      fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i) := by
  funext i
  rw [bb84PartEquiv_apply_fst]
  rfl

/-- **The general-`m` PE-round product carries the accepted weight of the per-σ family.**

At the trivial attack the general-`m` sifted key coarsening splits as (normalized key rounds) ⊗
(PE rounds) (`bb84_sifted_unitRegisterEmbed_coarsenKey_eq`), so the PE factor alone carries the
whole accepted weight of `bb84PairedHaarPerSigmaFamily` — an object that mentions no split
point. -/
lemma bb84_siftedPERoundProd_weight_eq_pairedHaar {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    ∑ p : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
        ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p).trace =
      ∑ x : Fin n → Fin signalDim,
        ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ ψ).stateMap x).trace := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hA : ∑ z, ((bb84CoarsenKey (m := m) peSel xSel Q δ ψ).stateMap z).trace =
      ∑ x, ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ).stateMap x).trace := by
    unfold bb84CoarsenKey
    rw [CQState.sum_coarsen_stateMap_trace_eq]
    simp_rw [CQState.reindexQ_stateMap, SubDensityOp.reindex_trace, bb84CastCQState_stateMap,
      SubDensityOp.castDim_trace]
  have hB : ∑ z, ((bb84CoarsenKey (m := m) peSel xSel Q δ ψ).stateMap z).trace =
      ∑ p, ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap p).trace := by
    rw [bb84_sifted_unitRegisterEmbed_coarsenKey_eq peSel xSel Q δ hcount ψ]
    simp_rw [bb84CastCQState_stateMap, SubDensityOp.castDim_trace]
    rw [CQState.tensor_sum_trace,
      CQState.tensorPower_sum_trace (bb84SiftedKeyRoundCQ ψ) (bb84SiftedKeyRoundCQ_weight ψ),
          one_mul]
  exact hB.symm.trans hA

end QKD.BB84.Engine

end -- noncomputable section
