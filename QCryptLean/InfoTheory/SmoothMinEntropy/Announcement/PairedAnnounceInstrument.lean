import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernelBlockRef
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.PairedTensorPow
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning
import QCryptLean.Quantum.TensorProducts.RoundRegrouping

/-!
# The announce instrument on the paired register, and the reference it produces

An announcement whose value is a deterministic function of a measurement on the **source** register
is carried into the conditioning register by a fixed, state-independent instrument

  `Λ : X ↦ Σ_p |p⟩⟨p| ⊗ 𝓘_p(X)`,   `𝓘_p(X) = Tr_A[(E_p ⊗ 1) X (E_p ⊗ 1)]`,

with `{E_p}` the announced measurement — a family of Hermitian idempotents on the measured factor
summing to `1`.  `𝓘_p` is `announceInstrument (E p)` below; the classical `Σ_p |p⟩⟨p| ⊗ (·)` wrapper
is `blockDiagRef` (`ClassicalAnnounceKernelBlockRef.lean`), against which the announcement costs
exactly `0` (Renner 2005, arXiv:quant-ph/0512258v2, `main.tex:2917`, `\label{lem:Hminclasscondr}`).

The point of the construction is that the **reference** obtained by applying the same `Λ` to the
paired CKR/de Finetti state is state-independent, and carries the same domination constant:

* `sum_announceInstrument_eq_partialTraceA` — `Σ_p 𝓘_p = Tr_A`, so the block family assembled here
  refines the unlabelled reference exactly: its block sum is the CKR de Finetti state itself
  (`sum_pairedAnnounceReferenceOp_eq_ckrDeFinettiState`), with **no** extra factor;
* `announceInstrument_pairedTensorPow_opLe_choose_smul_pairedAnnounceReference` — the labelled
  Löwner domination, at the **same single** `g = C(n + d² − 1, d² − 1)`.  It is the image of the
  paired domination `ψ^{⊗n}(interleaved) ⪯ g · pairedDeFinettiState d n`
  (`pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow`) under `𝓘_p`, which is completely
  positive; nothing about the deep CKR content is re-proved and no second de Finetti factor appears.

The register convention follows `interleavingEquiv`: on `Op (d^n * d^n)` the **first** factor is the
measured system `A` (whose basis digits are the first components of the interleaved `(d·d)`-digits,
`interleavingEquiv d n`), and the **second** factor is the purifying register that carries the
conditioning information (`DensityOp.partialTraceA ψ` is its per-round marginal).  Hence `E_p` acts
on the first factor and `partialTraceA` removes it.

The reference is **singular** — `𝓘_p` compresses onto the range of `E_p ⊗ 1` — and nothing here
needs it to be positive definite: the block-reference announce charge supplies feasibility from its
`hblock` hypothesis rather than deriving it from a positive-definite reference
(`conditionalMinEntropyReal_tensorLeftKernel_blockDiagRef_ge`).

References: Renner 2005 (arXiv:quant-ph/0512258v2) `main.tex:2917` `\label{lem:Hminclasscondr}` and
`main.tex:2936` `\label{eq:classcondeq}` (an announced classical register is free against a
reference
that is classical on it); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851)
`main.tex:452` (the round-by-round announcements `C^n` sit in the conditioning register from the
start) and `main.tex:1393` `\label{eq:splittingoffV}` (the only chain-rule charge is `2 log g`, for
the purifying register); Christandl–König–Renner 2009 (arXiv:0809.3019) `\label{lem:extractpart}`
(main.tex:319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The instrument -/

/-- **The announce-instrument component at announced value `p`.**

`𝓘_p(X) = Tr_A[(E_p ⊗ 1) X (E_p ⊗ 1)]`: condition the measured factor `A` on the announced
measurement operator `E_p`, then trace `A` out, leaving the conditioning register `B`.

This is the standard measure-and-record instrument with the announced classical value peeled off
into its own register by `blockDiagRef`; it is completely positive, and it does not depend on the
state it is applied to. -/
def announceInstrument {dA dB : ℕ} (E : Op dA) (X : Op (dA * dB)) : Op dB :=
  partialTraceA (Op.tensor E (1 : Op dB) * X * Op.tensor E (1 : Op dB))

lemma announceInstrument_smul {dA dB : ℕ} (E : Op dA) (c : ℂ) (X : Op (dA * dB)) :
    announceInstrument E (c • X) = c • announceInstrument E X := by
  unfold announceInstrument
  rw [Matrix.mul_smul, Matrix.smul_mul, partialTraceA_smul]

lemma announceInstrument_isHermitian {dA dB : ℕ} (E : Op dA) (hE : Eᴴ = E)
    {X : Op (dA * dB)} (hX : X.IsHermitian) :
    (announceInstrument E X).IsHermitian :=
  partialTraceA_projector_sandwich_isHermitian E X hE hX

lemma announceInstrument_quadraticForm_re_nonneg {dA dB : ℕ} (E : Op dA) (hE : Eᴴ = E)
    {X : Op (dA * dB)} (hX : X.PosSemidef) :
    ∀ v : Fin dB → ℂ, 0 ≤ (quadraticForm (announceInstrument E X) v).re :=
  partialTraceA_projector_sandwich_quadraticForm_re_nonneg E X hE hX

/-- **The instrument is Löwner monotone** — the completely-positive step.

`𝓘_p` is the composition of the Kraus sandwich by the Hermitian `E_p ⊗ 1` with the partial trace,
both of which preserve the quadratic-form order, so a domination between two operators on the paired
register transports to the announced blocks **without changing the constant**. -/
lemma announceInstrument_opLe_mono {dA dB : ℕ} (E : Op dA) (hE : Eᴴ = E)
    {X Y : Op (dA * dB)} (h : opLe X Y) :
    opLe (announceInstrument E X) (announceInstrument E Y) := by
  unfold announceInstrument
  refine partialTraceA_opLe_of_opLe ?_
  have hK : (Op.tensor E (1 : Op dB))ᴴ = Op.tensor E (1 : Op dB) :=
    tensor_projector_one_hermitian hE
  have hsand := opLe_kraus_sandwich (Op.tensor E (1 : Op dB)) h
  rwa [hK] at hsand

/-! ## The announced measurement of a deterministic labelling of the computational basis -/

/-- The projector onto the computational-basis states carrying announced label `p`.

This is the announced measurement of a deterministic classical labelling `lab` of the measured
register's computational basis.  It exists for every `lab`, so the hypotheses
`(Hermitian, idempotent, resolving the identity)` carried by the constructions below are always
satisfiable — in particular at the BB84 PE-block labelling. -/
def diagLabelProj {dA dC : ℕ} (lab : Fin dA → Fin dC) (p : Fin dC) : Op dA :=
  Matrix.diagonal (fun k => if lab k = p then 1 else 0)

lemma diagLabelProj_isHermitian {dA dC : ℕ} (lab : Fin dA → Fin dC) (p : Fin dC) :
    (diagLabelProj lab p)ᴴ = diagLabelProj lab p := by
  unfold diagLabelProj
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  by_cases h : lab k = p <;> simp [h]

lemma diagLabelProj_idem {dA dC : ℕ} (lab : Fin dA → Fin dC) (p : Fin dC) :
    diagLabelProj lab p * diagLabelProj lab p = diagLabelProj lab p := by
  unfold diagLabelProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : lab k = p <;> simp [h]

lemma sum_diagLabelProj {dA dC : ℕ} (lab : Fin dA → Fin dC) :
    ∑ p : Fin dC, diagLabelProj lab p = (1 : Op dA) := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    simp only [diagLabelProj, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [Finset.sum_eq_single (lab i)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ (lab i)) h
  · simp [diagLabelProj, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-! ## The instrument components resolve the partial trace -/

/-- Reordering a triple sum so that the outermost index moves innermost. -/
private lemma sum_swap_outer_to_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → κ → ℂ) :
    (∑ x : ι, ∑ a : κ, ∑ c : κ, f x a c) = ∑ a : κ, ∑ c : κ, ∑ x : ι, f x a c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- **The instrument components resolve the partial trace: `Σ_p 𝓘_p = Tr_A`.**

For a family of Hermitian idempotents summing to the identity, the announced blocks add back up to
the unannounced marginal.  Entrywise the `A`-trace turns the double sandwich into `E_p · E_p = E_p`
and the family sum then collapses against `1`.

This is what makes the labelled reference a *refinement* of the unlabelled one rather than a
different object: no weight is created or destroyed by announcing. -/
theorem sum_announceInstrument_eq_partialTraceA {dA dB dC : ℕ}
    (E : Fin dC → Op dA) (hidem : ∀ p, E p * E p = E p) (hsum : ∑ p : Fin dC, E p = 1)
    (X : Op (dA * dB)) :
    ∑ p : Fin dC, announceInstrument (E p) X = partialTraceA X := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [announceInstrument, partialTraceA, Matrix.of_apply]
  simp_rw [tensor_one_mul_mul_tensor_one_apply]
  -- Collapse the `k`-sum in each announced block: `E_p · E_p = E_p`.
  have hblock : ∀ p : Fin dC,
      (∑ k : Fin dA, ∑ a : Fin dA, ∑ c : Fin dA,
          E p k a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) * E p c k)
        = ∑ a : Fin dA, ∑ c : Fin dA,
            E p c a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) := by
    intro p
    rw [sum_swap_outer_to_inner
      (fun k a c => E p k a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) * E p c k)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    have : (∑ k : Fin dA,
          E p k a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) * E p c k)
        = (∑ k : Fin dA, E p c k * E p k a) *
            X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, ← Matrix.mul_apply, hidem p]
  simp_rw [hblock]
  -- Collapse the `p`-sum against the resolution of the identity.
  rw [sum_swap_outer_to_inner
    (fun p a c => E p c a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)))]
  have hone : ∀ a c : Fin dA,
      (∑ p : Fin dC, E p c a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)))
        = (1 : Op dA) c a * X (finProdFinEquiv (a, i)) (finProdFinEquiv (c, j)) := by
    intro a c
    rw [← Finset.sum_mul, ← Matrix.sum_apply, hsum]
  simp_rw [hone, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The announced blocks carry exactly the total weight of the state they are the image of. -/
theorem sum_trace_announceInstrument {dA dB dC : ℕ}
    (E : Fin dC → Op dA) (hidem : ∀ p, E p * E p = E p) (hsum : ∑ p : Fin dC, E p = 1)
    (X : Op (dA * dB)) :
    ∑ p : Fin dC, (announceInstrument (E p) X).trace = X.trace := by
  rw [← Matrix.trace_sum, sum_announceInstrument_eq_partialTraceA E hidem hsum X,
    trace_partialTraceA]

/-! ## The two partial traces of the paired symmetric projector agree -/

/-- The `A`-marginal of the paired symmetric projector, as the same permutation-weighted average
that `partialTraceB_symmetricProjectorPaired_eq_weighted_sum` gives for the `B`-marginal:
`P_paired = (1/n!) Σ_σ U_σ ⊗ U_σ` is symmetric in its two factors. -/
lemma partialTraceA_symmetricProjectorPaired_eq_weighted_sum {d n : ℕ} [NeZero d] [NeZero n] :
    partialTraceA (symmetricProjectorPaired d n) =
      (1 / (Nat.factorial n : ℂ)) •
        ∑ σ : Equiv.Perm (Fin n),
          (Math.RepresentationTheory.permutationRepresentation d n σ).trace •
            Math.RepresentationTheory.permutationRepresentation d n σ := by
  unfold symmetricProjectorPaired
  rw [partialTraceA_smul, partialTraceA_finset_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  simpa using partialTraceA_tensor_op
    (Math.RepresentationTheory.permutationRepresentation d n σ)
    (Math.RepresentationTheory.permutationRepresentation d n σ)

lemma partialTraceA_symmetricProjectorPaired_eq_partialTraceB {d n : ℕ} [NeZero d] [NeZero n] :
    partialTraceA (symmetricProjectorPaired d n) = partialTraceB (symmetricProjectorPaired d n) :=
        by
  rw [partialTraceA_symmetricProjectorPaired_eq_weighted_sum,
    partialTraceB_symmetricProjectorPaired_eq_weighted_sum]

/-- The `A`-marginal of the paired de Finetti state is the CKR de Finetti state — the marginal the
unlabelled reference is built from. -/
lemma partialTraceA_pairedDeFinettiState_eq_ckrDeFinettiState {d n : ℕ} [NeZero d] [NeZero n] :
    partialTraceA (pairedDeFinettiState d n).toOp = (ckrDeFinettiState d n).toOp := by
  have htoOp : (pairedDeFinettiState d n).toOp =
      (1 / (symmetricProjectorPaired d n).trace) • symmetricProjectorPaired d n := by
    rw [pairedDeFinettiState_eq_of_neZero]; rfl
  rw [htoOp, partialTraceA_smul, partialTraceA_symmetricProjectorPaired_eq_partialTraceB,
    ckrDeFinettiState_toOp_eq_normalized_partialTraceB_symmetricProjectorPaired]

/-! ## The labelled reference -/

/-- **The announce-instrument image of the paired CKR de Finetti state**, block by announced value.

`ν_p = 𝓘_p(pairedDeFinettiState d n)` — the state-independent reference the labelled announcement is
scored against.  It is an explicit compression of a fixed state: no choice, no state dependence, and
its block sum is the CKR de Finetti state itself. -/
def pairedAnnounceReferenceOp {d n dC : ℕ} [NeZero d] (E : Fin dC → Op (d ^ n)) (p : Fin dC) :
    Op (d ^ n) :=
  announceInstrument (E p) (pairedDeFinettiState d n).toOp

lemma pairedAnnounceReferenceOp_isHermitian {d n dC : ℕ} [NeZero d]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (p : Fin dC) :
    (pairedAnnounceReferenceOp E p).IsHermitian :=
  announceInstrument_isHermitian (E p) (hHerm p)
    (posSemidefOp_implies_mathlib (pairedDeFinettiState d n).toPosSemidefOp).isHermitian

lemma pairedAnnounceReferenceOp_quadraticForm_re_nonneg {d n dC : ℕ} [NeZero d]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (p : Fin dC) :
    ∀ v : Fin (d ^ n) → ℂ, 0 ≤ (quadraticForm (pairedAnnounceReferenceOp E p) v).re :=
  announceInstrument_quadraticForm_re_nonneg (E p) (hHerm p)
    (posSemidefOp_implies_mathlib (pairedDeFinettiState d n).toPosSemidefOp)

/-- **The block sum of the labelled reference is the unlabelled reference** — the statement that
labelling costs no second de Finetti factor. -/
theorem sum_pairedAnnounceReferenceOp_eq_ckrDeFinettiState {d n dC : ℕ} [NeZero d] [NeZero n]
    (E : Fin dC → Op (d ^ n)) (hidem : ∀ p, E p * E p = E p) (hsum : ∑ p : Fin dC, E p = 1) :
    ∑ p : Fin dC, pairedAnnounceReferenceOp E p = (ckrDeFinettiState d n).toOp := by
  simp only [pairedAnnounceReferenceOp]
  rw [show (∑ p : Fin dC, announceInstrument (E p) (pairedDeFinettiState d n).toOp)
      = partialTraceA (pairedDeFinettiState d n).toOp from
    sum_announceInstrument_eq_partialTraceA E hidem hsum _]
  exact partialTraceA_pairedDeFinettiState_eq_ckrDeFinettiState

/-- The labelled reference blocks have total weight `1`. -/
theorem sum_trace_pairedAnnounceReferenceOp {d n dC : ℕ} [NeZero d] [NeZero n]
    (E : Fin dC → Op (d ^ n)) (hidem : ∀ p, E p * E p = E p) (hsum : ∑ p : Fin dC, E p = 1) :
    ∑ p : Fin dC, (pairedAnnounceReferenceOp E p).trace = 1 := by
  simp only [pairedAnnounceReferenceOp]
  rw [sum_trace_announceInstrument E hidem hsum (pairedDeFinettiState d n).toOp]
  exact (pairedDeFinettiState d n).trace_one

/-- Each labelled reference block has nonnegative real trace. -/
lemma pairedAnnounceReferenceOp_trace_re_nonneg {d n dC : ℕ} [NeZero d]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (p : Fin dC) :
    0 ≤ (pairedAnnounceReferenceOp E p).trace.re := by
  have hpsd : (pairedAnnounceReferenceOp E p).PosSemidef :=
    partialTraceA_projector_sandwich_posSemidef (E p) (pairedDeFinettiState d n).toOp (hHerm p)
      (posSemidefOp_implies_mathlib (pairedDeFinettiState d n).toPosSemidefOp)
  simpa using (Complex.le_def.mp hpsd.trace_nonneg).1

/-- **The labelled reference**, as a `SubDensityOp` on the conditioning register — a legal block
family for `blockDiagRef`. -/
def pairedAnnounceReference {d n dC : ℕ} [NeZero d] [NeZero n]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (hidem : ∀ p, E p * E p = E p)
    (hsum : ∑ p : Fin dC, E p = 1) (p : Fin dC) : SubDensityOp (d ^ n) where
  toOp := pairedAnnounceReferenceOp E p
  isHermitian := pairedAnnounceReferenceOp_isHermitian E hHerm p
  pos_semidef := pairedAnnounceReferenceOp_quadraticForm_re_nonneg E hHerm p
  trace_le_one := by
    have hsumtr : ∑ q : Fin dC, (pairedAnnounceReferenceOp E q).trace.re = 1 := by
      have h := sum_trace_pairedAnnounceReferenceOp E hidem hsum
      have := congrArg Complex.re h
      rwa [Complex.re_sum, Complex.one_re] at this
    have hle : (pairedAnnounceReferenceOp E p).trace.re
        ≤ ∑ q : Fin dC, (pairedAnnounceReferenceOp E q).trace.re :=
      Finset.single_le_sum
        (fun q _ => pairedAnnounceReferenceOp_trace_re_nonneg E hHerm q) (Finset.mem_univ p)
    rw [hsumtr] at hle
    exact hle

@[simp] lemma pairedAnnounceReference_toOp {d n dC : ℕ} [NeZero d] [NeZero n]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (hidem : ∀ p, E p * E p = E p)
    (hsum : ∑ p : Fin dC, E p = 1) (p : Fin dC) :
    (pairedAnnounceReference E hHerm hidem hsum p).toOp = pairedAnnounceReferenceOp E p := rfl

/-- The labelled reference is sub-normalised as a block family: exactly the hypothesis
`blockDiagRef` demands. -/
theorem sum_pairedAnnounceReference_trace_le_one {d n dC : ℕ} [NeZero d] [NeZero n]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p) (hidem : ∀ p, E p * E p = E p)
    (hsum : ∑ p : Fin dC, E p = 1) :
    ∑ p : Fin dC, (pairedAnnounceReference E hHerm hidem hsum p).trace ≤ 1 := by
  have h := sum_trace_pairedAnnounceReferenceOp E hidem hsum
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.one_re] at hre
  exact le_of_eq hre

/-! ## The labelled domination, at the same constant -/

/-- **The labelled CKR domination — completely-positive push-forward of the paired one.**

For a **pure** `ψ` on `ℂ^d ⊗ ℂ^d`, every announced block of the interleaved IID power is dominated
by
`g` times the corresponding block of the labelled reference, with
`g = C(n + d² − 1, d² − 1) = dim Sym^n(ℂ^{d²})` — the **same single** constant as the unlabelled
domination `ckrDeFinettiState_opGe_inv_choose_smul_tensorPow`, and no second de Finetti factor.

The proof applies `𝓘_p` — a Kraus sandwich followed by a partial trace, hence completely positive —
to both sides of `pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow`.  The deep CKR content
(`symmetricProjectorPaired_sandwich_pairedTensorPow`, Christandl–König–Renner 2009 main.tex:268–:401
(\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}`
:319–:328)
`lem:extractpart`) is reused verbatim; only the completely-positive map downstream of it changes,
from `Tr_A` to `𝓘_p`. -/
theorem announceInstrument_pairedTensorPow_opLe_choose_smul_pairedAnnounceReference
    {d n dC : ℕ} [NeZero d] [NeZero n] [NeZero (d * d)]
    (E : Fin dC → Op (d ^ n)) (hHerm : ∀ p, (E p)ᴴ = E p)
    (ψ : DensityOp (d * d)) (hψ : ψ.IsPure) (p : Fin dC) :
    opLe (announceInstrument (E p)
        (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp)
      ((↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) • pairedAnnounceReferenceOp E p) := by
  have hmono := announceInstrument_opLe_mono (E p) (hHerm p)
    (pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow d n ψ hψ)
  rwa [announceInstrument_smul] at hmono

/-- Re-encoding a triple register sum in the round-major function encoding. -/
private lemma sum_reindex_roundMajor_triple {d n : ℕ}
    (g : Fin (d ^ n) → Fin (d ^ n) → Fin (d ^ n) → ℂ) :
    (∑ T : Fin (d ^ n), ∑ A : Fin (d ^ n), ∑ C : Fin (d ^ n), g T A C) =
      ∑ T : Fin n → Fin d, ∑ A : Fin n → Fin d, ∑ C : Fin n → Fin d,
        g (finFunctionFinEquiv T) (finFunctionFinEquiv A) (finFunctionFinEquiv C) := by
  rw [← Equiv.sum_comp finFunctionFinEquiv (fun T => ∑ A : Fin (d ^ n), ∑ C : Fin (d ^ n), g T A C)]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← Equiv.sum_comp finFunctionFinEquiv
    (fun A => ∑ C : Fin (d ^ n), g (finFunctionFinEquiv T) A C)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [← Equiv.sum_comp finFunctionFinEquiv
    (fun C => g (finFunctionFinEquiv T) (finFunctionFinEquiv A) C)]

/-- Exchanging a triple sum over round-major strings with a product over rounds. -/
private lemma sum_roundMajor_prod_triple {d n : ℕ} (g : Fin n → Fin d → Fin d → Fin d → ℂ) :
    (∑ T : Fin n → Fin d, ∑ A : Fin n → Fin d, ∑ C : Fin n → Fin d,
        ∏ a : Fin n, g a (T a) (A a) (C a)) =
      ∏ a : Fin n, ∑ t : Fin d, ∑ x : Fin d, ∑ c : Fin d, g a t x c := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The announce instrument of a round-major tensor family factorises over rounds.**

For `E = ⊗_a F_a` acting on the measured register of the interleaved IID paired power `ψ^{⊗n}`, the
instrument image `Tr_A[(E ⊗ 1) ψ^{⊗n} (E ⊗ 1)]` is the round-major tensor product of the
single-round instrument images `Tr_A[(F_a ⊗ 1) ψ (F_a ⊗ 1)]`.

The Kraus sandwich by `E ⊗ 1` and the partial trace `Tr_A` both act factor-by-factor once `E` is a
product over rounds and the source is the interleaved IID power. -/
theorem announceInstrument_tensorFamily_interleavedTensorPowGen
    {d n : ℕ} [NeZero d] (F : Fin n → Op d) (ψ : DensityOp (d * d)) :
    announceInstrument (tensorFamily F)
        (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp =
      tensorFamily
        (fun a => partialTraceA
          (Op.tensor (F a) (1 : Op d) * ψ.toOp * Op.tensor (F a) (1 : Op d))) := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ n) := NeZero.pow
  ext V V'
  obtain ⟨Vf, rfl⟩ : ∃ f : Fin n → Fin d, V = finFunctionFinEquiv f :=
    ⟨finFunctionFinEquiv.symm V, (Equiv.apply_symm_apply _ _).symm⟩
  obtain ⟨V'f, rfl⟩ : ∃ f : Fin n → Fin d, V' = finFunctionFinEquiv f :=
    ⟨finFunctionFinEquiv.symm V', (Equiv.apply_symm_apply _ _).symm⟩
  -- The right-hand side, entrywise.
  have hRHS : (tensorFamily
        (fun a => partialTraceA
          (Op.tensor (F a) (1 : Op d) * ψ.toOp * Op.tensor (F a) (1 : Op d))))
        (finFunctionFinEquiv Vf) (finFunctionFinEquiv V'f) =
      ∏ a : Fin n, ∑ t : Fin d, ∑ x : Fin d, ∑ c : Fin d,
        F a t x * ψ.toOp (finProdFinEquiv (x, Vf a)) (finProdFinEquiv (c, V'f a)) * F a c t := by
    simp only [tensorFamily_apply_finFunctionFinEquiv]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    simp only [partialTraceA, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun t _ => tensor_one_mul_mul_tensor_one_apply _ _ _ _ _ _ _)
  rw [hRHS]
  -- The left-hand side, entrywise.
  simp only [announceInstrument, partialTraceA, Matrix.of_apply]
  simp_rw [tensor_one_mul_mul_tensor_one_apply]
  rw [sum_reindex_roundMajor_triple (d := d) (n := n)
    (fun T A C => tensorFamily F T A *
      (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp
        (finProdFinEquiv (A, finFunctionFinEquiv Vf))
        (finProdFinEquiv (C, finFunctionFinEquiv V'f)) *
      tensorFamily F C T)]
  have hstep : ∀ T A C : Fin n → Fin d,
      tensorFamily F (finFunctionFinEquiv T) (finFunctionFinEquiv A) *
          (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp
            (finProdFinEquiv (finFunctionFinEquiv A, finFunctionFinEquiv Vf))
            (finProdFinEquiv (finFunctionFinEquiv C, finFunctionFinEquiv V'f)) *
          tensorFamily F (finFunctionFinEquiv C) (finFunctionFinEquiv T) =
        ∏ a : Fin n, (F a (T a) (A a) *
          ψ.toOp (finProdFinEquiv (A a, Vf a)) (finProdFinEquiv (C a, V'f a)) *
          F a (C a) (T a)) := by
    intro T A C
    have hentry := interleaved_tensorPowGen_toOp_apply ψ A Vf C V'f
    rw [show Equiv.roundGroupEquiv d d n = (interleavingEquiv d n).symm from
      Equiv.ext fun _ => rfl] at hentry
    change (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp
      (finProdFinEquiv (finFunctionFinEquiv A, finFunctionFinEquiv Vf))
      (finProdFinEquiv (finFunctionFinEquiv C, finFunctionFinEquiv V'f)) = _ at hentry
    rw [hentry]
    simp only [tensorFamily_apply_finFunctionFinEquiv]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [hstep]
  exact sum_roundMajor_prod_triple
    (fun a t x c => F a t x * ψ.toOp (finProdFinEquiv (x, Vf a)) (finProdFinEquiv (c, V'f a)) *
      F a c t)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
