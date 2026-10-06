import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.QuantumLHL.HashingError

/-!
# IID security conditions

Acceptance tests and privacy amplification are expressed separately.
`SatisfiesPrivacyAmplificationBound` uses `hashingError` of extended smooth min-entropy; infinite
entropy has zero hashing error. `combinedSecrecy` combines the acceptance and hashing budgets.
-/

open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL

namespace InfoTheory.Postselection

/-- **Nahar et al. `\label{eq:condS}` (main.tex:457–:459)** (lines 505–508) for a chosen accepting
subset `S ⊆ S_σ̂`.

    `ε_AT ∈ [0,1]`, `S ⊆ S_σ̂`, and every fixed-marginal state outside `S` accepts with
    probability at most `ε_AT`:  `σ ∈ S_σ̂ \ S ⟹ Pr(Ω_acc)_σ ≤ ε_AT`.

    `Sσhat` is the fixed-marginal set `S_σ̂`; `pAcc σ = Pr(Ω_acc)_σ` is the accept
    probability on the IID input `σ^{⊗n}`. -/
def SatisfiesAcceptTestBound {ι : Type*} (Sσhat S : Set ι) (pAcc : ι → ℝ) (εAT : ℝ) : Prop :=
  εAT ∈ Set.Icc (0 : ℝ) 1 ∧ S ⊆ Sσhat ∧ ∀ σ ∈ Sσhat \ S, pAcc σ ≤ εAT

/-- **Nahar et al. `\label{eq:condS}` (main.tex:457–:459)**, "construct a set `S`" form: there
exists an accepting subset for
    which the accept-test bound holds. -/
def AcceptTestBoundHolds {ι : Type*} (Sσhat : Set ι) (pAcc : ι → ℝ) (εAT : ℝ) : Prop :=
  εAT ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ S : Set ι, S ⊆ Sσhat ∧ ∀ σ ∈ Sσhat \ S, pAcc σ ≤ εAT

/-- `SatisfiesAcceptTestBound` for some `S` yields the `∃ S` form. -/
theorem AcceptTestBoundHolds.of_satisfies {ι : Type*} {Sσhat S : Set ι} {pAcc : ι → ℝ}
    {εAT : ℝ} (h : SatisfiesAcceptTestBound Sσhat S pAcc εAT) :
    AcceptTestBoundHolds Sσhat pAcc εAT :=
  ⟨h.1, S, h.2.1, h.2.2⟩

/-- The IID privacy-amplification condition with extended smooth entropy and nonnegative
hashing budget and smoothing radius.
Infinite entropy leaves only the smoothing charge, including when the hashing budget is zero. -/
def SatisfiesPrivacyAmplificationBound {ι : Type*} {rawKeyDim condDim : ℕ}
    [NeZero rawKeyDim] [NeZero condDim]
    (S : Set ι) (pAcc condTraceDist : ι → ℝ)
    (rawKeyCQ : ι → CQState (Fin rawKeyDim) condDim)
    (ref : ι → SubDensityOp condDim)
    (l : ℕ) (εPA εbar : ℝ) : Prop :=
  0 ≤ εPA ∧ 0 ≤ εbar ∧
    ∀ σ ∈ S,
      (1 / 2 : ℝ) * pAcc σ * condTraceDist σ ≤
          hashingError l (smoothMinEntropy εbar (rawKeyCQ σ) (ref σ)) + 2 * εbar ∧
        hashingError l (smoothMinEntropy εbar (rawKeyCQ σ) (ref σ)) + 2 * εbar ≤
          εPA + 2 * εbar

/-- **Nahar et al. `\label{eq:condsecrecy}` (main.tex:470–:472)** combined secrecy parameter:
`\label{eq:condS}` (main.tex:457–:459) and `\label{eq:condLHL}` (main.tex:462–:467) together imply
    `ε_sec`-secrecy with `ε_sec = max {ε_AT, ε_PA + 2ε̄}` (line 520). -/
def combinedSecrecy (εAT εPA εbar : ℝ) : ℝ := max εAT (εPA + 2 * εbar)

/-- `combinedSecrecy` dominates the accept-test parameter. -/
theorem le_combinedSecrecy_left (εAT εPA εbar : ℝ) :
    εAT ≤ combinedSecrecy εAT εPA εbar :=
  le_max_left _ _

/-- `combinedSecrecy` dominates the privacy-amplification parameter. -/
theorem le_combinedSecrecy_right (εAT εPA εbar : ℝ) :
    εPA + 2 * εbar ≤ combinedSecrecy εAT εPA εbar :=
  le_max_right _ _

end InfoTheory.Postselection
