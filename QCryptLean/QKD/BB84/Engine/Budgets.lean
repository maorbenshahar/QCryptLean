import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound

/-!
# BB84 general-`m` key-rate condition

The finite-size key-rate condition for BB84 with an announced parameter-estimation test of
general size `m`: it charges the error-correction syndrome, the error-verification tag, the
AEP smoothing penalty (at a fixed smoothing radius `ε_AEP`), and the `C(n+15,15)` de Finetti
postselection overhead against the secret-rate term at entropy argument `Q + 2δ`.

Correctness is by error verification: an `ℓEV`-bit tag comparison on the reconciled key, whose
real and ideal differ-and-accept blocks cost a total of `2·2^(−ℓEV)` in trace norm
(Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024,
arXiv:2403.11851, §V.C "Classical part", main.tex:906–919, the error-verification-by-hash-comparison
step at main.tex:917).

The privacy-amplification exponent is `n_K/4`: of the two leftover-hash caps,
`real_lhl_budget_at_key_rate_with_log_loss` concludes at `½·exp(−n_K/4·α)`, and
`real_lhl_budget_with_pa_loss` reaches `½·exp(−lpa)` only under
`ℓ·log 2 + loss + 2·lpa ≤ n_K·α`; neither reaches `exp(−n_K·α/2)`.

## Main definitions

- `QKD.BB84.Engine.basicKeyRateCondition`: the general-`m` key-rate condition.

References (paper `.tex` sources; `\label`s, not rendered equation numbers):
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) — the key-length and
error-correction-leakage decision rule `\label{eq:varlengthdecision}` (`main.tex:933`–`:940`), the
acceptance box `\label{eq:Vset}` (`:957`–`:959`) with its half-width `\label{eq:confinterval}`
(`:951`–`:954`), the secrecy composition `\label{eq:condS}` / `\label{eq:condLHL}` /
`\label{eq:condsecrecy}` (`:457`–`:472`), the postselection cost `\label{item:PScost}` (`:846`), and
§V.C `\subsection{Classical part}` (`:906`–`:919`);
Renner 2005 (arXiv:quant-ph/0512258v2) §6.5 `\label{sec:eQKD}` (`main.tex:7999`);
Christandl–König–Renner 2009 (arXiv:0809.3019), whose QKD application is `main.tex:403`–`:525` (the
paper is a REVTeX letter with no `\section` at all, so it has no numbered sections to cite).
-/

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.Engine

/-- **The general-`m` key-rate condition**: charges the error-correction syndrome
(`leakEC` bits) and the error-verification tag (`ℓEV` bits), the AEP smoothing penalty over the
key-round count `bb84KeyRoundCount n m = n − m` at the fixed smoothing radius `ε_AEP`, and
the `4·log C(n+15, 15)` de Finetti postselection overhead, against the secret-rate term at entropy
argument `Q + 2·δ`.

At `m = ⌈n/2⌉`, `n − m` is the key-round count `⌊n/2⌋`.

Dividing by `2 log 2` gives the purifier key-length charge `2 log₂ C(n+15,15)`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:913`, `\nkey = n − m`), inside
§V.C `\subsection{Classical part}` (`:906`); key-length rule `\label{eq:varlengthdecision}`
(`:933`–`:940`); postselection cost `\label{item:PScost}` (`:846`). Renner 2005 §6.5
`\label{sec:eQKD}` (`arXiv:quant-ph/0512258v2`, `main.tex:7999`); CKR 2009 (`arXiv:0809.3019`, QKD
application `main.tex:403`–`:525`). -/
def basicKeyRateCondition (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP : ℝ) : Prop :=
  2 * (ℓ : ℝ) * Real.log 2 + 2 * (leakEC : ℝ) * Real.log 2 +
      2 * (ℓEV : ℝ) * Real.log 2 +
      4 * Real.log
        (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) +
      2 * Real.log 2 *
        finiteSizePenalty (bb84KeyRoundCount n m) ε_AEP ≤
    (bb84KeyRoundCount n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ))

end QKD.BB84.Engine

end
