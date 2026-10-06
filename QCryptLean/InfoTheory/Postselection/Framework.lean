import QCryptLean.InfoTheory.DeFinetti.DeFinettiPrefactor
import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.Postselection.IIDProof
import QCryptLean.InfoTheory.Postselection.Mixture
import QCryptLean.InfoTheory.Postselection.MapSymmetry

/-!
# QKD postselection framework — shared layer (G0–G5)

Aggregator for the shared, protocol-generic postselection layer of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851). Every later
statement (Thm 3 / Cor 3.1 / Cor 3.2 / Cor 3.3, Def 8 / Thm 4) attaches to these
definitions.

- **G0** `InfoTheory.Postselection.PMQKDProtocol` — the generic PMQKD object
  `E_QKD ∈ C(AⁿBⁿ, K_A C̃_e)` (Section III A).
  Inhabited by `InfoTheory.Postselection.PMQKDProtocol.trivial`.
- **G1** `InfoTheory.DeFinetti.deFinettiPrefactor` — the exact penalty
  `g_{n,x} = C(n+x-1, x-1) = dim Sym^n(ℂ^x)` (Table I / main.tex:232–:234 (unlabeled; the
  `\cost`-domination bound opening \S2));
  `InfoTheory.DeFinetti.deFinettiPrefactor_eq_card_sym`,
  `InfoTheory.DeFinetti.deFinettiPrefactor_le_pow`.
- **G2** `InfoTheory.Postselection.IsFixedMarginalSecret` — Nahar et al. Definition 4, with the `½`
  baked in; teeth via `InfoTheory.Postselection.not_isFixedMarginalSecret_of_input_violation`,
  non-vacuous quantifier via `InfoTheory.Postselection.exists_fixedMarginal_input`.
- **G3** `InfoTheory.Postselection.SatisfiesAcceptTestBound` /
  `InfoTheory.Postselection.SatisfiesPrivacyAmplificationBound` /
  `InfoTheory.Postselection.combinedSecrecy` — the IID security-proof conditions
  `\label{eq:condS}` (main.tex:457–:459) / `\label{eq:condLHL}` (main.tex:462–:467) /
  `\label{eq:condsecrecy}` (main.tex:470–:472).
- **G4** `InfoTheory.Postselection.deFinettiMixtureFixedMarginal` /
  `InfoTheory.Postselection.deFinettiMixturePurification` — the main.tex:483–:486 (unlabeled; the
  `\tau_{A^nB^n}` mixture inside `\label{thm:maintheorem}` :481–:491) mixture `τ`
  and its purification `τ_R`.
- **G5** `InfoTheory.Postselection.IsPermutationInvariantMap` (Def 5, = `PermutationCovariant`),
  `InfoTheory.Postselection.IsIIDGroupInvariantMap` (Def 6),
  `InfoTheory.Postselection.IsIIDBlockDiagonalMap` (Def 7).
-/
