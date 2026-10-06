import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.TensorBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilationChannel
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementTransport
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothBipartiteRegularity
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SmoothUncertaintyRelation
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementUncertaintyInstances
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CanonicalPurification

/-!
# The measurement-dilation entropic uncertainty family

Aggregator for the entropic uncertainty layer built on the Stinespring dilation of two rank-one
projective measurements.  It contains no declarations of its own.

Reading order:

* `MeasurementDilation.lean` — the measurement dilation isometry `U`, the partial isometry
  `W = U Vᴴ`, the overlap constant `c` with `0 < c ≤ 1`, the preparation quality `q = log₂(1/c)`,
  and the operator feasibility transport `measDilation_mo6`;
* `ConcreteMeasurementBases.lean` — the computational and Walsh–Hadamard instances with
  `c = 2^{-n}`;
* `TensorBasis.lean` — tensor products and powers of measurements: `c` multiplies, `q` adds;
* `MeasurementDilationChannel.lean` — the conjugation-trace map is a completely positive
  trace-non-increasing sub-channel;
* `PureCoreUncertainty.lean` — the recovery identity `Ξ(ρ_ZZ′AB) = ρ_XB` and the trace
  bookkeeping;
* `MeasurementTransport.lean` — the `ε = 0` uncertainty relation
  `H_min(Z|Z′AB) ≤ H_min(X|B) − q`;
* `SmoothBipartiteRegularity.lean` — when the smooth optimization set is bounded above;
* `SmoothUncertaintyRelation.lean` — the ε-smooth relation;
* `MeasurementUncertaintyInstances.lean` — both relations at the computational/Walsh–Hadamard
  pair, where `q = n`, together with the negative instance showing the nonvanishing hypothesis of
  the `ε = 0` relation is necessary;
* `CanonicalPurification.lean` — the canonical purification as a `PureTripartite` and the
  associated dual-form quantity, not yet identified with fidelity-form max-entropy.

Source anchor: arXiv:1504.00233, `apps.tex`, section `sc:app-ucr` — the overlap constant
`eq:defc` (`apps.tex:174`), the dual-form inequality `eq:ucr-dual` (`apps.tex:198`) that the two
uncertainty relations here realize at `α = ∞`, and the `M_X ∘ U_Y` domination `apps.tex:209–213`
that is their operator core. The strictly stronger tripartite relation `th:ur`
(`apps.tex:183–192`) needs the min–max duality `pr:dual-new` and is *not* claimed.
-/
