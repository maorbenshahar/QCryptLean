import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor

/-!
# Scalar finite-set algebra (B0)–(B3.1)

This helper module isolates the finite-set algebra lemmas that are part of the
(B0)–(B3.1) chain. These are honest proved results that may be reusable.

The decomposition is:

* (B0) `sum_indicator_mul_indicator` — collapse `∑_z 1[a=z]·1[b=z] = 1[a=b]`.
* (B1) `collision_count_eq_double_sum_indicators` — uncentred Gram identity.
* (B1c) `collision_count_sub_eq_double_sum_centred` — centred Gram identity.
* (B2) `scalar_two_universal_quadratic_rewrite` — rewrite the hash-weighted
  quadratic form as `(1/|S|) · ∑_s ∑_z (∑_x v(x) · (1[H s x = z] − 1/|Z|))²`
  (pure algebra, no universality).
* (B3.1) `scalar_two_universal_upper_bound_diag_off_split` — pure-algebra
  identity: rewrites the post-(B2) sum-of-squares form as
  `(1 − c) · ‖v‖² + offdiag`, where `offdiag` zeros out the diagonal.

The bound `∑_{x,x'} (τ x x' − c) · v x · v x' ≤ ∑_x (v x)^2` (the (♣)
inequality proper) requires an operator-level argument beyond this scalar
chain; it is stated and proved at the operator level in
`SeedAvgVarianceCore.lean` and `LambdaBoundSingleSigmaVariance.lean`.

This module deliberately does **not** depend on the matrix / Hermitian / HS-Gram
layer. It is purely real-arithmetic over finite types.
-/

noncomputable section

namespace InfoTheory.QuantumLHL

/-! ## (B0): Indicator collapse over `z` -/

/-- **Indicator collapse over `z` (B0).** For any two elements `a b : Z`,
the sum over `z` of the product of indicators `1[a=z] · 1[b=z]` equals
the single indicator `1[a=b]`. -/
lemma sum_indicator_mul_indicator
    {Z : Type*} [Fintype Z] [DecidableEq Z] (a b : Z) :
    ∑ z : Z, (if a = z then (1:ℝ) else 0) * (if b = z then (1:ℝ) else 0)
      = if a = b then (1:ℝ) else 0 := by
  have hpt : ∀ z : Z,
      (if a = z then (1:ℝ) else 0) * (if b = z then (1:ℝ) else 0)
        = if a = z then (if b = z then (1:ℝ) else 0) else 0 := by
    intro z; split_ifs <;> simp
  simp_rw [hpt]
  rw [Finset.sum_ite_eq Finset.univ a (fun z => if b = z then (1:ℝ) else 0)]
  simp [eq_comm]

/-- Helper: `∑_z 1[H.hash s x = z] = 1`. Each input hits exactly one bucket. -/
lemma sum_indicator_z_eq_one
    {S X Z : Type*} [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (s : S) (x : X) :
    ∑ z : Z, (if H.hash s x = z then (1:ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq Finset.univ (H.hash s x) (fun _ => (1:ℝ))]
  simp

/-! ## (B1): Pointwise Gram identity (uncentred) -/

/-- **Uncentred pointwise Gram identity (B1).** For each pair `x x' : X`,
the cardinality of the collision filter equals the double sum of indicator
products:
  `((filter card) : ℝ)
    = ∑_s ∑_z (1[H.hash s x = z]) · (1[H.hash s x' = z])`. -/
lemma collision_count_eq_double_sum_indicators
    {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (x x' : X) :
    ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
      = ∑ s : S, ∑ z : Z,
          (if H.hash s x = z then (1:ℝ) else 0) *
          (if H.hash s x' = z then (1:ℝ) else 0) := by
  calc ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
      = ∑ s : S, if H.hash s x = H.hash s x' then (1:ℝ) else 0 := by
        rw [Finset.sum_boole]
    _ = ∑ s : S, ∑ z : Z,
          (if H.hash s x = z then (1:ℝ) else 0) *
          (if H.hash s x' = z then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun s _ =>
          (sum_indicator_mul_indicator (H.hash s x) (H.hash s x')).symm)

/-! ## (B1c): Centred Gram identity -/

/-- **Centred pointwise Gram identity (B1c).** With `c := 1/|Z|`,
  `(filter card) − |S|·c = ∑_s ∑_z (1[H.hash s x = z] − c)·(1[H.hash s x' = z] − c)`.
This uses the indicator sum `∑_z 1[H.hash s x = z] = 1` and the cancellation
`c · |Z| = 1` (using `Nonempty Z`). -/
lemma collision_count_sub_eq_double_sum_centred
    {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (x x' : X) :
    ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
      - (Fintype.card S : ℝ) * (1 / (Fintype.card Z : ℝ))
      = ∑ s : S, ∑ z : Z,
          ((if H.hash s x = z then (1:ℝ) else 0) - (1 / (Fintype.card Z : ℝ))) *
          ((if H.hash s x' = z then (1:ℝ) else 0) - (1 / (Fintype.card Z : ℝ))) := by
  haveI : Nonempty Z := H.outputNonempty
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  -- `|Z|` is nonzero (via H.outputNonempty).
  have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
    have h : 0 < Fintype.card Z := Fintype.card_pos
    exact_mod_cast h
  have hZ_ne : (Fintype.card Z : ℝ) ≠ 0 := ne_of_gt hZ_pos
  have hcZ : c * (Fintype.card Z : ℝ) = 1 := by
    rw [hc_def]; field_simp
  -- Single-row indicator identities (B0 + each input hits exactly one bucket).
  have hZx : ∀ s : S, ∑ z : Z, (if H.hash s x = z then (1:ℝ) else 0) = 1 :=
    fun s => sum_indicator_z_eq_one H s x
  have hZx' : ∀ s : S, ∑ z : Z, (if H.hash s x' = z then (1:ℝ) else 0) = 1 :=
    fun s => sum_indicator_z_eq_one H s x'
  -- Aggregate identities over `S`.
  have h_diag :
      (∑ s : S, ∑ z : Z,
        (if H.hash s x = z then (1:ℝ) else 0) *
        (if H.hash s x' = z then (1:ℝ) else 0))
      = ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) :=
    (collision_count_eq_double_sum_indicators H x x').symm
  have h_xrow : (∑ s : S, ∑ z : Z, (if H.hash s x = z then (1:ℝ) else 0))
                = (Fintype.card S : ℝ) := by
    simp_rw [hZx]
    rw [Finset.sum_const]
    simp [Finset.card_univ]
  have h_x'row : (∑ s : S, ∑ z : Z, (if H.hash s x' = z then (1:ℝ) else 0))
                 = (Fintype.card S : ℝ) := by
    simp_rw [hZx']
    rw [Finset.sum_const]
    simp [Finset.card_univ]
  have h_const : (∑ _s : S, ∑ _z : Z, c * c)
                = c * c * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ)) := by
    simp [Finset.sum_const, Finset.card_univ, mul_comm, mul_assoc]
  -- Pointwise expansion `(a − c)(b − c) = ab − c·a − c·b + c²`.
  have h_each : ∀ s : S, ∀ z : Z,
      ((if H.hash s x = z then (1:ℝ) else 0) - c) *
        ((if H.hash s x' = z then (1:ℝ) else 0) - c)
      = (if H.hash s x = z then (1:ℝ) else 0) *
          (if H.hash s x' = z then (1:ℝ) else 0)
        - c * (if H.hash s x = z then (1:ℝ) else 0)
        - c * (if H.hash s x' = z then (1:ℝ) else 0)
        + c * c := by intros; ring
  -- Distribute the outer/inner sums over `+` and `−` after applying `h_each`.
  have h_expand_rhs :
      (∑ s : S, ∑ z : Z,
        ((if H.hash s x = z then (1:ℝ) else 0) - c) *
        ((if H.hash s x' = z then (1:ℝ) else 0) - c))
      = (∑ s : S, ∑ z : Z,
          (if H.hash s x = z then (1:ℝ) else 0) *
          (if H.hash s x' = z then (1:ℝ) else 0))
        - c * (∑ s : S, ∑ z : Z, (if H.hash s x = z then (1:ℝ) else 0))
        - c * (∑ s : S, ∑ z : Z, (if H.hash s x' = z then (1:ℝ) else 0))
        + (∑ _s : S, ∑ _z : Z, c * c) := by
    rw [show (∑ s : S, ∑ z : Z,
            ((if H.hash s x = z then (1:ℝ) else 0) - c) *
            ((if H.hash s x' = z then (1:ℝ) else 0) - c))
          = ∑ s : S, ∑ z : Z,
              ((if H.hash s x = z then (1:ℝ) else 0) *
                (if H.hash s x' = z then (1:ℝ) else 0)
                - c * (if H.hash s x = z then (1:ℝ) else 0)
                - c * (if H.hash s x' = z then (1:ℝ) else 0)
                + c * c) from
        Finset.sum_congr rfl (fun s _ =>
          Finset.sum_congr rfl (fun z _ => h_each s z))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  -- Combine and close by linear_combination using `hcZ`.
  rw [h_expand_rhs, h_diag, h_xrow, h_x'row, h_const]
  -- Goal: F − |S| · c = F − c · |S| − c · |S| + c·c · (|S| · |Z|).
  -- LHS − RHS = c · |S| · (1 − c · |Z|) = −c · |S| · (c · |Z| − 1), closed by hcZ.
  linear_combination (-c) * (Fintype.card S : ℝ) * hcZ

/-! ## (B2): Quadratic-form rewrite -/

/-- **Quadratic-form rewrite (B2).** The LHS of the scalar 2-universal L²
bound is rewritten as a non-negative quadratic form in `v`:
```
  ∑_{x,x'} ((1/|S|)·|{s : H s x = H s x'}| − 1/|Z|) · v(x) · v(x')
   = (1/|S|) · ∑_s ∑_z (∑_x v(x) · (1[H s x = z] − 1/|Z|))².
```
This is pure algebra (uses (B1c) + sum-swap + bilinearity); no universality. -/
lemma scalar_two_universal_quadratic_rewrite
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (v : X → ℝ) :
    ∑ x : X, ∑ x' : X,
      ((1 / (Fintype.card S : ℝ)) *
        ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) -
        (1 / (Fintype.card Z : ℝ))) * v x * v x'
    = (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ z : Z,
          (∑ x : X, v x * ((if H.hash s x = z then (1:ℝ) else 0) -
                            (1 / (Fintype.card Z : ℝ))))^2 := by
  haveI : Nonempty S := H.seedNonempty
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  set nSinv : ℝ := 1 / (Fintype.card S : ℝ) with hnSinv_def
  -- `|S|` is nonzero (via H.seedNonempty).
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    have h : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast h
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hSinv_S : nSinv * (Fintype.card S : ℝ) = 1 := by
    rw [hnSinv_def]; exact one_div_mul_cancel hS_ne
  -- Centred indicator abbreviation.
  set e : S → X → Z → ℝ := fun s x z =>
    (if H.hash s x = z then (1:ℝ) else 0) - c with he_def
  -- Step (i): rewrite the prefactor using the centred Gram identity (B1c).
  --   `(nSinv·F − c) = nSinv·(F − |S|·c) = nSinv · ∑_{s,z} e(s,x,z)·e(s,x',z)`.
  have h_pref : ∀ x x' : X,
      (nSinv *
        ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
      = nSinv * ∑ s : S, ∑ z : Z, e s x z * e s x' z := by
    intro x x'
    have h_centred := collision_count_sub_eq_double_sum_centred (Z := Z) H x x'
    -- `h_centred : F − |S|·(1/|Z|) = ∑_{s,z} (1[..=z]−c)·(1[..=z']−c)`.
    -- The RHS of `h_centred` matches `∑_{s,z} e(s,x,z)·e(s,x',z)` definitionally.
    have h_centred_e :
        ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
          - (Fintype.card S : ℝ) * c
          = ∑ s : S, ∑ z : Z, e s x z * e s x' z := by
      change ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
              - (Fintype.card S : ℝ) * (1 / (Fintype.card Z : ℝ))
              = _
      exact h_centred
    -- Multiply both sides by `nSinv`.
    have h_lhs_distrib :
        nSinv * (((Finset.univ.filter
                    (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
                  - (Fintype.card S : ℝ) * c)
          = nSinv * ((Finset.univ.filter
                        (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c := by
      have h : nSinv * ((Fintype.card S : ℝ) * c) = c := by
        rw [← mul_assoc, hSinv_S, one_mul]
      linarith [h]
    linarith [h_lhs_distrib, congrArg (nSinv * ·) h_centred_e]
  -- Per-(s,z) factorisation: `∑_{x,x'} e(s,x,z)·e(s,x',z)·v(x)·v(x') = (∑_x v(x)·e(s,x,z))²`.
  have h_factor : ∀ s : S, ∀ z : Z,
      (∑ x : X, ∑ x' : X, e s x z * v x * (e s x' z * v x'))
        = (∑ x : X, v x * e s x z) ^ 2 := by
    intro s z
    have h1 : (∑ x : X, ∑ x' : X, e s x z * v x * (e s x' z * v x'))
              = (∑ x : X, v x * e s x z) * (∑ x' : X, v x' * e s x' z) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
      ring
    rw [h1, sq]
  -- Now combine everything via a calc.
  calc (∑ x : X, ∑ x' : X,
        (nSinv *
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
          * v x * v x')
      = ∑ x : X, ∑ x' : X,
          (nSinv * ∑ s : S, ∑ z : Z, e s x z * e s x' z) * v x * v x' :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => by
          rw [h_pref x x']))
    _ = ∑ x : X, ∑ x' : X, ∑ s : S, ∑ z : Z,
          nSinv * (e s x z * v x * (e s x' z * v x')) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
        -- Goal: (nSinv · ∑_{s,z} e e) · v(x) · v(x') = ∑_{s,z} nSinv · (e·v · e·v).
        rw [show (nSinv * ∑ s : S, ∑ z : Z, e s x z * e s x' z) * v x * v x'
             = nSinv * v x * v x' * ∑ s : S, ∑ z : Z, e s x z * e s x' z from by ring]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        ring
    _ = ∑ s : S, ∑ z : Z, ∑ x : X, ∑ x' : X,
          nSinv * (e s x z * v x * (e s x' z * v x')) := by
        -- Reorder ∑x ∑x' ∑s ∑z = ∑s ∑z ∑x ∑x' by 4 adjacent swaps.
        -- Step 1: inside ∑x, swap x' with s.
        have step1 : (∑ x : X, ∑ x' : X, ∑ s : S, ∑ z : Z,
                        nSinv * (e s x z * v x * (e s x' z * v x')))
                  = (∑ x : X, ∑ s : S, ∑ x' : X, ∑ z : Z,
                        nSinv * (e s x z * v x * (e s x' z * v x'))) :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        -- Step 2: outer, swap x with s.
        have step2 : (∑ x : X, ∑ s : S, ∑ x' : X, ∑ z : Z,
                        nSinv * (e s x z * v x * (e s x' z * v x')))
                  = (∑ s : S, ∑ x : X, ∑ x' : X, ∑ z : Z,
                        nSinv * (e s x z * v x * (e s x' z * v x'))) :=
          Finset.sum_comm
        -- Step 3: inside ∑s ∑x, swap x' with z.
        have step3 : (∑ s : S, ∑ x : X, ∑ x' : X, ∑ z : Z,
                        nSinv * (e s x z * v x * (e s x' z * v x')))
                  = (∑ s : S, ∑ x : X, ∑ z : Z, ∑ x' : X,
                        nSinv * (e s x z * v x * (e s x' z * v x'))) :=
          Finset.sum_congr rfl (fun _ _ =>
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
        -- Step 4: inside ∑s, swap x with z.
        have step4 : (∑ s : S, ∑ x : X, ∑ z : Z, ∑ x' : X,
                        nSinv * (e s x z * v x * (e s x' z * v x')))
                  = (∑ s : S, ∑ z : Z, ∑ x : X, ∑ x' : X,
                        nSinv * (e s x z * v x * (e s x' z * v x'))) :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        rw [step1, step2, step3, step4]
    _ = ∑ s : S, ∑ z : Z, nSinv *
          (∑ x : X, ∑ x' : X, e s x z * v x * (e s x' z * v x')) := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun z _ => ?_))
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ s : S, ∑ z : Z, nSinv * (∑ x : X, v x * e s x z) ^ 2 := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun z _ => ?_))
        rw [h_factor s z]
    _ = nSinv * ∑ s : S, ∑ z : Z, (∑ x : X, v x * e s x z) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.mul_sum]

/-! ## (B3.1): Diagonal/off-diagonal split -/

/-- **Diagonal/off-diagonal split (B3.1).** Pure algebra, no universality.

With `c := 1/|Z|` and `τ x x' := (1/|S|) · |{s : H.hash s x = H.hash s x'}|`,
the post-(B2) sum-of-squares form decomposes as
```
  (1/|S|) · ∑_s ∑_z (∑_x v(x) · (1[H s x = z] − c))²
   = (1 − c) · ∑_x (v x)²
   + ∑_{x, x'} (if x = x' then 0 else (τ x x' − c)) · v x · v x'.
```
The diagonal contribution collapses because `τ(x, x) = 1`: the filter
`{s : H.hash s x = H.hash s x}` is all of `S`, so its cardinality is `|S|`,
divided by `|S|` gives `1`. -/
lemma scalar_two_universal_upper_bound_diag_off_split
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (v : X → ℝ) :
    (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ z : Z,
          (∑ x : X, v x * ((if H.hash s x = z then (1:ℝ) else 0) -
                            (1 / (Fintype.card Z : ℝ))))^2
      = (1 - 1 / (Fintype.card Z : ℝ)) * ∑ x : X, (v x)^2
        + ∑ x : X, ∑ x' : X,
            (if x = x' then (0:ℝ) else
              (1 / (Fintype.card S : ℝ)) *
                ((Finset.univ.filter
                    (fun s : S => H.hash s x = H.hash s x')).card : ℝ) -
                (1 / (Fintype.card Z : ℝ)))
              * v x * v x' := by
  haveI : Nonempty S := H.seedNonempty
  -- Convert post-(B2) form to pre-(B2) form via (B2) read backward.
  rw [← scalar_two_universal_quadratic_rewrite H v]
  -- Now split the pre-(B2) double sum into diagonal + off-diagonal.
  set nSinv : ℝ := 1 / (Fintype.card S : ℝ) with hnSinv_def
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  -- |S| > 0.
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    have h : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast h
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hSinv_S : nSinv * (Fintype.card S : ℝ) = 1 := by
    rw [hnSinv_def]; exact one_div_mul_cancel hS_ne
  -- Each summand splits as (diag piece) + (offdiag piece).
  have h_each : ∀ x x' : X,
      (nSinv *
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
        * v x * v x'
      = (if x = x' then (1 - c) * (v x)^2 else 0)
        + (if x = x' then (0:ℝ) else
            nSinv *
              ((Finset.univ.filter
                  (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
          * v x * v x' := by
    intro x x'
    by_cases hxx' : x = x'
    · -- Diagonal: filter = univ, so card = |S|, hence τ(x,x) = 1.
      subst hxx'
      have hfilter :
          (Finset.univ.filter (fun s : S => H.hash s x = H.hash s x))
            = (Finset.univ : Finset S) :=
        Finset.filter_true_of_mem (fun _ _ => rfl)
      rw [hfilter, if_pos rfl, if_pos rfl, Finset.card_univ]
      -- Goal: (nSinv * |S| - c) * v x * v x = (1 - c) * (v x)^2 + 0 * v x * v x
      have h_collapse :
          (nSinv * (Fintype.card S : ℝ) - c) * v x * v x
            = (1 - c) * (v x)^2 := by
        rw [show (nSinv * (Fintype.card S : ℝ) - c) * v x * v x
              = (nSinv * (Fintype.card S : ℝ) - c) * (v x)^2 from by ring,
            hSinv_S]
      linarith [h_collapse]
    · -- Off-diagonal: the diag piece is 0; the offdiag piece is itself.
      rw [if_neg hxx', if_neg hxx']
      ring
  -- Apply the pointwise split.
  have h_sum_split :
      (∑ x : X, ∑ x' : X,
          (nSinv *
            ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
            * v x * v x')
      = (∑ x : X, ∑ x' : X, if x = x' then (1 - c) * (v x)^2 else 0)
        + ∑ x : X, ∑ x' : X,
            (if x = x' then (0:ℝ) else
              nSinv *
                ((Finset.univ.filter
                    (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
              * v x * v x' := by
    rw [show (∑ x : X, ∑ x' : X,
              (nSinv *
                ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
                  - c) * v x * v x')
          = ∑ x : X, ∑ x' : X,
              ((if x = x' then (1 - c) * (v x)^2 else 0)
              + (if x = x' then (0:ℝ) else
                  nSinv *
                    ((Finset.univ.filter
                        (fun s : S => H.hash s x = H.hash s x')).card : ℝ) - c)
                * v x * v x') from
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => h_each x x'))]
    simp only [Finset.sum_add_distrib]
  rw [h_sum_split]
  -- Diagonal sum collapses via `Finset.sum_ite_eq`.
  have h_diag_collapse :
      (∑ x : X, ∑ x' : X, if x = x' then (1 - c) * (v x)^2 else 0)
        = (1 - c) * ∑ x : X, (v x)^2 := by
    have h : ∀ x : X, (∑ x' : X, if x = x' then (1 - c) * (v x)^2 else 0)
                  = (1 - c) * (v x)^2 := by
      intro x
      simp
    simp_rw [h]
    rw [Finset.mul_sum]
  rw [h_diag_collapse]

/-! ## Off-diagonal sign helpers -/

/-- The centered 2-universal collision coefficient is non-positive away from
the diagonal. -/
lemma quantumHash_offdiag_coeff_nonpos
    {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (hH : H.isUniversal)
    {x x' : X} (hxx' : x ≠ x') :
    (1 / (Fintype.card S : ℝ)) *
        ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) -
      1 / (Fintype.card Z : ℝ) ≤ 0 := by
  haveI : Nonempty S := H.seedNonempty
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have h_inv_nonneg : 0 ≤ 1 / (Fintype.card S : ℝ) := by positivity
  have hle := mul_le_mul_of_nonneg_left (hH x x' hxx') h_inv_nonneg
  have hcollapse :
      (1 / (Fintype.card S : ℝ)) *
          ((Fintype.card S : ℝ) / (Fintype.card Z : ℝ))
        = 1 / (Fintype.card Z : ℝ) := by
    field_simp [hS_ne]
  have hcoeff_le :
      (1 / (Fintype.card S : ℝ)) *
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
        ≤ 1 / (Fintype.card Z : ℝ) :=
    hcollapse ▸ hle
  linarith

/-- A finite off-diagonal sum with non-positive centered hash coefficients and
non-negative weights is non-positive. -/
lemma quantumHash_offdiag_weighted_sum_nonpos
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (hH : H.isUniversal)
    (G : X → X → ℝ) (hG_nonneg : ∀ x x' : X, 0 ≤ G x x') :
    ∑ x : X, ∑ x' : X,
      (if x = x' then (0 : ℝ) else
        (1 / (Fintype.card S : ℝ)) *
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ) -
          1 / (Fintype.card Z : ℝ)) *
      G x x' ≤ 0 := by
  refine Finset.sum_nonpos ?_
  intro x _
  refine Finset.sum_nonpos ?_
  intro x' _
  by_cases hxx' : x = x'
  · simp [hxx']
  · have hcoeff := quantumHash_offdiag_coeff_nonpos H hH hxx'
    exact mul_nonpos_of_nonpos_of_nonneg (by simpa [hxx'] using hcoeff) (hG_nonneg x x')

end InfoTheory.QuantumLHL

end -- noncomputable section
