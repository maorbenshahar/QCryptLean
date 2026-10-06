import QCryptLean.LOCC.Typed.Program.Denotation
import QCryptLean.LOCC.Typed.Boundary.Graft

/-!
# Denotation of exit-dependent program grafting

A continuation graft is not composition with one continuation program: every complete public exit of
the base program selects a continuation with its own input multipartite system and output boundary.
This module packages that dependent family as one ordinary channel between the direct-sum boundary
spaces and identifies program grafting with composition by that exit-controlled channel.  The
continuation family remains dependent on the public exit throughout this construction.

The construction formalizes exit-dependent classical control in the finite-round LOCC instrument
trees of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II.
-/

open scoped Matrix BigOperators

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Program

/-- One Kraus matrix of an exit-controlled continuation family.

The rightmost adjoint exit inclusion extracts the selected base-exit block, the middle matrix runs
one hidden branch of that exit's continuation, and the leftmost graft inclusion writes the result
into the corresponding base-exit summand of the native grafted boundary space.
-/
noncomputable def controlledContinuationKraus {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    (e : B.Exit) (b : (k e).Branch) :
    Matrix (B.graft C).space B.space ℂ :=
  Boundary.graftInclKraus B C e *
    ((k e).kraus b * (Boundary.exitKraus B e)ᴴ)

/-- The Kraus matrices of an exit-controlled continuation family are complete on the base
boundary space. -/
theorem controlledContinuationKraus_complete {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    ∑ e : B.Exit, ∑ b : (k e).Branch,
      (controlledContinuationKraus k e b)ᴴ * controlledContinuationKraus k e b = 1 := by
  calc
    _ = ∑ e : B.Exit, Boundary.exitKraus B e *
        (∑ b : (k e).Branch, ((k e).kraus b)ᴴ * (k e).kraus b) *
          (Boundary.exitKraus B e)ᴴ := by
      apply Finset.sum_congr rfl
      intro e _
      calc
        _ = ∑ b : (k e).Branch, Boundary.exitKraus B e *
            (((k e).kraus b)ᴴ * (k e).kraus b) *
              (Boundary.exitKraus B e)ᴴ := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [controlledContinuationKraus, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
          rw [Matrix.mul_assoc
            (Boundary.exitKraus B e * ((k e).kraus b)ᴴ)
            (Boundary.graftInclKraus B C e)ᴴ
            (Boundary.graftInclKraus B C e *
              ((k e).kraus b * (Boundary.exitKraus B e)ᴴ)),
            ← Matrix.mul_assoc (Boundary.graftInclKraus B C e)ᴴ
              (Boundary.graftInclKraus B C e)
              ((k e).kraus b * (Boundary.exitKraus B e)ᴴ),
            Boundary.graftInclKraus_conjTranspose_mul_self, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ e : B.Exit,
        Boundary.exitKraus B e * (Boundary.exitKraus B e)ᴴ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [(k e).kraus_complete, Matrix.mul_one]
    _ = 1 := Boundary.sum_exitKraus_mul_conjTranspose B

/-- At a terminal base boundary, running a controlled continuation Kraus matrix after the unique
exit inclusion recovers the continuation Kraus matrix. -/
@[simp] theorem controlledContinuationKraus_leaf_mul_exitKraus (R : MultipartiteSystem P)
    {C : (Boundary.leaf R).Exit → Boundary P}
    (k : ∀ e : (Boundary.leaf R).Exit, Program ((Boundary.leaf R).system e) (C e))
    (b : (k ()).Branch) :
    controlledContinuationKraus k () b * Boundary.exitKraus (.leaf R) () =
      (k ()).kraus b := by
  rw [controlledContinuationKraus, Boundary.graftInclKraus_leaf]
  change (1 : Op (C ()).space) * ((k ()).kraus b *
    (Boundary.exitKraus (.leaf R) ())ᴴ) * Boundary.exitKraus (.leaf R) () = _
  rw [Matrix.one_mul, Matrix.mul_assoc,
    Boundary.exitKraus_conjTranspose_mul_self, Matrix.mul_one]

/-- Restricting a controlled continuation on an announced base boundary to the matching public
block is the corresponding child controlled continuation, included into the matching grafted
public block. -/
theorem controlledContinuationKraus_announce_mul_publicInclKraus
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P)
    {C : (Boundary.announce Y next).Exit → Boundary P}
    (k : ∀ e : (Boundary.announce Y next).Exit,
      Program ((Boundary.announce Y next).system e) (C e))
    (y : Y) (e : (next y).Exit) (b : (k ⟨y, e⟩).Branch) :
    controlledContinuationKraus k ⟨y, e⟩ b * Boundary.publicInclKraus next y =
      Boundary.publicInclKraus
          (fun z => (next z).graft fun f => C ⟨z, f⟩) y *
        controlledContinuationKraus (fun f => k ⟨y, f⟩) e b := by
  simp only [controlledContinuationKraus, Boundary.graftInclKraus_announce]
  let G := Boundary.graftInclKraus (next y) (fun f => C ⟨y, f⟩) e
  let K : Matrix (C ⟨y, e⟩).space ((next y).system e).total ℂ := (k ⟨y, e⟩).kraus b
  let E : Matrix (Boundary.announce Y next).space ((next y).system e).total ℂ :=
    Boundary.exitKraus (Boundary.announce Y next) ⟨y, e⟩
  let I := Boundary.publicInclKraus next y
  let F := Boundary.exitKraus (next y) e
  let J := Boundary.publicInclKraus (fun z => (next z).graft fun f => C ⟨z, f⟩) y
  change (J * G) * (K * Eᴴ) * I = J * (G * (K * Fᴴ))
  simp only [Matrix.mul_assoc]
  rw [show Eᴴ * I = Fᴴ from
    Boundary.exitKraus_announce_conjTranspose_mul_publicInclKraus next y e]

/-- Restricting a controlled-continuation Kraus matrix to a distinct outer public block gives the
rectangular zero matrix. -/
theorem controlledContinuationKraus_announce_mul_publicInclKraus_of_ne
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P)
    {C : (Boundary.announce Y next).Exit → Boundary P}
    (k : ∀ e : (Boundary.announce Y next).Exit,
      Program ((Boundary.announce Y next).system e) (C e))
    {y z : Y} (e : (next y).Exit) (b : (k ⟨y, e⟩).Branch) (h : y ≠ z) :
    controlledContinuationKraus k ⟨y, e⟩ b * Boundary.publicInclKraus next z = 0 := by
  simp only [controlledContinuationKraus, Matrix.mul_assoc]
  rw [Boundary.exitKraus_announce_conjTranspose_mul_publicInclKraus_of_ne next e h,
    Matrix.mul_zero, Matrix.mul_zero]

/-- The certified instrument implementing an exit-controlled continuation family.  Its unique
observed outcome is `Unit`; the selected base exit remains in the grafted boundary coordinate and
is not duplicated as an instrument outcome. -/
noncomputable def controlledContinuationInstrument {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    Instrument B.space (B.graft C).space Unit where
  krausIndex _ := Σ e : B.Exit, (k e).Branch
  kraus _ b := controlledContinuationKraus k b.1 b.2
  complete := by
    simpa only [Fintype.sum_unique, Fintype.sum_sigma] using
      controlledContinuationKraus_complete k

/-- The linear channel controlled by the complete public exit of a base boundary. -/
noncomputable def controlledContinuation {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    Op B.space →ₗ[ℂ] Op (B.graft C).space :=
  (controlledContinuationInstrument k).channel

/-- The controlled continuation is the sum over base exits and hidden continuation branches. -/
theorem controlledContinuation_eq_krausSum {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    controlledContinuation k =
      ∑ e : B.Exit, ∑ b : (k e).Branch,
        matrixConjLinear (controlledContinuationKraus k e b) := by
  simp only [controlledContinuation, controlledContinuationInstrument,
    Instrument.channel, Instrument.operation, Fintype.sum_unique]
  exact Fintype.sum_sigma _

/-- On the unique block of a terminal base boundary, the controlled family simply runs its sole
continuation. -/
theorem controlledContinuation_comp_denote_done (R : MultipartiteSystem P)
    {C : (Boundary.leaf R).Exit → Boundary P}
    (k : ∀ e : (Boundary.leaf R).Exit, Program ((Boundary.leaf R).system e) (C e)) :
    (controlledContinuation k).comp (Program.done : Program R (.leaf R)).denote =
      (k ()).denote := by
  apply LinearMap.ext
  intro ρ
  change controlledContinuation k ((Program.done : Program R (.leaf R)).denote ρ) =
    (k ()).denote ρ
  rw [controlledContinuation_eq_krausSum, (k ()).denote_eq_krausSum,
    (Program.done : Program R (.leaf R)).denote_eq_krausSum]
  have houter :
      (∑ e : (Boundary.leaf R).Exit, ∑ b : (k e).Branch,
        matrixConjLinear (controlledContinuationKraus k e b)) =
      ∑ b : (k ()).Branch, matrixConjLinear (controlledContinuationKraus k () b) := by
    apply Finset.sum_eq_single ()
    · intro e _ he
      exact (he (Subsingleton.elim _ _)).elim
    · intro he
      exact (he (Finset.mem_univ ())).elim
  rw [houter]
  simp only [Branch, Fintype.sum_unique, LinearMap.sum_apply]
  have hdone : (Program.done : Program R (.leaf R)).kraus () =
      Boundary.exitKraus (.leaf R) () := by
    exact Matrix.mul_one _
  rw [hdone]
  apply Finset.sum_congr rfl
  intro b _
  change ((matrixConjLinear (controlledContinuationKraus k () b)).comp
    (matrixConjLinear (Boundary.exitKraus (.leaf R) ()))) ρ =
      matrixConjLinear ((k ()).kraus b) ρ
  rw [← matrixConjLinear_mul, controlledContinuationKraus_leaf_mul_exitKraus]
  rfl

/-- Exit-controlled continuation commutes with entering a selected outer public block.  The
continuations on all other public blocks vanish under the matching block extraction. -/
theorem controlledContinuation_comp_publicInclKraus
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P)
    {C : (Boundary.announce Y next).Exit → Boundary P}
    (k : ∀ e : (Boundary.announce Y next).Exit,
      Program ((Boundary.announce Y next).system e) (C e))
    (y : Y) :
    (controlledContinuation k).comp (matrixConjLinear (Boundary.publicInclKraus next y)) =
      (matrixConjLinear (Boundary.publicInclKraus
        (fun z => (next z).graft fun f => C ⟨z, f⟩) y)).comp
          (controlledContinuation (fun f => k ⟨y, f⟩)) := by
  apply LinearMap.ext
  intro ρ
  change controlledContinuation k (matrixConjLinear (Boundary.publicInclKraus next y) ρ) =
    matrixConjLinear
      (Boundary.publicInclKraus (fun z => (next z).graft fun f => C ⟨z, f⟩) y)
      (controlledContinuation (fun f => k ⟨y, f⟩) ρ)
  rw [controlledContinuation_eq_krausSum, controlledContinuation_eq_krausSum]
  have hsigma :
      (∑ e : (Boundary.announce Y next).Exit,
        ∑ b : (k e).Branch, matrixConjLinear (controlledContinuationKraus k e b)) =
      ∑ z : Y, ∑ e : (next z).Exit, ∑ b : (k ⟨z, e⟩).Branch,
        matrixConjLinear (controlledContinuationKraus k ⟨z, e⟩ b) := by
    simpa only [Boundary.Exit, Boundary.instFintypeExit] using
      (Fintype.sum_sigma (fun e : (Boundary.announce Y next).Exit =>
        ∑ b : (k e).Branch, matrixConjLinear (controlledContinuationKraus k e b)))
  rw [hsigma]
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single y]
  · apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro b _
    change ((matrixConjLinear (controlledContinuationKraus k ⟨y, e⟩ b)).comp
        (matrixConjLinear (Boundary.publicInclKraus next y))) ρ =
      ((matrixConjLinear (Boundary.publicInclKraus
        (fun z => (next z).graft fun f => C ⟨z, f⟩) y)).comp
        (matrixConjLinear (controlledContinuationKraus (fun f => k ⟨y, f⟩) e b))) ρ
    rw [← matrixConjLinear_mul, ← matrixConjLinear_mul,
      controlledContinuationKraus_announce_mul_publicInclKraus]
    rfl
  · intro z _ hzy
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro b _
    change ((matrixConjLinear (controlledContinuationKraus k ⟨z, e⟩ b)).comp
      (matrixConjLinear (Boundary.publicInclKraus next y))) ρ = 0
    rw [← matrixConjLinear_mul,
      controlledContinuationKraus_announce_mul_publicInclKraus_of_ne next k e b hzy,
      matrixConjLinear]
    simp
  · simp

/-- Grafting a dependent continuation family denotes composition by its exit-controlled channel.

No single continuation is asserted: `controlledContinuation k` first extracts the complete public
exit of the base boundary and then runs the corresponding member of `k`.  Its output is in native
`(B.graft C).space` coordinates; `Boundary.graftSpaceEquiv` is oriented from those native
coordinates to `Σ e : B.Exit, (C e).space`.

This is sequential composition with public-history-dependent continuation in the finite-round
LOCC instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583,
Section II.
-/
theorem denote_graft {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    (p.graft k).denote = (controlledContinuation k).comp p.denote := by
  induction p with
  | done =>
      exact (controlledContinuation_comp_denote_done _ k).symm
  | @announced R Y _ _ A B next ih =>
      rw [graft_announced, denote_announced]
      conv_lhs =>
        tactic => exact denote_announced A (fun y => (next y).graft (fun e => k ⟨y, e⟩))
      have hdist :
          (controlledContinuation k).comp
              (∑ o : A.Outcome, ∑ r : A.krausIndex o,
                (matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
                  ((next (A.announce o)).denote.comp
                    (matrixConjLinear (A.liftedKraus o r)))) =
            ∑ o : A.Outcome, ∑ r : A.krausIndex o,
              (controlledContinuation k).comp
                ((matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
                  ((next (A.announce o)).denote.comp
                    (matrixConjLinear (A.liftedKraus o r)))) := by
        apply LinearMap.ext
        intro ρ
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      rw [hdist]
      apply Finset.sum_congr rfl
      intro o _
      apply Finset.sum_congr rfl
      intro r _
      have hchild := ih (A.announce o)
        (C := fun e => C ⟨A.announce o, e⟩)
        (fun e => k ⟨A.announce o, e⟩)
      have hblock := controlledContinuation_comp_publicInclKraus B k (A.announce o)
      rw [hchild]
      apply LinearMap.ext
      intro ρ
      have hblockApply := LinearMap.congr_fun hblock
        ((next (A.announce o)).denote (matrixConjLinear (A.liftedKraus o r) ρ))
      simpa only [LinearMap.comp_apply] using hblockApply.symm
  | @priv R B A next ih =>
      rw [graft_priv, denote_priv, denote_priv, ih]
      apply LinearMap.ext
      intro ρ
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]

/-- A controlled-continuation Kraus matrix has no row support outside its selected base-exit
summand in graft coordinates. -/
theorem controlledContinuationKraus_apply_eq_zero_of_exit_ne {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {e f : B.Exit} (h : e ≠ f) (b : (k f).Branch) (a : (C e).space)
    (x : B.space) :
    controlledContinuationKraus k f b
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩) x = 0 := by
  simp only [controlledContinuationKraus, Matrix.mul_apply,
    Boundary.graftInclKraus_apply, Equiv.apply_symm_apply]
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg, zero_mul]
  intro heq
  exact h (congrArg Sigma.fst heq)

/-- The output of an exit-controlled continuation has zero entries between distinct base-exit
summands, for every ambient input operator. -/
theorem controlledContinuation_block_zero {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (ρ : Op B.space)
    {e f : B.Exit} (hef : e ≠ f) (a : (C e).space) (c : (C f).space) :
    controlledContinuation k ρ
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩)
        ((Boundary.graftSpaceEquiv B C).symm ⟨f, c⟩) = 0 := by
  rw [controlledContinuation_eq_krausSum]
  simp only [LinearMap.sum_apply, matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro g _
  apply Finset.sum_eq_zero
  intro b _
  by_cases he : e = g
  · have hf : f ≠ g := fun h => hef (he.trans h.symm)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [controlledContinuationKraus_apply_eq_zero_of_exit_ne k hf b c x,
      star_zero, mul_zero]
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [show (∑ j, controlledContinuationKraus k g b
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩) j * ρ j x) = 0 by
      apply Finset.sum_eq_zero
      intro j _
      rw [controlledContinuationKraus_apply_eq_zero_of_exit_ne k he b a j, zero_mul],
      zero_mul]

/-- Restricting a controlled continuation to one output summand runs exactly the selected
continuation on the corresponding extracted input block. -/
theorem controlledContinuation_sameExit {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (rho : Op B.space)
    (e : B.Exit) (a b : (C e).space) :
    controlledContinuation k rho
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩)
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, b⟩) =
      (k e).denote ((Boundary.exitKraus B e)ᴴ * rho * Boundary.exitKraus B e) a b := by
  rw [controlledContinuation_eq_krausSum, (k e).denote_eq_krausSum]
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single e]
  · apply Finset.sum_congr rfl
    intro branch _
    simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
      controlledContinuationKraus]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_apply, Boundary.graftInclKraus_apply, Equiv.apply_symm_apply,
      Sigma.mk.injEq, heq_eq_eq, true_and, Matrix.conjTranspose_apply, Boundary.exitKraus_apply,
      RCLike.star_def, MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_ite_eq']
    conv_lhs =>
      rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single e]
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      · rw [Fintype.sum_sigma, Finset.sum_eq_single e]
        · simp
        · intro f _ hfe
          simp [hfe]
        · simp
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        rw [if_neg]
        intro hxy
        apply hy
        exact eq_of_heq ((Sigma.mk.inj_iff.mp hxy).2.symm)
      · simp
    · intro f _ hfe
      simp [hfe]
    · simp
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro branch _
    simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    have hinner : (∑ j, controlledContinuationKraus k f branch
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩) j * rho j x) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [controlledContinuationKraus_apply_eq_zero_of_exit_ne
        k (Ne.symm hfe) branch a j, zero_mul]
    rw [hinner, zero_mul]
  · simp

/-- The exit-controlled continuation is CPTP after any explicit finite coordinate choices. -/
theorem coordinateControlledContinuation_isCPTP {B : Boundary P}
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {dB dG : ℕ} [NeZero dB] [NeZero dG]
    (eB : B.space ≃ Fin dB) (eG : (B.graft C).space ≃ Fin dG) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eB eG (controlledContinuation k)) := by
  exact (controlledContinuationInstrument k).coordinateChannel_isCPTP eB eG

end Program
end TypedLOCC
