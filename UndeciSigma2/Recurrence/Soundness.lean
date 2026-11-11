import UndeciSigma2.Recurrence.Clauses

/-! # Soundness of the recurrence reduction

If the recurrence sentence holds over arbitrary trees, the program recurs. The counter trees
and the state tree record a run of the program step by step: at step `j` the state tree has
the stub of the state `qⱼ`, which is a working state, and counter `d` has exactly the teeth of
depth at most its value. The run is built by recursion; at a `choice` instruction it follows a
branch whose stub is present. The positive root atom excludes stubs of the state `n`, so every
recorded state has an instruction and the run never stops. The recurrence clause gives stubs of
state `0` at arbitrarily late steps, and uniqueness identifies them with the recorded state.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree Sentence

namespace Recurrence

variable {P : NProgram} {C : Fin 2 → Tree} {U : Tree}

/-- The trees record the configuration `s` at step `j`: the state of `s` is one of the `n`
working states, the state tree has its stub at step `j`, and each counter tree has exactly the
teeth of depth at most the value of its counter. -/
def Records (n : ℕ) (C : Fin 2 → Tree) (U : Tree) (j : ℕ) (s : Config) : Prop :=
  s.state < n ∧ StubAt U s.state j ∧ ∀ d x, ToothAt (C d) j x ↔ x ≤ s.counter d

/-- The comb of state `n` has no stub. -/
theorem not_stubAt_of_initialConditions {n : ℕ} (h : InitialConditions n C U) (j : ℕ) :
    ¬StubAt U n j := fun hs =>
  not_isOnes_stub j ((le_haltContext_iff h.2.1 n).mp h.2.2.2.2 _ hs)

/-- At step zero the trees record the initial configuration. -/
theorem records_init {n : ℕ} (h : InitialConditions n C U) : Records n C U 0 Config.init := by
  have hn := not_stubAt_of_initialConditions h
  obtain ⟨hC, hU, hcounter, hstate, -⟩ := h
  have hs : StubAt U 0 0 := ((pack_le_iff (by simp) hU 0).mp hstate).2 (stub 0) (by simp)
  refine ⟨?_, hs, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd hs (hn 0)
    · exact hpos
  · intro d x
    simp only [Config.init_counter, Nat.le_zero]
    obtain ⟨hlo, hhi⟩ := hcounter d
    constructor
    · intro hx
      have hz := ((le_f_iff topFree_e topFree_full (hC d)).mp hhi).1 (zeros x) hx
      have he := (mem_constructorPaths_e _).mp hz
      have := congrArg List.length he
      simpa using this
    · rintro rfl
      exact ((f_le_iff topFree_e topFree_bot (hC d)).mp hlo).2.1 []
        nil_mem_constructorPaths_e

/-- From a recorded configuration, some step of the program leads to a configuration recorded
at the next step. -/
theorem exists_step_records (h : InitialConditions P.length C U)
    (hspec : ∀ q ins, P[q]? = some ins → InstructionSpecs P.length C U q ins)
    {j : ℕ} {s : Config} (hs : Records P.length C U j s) :
    ∃ t, P.Step s t ∧ Records P.length C U (j + 1) t := by
  obtain ⟨hlt, hstub, hc⟩ := hs
  obtain ⟨ins, hins⟩ : ∃ ins, P[s.state]? = some ins := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hspec' := hspec _ _ hins
  have hn := not_stubAt_of_initialConditions h
  -- A clipped target with a stub at the next step is a working state.
  have htarget : ∀ r, StubAt U (min r P.length) (j + 1) →
      r < P.length ∧ StubAt U r (j + 1) := by
    intro r hr
    by_cases hrn : r < P.length
    · exact ⟨hrn, by rwa [min_eq_left hrn.le] at hr⟩
    · rw [min_eq_right (not_lt.mp hrn)] at hr
      exact absurd hr (hn _)
  cases ins with
  | inc c r =>
    obtain ⟨ht, hu, hl, hu', hl'⟩ := hspec'
    obtain ⟨hr, hsr⟩ := htarget r (ht j hstub)
    refine ⟨(Instr.inc c r).exec s, ⟨_, hins, rfl⟩, hr, hsr, ?_⟩
    intro d x
    rcases eq_or_eq_otherCounter c d with hd | hd <;> subst d
    · simpa using toothAt_succ_iff_of_bounds hstub (hc c) hu hl
        (b := s.counter c + 1) (by omega) (by omega) x
    · simpa [otherCounter_ne] using
        toothAt_succ_iff_of_bounds hstub (hc (otherCounter c)) hu' hl'
          (b := s.counter (otherCounter c)) (by omega) (by omega) x
  | jzdec c z p =>
    obtain ⟨hz, hp, hu, hl, hnext, hu', hl'⟩ := hspec'
    have hdec := toothAt_succ_iff_of_decrement hstub (hc c) hu hl hnext
    have hcopy := toothAt_succ_iff_of_bounds hstub (hc (otherCounter c)) hu' hl'
      (b := s.counter (otherCounter c)) (by omega) (by omega)
    by_cases hc0 : s.counter c = 0
    · obtain ⟨hzl, hsz⟩ := htarget z (hz j hstub fun ht => by
        have := (hc c 1).mp ht
        omega)
      refine ⟨(Instr.jzdec c z p).exec s, ⟨_, hins, rfl⟩, ?_⟩
      rw [Instr.exec_jzdec_of_eq_zero hc0]
      refine ⟨hzl, hsz, ?_⟩
      intro d x
      rcases eq_or_eq_otherCounter c d with rfl | rfl
      · simpa [hc0] using hdec x
      · exact hcopy x
    · obtain ⟨hpl, hsp⟩ := htarget p (hp j hstub ((hc c 1).mpr (by omega)))
      refine ⟨(Instr.jzdec c z p).exec s, ⟨_, hins, rfl⟩, ?_⟩
      rw [Instr.exec_jzdec_of_ne_zero hc0]
      refine ⟨hpl, hsp, ?_⟩
      intro d x
      rcases eq_or_eq_otherCounter c d with rfl | rfl
      · simpa using hdec x
      · simpa [otherCounter_ne] using hcopy x
  | choice l r =>
    obtain ⟨hb, hu₀, hl₀, hu₁, hl₁⟩ := hspec'
    have hcopy : ∀ d x, ToothAt (C d) (j + 1) x ↔ x ≤ s.counter d := by
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact toothAt_succ_iff_of_bounds hstub (hc 0) hu₀ hl₀ (b := s.counter 0)
          (by omega) (by omega)
      · exact toothAt_succ_iff_of_bounds hstub (hc 1) hu₁ hl₁ (b := s.counter 1)
          (by omega) (by omega)
    rcases hb j hstub with hb' | hb'
    · obtain ⟨hl, hsl⟩ := htarget l hb'
      exact ⟨⟨l, s.counter⟩, ⟨_, hins, Or.inl rfl⟩, hl, hsl, hcopy⟩
    · obtain ⟨hr, hsr⟩ := htarget r hb'
      exact ⟨⟨r, s.counter⟩, ⟨_, hins, Or.inr rfl⟩, hr, hsr, hcopy⟩

/-- The trees record an infinite run of the program from the initial configuration. -/
theorem exists_run_records (h : InitialConditions P.length C U)
    (hspec : ∀ q ins, P[q]? = some ins → InstructionSpecs P.length C U q ins) :
    ∃ run : ℕ → Config, run 0 = Config.init ∧ (∀ t, P.Step (run t) (run (t + 1))) ∧
      ∀ j, Records P.length C U j (run j) := by
  let next (j : ℕ) (s : {s // Records P.length C U j s}) :
      {s // Records P.length C U (j + 1) s} :=
    ⟨Classical.choose (exists_step_records h hspec s.2),
      (Classical.choose_spec (exists_step_records h hspec s.2)).2⟩
  let seq (j : ℕ) : {s // Records P.length C U j s} :=
    Nat.rec (motive := fun j => {s // Records P.length C U j s}) ⟨Config.init, records_init h⟩
      next j
  exact ⟨fun j => (seq j).1, rfl,
    fun t => (Classical.choose_spec (exists_step_records h hspec (seq t).2)).1,
    fun j => (seq j).2⟩

/-- Trees satisfying the initial conditions and all specifications witness recurrence. -/
theorem recurs_of_specs (h : InitialConditions P.length C U) (hspec : AllSpecs P C U) :
    P.Recurs := by
  obtain ⟨hins, huniq, hrec⟩ := hspec
  obtain ⟨run, h0, hstep, hrun⟩ := exists_run_records h hins
  refine ⟨run, h0, hstep, fun t => ?_⟩
  obtain ⟨t', ht', hs0⟩ := hrec t
  refine ⟨t', ht', ?_⟩
  obtain ⟨hlt, hstub, -⟩ := hrun t'
  by_contra hne
  exact huniq 0 _ (Nat.pos_of_ne_zero hne) hlt t' ⟨hstub, hs0⟩

/-- Soundness: the semantic content of the recurrence sentence implies recurrence. -/
theorem recurs_of_recurrenceConditions (h : RecurrenceConditions P) : P.Recurs := by
  obtain ⟨C, U, hinit, hcl⟩ := h
  exact recurs_of_specs hinit (allSpecs_of_clauses hinit.2.1 hinit.1 hcl)

end Recurrence

end UndeciSigma2
