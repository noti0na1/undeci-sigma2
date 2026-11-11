import UndeciSigma2.Recurrence.Clauses

/-! # Completeness of the recurrence reduction

If the program recurs, the infinite trees of a recurring run, together with the helper trees,
satisfy the recurrence sentence over arbitrary trees. The counter comb of `d` has the spine
words `1ⁱ` and the teeth `1ʲ 0 0ˣ` for `x` at most the value of `d` at step `j`. For `n`
working states, the state tree has the spine words `1ⁱ` for `i < n`, the words `1^q 0 1ⁱ` for
`q < n`, and the stubs `1^q 0 1ʲ 0` with `q` the state at step `j`. These trees are in
general not regular.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree Sentence

namespace Recurrence

/-- The counter comb of counter `d` along an infinite sequence of configurations. -/
noncomputable def runComb (run : ℕ → Config) (d : Fin 2) : Tree :=
  sjoin {t | ∃ j, ∃ x ≤ (run j).counter d, t = path (tooth j x)}

/-- The state tree with `n` working states along an infinite sequence of configurations. -/
noncomputable def runStates (n : ℕ) (run : ℕ → Config) : Tree :=
  sjoin ({t | ∃ q < n, ∃ i, t = path (ones q ++ 0 :: ones i)} ∪
    {t | ∃ j, (run j).state < n ∧ t = path (ones (run j).state ++ 0 :: stub j)})

variable (run : ℕ → Config)

theorem mem_constructorPaths_runComb (d : Fin 2) (w : Word) :
    w ∈ (runComb run d).constructorPaths ↔
      (∃ i, w = ones i) ∨ ∃ j, ∃ x ≤ (run j).counter d, w = tooth j x := by
  rw [runComb, sjoin_constructorPaths, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨j, x, hx, rfl⟩, hw⟩
    rw [mem_constructorPaths_path, prefix_tooth_iff] at hw
    rcases hw with ⟨i, -, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j, y, hy.trans hx, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, x, hx, rfl⟩)
    · exact ⟨path (tooth i 0), ⟨i, 0, Nat.zero_le _, rfl⟩,
        (mem_constructorPaths_path _ _).mpr (prefix_tooth_iff.mpr (Or.inl ⟨i, le_rfl, rfl⟩))⟩
    · exact ⟨path (tooth j x), ⟨j, x, hx, rfl⟩,
        (mem_constructorPaths_path _ _).mpr List.prefix_rfl⟩

theorem mem_constructorPaths_runStates (n : ℕ) (w : Word) :
    w ∈ (runStates n run).constructorPaths ↔
      (∃ i < n, w = ones i) ∨ ∃ q < n, ∃ v, w = ones q ++ 0 :: v ∧
        ((∃ i, v = ones i) ∨ ∃ j, (run j).state = q ∧ v = stub j) := by
  rw [runStates, sjoin_constructorPaths, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨q, hq, i, rfl⟩ | ⟨j, hj, rfl⟩, hw⟩
    · rw [mem_constructorPaths_path, prefix_ones_append_zero_cons_iff] at hw
      rcases hw with ⟨i', hi', rfl⟩ | ⟨v, hv, rfl⟩
      · exact Or.inl ⟨i', by omega, rfl⟩
      · obtain ⟨i', -, rfl⟩ := prefix_ones_iff.mp hv
        exact Or.inr ⟨q, hq, ones i', rfl, Or.inl ⟨i', rfl⟩⟩
    · rw [mem_constructorPaths_path, prefix_ones_append_zero_cons_iff] at hw
      rcases hw with ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
      · exact Or.inl ⟨i, by omega, rfl⟩
      · rw [stub, prefix_tooth_iff] at hv
        rcases hv with ⟨i, -, rfl⟩ | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨_, hj, ones i, rfl, Or.inl ⟨i, rfl⟩⟩
        · obtain rfl : y = 0 := Nat.le_zero.mp hy
          exact Or.inr ⟨_, hj, stub j, rfl, Or.inr ⟨j, rfl, rfl⟩⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨q, hq, v, rfl, ⟨i, rfl⟩ | ⟨j, rfl, rfl⟩⟩)
    · exact ⟨_, Or.inl ⟨i, hi, 0, rfl⟩, (mem_constructorPaths_path _ _).mpr
        (prefix_ones_append_zero_cons_iff.mpr (Or.inl ⟨i, le_rfl, rfl⟩))⟩
    · exact ⟨_, Or.inl ⟨q, hq, i, rfl⟩, (mem_constructorPaths_path _ _).mpr List.prefix_rfl⟩
    · exact ⟨_, Or.inr ⟨j, hq, rfl⟩, (mem_constructorPaths_path _ _).mpr List.prefix_rfl⟩

@[simp] theorem topFree_runComb (d : Fin 2) : (runComb run d).TopFree := topFree_sjoin _

@[simp] theorem topFree_runStates (n : ℕ) : (runStates n run).TopFree := topFree_sjoin _

theorem isComb_runComb (d : Fin 2) : IsComb (runComb run d) := by
  intro w hw
  rcases (mem_constructorPaths_runComb run d w).mp hw with ⟨i, rfl⟩ | ⟨j, x, -, rfl⟩
  · exact Or.inl (isOnes_ones i)
  · exact Or.inr ⟨j, x, rfl⟩

theorem stubShaped_runStates (n q : ℕ) : StubShaped (runStates n run) q := by
  intro w hw
  rcases (mem_constructorPaths_runStates run n _).mp hw with ⟨i, -, h⟩ | ⟨q', -, v, h, hv⟩
  · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons q w)
  · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp h
    rcases hv with ⟨i, rfl⟩ | ⟨j, -, rfl⟩
    · exact Or.inl (isOnes_ones i)
    · exact Or.inr ⟨j, rfl⟩

theorem toothAt_runComb_iff (d : Fin 2) (j x : ℕ) :
    ToothAt (runComb run d) j x ↔ x ≤ (run j).counter d := by
  unfold ToothAt
  rw [mem_constructorPaths_runComb]
  constructor
  · rintro (⟨i, h⟩ | ⟨j', x', hx, h⟩)
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_tooth j x)
    · obtain ⟨rfl, rfl⟩ := tooth_inj.mp h
      exact hx
  · intro hx
    exact Or.inr ⟨j, x, hx, rfl⟩

theorem stubAt_runStates_iff (n q j : ℕ) :
    StubAt (runStates n run) q j ↔ q < n ∧ (run j).state = q := by
  unfold StubAt
  rw [mem_constructorPaths_runStates]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨q', hq', v, h, hv⟩)
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons q (stub j))
    · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp h
      rcases hv with ⟨i, h⟩ | ⟨j', hq, h⟩
      · exact absurd (h ▸ isOnes_ones i) (not_isOnes_stub j)
      · obtain rfl := stub_inj.mp h
        exact ⟨hq', hq⟩
  · rintro ⟨hq, rfl⟩
    exact Or.inr ⟨_, hq, stub j, rfl, Or.inr ⟨j, rfl, rfl⟩⟩

/-- The upper bound specification for the run comb of counter `d`, from a bound on the value
of `d` after each step from state `q`. -/
theorem upperBoundSpec_run {U : Tree} {d : Fin 2} {δ : ℕ} {trunc : Bool} {q : ℕ}
    (h : ∀ j, StubAt U q j → ∀ x, x ≤ (run (j + 1)).counter d → (trunc = true → 1 ≤ x) →
      x + δ ≤ (run j).counter d + 1) :
    UpperBoundSpec U (runComb run d) δ trunc q := by
  intro j x₁ x₂ hs h₁ h₂ ht
  rw [toothAt_runComb_iff] at h₁ h₂
  have := h j hs x₂ h₂ ht
  omega

/-- The lower bound specification for the run comb of counter `d`, from a bound on the value
of `d` after each step from state `q`. -/
theorem lowerBoundSpec_run {U : Tree} {d : Fin 2} {δ q : ℕ}
    (h : ∀ j, StubAt U q j → (run j).counter d + δ ≤ (run (j + 1)).counter d + 1) :
    LowerBoundSpec U (runComb run d) δ q := by
  intro j x₁ x₂ hs h₁ h₂
  rw [toothAt_runComb_iff] at h₁ h₂
  have := h j hs
  omega

/-- The run trees satisfy the initial conditions when the run starts in the initial
configuration and the program has a working state. -/
theorem initialConditions_run {n : ℕ} (hn : 0 < n) (h0 : run 0 = Config.init) :
    InitialConditions n (runComb run) (runStates n run) := by
  refine ⟨topFree_runComb run, topFree_runStates run n, fun d => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [f_le_iff topFree_e topFree_bot (topFree_runComb run d)]
    refine ⟨(mem_constructorPaths_runComb run d []).mpr (Or.inl ⟨0, rfl⟩),
      fun w hw => ?_, fun w hw => absurd hw (not_mem_constructorPaths_bot w)⟩
    rw [mem_constructorPaths_e] at hw
    subst hw
    exact (mem_constructorPaths_runComb run d _).mpr (Or.inr ⟨0, 0, Nat.zero_le _, rfl⟩)
  · rw [le_f_iff topFree_e topFree_full (topFree_runComb run d)]
    refine ⟨fun w hw => ?_, fun w _ => mem_constructorPaths_full w⟩
    rw [mem_constructorPaths_e]
    rcases (mem_constructorPaths_runComb run d _).mp hw with ⟨i, h⟩ | ⟨j, x, hx, h⟩
    · exact absurd h (zero_cons_ne_ones w i)
    · obtain ⟨rfl, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
      rw [h0] at hx
      simp only [Config.init_counter, Nat.le_zero] at hx
      subst hx
      rfl
  · rw [pack_le_iff ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩) (topFree_runStates run n)]
    refine ⟨fun i hi => ?_, fun w hw => ?_⟩
    · obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact (mem_constructorPaths_runStates run n _).mpr (Or.inl ⟨0, hn, rfl⟩)
    · rcases (mem_constructorPaths_f_e_bot w).mp hw with rfl | rfl
      · exact (mem_constructorPaths_runStates run n _).mpr
          (Or.inr ⟨0, hn, [], rfl, Or.inl ⟨0, rfl⟩⟩)
      · exact (mem_constructorPaths_runStates run n _).mpr
          (Or.inr ⟨0, hn, [0], rfl, Or.inr ⟨0, by rw [h0]; rfl, rfl⟩⟩)
  · rw [le_haltContext_iff (topFree_runStates run n)]
    intro w hw
    rcases (mem_constructorPaths_runStates run n _).mp hw with ⟨i, -, h⟩ | ⟨q, hq, v, h, -⟩
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons n w)
    · obtain ⟨rfl, -⟩ := ones_append_zero_cons_inj.mp h
      exact absurd hq (lt_irrefl _)

variable {run} {P : NProgram}

/-- The run trees satisfy the specifications of every instruction when consecutive
configurations are related by steps of the program. -/
theorem instructionSpecs_run (hstep : ∀ t, P.Step (run t) (run (t + 1))) :
    ∀ q ins, P[q]? = some ins →
      InstructionSpecs P.length (runComb run) (runStates P.length run) q ins := by
  intro q ins hq
  -- A step from a stub of `q` executes instruction `q`.
  have hexec : ∀ j, StubAt (runStates P.length run) q j → ins.Step (run j) (run (j + 1)) := by
    intro j hs
    obtain ⟨-, hjq⟩ := (stubAt_runStates_iff run _ q j).mp hs
    obtain ⟨i, hi, hstep'⟩ := hstep j
    rw [hjq, hq] at hi
    cases Option.some.inj hi
    exact hstep'
  -- Every next state is a working state with its stub at the next step.
  have hnext : ∀ j,
      StubAt (runStates P.length run) (min (run (j + 1)).state P.length) (j + 1) := by
    intro j
    have hlt := (hstep (j + 1)).state_lt_length
    rw [min_eq_left hlt.le]
    exact (stubAt_runStates_iff run _ _ _).mpr ⟨hlt, rfl⟩
  cases ins with
  | inc c r =>
    have hc : ∀ j, StubAt (runStates P.length run) q j →
        (run (j + 1)).counter c = (run j).counter c + 1 ∧
        (run (j + 1)).counter (otherCounter c) = (run j).counter (otherCounter c) ∧
        (run (j + 1)).state = r := by
      intro j hs
      rw [(NInstr.step_inc_iff c r _ _).mp (hexec j hs), Instr.exec_inc_counter,
        Instr.exec_inc_counter, Instr.exec_inc_state, ite_eq_right (otherCounter_ne c)]
      exact ⟨by simp, rfl, rfl⟩
    refine ⟨fun j hs => (hc j hs).2.2 ▸ hnext j,
      upperBoundSpec_run run fun j hs x hx _ => ?_,
      lowerBoundSpec_run run fun j hs => ?_,
      upperBoundSpec_run run fun j hs x hx _ => ?_,
      lowerBoundSpec_run run fun j hs => ?_⟩ <;>
    · have hcj := hc j hs
      omega
  | jzdec c z p =>
    have hc : ∀ j, StubAt (runStates P.length run) q j →
        (run (j + 1)).counter c = (run j).counter c - 1 ∧
        (run (j + 1)).counter (otherCounter c) = (run j).counter (otherCounter c) ∧
        (run (j + 1)).state = if (run j).counter c = 0 then z else p := by
      intro j hs
      rw [(NInstr.step_jzdec_iff c z p _ _).mp (hexec j hs)]
      by_cases h0 : (run j).counter c = 0
      · rw [Instr.exec_jzdec_of_eq_zero h0, ite_eq_left h0]
        exact ⟨by simp [h0], rfl, rfl⟩
      · rw [Instr.exec_jzdec_of_ne_zero h0, ite_eq_right h0]
        exact ⟨by simp, by simp [otherCounter_ne c], rfl⟩
    refine ⟨fun j hs h0 => ?_, fun j hs h1 => ?_,
      upperBoundSpec_run run fun j hs x hx hx₁ => ?_,
      lowerBoundSpec_run run fun j hs => ?_,
      fun j _ => (toothAt_runComb_iff run c _ 0).mpr (Nat.zero_le _),
      upperBoundSpec_run run fun j hs x hx _ => ?_,
      lowerBoundSpec_run run fun j hs => ?_⟩
    · -- the counter is zero: the next state is `z`
      have hz : (run j).counter c = 0 := by
        by_contra hne
        exact h0 ((toothAt_runComb_iff run c j 1).mpr (by omega))
      have := hnext j
      rwa [(hc j hs).2.2, ite_eq_left hz] at this
    · -- the counter is positive: the next state is `p`
      have hp : (run j).counter c ≠ 0 := by
        have := (toothAt_runComb_iff run c j 1).mp h1
        omega
      have := hnext j
      rwa [(hc j hs).2.2, ite_eq_right hp] at this
    · have hcj := hc j hs
      have hx₂ := hx₁ rfl
      omega
    all_goals
      have hcj := hc j hs
      omega
  | choice l r =>
    have hc : ∀ j, StubAt (runStates P.length run) q j →
        (run (j + 1)).counter = (run j).counter ∧
        ((run (j + 1)).state = l ∨ (run (j + 1)).state = r) := by
      intro j hs
      rcases (NInstr.step_choice_iff l r _ _).mp (hexec j hs) with h | h <;> rw [h]
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    refine ⟨fun j hs => ?_,
      upperBoundSpec_run run fun j hs x hx _ => ?_,
      lowerBoundSpec_run run fun j hs => ?_,
      upperBoundSpec_run run fun j hs x hx _ => ?_,
      lowerBoundSpec_run run fun j hs => ?_⟩
    · rcases (hc j hs).2 with h | h
      · exact Or.inl (h ▸ hnext j)
      · exact Or.inr (h ▸ hnext j)
    all_goals
      have hcj := congrFun (hc j hs).1
      first
        | (have := hcj 0; omega)
        | (have := hcj 1; omega)

/-- In the run trees, every step has exactly one state. -/
theorem uniquenessSpecs_run (n : ℕ) : UniquenessSpecs (runStates n run) n := by
  rintro r q hrq - j ⟨hq, hr⟩
  have e₁ := ((stubAt_runStates_iff run _ _ _).mp hq).2
  have e₂ := ((stubAt_runStates_iff run _ _ _).mp hr).2
  omega

/-- The run trees have stubs of state `0` at arbitrarily late steps when the run visits
state `0` infinitely often. -/
theorem recurrenceSpec_run {n : ℕ} (hn : 0 < n)
    (hrec : ∀ t, ∃ t', t ≤ t' ∧ (run t').state = 0) : RecurrenceSpec (runStates n run) := by
  intro t
  obtain ⟨t', ht', h0⟩ := hrec t
  exact ⟨t', ht', (stubAt_runStates_iff run _ _ _).mpr ⟨hn, h0⟩⟩

/-- The run trees of a recurring run satisfy all specifications. -/
theorem allSpecs_run (hstep : ∀ t, P.Step (run t) (run (t + 1)))
    (hrec : ∀ t, ∃ t', t ≤ t' ∧ (run t').state = 0) (hn : 0 < P.length) :
    AllSpecs P (runComb run) (runStates P.length run) :=
  ⟨instructionSpecs_run hstep, uniquenessSpecs_run _, recurrenceSpec_run hn hrec⟩

/-- Completeness: a recurring program satisfies the semantic content of the sentence. -/
theorem recurrenceConditions_of_recurs (h : P.Recurs) : RecurrenceConditions P := by
  have hn := h.length_pos
  obtain ⟨run, h0, hstep, hrec⟩ := h
  have hinit := initialConditions_run run hn h0
  exact ⟨runComb run, runStates P.length run, hinit, fun v hv =>
    allClauses_of_specs hinit.2.1 hinit.1 (isComb_runComb run) (stubShaped_runStates run _)
      (allSpecs_run hstep hrec hn) hv⟩

end Recurrence

end UndeciSigma2
