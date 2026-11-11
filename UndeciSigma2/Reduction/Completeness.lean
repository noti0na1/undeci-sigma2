import UndeciSigma2.Clauses.Complete

/-! # Completeness of the reduction

If the program halts at step `J`, the finite trees of its run, together with the helper
trees, satisfy the sentence.
The counter comb of `d` has the spine words `1ⁱ` for `i ≤ J` and the teeth `1ʲ 0 0ˣ` for
`j ≤ J` and `x` at most the value of `d` at step `j`. The state tree has the spine words
`1ⁱ` for `i ≤ n`, the words `1^q 0 1ⁱ` for `q ≤ n` and `i ≤ J`, and the stubs
`1^q 0 1ʲ 0` for `j ≤ J` with `q` the state at step `j` clipped to `n`.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Program

/-- A step increases a counter by at most one. -/
theorem counter_step_le (P : Program) (s : Config) (d : Fin 2) :
    (P.step s).counter d ≤ s.counter d + 1 := by
  rcases h : P[s.state]? with _ | ins
  · have hs : P.step s = s := by simp [step, h]
    rw [hs]
    omega
  · rw [step_of_getElem? h]
    cases ins with
    | inc c r =>
      rw [Instr.exec_inc_counter]
      split_ifs with hd
      · subst hd
        exact le_rfl
      · omega
    | jzdec c z p =>
      by_cases h0 : s.counter c = 0
      · rw [Instr.exec_jzdec_of_eq_zero h0]
        dsimp only
        omega
      · rw [Instr.exec_jzdec_of_ne_zero h0]
        dsimp only
        rw [Function.update_apply]
        split_ifs with hd
        · subst hd
          omega
        · omega

/-- After `t` steps every counter is at most `t`. -/
theorem counter_run_le (P : Program) (t : ℕ) (d : Fin 2) : (P.run t).counter d ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [run_succ]
    have := P.counter_step_le (P.run t) d
    omega

end Program

namespace Sentence

/-- The counter comb of counter `d` along the first `J` steps of the run. -/
noncomputable def runComb (P : Program) (J : ℕ) (d : Fin 2) : Tree :=
  sjoin {t | ∃ j ≤ J, ∃ x ≤ (P.run j).counter d, t = path (tooth j x)}

/-- The state tree along the first `J` steps of the run. -/
noncomputable def runStates (P : Program) (J : ℕ) : Tree :=
  sjoin ({t | ∃ q ≤ P.length, t = path (ones q ++ 0 :: ones J)} ∪
    {t | ∃ j ≤ J, t = path (ones (min (P.run j).state P.length) ++ 0 :: stub j)})

variable (P : Program) (J : ℕ)

theorem mem_constructorPaths_runComb (d : Fin 2) (w : Word) :
    w ∈ (runComb P J d).constructorPaths ↔
      (∃ i ≤ J, w = ones i) ∨ ∃ j ≤ J, ∃ x ≤ (P.run j).counter d, w = tooth j x := by
  rw [runComb, sjoin_constructorPaths, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨j, hj, x, hx, rfl⟩, hw⟩
    rw [mem_constructorPaths_path, prefix_tooth_iff] at hw
    rcases hw with ⟨i, hi, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨i, hi.trans hj, rfl⟩
    · exact Or.inr ⟨j, hj, y, hy.trans hx, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, x, hx, rfl⟩)
    · exact ⟨path (tooth i 0), ⟨i, hi, 0, Nat.zero_le _, rfl⟩,
        (mem_constructorPaths_path _ _).mpr (prefix_tooth_iff.mpr (Or.inl ⟨i, le_rfl, rfl⟩))⟩
    · exact ⟨path (tooth j x), ⟨j, hj, x, hx, rfl⟩,
        (mem_constructorPaths_path _ _).mpr List.prefix_rfl⟩

theorem mem_constructorPaths_runStates (w : Word) :
    w ∈ (runStates P J).constructorPaths ↔
      (∃ i ≤ P.length, w = ones i) ∨ ∃ q ≤ P.length, ∃ v, w = ones q ++ 0 :: v ∧
        ((∃ i ≤ J, v = ones i) ∨ ∃ j ≤ J, min (P.run j).state P.length = q ∧ v = stub j) := by
  rw [runStates, sjoin_constructorPaths, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨q, hq, rfl⟩ | ⟨j, hj, rfl⟩, hw⟩
    · rw [mem_constructorPaths_path, prefix_ones_append_zero_cons_iff] at hw
      rcases hw with ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
      · exact Or.inl ⟨i, hi.trans hq, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := prefix_ones_iff.mp hv
        exact Or.inr ⟨q, hq, ones i, rfl, Or.inl ⟨i, hi, rfl⟩⟩
    · have hq : min (P.run j).state P.length ≤ P.length := min_le_right _ _
      rw [mem_constructorPaths_path, prefix_ones_append_zero_cons_iff] at hw
      rcases hw with ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
      · exact Or.inl ⟨i, hi.trans hq, rfl⟩
      · rw [stub, prefix_tooth_iff] at hv
        rcases hv with ⟨i, hi, rfl⟩ | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨_, hq, ones i, rfl, Or.inl ⟨i, hi.trans hj, rfl⟩⟩
        · obtain rfl : y = 0 := Nat.le_zero.mp hy
          exact Or.inr ⟨_, hq, stub j, rfl, Or.inr ⟨j, hj, rfl, rfl⟩⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨q, hq, v, rfl, ⟨i, hi, rfl⟩ | ⟨j, hj, rfl, rfl⟩⟩)
    · exact ⟨_, Or.inl ⟨i, hi, rfl⟩, (mem_constructorPaths_path _ _).mpr
        (prefix_ones_append_zero_cons_iff.mpr (Or.inl ⟨i, le_rfl, rfl⟩))⟩
    · exact ⟨_, Or.inl ⟨q, hq, rfl⟩, (mem_constructorPaths_path _ _).mpr
        (prefix_ones_append_zero_cons_iff.mpr
          (Or.inr ⟨ones i, prefix_ones_iff.mpr ⟨i, hi, rfl⟩, rfl⟩))⟩
    · exact ⟨_, Or.inr ⟨j, hj, rfl⟩, (mem_constructorPaths_path _ _).mpr List.prefix_rfl⟩

@[simp] theorem topFree_runComb (d : Fin 2) : (runComb P J d).TopFree := topFree_sjoin _

@[simp] theorem topFree_runStates : (runStates P J).TopFree := topFree_sjoin _

theorem finite_runComb (d : Fin 2) : (runComb P J d).IsFinite := by
  apply finite_of_bounded (topFree_runComb P J d) (2 * J + 2)
  intro w hw
  rcases (mem_constructorPaths_runComb P J d w).mp hw with
    ⟨i, hi, rfl⟩ | ⟨j, hj, x, hx, rfl⟩
  · rw [length_ones]
    omega
  · have := P.counter_run_le j d
    rw [length_tooth]
    omega

theorem finite_runStates : (runStates P J).IsFinite := by
  apply finite_of_bounded (topFree_runStates P J) (P.length + J + 3)
  intro w hw
  rcases (mem_constructorPaths_runStates P J w).mp hw with
    ⟨i, hi, rfl⟩ | ⟨q, hq, v, rfl, ⟨i, hi, rfl⟩ | ⟨j, hj, -, rfl⟩⟩
  · rw [length_ones]
    omega
  · simp only [List.length_append, List.length_cons, length_ones]
    omega
  · simp only [List.length_append, List.length_cons, length_ones, stub, length_tooth]
    omega

theorem isComb_runComb (d : Fin 2) : IsComb (runComb P J d) := by
  intro w hw
  rcases (mem_constructorPaths_runComb P J d w).mp hw with ⟨i, -, rfl⟩ | ⟨j, -, x, -, rfl⟩
  · exact Or.inl (isOnes_ones i)
  · exact Or.inr ⟨j, x, rfl⟩

theorem stubShaped_runStates (q : ℕ) : StubShaped (runStates P J) q := by
  intro w hw
  rcases (mem_constructorPaths_runStates P J _).mp hw with ⟨i, -, h⟩ | ⟨q', -, v, h, hv⟩
  · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons q w)
  · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp h
    rcases hv with ⟨i, -, rfl⟩ | ⟨j, -, -, rfl⟩
    · exact Or.inl (isOnes_ones i)
    · exact Or.inr ⟨j, rfl⟩

theorem toothAt_runComb_iff (d : Fin 2) (j x : ℕ) :
    ToothAt (runComb P J d) j x ↔ j ≤ J ∧ x ≤ (P.run j).counter d := by
  unfold ToothAt
  rw [mem_constructorPaths_runComb]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨j', hj, x', hx, h⟩)
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_tooth j x)
    · obtain ⟨rfl, rfl⟩ := tooth_inj.mp h
      exact ⟨hj, hx⟩
  · rintro ⟨hj, hx⟩
    exact Or.inr ⟨j, hj, x, hx, rfl⟩

theorem stubAt_runStates_iff (q j : ℕ) :
    StubAt (runStates P J) q j ↔ j ≤ J ∧ min (P.run j).state P.length = q := by
  unfold StubAt
  rw [mem_constructorPaths_runStates]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨q', -, v, h, hv⟩)
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons q (stub j))
    · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp h
      rcases hv with ⟨i, -, h⟩ | ⟨j', hj', hq, h⟩
      · exact absurd (h ▸ isOnes_ones i) (not_isOnes_stub j)
      · obtain rfl := stub_inj.mp h
        exact ⟨hj', hq⟩
  · rintro ⟨hj, rfl⟩
    exact Or.inr ⟨_, min_le_right _ _, stub j, rfl, Or.inr ⟨j, hj, rfl, rfl⟩⟩

variable {P J}

/-- A step from a stub of a working state `q` executes instruction `q`, and the run has not
halted before the next step. -/
theorem step_of_stubAt (hJ : P.length ≤ (P.run J).state) {q j : ℕ} {ins : Instr}
    (hq : P[q]? = some ins) (h : StubAt (runStates P J) q j) :
    j + 1 ≤ J ∧ (P.run j).state = q ∧ P.run (j + 1) = ins.exec (P.run j) := by
  obtain ⟨hj, hmin⟩ := (stubAt_runStates_iff P J q j).mp h
  have hlt : q < P.length := (List.getElem?_eq_some_iff.mp hq).1
  have hs : (P.run j).state = q := by omega
  refine ⟨?_, hs, ?_⟩
  · rcases Nat.lt_or_ge j J with h' | h'
    · omega
    · obtain rfl : j = J := le_antisymm hj h'
      omega
  · rw [Program.run_succ]
    exact Program.step_of_getElem? (by rw [hs]; exact hq)

/-- The upper bound specification for the run comb of counter `d`, from a bound on the value
of `d` after each step from state `q`. -/
theorem upperBoundSpec_run {d : Fin 2} {δ : ℕ} {trunc : Bool} {q : ℕ}
    (h : ∀ j, StubAt (runStates P J) q j → j + 1 ≤ J ∧
      ∀ x, x ≤ (P.run (j + 1)).counter d → (trunc = true → 1 ≤ x) →
        x + δ ≤ (P.run j).counter d + 1) :
    UpperBoundSpec (runStates P J) (runComb P J d) δ trunc q := by
  intro j x₁ x₂ hs h₁ h₂ ht
  obtain ⟨hj, hx⟩ := h j hs
  rw [toothAt_runComb_iff] at h₁ h₂
  have h₃ : (P.run j).counter d < x₁ := by
    by_contra hc
    exact h₁ ⟨by omega, by omega⟩
  have := hx x₂ h₂.2 ht
  omega

/-- The lower bound specification for the run comb of counter `d`, from a bound on the value
of `d` after each step from state `q`. -/
theorem lowerBoundSpec_run {d : Fin 2} {δ q : ℕ}
    (h : ∀ j, StubAt (runStates P J) q j → j + 1 ≤ J ∧
      (P.run j).counter d + δ ≤ (P.run (j + 1)).counter d + 1) :
    LowerBoundSpec (runStates P J) (runComb P J d) δ q := by
  intro j x₁ x₂ hs h₁ h₂
  obtain ⟨hj, hx⟩ := h j hs
  rw [toothAt_runComb_iff] at h₁ h₂
  have h₃ : (P.run (j + 1)).counter d < x₂ := by
    by_contra hc
    exact h₂ ⟨hj, by omega⟩
  omega

/-- The run trees satisfy the initial conditions when the run has halted by step `J`. -/
theorem initialConditions_run (hJ : P.length ≤ (P.run J).state) :
    InitialConditions P.length (runComb P J) (runStates P J) := by
  refine ⟨topFree_runComb P J, topFree_runStates P J, fun d => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [f_le_iff topFree_e topFree_bot (topFree_runComb P J d)]
    refine ⟨(mem_constructorPaths_runComb P J d []).mpr (Or.inl ⟨0, Nat.zero_le _, rfl⟩),
      fun w hw => ?_, fun w hw => absurd hw (not_mem_constructorPaths_bot w)⟩
    rw [mem_constructorPaths_e] at hw
    subst hw
    exact (mem_constructorPaths_runComb P J d _).mpr
      (Or.inr ⟨0, Nat.zero_le _, 0, Nat.zero_le _, rfl⟩)
  · rw [le_f_iff topFree_e topFree_full (topFree_runComb P J d)]
    refine ⟨fun w hw => ?_, fun w _ => mem_constructorPaths_full w⟩
    rw [mem_constructorPaths_e]
    rcases (mem_constructorPaths_runComb P J d _).mp hw with ⟨i, -, h⟩ | ⟨j, -, x, hx, h⟩
    · exact absurd h (zero_cons_ne_ones w i)
    · obtain ⟨rfl, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
      simp only [Program.run_zero, Config.init_counter, Nat.le_zero] at hx
      subst hx
      rfl
  · rw [pack_le_iff ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩) (topFree_runStates P J)]
    refine ⟨fun i hi => ?_, fun w hw => ?_⟩
    · obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact (mem_constructorPaths_runStates P J _).mpr (Or.inl ⟨0, Nat.zero_le _, rfl⟩)
    · rcases (mem_constructorPaths_f_e_bot w).mp hw with rfl | rfl
      · exact (mem_constructorPaths_runStates P J _).mpr
          (Or.inr ⟨0, Nat.zero_le _, [], rfl, Or.inl ⟨0, Nat.zero_le _, rfl⟩⟩)
      · exact (mem_constructorPaths_runStates P J _).mpr
          (Or.inr ⟨0, Nat.zero_le _, [0], rfl, Or.inr ⟨0, Nat.zero_le _, by simp, rfl⟩⟩)
  · rw [le_haltContext_iff (topFree_runStates P J)]
    intro h
    exact not_isOnes_stub J
      (h _ ((stubAt_runStates_iff P J _ J).mpr ⟨le_rfl, min_eq_right hJ⟩))

/-- The run trees satisfy the specifications of every instruction when the run has
halted by step `J`. -/
theorem instructionSpecs_run (hJ : P.length ≤ (P.run J).state) :
    ∀ q ins, P[q]? = some ins →
      InstructionSpecs P.length (runComb P J) (runStates P J) q ins := by
  intro q ins hq
  have hlt : q < P.length := (List.getElem?_eq_some_iff.mp hq).1
  have huniq : HaltUniqueSpec (runStates P J) P.length q := by
    rintro j ⟨h₁, h₂⟩
    have e₁ := ((stubAt_runStates_iff P J _ _).mp h₁).2
    have e₂ := ((stubAt_runStates_iff P J _ _).mp h₂).2
    omega
  have hlast : ∀ j, StubAt (runStates P J) q j → j + 1 ≤ J :=
    fun j hs => (step_of_stubAt hJ hq hs).1
  have hnext : ∀ j, StubAt (runStates P J) q j → ∀ r,
      (P.run (j + 1)).state = r → StubAt (runStates P J) (min r P.length) (j + 1) := by
    rintro j hs r rfl
    exact (stubAt_runStates_iff P J _ _).mpr ⟨hlast j hs, rfl⟩
  cases ins with
  | inc c r =>
    have hc : ∀ j, StubAt (runStates P J) q j →
        (P.run (j + 1)).counter c = (P.run j).counter c + 1 ∧
        (P.run (j + 1)).counter (otherCounter c) = (P.run j).counter (otherCounter c) ∧
        (P.run (j + 1)).state = r := by
      intro j hs
      rw [(step_of_stubAt hJ hq hs).2.2, Instr.exec_inc_counter, Instr.exec_inc_counter,
        Instr.exec_inc_state, ite_eq_right (otherCounter_ne c)]
      exact ⟨by simp, rfl, rfl⟩
    refine ⟨huniq, fun j hs => hnext j hs r (hc j hs).2.2,
      upperBoundSpec_run fun j hs => ⟨hlast j hs, fun x hx _ => ?_⟩,
      lowerBoundSpec_run fun j hs => ⟨hlast j hs, ?_⟩,
      upperBoundSpec_run fun j hs => ⟨hlast j hs, fun x hx _ => ?_⟩,
      lowerBoundSpec_run fun j hs => ⟨hlast j hs, ?_⟩⟩ <;>
    · have hcj := hc j hs
      omega
  | jzdec c z p =>
    have hc : ∀ j, StubAt (runStates P J) q j →
        (P.run (j + 1)).counter c = (P.run j).counter c - 1 ∧
        (P.run (j + 1)).counter (otherCounter c) = (P.run j).counter (otherCounter c) ∧
        (P.run (j + 1)).state = if (P.run j).counter c = 0 then z else p := by
      intro j hs
      rw [(step_of_stubAt hJ hq hs).2.2]
      by_cases h0 : (P.run j).counter c = 0
      · rw [Instr.exec_jzdec_of_eq_zero h0, ite_eq_left h0]
        exact ⟨by simp [h0], rfl, rfl⟩
      · rw [Instr.exec_jzdec_of_ne_zero h0, ite_eq_right h0]
        exact ⟨by simp, by simp [otherCounter_ne c], rfl⟩
    refine ⟨huniq, fun j hs h0 => hnext j hs z ?_, fun j hs h0 => hnext j hs p ?_,
      upperBoundSpec_run fun j hs => ⟨hlast j hs, fun x hx hx₁ => ?_⟩,
      lowerBoundSpec_run fun j hs => ⟨hlast j hs, ?_⟩,
      fun j hs => (toothAt_runComb_iff P J c _ 0).mpr ⟨hlast j hs, Nat.zero_le _⟩,
      upperBoundSpec_run fun j hs => ⟨hlast j hs, fun x hx _ => ?_⟩,
      lowerBoundSpec_run fun j hs => ⟨hlast j hs, ?_⟩⟩
    · -- the counter is zero: the next state is `z`
      have hj := hlast j hs
      rw [(hc j hs).2.2, ite_eq_left]
      by_contra h1
      exact h0 ((toothAt_runComb_iff P J c j 1).mpr ⟨by omega, by omega⟩)
    · -- the counter is positive: the next state is `p`
      have h1 := ((toothAt_runComb_iff P J c j 1).mp h0).2
      rw [(hc j hs).2.2, ite_eq_right]
      omega
    · have hcj := hc j hs
      have hx₂ := hx₁ rfl
      omega
    all_goals
      have hcj := hc j hs
      omega

/-- Completeness: a halting program satisfies the semantic content of the sentence. -/
theorem machineConditions_of_halts {c : TreeClass} {top : Bool} (h : P.Halts) :
    MachineConditions c top P := by
  obtain ⟨J, hJ⟩ := h
  have hinit := initialConditions_run (P := P) (J := J) hJ
  refine ⟨runComb P J, runStates P J,
    fun d => domain_of_isFinite (finite_runComb P J d) (topFree_runComb P J d),
    domain_of_isFinite (finite_runStates P J) (topFree_runStates P J), hinit, ?_⟩
  intro v hv q ins hq
  exact instructionClauses_of_specs hinit.2.1 hinit.1 (isComb_runComb P J)
    (stubShaped_runStates P J q) (instructionSpecs_run hJ q ins hq)
    (hv.imp fun _ ha => ha.2)

end Sentence

end UndeciSigma2
