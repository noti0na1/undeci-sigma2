import UndeciSigma2.Clock.Specs

/-! # Soundness of the clock sentence

If twenty-one trees satisfy the guards, the root conditions and the specifications of all
clauses, the program halts. The trees are top-free by the guards, so the argument is about
their address sets, which may be infinite; every number used (a tooth length, a counter value)
is shown to exist from the clauses, never assumed.

For a tree `X` and a stamp `s`, the tooth words of `X` at `s` are the words `1^s 0 1^y`.

The proof proceeds in order:

* The ray has only words of ones.
* The chain has a word outside its head; with the chain clause and the chain loop this gives
  a stamp `E` with `1^E 0 1^E` in the head, hence in the component of the end label.
* The clock has the tooth `s` at every stamp `s ≤ E`: it has the tooth `0` at stamp `0`, the
  window clause lets each tooth grow by at most one, and the tooth `E` is reached at `E`.
* The stamps of the clock form an initial segment. Each stamp carries exactly one label: some
  label by the covering clause and at most one by the uniqueness clauses. Stamp `0` carries the
  start label, the label at `s + 1` follows the label at `s` by the transition clauses, the end
  label is last, and the stamps are exactly `0, …, E`.
* The tooth of the clock at `s` lies in the component of the label at `s`.
* Each counter comb has at every stamp `s ≤ E` a finite tooth `s + cᵢ(s)` with `cᵢ(0) = 0` and
  `cᵢ(s + 1) ≤ cᵢ(s) + effect`: a longer tooth puts new tooth words into a class comb, whose
  stub fixes the effect of the label at `s + 1`, and the window clauses bound the number of new
  words by the effect plus one.
* The unwinding comb has at every stamp a tooth of length at most the number of unwinding
  labels so far.
* The number of build-up labels is at most the number of unwinding labels: the tooth of the
  last build-up stamp passes through the build-up loop into the ray `N`, and the unwinding
  bound puts it into some tooth of the unwinding comb.
* Hence the counters follow the effects exactly: the sum of the three counters minus the
  build-up labels plus the unwinding labels so far does not increase, starts at `0` and ends
  at a nonnegative value.
* A counter is zero before a zero branch testing it, by the zero-test clause and the tooth of
  the clock.
* The labels and counters form an exact run, so the program halts.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

/-! ## Teeth -/

private theorem toothWord_mem_windowSet_iff {X B : Tree} {s y : ℕ} :
    toothWord s y ∈ windowSet X B ↔
      toothWord (s + 1) y ∈ X.constructorPaths ∧ toothWord s y ∉ B.constructorPaths :=
  Iff.rfl

/-- The tooth of `X` at stamp `s` has length `t`: the tooth words of `X` at `s` are those of
length at most `t`. -/
def HasTooth (X : Tree) (s t : ℕ) : Prop := ∀ y, toothWord s y ∈ X.constructorPaths ↔ y ≤ t

/-- The largest `y` with `1^s 0 1^y` an address of `X`, or `0` if there is none or no largest
one. -/
noncomputable def toothTop (X : Tree) (s : ℕ) : ℕ := sSup {y | toothWord s y ∈ X.constructorPaths}

/-- The length of a tooth is the largest depth of its words. -/
theorem HasTooth.toothTop_eq {X : Tree} {s t : ℕ} (h : HasTooth X s t) : toothTop X s = t := by
  have hset : {y | toothWord s y ∈ X.constructorPaths} = Set.Iic t := Set.ext fun y => h y
  rw [toothTop, hset, csSup_Iic]

/-- A tooth containing the word of depth `a` and no word deeper than `B` has a length. -/
theorem exists_hasTooth_of_bounded {X : Tree} {s a B : ℕ}
    (ha : toothWord s a ∈ X.constructorPaths)
    (hB : ∀ y, toothWord s y ∈ X.constructorPaths → y ≤ B) : ∃ t, HasTooth X s t := by
  classical
  refine ⟨Nat.findGreatest (fun y => toothWord s y ∈ X.constructorPaths) B, fun y =>
    ⟨fun hy => Nat.le_findGreatest (hB y hy) hy, fun hy => ?_⟩⟩
  exact toothWord_mem_of_le hy
    (Nat.findGreatest_spec (P := fun y => toothWord s y ∈ X.constructorPaths) (hB a ha) ha)

/-- The label at stamp `s`: the least `l` whose component has the stub `1^s 0`, or the start
label if there is none. -/
noncomputable def stampLabel (x : ClockExistentials Tree) (s : ℕ) : ℕ := by
  classical
  exact if h : ∃ l, ones l ++ 0 :: stub s ∈ x.labels.constructorPaths then Nat.find h
    else startLabel

/-- The value of counter `i` at stamp `s`: the tooth length of the counter comb minus the
stamp. -/
noncomputable def counterValue (x : ClockExistentials Tree) (i : Fin 3) (s : ℕ) : ℕ :=
  toothTop (x.counter i) s - s

/-- If some component has the stub of `s`, so does the component of the label at `s`. -/
theorem stampLabel_mem_of_mem {x : ClockExistentials Tree} {s l : ℕ}
    (hl : ones l ++ 0 :: stub s ∈ x.labels.constructorPaths) :
    ones (stampLabel x s) ++ 0 :: stub s ∈ x.labels.constructorPaths := by
  classical
  have hex : ∃ l, ones l ++ 0 :: stub s ∈ x.labels.constructorPaths := ⟨l, hl⟩
  unfold stampLabel
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

/-- How much less counter `i` grows from `s` to `s + 1` than the effect of the label at
`s + 1`. -/
private noncomputable def counterSlack (P : Program) (x : ClockExistentials Tree) (i : Fin 3)
    (s : ℕ) : ℤ :=
  counterValue x i s + effect P (stampLabel x (s + 1)) i - counterValue x i (s + 1)

/-! ## Reading root conditions -/

/-- A comb root `f(e, ⊥) ≤ X ≤ f(e, K)` gives the tooth `0` at stamp `0`. -/
private theorem hasTooth_zero_of_root {X K : Tree} (hX : X.TopFree) (hK : K.TopFree)
    (hlo : f e bot ≤ X) (hup : X ≤ f e K) : HasTooth X 0 0 := by
  intro y
  constructor
  · intro hy
    have hm := (le_iff_constructorPaths_subset hX ((topFree_f _ _).mpr ⟨topFree_e, hK⟩)).mp hup hy
    have he : ones y ∈ e.constructorPaths := hm
    rw [mem_constructorPaths_e] at he
    have := congrArg List.length he
    simp only [length_ones, List.length_nil] at this
    omega
  · intro hy
    obtain rfl : y = 0 := Nat.le_zero.mp hy
    exact (le_iff_constructorPaths_subset ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩) hX).mp
      hlo (show [0] ∈ (f e bot).constructorPaths by simp)

private theorem false_of_window_two {X B : Tree} (hspec : WindowSpec 2 (windowSet X B))
    (s : ℕ) {y₁ y₂ : ℕ} (hlt : y₁ < y₂) (h₁ : toothWord s y₁ ∈ windowSet X B)
    (h₂ : toothWord s y₂ ∈ windowSet X B) : False := by
  refine hspec.not_strictMono s ![y₁, y₂] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.mpr fun j => ?_
    fin_cases j
    simpa using hlt
  · intro j
    fin_cases j
    · simpa using h₁
    · simpa using h₂

private theorem false_of_window_three {X B : Tree} (hspec : WindowSpec 3 (windowSet X B))
    (s : ℕ) {y₁ y₂ y₃ : ℕ} (hlt₁ : y₁ < y₂) (hlt₂ : y₂ < y₃) (h₁ : toothWord s y₁ ∈ windowSet X B)
    (h₂ : toothWord s y₂ ∈ windowSet X B) (h₃ : toothWord s y₃ ∈ windowSet X B) : False := by
  refine hspec.not_strictMono s ![y₁, y₂, y₃] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.mpr fun j => ?_
    fin_cases j
    · simpa using hlt₁
    · simpa using hlt₂
  · intro j
    fin_cases j
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃

variable {P : Program} {x : ClockExistentials Tree}

namespace SpecConditions

variable (h : SpecConditions P x)
include h

/-! ## Readings of the root conditions -/

/-- The guards make every witness top-free. -/
theorem topFree : ∀ t ∈ x.toList, t.TopFree := h.guarded.topFree

theorem topFree_clock : x.clock.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_chain : x.chain.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_chainHead : x.chainHead.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_chainLoop : x.chainLoop.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_labels : x.labels.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_counter (i : Fin 3) : (x.counter i).TopFree :=
  h.topFree _ (by fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_plusClass (i : Fin 3) : (x.plusClass i).TopFree :=
  h.topFree _ (by fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_zeroClass (i : Fin 3) : (x.zeroClass i).TopFree :=
  h.topFree _ (by fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_unwind : x.unwind.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_unwindPart : x.unwindPart.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_buildRay : x.buildRay.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_buildLoop : x.buildLoop.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

theorem topFree_sink : x.sink.TopFree :=
  h.topFree _ (by simp [ClockExistentials.toList, ClockExistentials.guarded])

/-- Every component lies inside the clock. -/
theorem mem_clock_of_mem_component {l : ℕ} {w : Word}
    (hw : ones l ++ 0 :: w ∈ x.labels.constructorPaths) : w ∈ x.clock.constructorPaths :=
  (mem_of_le_select_bot h.topFree_labels h.root.labels_clock h.topFree_clock hw).2

/-- Only labels below `m` have components. -/
theorem lt_labelCount_of_mem_component {l : ℕ} {w : Word}
    (hw : ones l ++ 0 :: w ∈ x.labels.constructorPaths) : l < labelCount P :=
  (mem_of_le_select_bot h.topFree_labels h.root.labels_clock h.topFree_clock hw).1

/-- The clock has the tooth `0` at stamp `0`. -/
theorem clock_hasTooth_zero : HasTooth x.clock 0 0 :=
  hasTooth_zero_of_root h.topFree_clock h.topFree_sink h.root.clock_lower h.root.clock_upper

/-- The component of the start label has the stub at stamp `0`. -/
theorem start_stub_mem : ones startLabel ++ 0 :: stub 0 ∈ x.labels.constructorPaths :=
  mem_of_pack_le ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩) h.topFree_labels
    h.root.labels_start (by simp)

/-- Only the start label has a tooth at stamp `0`. -/
theorem eq_startLabel_of_stub_zero {l : ℕ}
    (hl : ones l ++ 0 :: stub 0 ∈ x.labels.constructorPaths) : l = startLabel := by
  have htf : (if l = startLabel then x.sink else f bot x.sink).TopFree := by
    split_ifs
    · exact h.topFree_sink
    · exact (topFree_f _ _).mpr ⟨topFree_bot, h.topFree_sink⟩
  have hm := (mem_of_le_select_bot h.topFree_labels h.root.labels_left htf hl).2
  by_contra hne
  simp only [ite_eq_right hne] at hm
  simp at hm

/-- Each counter comb has the tooth `0` at stamp `0` and contains the clock. -/
theorem counter_hasTooth_zero (i : Fin 3) : HasTooth (x.counter i) 0 0 :=
  hasTooth_zero_of_root (h.topFree_counter i) h.topFree_sink (h.root.counter_lower i)
    (h.root.counter_upper i)

/-- Every counter comb contains the clock. -/
theorem mem_counter_of_mem_clock (i : Fin 3) {w : Word} (hw : w ∈ x.clock.constructorPaths) :
    w ∈ (x.counter i).constructorPaths :=
  (le_iff_constructorPaths_subset h.topFree_clock (h.topFree_counter i)).mp
    (h.root.clock_le_counter i) hw

/-- The increasing class combs have no tooth at stamp `0`. -/
theorem stub_zero_not_mem_plusClass (i : Fin 3) : stub 0 ∉ (x.plusClass i).constructorPaths := by
  intro hw
  have hm := (le_iff_constructorPaths_subset (h.topFree_plusClass i)
    ((topFree_f _ _).mpr ⟨topFree_bot, h.topFree_sink⟩)).mp (h.root.plusClass_le i) hw
  simp at hm

/-- The keeping class combs have no tooth at stamp `0`. -/
theorem stub_zero_not_mem_zeroClass (i : Fin 3) : stub 0 ∉ (x.zeroClass i).constructorPaths := by
  intro hw
  have hm := (le_iff_constructorPaths_subset (h.topFree_zeroClass i)
    ((topFree_f _ _).mpr ⟨topFree_bot, h.topFree_sink⟩)).mp (h.root.zeroClass_le i) hw
  simp at hm

/-- The unwinding comb has the tooth `0` at stamp `0`. -/
theorem unwind_hasTooth_zero : HasTooth x.unwind 0 0 :=
  hasTooth_zero_of_root h.topFree_unwind h.topFree_sink h.root.unwind_lower h.root.unwind_upper

/-- The unwinding part lies inside the component of the unwinding label. -/
theorem mem_component_of_mem_unwindPart {w : Word} (hw : w ∈ x.unwindPart.constructorPaths) :
    ones unwindLabel ++ 0 :: w ∈ x.labels.constructorPaths :=
  mem_of_pack_le h.topFree_unwindPart h.topFree_labels h.root.labels_unwind hw

/-- A word `1^a 0 w` of the component of the build-up label gives the address `w` of the ray
`N`. -/
theorem mem_buildRay_of_mem_component {a : ℕ} {w : Word}
    (hw : ones buildLabel ++ 0 :: (ones a ++ 0 :: w) ∈ x.labels.constructorPaths) :
    w ∈ x.buildRay.constructorPaths := by
  have htf : (f x.sink (f x.buildLoop x.sink)).TopFree :=
    (topFree_f _ _).mpr ⟨h.topFree_sink, (topFree_f _ _).mpr ⟨h.topFree_buildLoop, h.topFree_sink⟩⟩
  have hm := (le_iff_constructorPaths_subset h.topFree_labels htf).mp h.root.labels_build hw
  have hk : ones a ++ 0 :: w ∈ x.buildLoop.constructorPaths := hm
  exact mem_of_ones_append_zero_cons_mem h.root.buildLoop_le h.topFree_buildRay
    h.topFree_buildLoop a hk

/-! ## The specifications of the clauses -/

/-- The addresses of the chain are pairwise comparable. -/
theorem isChain_chain : IsChain x.chain.constructorPaths := by
  obtain ⟨h₁, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (chainClause_spec_iff x).mp h₁

/-- The words of the chain with at most one zero lie in its head. -/
theorem mem_chainHead {w : Word} (hw : w ∈ x.chain.constructorPaths)
    (hs : IsOnes w ∨ ∃ j i, w = toothWord j i) : w ∈ x.chainHead.constructorPaths := by
  obtain ⟨-, h₂, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (chainHeadClause_spec_iff x).mp h₂ w hw hs

/-- The window specification of the clock. -/
theorem windowSpec_clock : WindowSpec 2 (windowSet x.clock x.clock) := by
  obtain ⟨-, -, h₃, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (clockClause_spec_iff x).mp h₃

/-- The spine words and stubs of the right child of the clock are addresses of the clock. -/
theorem mem_clock_of_gap {w : Word} (hw : 1 :: w ∈ x.clock.constructorPaths)
    (hs : IsOnes w ∨ ∃ j, w = stub j) : w ∈ x.clock.constructorPaths := by
  obtain ⟨-, -, -, h₄, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (gapClause_spec_iff x).mp h₄ w hw hs

/-- A word of the component of the end label and of the right child of the clock lies in the
ray. -/
theorem mem_ray_of_endLast {w : Word}
    (hw : ones endLabel ++ 0 :: w ∈ x.labels.constructorPaths)
    (hw' : 1 :: w ∈ x.clock.constructorPaths) : w ∈ x.ray.constructorPaths := by
  obtain ⟨-, -, -, -, h₅, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (endLastClause_spec_iff x).mp h₅ w hw hw'

/-- Every address of the clock lies in some component. -/
theorem exists_component_of_mem_clock {w : Word} (hw : w ∈ x.clock.constructorPaths) :
    ∃ l < labelCount P, ones l ++ 0 :: w ∈ x.labels.constructorPaths := by
  obtain ⟨-, -, -, -, -, h₆, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (coverClause_spec_iff P x).mp h₆ w hw

/-- A word shared by two components lies in the ray. -/
theorem mem_ray_of_unique {l l' : ℕ} (hl' : l' < labelCount P) (hll' : l < l') {w : Word}
    (hw : ones l ++ 0 :: w ∈ x.labels.constructorPaths)
    (hw' : ones l' ++ 0 :: w ∈ x.labels.constructorPaths) : w ∈ x.ray.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, h₇, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (uniqueClause_spec_iff x l l').mp (h₇ l' hl' l hll') w hw hw'

/-- A word of the component of a label `l` other than the end label lies in the ray, or the
component of a successor of `l` contains it one stamp later. -/
theorem transition {l : ℕ} (hl : l < labelCount P) (hend : l ≠ endLabel) {w : Word}
    (hw : ones l ++ 0 :: w ∈ x.labels.constructorPaths) :
    w ∈ x.ray.constructorPaths ∨ ∃ μ < labelCount P, isSuccessor P l μ = true ∧
      ones μ ++ 0 :: 1 :: w ∈ x.labels.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, h₈, -⟩ := (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (transitionClause_spec_iff P x l).mp (h₈ l hl hend) w hw

/-- A word of the right child of a counter comb lies in the counter comb or in the right child
of one of its class combs. -/
theorem counterStep (i : Fin 3) {w : Word} (hw : 1 :: w ∈ (x.counter i).constructorPaths) :
    w ∈ (x.counter i).constructorPaths ∨ 1 :: w ∈ (x.plusClass i).constructorPaths ∨
      1 :: w ∈ (x.zeroClass i).constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, h₉, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (counterStepClause_spec_iff x i).mp (h₉ i).1 w hw

/-- The window specification of the keeping class comb of counter `i`. -/
theorem windowSpec_zeroClass (i : Fin 3) :
    WindowSpec 2 (windowSet (x.zeroClass i) (x.counter i)) := by
  obtain ⟨-, -, -, -, -, -, -, -, h₉, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (zeroWindowClause_spec_iff x i).mp (h₉ i).2.1

/-- The triple window specification of the increasing class comb of counter `i`. -/
theorem windowSpec_plusClass (i : Fin 3) :
    WindowSpec 3 (windowSet (x.plusClass i) (x.counter i)) := by
  obtain ⟨-, -, -, -, -, -, -, -, h₉, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (plusWindowClause_spec_iff x i).mp (h₉ i).2.2.1

/-- The stubs of the increasing class comb of counter `i` lie in components of labels other
than the start label that increase counter `i`. -/
theorem classLabel_plus (i : Fin 3) {w : Word} (hw : w ∈ (x.plusClass i).constructorPaths)
    (hs : IsOnes w ∨ ∃ j, w = stub j) :
    w ∈ x.ray.constructorPaths ∨ ∃ ν < labelCount P, (ν ≠ startLabel ∧ effect P ν i = 1) ∧
      ones ν ++ 0 :: w ∈ x.labels.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, h₉, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (classLabelClause_spec_iff P x i 1 (x.plusClass i)).mp (h₉ i).2.2.2.1 w hw hs

/-- The stubs of the keeping class comb of counter `i` lie in components of labels other than
the start label that keep counter `i`. -/
theorem classLabel_zero (i : Fin 3) {w : Word} (hw : w ∈ (x.zeroClass i).constructorPaths)
    (hs : IsOnes w ∨ ∃ j, w = stub j) :
    w ∈ x.ray.constructorPaths ∨ ∃ ν < labelCount P, (ν ≠ startLabel ∧ effect P ν i = 0) ∧
      ones ν ++ 0 :: w ∈ x.labels.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, h₉, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (classLabelClause_spec_iff P x i 0 (x.zeroClass i)).mp (h₉ i).2.2.2.2 w hw hs

/-- A word of counter comb `c` that lies, one stamp later, in the component of a zero branch
testing `c` is an address of the clock. -/
theorem mem_clock_of_zeroTest {μ : ℕ} (hμ : μ < labelCount P) {c : Fin 2}
    (hc : zeroTest P μ = some c) {w : Word}
    (hw : w ∈ (x.counter (Fin.castSucc c)).constructorPaths)
    (hw' : ones μ ++ 0 :: 1 :: w ∈ x.labels.constructorPaths) : w ∈ x.clock.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h₁₀, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (zeroTestClause_spec_iff x μ c).mp (h₁₀ μ hμ c hc) w hw hw'

/-- A word of the right child of the unwinding comb lies in the unwinding comb or in the right
child of its unwinding part. -/
theorem unwindStep {w : Word} (hw : 1 :: w ∈ x.unwind.constructorPaths) :
    w ∈ x.unwind.constructorPaths ∨ 1 :: w ∈ x.unwindPart.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h₁₁, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (unwindStepClause_spec_iff x).mp h₁₁ w hw

/-- The window specification of the unwinding part. -/
theorem windowSpec_unwind : WindowSpec 2 (windowSet x.unwindPart x.unwind) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h₁₂, -⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (unwindWindowClause_spec_iff x).mp h₁₂

/-- Every address of the ray `N` lies in the tails of the unwinding comb. -/
theorem unwindBound {w : Word} (hw : w ∈ x.buildRay.constructorPaths) :
    ∃ a, ones a ++ 0 :: w ∈ x.unwind.constructorPaths := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h₁₃⟩ :=
    (forall_mem_clauses_iff P x ClockClause.Spec).mp h.spec
  exact (unwindBoundClause_spec_iff x).mp h₁₃ w hw

/-! ## The steps -/

/-- The addresses of the ray are words of ones. -/
theorem isOnes_of_mem_ray {w : Word} (hw : w ∈ x.ray.constructorPaths) : IsOnes w :=
  h.guarded.isOnes_of_mem_ray hw

/-- There is a stamp `E` with `1^E 0 1^E` in the head of the chain. -/
theorem exists_last : ∃ E, toothWord E E ∈ x.chainHead.constructorPaths := by
  obtain ⟨w, hwB, hwH⟩ :=
    (not_le_iff_exists h.topFree_chain h.topFree_chainHead).mp h.root.chain_not_le_head
  have hw₁ : ¬IsOnes w := fun hw => hwH (h.mem_chainHead hwB (Or.inl hw))
  obtain ⟨a, γ, rfl⟩ := (not_isOnes_iff w).mp hw₁
  have hγ₁ : ¬IsOnes γ := by
    intro hγ
    obtain ⟨b, rfl⟩ := (isOnes_iff γ).mp hγ
    exact hwH (h.mem_chainHead hwB (Or.inr ⟨a, b, rfl⟩))
  obtain ⟨b, δ, rfl⟩ := (not_isOnes_iff γ).mp hγ₁
  have hγB : ones b ++ 0 :: δ ∈ x.chain.constructorPaths :=
    mem_of_ones_append_zero_cons_mem h.root.chainLoop_le h.topFree_chain h.topFree_chainLoop a
      ((le_iff_constructorPaths_subset h.topFree_chain h.topFree_chainLoop).mp
        h.root.chain_le_loop hwB)
  rcases h.isChain_chain _ hγB _ hwB with hp | hp
  · rcases prefix_ones_append_zero_cons_iff.mp hp with ⟨i, -, he⟩ | ⟨v, -, he⟩
    · exact absurd (isOnes_ones i) (he ▸ not_isOnes_ones_append_zero_cons b δ)
    · obtain ⟨hba, -⟩ := ones_append_zero_cons_inj.mp he
      rw [hba] at hwB
      refine ⟨a, h.mem_chainHead ?_ (Or.inr ⟨a, a, rfl⟩)⟩
      exact mem_constructorPaths_of_prefix ⟨0 :: δ, by simp [toothWord]⟩ hwB
  · have := hp.length_le
    simp only [List.length_append, List.length_cons, length_ones] at this
    omega

/-! ### Steps before the last stamp is fixed -/

/-- The tooth of the clock at any stamp `s` is at most `s` long. -/
theorem clock_tooth_le {s y : ℕ} (hy : toothWord s y ∈ x.clock.constructorPaths) : y ≤ s := by
  induction s generalizing y with
  | zero => exact (h.clock_hasTooth_zero y).mp hy
  | succ s ih =>
    by_contra hlt
    push Not at hlt
    have hw : ∀ z, s < z → z ≤ y → toothWord s z ∈ windowSet x.clock x.clock := fun z hz hzy =>
      toothWord_mem_windowSet_iff.mpr ⟨toothWord_mem_of_le hzy hy, fun hm => by
        have := ih hm
        omega⟩
    exact false_of_window_two h.windowSpec_clock s (Nat.lt_succ_self (s + 1))
      (hw (s + 1) (by omega) (by omega)) (hw (s + 2) (by omega) (by omega))

/-- The tooth of the clock shrinks by at most one from each stamp to the previous one. -/
theorem clock_tooth_pred {s y : ℕ} (hy : toothWord (s + 1) (y + 1) ∈ x.clock.constructorPaths) :
    toothWord s y ∈ x.clock.constructorPaths := by
  by_contra hn
  exact false_of_window_two h.windowSpec_clock s (Nat.lt_succ_self y)
    (toothWord_mem_windowSet_iff.mpr ⟨toothWord_mem_of_le (Nat.le_succ y) hy, hn⟩)
    (toothWord_mem_windowSet_iff.mpr ⟨hy, fun hm => hn (toothWord_mem_of_le (Nat.le_succ y) hm)⟩)

/-- Going back `j` stamps shortens the tooth of the clock by at most `j`. -/
theorem clock_tooth_down {s y : ℕ} (j : ℕ)
    (hy : toothWord (s + j) (y + j) ∈ x.clock.constructorPaths) :
    toothWord s y ∈ x.clock.constructorPaths := by
  induction j with
  | zero => exact hy
  | succ j ih => exact ih (h.clock_tooth_pred (s := s + j) (y := y + j) hy)

/-- The stamps of the clock form an initial segment. -/
theorem stub_mem_clock_of_le {s t : ℕ} (hst : s ≤ t) (ht : stub t ∈ x.clock.constructorPaths) :
    stub s ∈ x.clock.constructorPaths := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hst
  induction j with
  | zero => exact ht
  | succ j ih =>
    exact ih (Nat.le_add_right _ _) (h.mem_clock_of_gap (w := stub (s + j)) ht (Or.inr ⟨_, rfl⟩))

/-- Two components sharing a word outside the spine are the same. -/
theorem label_unique_of_not_isOnes {l l' : ℕ} {w : Word} (hw : ¬IsOnes w)
    (hl : ones l ++ 0 :: w ∈ x.labels.constructorPaths)
    (hl' : ones l' ++ 0 :: w ∈ x.labels.constructorPaths) : l = l' := by
  have hm := h.lt_labelCount_of_mem_component hl
  have hm' := h.lt_labelCount_of_mem_component hl'
  rcases lt_trichotomy l l' with hlt | rfl | hlt
  · exact absurd (h.isOnes_of_mem_ray (h.mem_ray_of_unique hm' hlt hl hl')) hw
  · rfl
  · exact absurd (h.isOnes_of_mem_ray (h.mem_ray_of_unique hm hlt hl' hl)) hw

/-- A component with the stub of `s` is the component of the label at `s`. -/
theorem stampLabel_eq {s l : ℕ} (hl : ones l ++ 0 :: stub s ∈ x.labels.constructorPaths) :
    stampLabel x s = l :=
  h.label_unique_of_not_isOnes (not_isOnes_stub s) (stampLabel_mem_of_mem hl) hl

/-- A tooth word of counter comb `i` at stamp `s + 1` beyond its tooth at `s` lies in the
right child of a class comb, and the class is the effect of the label at `s + 1`. -/
theorem counter_new_word (i : Fin 3) {s t y : ℕ} (ht : HasTooth (x.counter i) s t) (hty : t < y)
    (hy : toothWord (s + 1) y ∈ (x.counter i).constructorPaths) :
    (toothWord s y ∈ windowSet (x.plusClass i) (x.counter i) ∧
        effect P (stampLabel x (s + 1)) i = 1) ∨
      (toothWord s y ∈ windowSet (x.zeroClass i) (x.counter i) ∧
        effect P (stampLabel x (s + 1)) i = 0) := by
  have hn : toothWord s y ∉ (x.counter i).constructorPaths := fun hm => by
    have := (ht y).mp hm
    omega
  rcases h.counterStep i (w := toothWord s y) hy with hc | hp | hz
  · exact absurd hc hn
  · refine Or.inl ⟨toothWord_mem_windowSet_iff.mpr ⟨hp, hn⟩, ?_⟩
    rcases h.classLabel_plus i (stub_mem_of_toothWord_mem (s := s + 1) (y := y) hp)
      (Or.inr ⟨_, rfl⟩) with hr | ⟨ν, -, ⟨-, heff⟩, hν⟩
    · exact absurd (h.isOnes_of_mem_ray hr) (not_isOnes_stub _)
    · rw [h.stampLabel_eq hν]
      exact heff
  · refine Or.inr ⟨toothWord_mem_windowSet_iff.mpr ⟨hz, hn⟩, ?_⟩
    rcases h.classLabel_zero i (stub_mem_of_toothWord_mem (s := s + 1) (y := y) hz)
      (Or.inr ⟨_, rfl⟩) with hr | ⟨ν, -, ⟨-, heff⟩, hν⟩
    · exact absurd (h.isOnes_of_mem_ray hr) (not_isOnes_stub _)
    · rw [h.stampLabel_eq hν]
      exact heff

/-- From a tooth of length `t` at `s`, the tooth words of counter comb `i` at `s + 1` have
depth at most `t + 1 + effect`. -/
theorem counter_tooth_succ_le (i : Fin 3) {s t y : ℕ} (ht : HasTooth (x.counter i) s t)
    (hy : toothWord (s + 1) y ∈ (x.counter i).constructorPaths) :
    (y : ℤ) ≤ t + 1 + effect P (stampLabel x (s + 1)) i := by
  by_contra hlt
  push Not at hlt
  have hm := effect_mem (P := P) (stampLabel x (s + 1)) i
  have hy₁ : t + 1 ≤ y := by omega
  rcases h.counter_new_word i ht (by omega) (toothWord_mem_of_le hy₁ hy) with
    ⟨-, he⟩ | ⟨-, he⟩
  · have hw : ∀ z, t < z → z ≤ y → toothWord s z ∈ windowSet (x.plusClass i) (x.counter i) := by
      intro z hz hzy
      rcases h.counter_new_word i ht hz (toothWord_mem_of_le hzy hy) with
        ⟨hw, -⟩ | ⟨-, he'⟩
      · exact hw
      · rw [he] at he'
        exact absurd he' one_ne_zero
    rw [he] at hlt
    exact false_of_window_three (h.windowSpec_plusClass i) s (y₁ := t + 1) (y₂ := t + 2)
      (y₃ := t + 3) (by omega) (by omega) (hw (t + 1) (by omega) (by omega))
      (hw (t + 2) (by omega) (by omega)) (hw (t + 3) (by omega) (by omega))
  · have hw : ∀ z, t < z → z ≤ y → toothWord s z ∈ windowSet (x.zeroClass i) (x.counter i) := by
      intro z hz hzy
      rcases h.counter_new_word i ht hz (toothWord_mem_of_le hzy hy) with
        ⟨-, he'⟩ | ⟨hw, -⟩
      · rw [he] at he'
        exact absurd he' zero_ne_one
      · exact hw
    rw [he] at hlt
    exact false_of_window_two (h.windowSpec_zeroClass i) s (y₁ := t + 1) (y₂ := t + 2)
      (by omega) (hw (t + 1) (by omega) (by omega)) (hw (t + 2) (by omega) (by omega))

/-- At most one component has the stub of a given stamp. -/
theorem label_unique {l l' s : ℕ} (hl : ones l ++ 0 :: stub s ∈ x.labels.constructorPaths)
    (hl' : ones l' ++ 0 :: stub s ∈ x.labels.constructorPaths) : l = l' :=
  h.label_unique_of_not_isOnes (not_isOnes_stub s) hl hl'

/-- Stamp `0` carries the start label. -/
theorem stampLabel_zero : stampLabel x 0 = startLabel :=
  h.stampLabel_eq h.start_stub_mem

/-- Every counter is zero at stamp `0`. -/
theorem counterValue_zero (i : Fin 3) : counterValue x i 0 = 0 := by
  simp [counterValue, (h.counter_hasTooth_zero i).toothTop_eq]

/-- The potential: the sum of the counters minus the build-up labels plus the unwinding labels
up to `n` is minus the total slack before `n`. -/
private theorem potential_eq (n : ℕ) :
    (∑ i, (counterValue x i n : ℤ)) - occurrences (stampLabel x) buildLabel n +
        occurrences (stampLabel x) unwindLabel n =
      -∑ s ∈ Finset.range n, ∑ i, counterSlack P x i s := by
  induction n with
  | zero => simp [h.counterValue_zero, occurrences]
  | succ n ih =>
    have hsum := sum_effect (P := P) (stampLabel x (n + 1))
    rw [Finset.sum_range_succ, occurrences_succ, occurrences_succ]
    simp only [counterSlack, Fin.sum_univ_three] at ih hsum ⊢
    by_cases hb : stampLabel x (n + 1) = buildLabel
    · have hu : stampLabel x (n + 1) ≠ unwindLabel := by rw [hb]; decide
      rw [ite_eq_left hb] at hsum
      rw [ite_eq_left hb, ite_eq_right hu]
      push_cast
      linarith
    · by_cases hu : stampLabel x (n + 1) = unwindLabel
      · rw [ite_eq_right hb, ite_eq_left hu] at hsum
        rw [ite_eq_right hb, ite_eq_left hu]
        push_cast
        linarith
      · rw [ite_eq_right hb, ite_eq_right hu] at hsum
        rw [ite_eq_right hb, ite_eq_right hu]
        push_cast
        linarith

variable {E : ℕ} (hE : toothWord E E ∈ x.chainHead.constructorPaths)
include hE

/-- The word `1^E 0 1^E` lies in the component of the end label. -/
theorem end_tooth_mem : ones endLabel ++ 0 :: toothWord E E ∈ x.labels.constructorPaths :=
  mem_of_pack_le h.topFree_chainHead h.topFree_labels h.root.labels_end hE

/-- The clock has the tooth `s` at every stamp `s ≤ E`. -/
theorem clock_hasTooth {s : ℕ} (hs : s ≤ E) : HasTooth x.clock s s := by
  intro y
  refine ⟨h.clock_tooth_le, fun hy => toothWord_mem_of_le hy ?_⟩
  have hE' : toothWord E E ∈ x.clock.constructorPaths :=
    h.mem_clock_of_mem_component (h.end_tooth_mem hE)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact h.clock_tooth_down j hE'

/-- The stamps of the clock are exactly `0, …, E`. -/
theorem stub_mem_clock_iff (s : ℕ) : stub s ∈ x.clock.constructorPaths ↔ s ≤ E := by
  refine ⟨fun hs => ?_, fun hs => (h.clock_hasTooth hE hs 0).mpr (Nat.zero_le s)⟩
  by_contra hlt
  push Not at hlt
  have h₁ : stub (E + 1) ∈ x.clock.constructorPaths := h.stub_mem_clock_of_le hlt hs
  have h₂ : ones endLabel ++ 0 :: stub E ∈ x.labels.constructorPaths :=
    mem_constructorPaths_of_prefix (ones_append_zero_cons_prefix _ (stub_prefix_toothWord E E))
      (h.end_tooth_mem hE)
  exact not_isOnes_stub E (h.isOnes_of_mem_ray (h.mem_ray_of_endLast h₂ h₁))

/-- The label at each stamp `s ≤ E` has the stub of `s` in its component. -/
theorem stampLabel_mem {s : ℕ} (hs : s ≤ E) :
    ones (stampLabel x s) ++ 0 :: stub s ∈ x.labels.constructorPaths := by
  obtain ⟨l, -, hl⟩ := h.exists_component_of_mem_clock ((h.stub_mem_clock_iff hE s).mpr hs)
  exact stampLabel_mem_of_mem hl

/-- The last stamp carries the end label. -/
theorem stampLabel_last : stampLabel x E = endLabel :=
  h.stampLabel_eq (mem_constructorPaths_of_prefix
    (ones_append_zero_cons_prefix _ (stub_prefix_toothWord E E)) (h.end_tooth_mem hE))

/-- The label at each stamp `s + 1 ≤ E` is a successor of the label at `s`. -/
theorem isSuccessor_stampLabel {s : ℕ} (hs : s < E) :
    isSuccessor P (stampLabel x s) (stampLabel x (s + 1)) = true := by
  have hm := h.stampLabel_mem hE hs.le
  have hlt := h.lt_labelCount_of_mem_component hm
  have hstub : stub (s + 1) ∈ x.clock.constructorPaths := (h.stub_mem_clock_iff hE (s + 1)).mpr hs
  have hne : stampLabel x s ≠ endLabel := by
    intro heq
    rw [heq] at hm
    exact not_isOnes_stub s (h.isOnes_of_mem_ray (h.mem_ray_of_endLast hm hstub))
  rcases h.transition hlt hne hm with hr | ⟨μ, -, hsucc, hμ⟩
  · exact absurd (h.isOnes_of_mem_ray hr) (not_isOnes_stub s)
  · rw [h.stampLabel_eq (s := s + 1) hμ]
    exact hsucc

/-- The tooth of the clock at `s ≤ E` lies in the component of the label at `s`. -/
theorem tooth_mem_component {s : ℕ} (hs : s ≤ E) :
    ones (stampLabel x s) ++ 0 :: toothWord s s ∈ x.labels.constructorPaths := by
  obtain ⟨l, -, hl⟩ := h.exists_component_of_mem_clock ((h.clock_hasTooth hE hs s).mpr le_rfl)
  rw [h.stampLabel_eq (mem_constructorPaths_of_prefix
    (ones_append_zero_cons_prefix _ (stub_prefix_toothWord s s)) hl)]
  exact hl

/-- Each counter comb has a tooth of some length at least `s` at every stamp `s ≤ E`. -/
theorem counter_exists_hasTooth (i : Fin 3) {s : ℕ} (hs : s ≤ E) :
    ∃ t, s ≤ t ∧ HasTooth (x.counter i) s t := by
  induction s with
  | zero => exact ⟨0, le_rfl, h.counter_hasTooth_zero i⟩
  | succ s ih =>
    obtain ⟨t, hst, ht⟩ := ih (by omega)
    have hlow : toothWord (s + 1) (s + 1) ∈ (x.counter i).constructorPaths :=
      h.mem_counter_of_mem_clock i ((h.clock_hasTooth hE hs (s + 1)).mpr le_rfl)
    have hbound : ∀ y, toothWord (s + 1) y ∈ (x.counter i).constructorPaths → y ≤ t + 2 := by
      intro y hy
      have h₁ := h.counter_tooth_succ_le i ht hy
      have h₂ := effect_mem (P := P) (stampLabel x (s + 1)) i
      omega
    obtain ⟨t', ht'⟩ := exists_hasTooth_of_bounded hlow hbound
    exact ⟨t', (ht' _).mp hlow, ht'⟩

/-- At every stamp `s ≤ E`, the tooth of each counter comb has the length `toothTop`, at least
`s`. -/
theorem counter_hasTooth (i : Fin 3) {s : ℕ} (hs : s ≤ E) :
    s ≤ toothTop (x.counter i) s ∧ HasTooth (x.counter i) s (toothTop (x.counter i) s) := by
  obtain ⟨t, hst, ht⟩ := h.counter_exists_hasTooth hE i hs
  rw [ht.toothTop_eq]
  exact ⟨hst, ht⟩

/-- A counter grows by at most the effect of the next label. -/
theorem counterValue_succ_le (i : Fin 3) {s : ℕ} (hs : s < E) :
    (counterValue x i (s + 1) : ℤ) ≤ counterValue x i s + effect P (stampLabel x (s + 1)) i := by
  obtain ⟨h₁, ht₁⟩ := h.counter_hasTooth hE i hs.le
  obtain ⟨h₂, ht₂⟩ := h.counter_hasTooth hE i (s := s + 1) (by omega)
  have h₃ := h.counter_tooth_succ_le i ht₁ ((ht₂ _).mpr le_rfl)
  simp only [counterValue]
  omega

/-- The tooth of the unwinding comb at any stamp is at most the number of unwinding labels up
to that stamp, or up to `E`. -/
theorem unwind_tooth_le {s y : ℕ} (hy : toothWord s y ∈ x.unwind.constructorPaths) :
    y ≤ occurrences (stampLabel x) unwindLabel (min s E) := by
  induction s generalizing y with
  | zero =>
    have := (h.unwind_hasTooth_zero y).mp hy
    simp only [Nat.zero_min, occurrences_zero]
    omega
  | succ s ih =>
    have hmono : occurrences (stampLabel x) unwindLabel (min s E) ≤
        occurrences (stampLabel x) unwindLabel (min (s + 1) E) :=
      occurrences_mono _ _ (min_le_min (Nat.le_succ s) le_rfl)
    by_cases hyu : y ≤ occurrences (stampLabel x) unwindLabel (min s E)
    · exact hyu.trans hmono
    push Not at hyu
    have hpart : ∀ z, occurrences (stampLabel x) unwindLabel (min s E) < z → z ≤ y →
        toothWord s z ∈ windowSet x.unwindPart x.unwind := by
      intro z hz hzy
      have hzn : toothWord s z ∉ x.unwind.constructorPaths := fun hm => by
        have := ih hm
        omega
      rcases h.unwindStep (w := toothWord s z) (toothWord_mem_of_le (s := s + 1) hzy hy) with
        hc | hp
      · exact absurd hc hzn
      · exact toothWord_mem_windowSet_iff.mpr ⟨hp, hzn⟩
    set u := occurrences (stampLabel x) unwindLabel (min s E) with hu
    have hp₁ := (toothWord_mem_windowSet_iff.mp (hpart (u + 1) (by omega) hyu)).1
    have hcomp := h.mem_component_of_mem_unwindPart (stub_mem_of_toothWord_mem hp₁)
    have hsE : s + 1 ≤ E :=
      (h.stub_mem_clock_iff hE (s + 1)).mp (h.mem_clock_of_mem_component hcomp)
    have hlab : stampLabel x (s + 1) = unwindLabel := h.stampLabel_eq hcomp
    have hy' : y = u + 1 := by
      by_contra hne
      exact false_of_window_two h.windowSpec_unwind s (y₁ := u + 1) (y₂ := u + 2) (by omega)
        (hpart (u + 1) (by omega) (by omega)) (hpart (u + 2) (by omega) (by omega))
    rw [min_eq_left hsE, occurrences_succ, ite_eq_left hlab, hy']
    rw [min_eq_left (Nat.le_of_succ_le hsE)] at hu
    omega

/-- There are at most as many build-up labels as unwinding labels. -/
theorem occurrences_build_le :
    occurrences (stampLabel x) buildLabel E ≤ occurrences (stampLabel x) unwindLabel E := by
  classical
  by_cases hex : ∃ t, t ≤ E ∧ stampLabel x t = buildLabel
  · obtain ⟨t₀, ht₀E, ht₀⟩ := hex
    have hbE : Nat.findGreatest (fun t => stampLabel x t = buildLabel) E ≤ E :=
      Nat.findGreatest_le E
    have hbl : stampLabel x (Nat.findGreatest (fun t => stampLabel x t = buildLabel) E) =
        buildLabel :=
      Nat.findGreatest_spec (P := fun t => stampLabel x t = buildLabel) ht₀E ht₀
    have hNb : occurrences (stampLabel x) buildLabel E ≤
        Nat.findGreatest (fun t => stampLabel x t = buildLabel) E :=
      occurrences_le_of_forall_ne hbE fun t h₁ h₂ =>
        Nat.findGreatest_is_greatest (P := fun t => stampLabel x t = buildLabel) h₁ h₂
    set b := Nat.findGreatest (fun t => stampLabel x t = buildLabel) E
    have hcomp := h.tooth_mem_component hE hbE
    rw [hbl] at hcomp
    obtain ⟨a, ha⟩ := h.unwindBound (h.mem_buildRay_of_mem_component (a := b) (w := ones b) hcomp)
    have h₁ := h.unwind_tooth_le hE (s := a) (y := b) ha
    have h₂ := occurrences_mono (stampLabel x) unwindLabel (min_le_right a E)
    omega
  · push Not at hex
    have : occurrences (stampLabel x) buildLabel E ≤ 0 :=
      occurrences_le_of_forall_ne (Nat.zero_le E) fun t _ ht => hex t ht
    omega

private theorem counterSlack_nonneg (i : Fin 3) {s : ℕ} (hs : s < E) :
    0 ≤ counterSlack P x i s := by
  have := h.counterValue_succ_le hE i hs
  simp only [counterSlack]
  linarith

/-- The counters follow the effects exactly. -/
theorem counterValue_succ (i : Fin 3) {s : ℕ} (hs : s < E) :
    (counterValue x i (s + 1) : ℤ) = counterValue x i s + effect P (stampLabel x (s + 1)) i := by
  have hnonneg : ∀ s' ∈ Finset.range E, 0 ≤ ∑ j, counterSlack P x j s' := fun s' hs' =>
    Finset.sum_nonneg fun j _ => h.counterSlack_nonneg hE j (Finset.mem_range.mp hs')
  have hle : ∑ s' ∈ Finset.range E, ∑ j, counterSlack P x j s' ≤ 0 := by
    have hpot := h.potential_eq E
    have hocc := h.occurrences_build_le hE
    have hpos : 0 ≤ ∑ i, (counterValue x i E : ℤ) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    have hocc' : (occurrences (stampLabel x) buildLabel E : ℤ) ≤
        occurrences (stampLabel x) unwindLabel E := by exact_mod_cast hocc
    linarith
  have h₀ := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
    (le_antisymm hle (Finset.sum_nonneg hnonneg)) s (Finset.mem_range.mpr hs)
  have h₁ := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h.counterSlack_nonneg hE j hs).mp h₀ i
    (Finset.mem_univ i)
  simp only [counterSlack] at h₁
  linarith

/-- A counter is zero before a zero branch testing it. -/
theorem counterValue_eq_zero {s : ℕ} (hs : s < E) {c : Fin 2}
    (hc : zeroTest P (stampLabel x (s + 1)) = some c) : counterValue x (Fin.castSucc c) s = 0 := by
  by_contra hne
  obtain ⟨hst, ht⟩ := h.counter_hasTooth hE (Fin.castSucc c) hs.le
  have hmem : toothWord s (s + 1) ∈ (x.counter (Fin.castSucc c)).constructorPaths := by
    refine (ht _).mpr ?_
    simp only [counterValue] at hne
    omega
  have hcomp := h.tooth_mem_component hE (s := s + 1) (by omega)
  have hlt := h.lt_labelCount_of_mem_component hcomp
  have hclock := h.mem_clock_of_zeroTest hlt hc hmem hcomp
  have := (h.clock_hasTooth hE hs.le (s + 1)).mp hclock
  omega

/-- The labels and counters read off the trees form an exact run. -/
noncomputable def exactRun : ExactRun P where
  last := E
  label := stampLabel x
  count s i := counterValue x i s
  label_zero := h.stampLabel_zero
  label_last := h.stampLabel_last hE
  count_zero i := h.counterValue_zero i
  isSuccessor_label _ hs := h.isSuccessor_stampLabel hE hs
  count_succ _ hs i := h.counterValue_succ hE i hs
  count_eq_zero _ hs _ hc := h.counterValue_eq_zero hE hs hc

end SpecConditions

/-- Trees satisfying the guards, the root conditions and the specifications of all clauses
witness halting. -/
theorem SpecConditions.halts (h : SpecConditions P x) : P.Halts := by
  obtain ⟨E, hE⟩ := h.exists_last
  exact (h.exactRun hE).halts

/-- Soundness: if the clock sentence holds in one of the six structures, the program halts. -/
theorem halts_of_clockConditions {c : TreeClass} {top : Bool} (h : ClockConditions c top P) :
    P.Halts := by
  obtain ⟨x, -, hx⟩ := (clockConditions_iff c top P).mp h
  exact hx.halts

end Clock

end UndeciSigma2
