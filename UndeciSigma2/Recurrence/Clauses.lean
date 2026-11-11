import UndeciSigma2.Clauses.Sound
import UndeciSigma2.Clauses.Complete
import UndeciSigma2.Recurrence.Semantics

/-! # Numeric meaning of the recurrence clauses

The two clauses that the recurrence sentence adds to those of the machine sentence have
specifications in terms of the stubs of the state tree: the branch clause of `choice l r` in
state `q` states that a step from `q` reaches `l` or `r`, and the recurrence clause states that
state `0` occurs at arbitrarily late steps. As for the clauses of the machine sentence, the
sound direction derives the specification from the clause for all admissible values, and the
complete direction derives the clause from the specification for a state tree of the intended
shape.

The specifications of all clauses of an instruction, of the uniqueness clauses and of the
recurrence clause are collected in `AllSpecs`; over arbitrary trees the clauses hold for all
top-free values exactly when the specifications hold, for trees of the intended shape.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree Sentence

namespace Recurrence

/-! ## Specifications -/

/-- A step from state `q` goes to state `l` or to state `r`. -/
def BranchSpec (U : Tree) (q l r : ℕ) : Prop :=
  ∀ j, StubAt U q j → StubAt U l (j + 1) ∨ StubAt U r (j + 1)

/-- State `0` occurs at arbitrarily late steps. -/
def RecurrenceSpec (U : Tree) : Prop :=
  ∀ j, ∃ j', j ≤ j' ∧ StubAt U 0 j'

/-- The specifications of the clauses of instruction `q`, mirroring `InstructionClauses`. -/
def InstructionSpecs (n : ℕ) (C : Fin 2 → Tree) (U : Tree) (q : ℕ) : NInstr → Prop
  | .inc c r =>
    TransitionSpec U q (min r n) ∧
      UpperBoundSpec U (C c) 0 false q ∧ LowerBoundSpec U (C c) 2 q ∧
      UpperBoundSpec U (C (otherCounter c)) 1 false q ∧ LowerBoundSpec U (C (otherCounter c)) 1 q
  | .jzdec c z p =>
    ZeroTestSpec U (C c) q (min z n) ∧
      PositiveTestSpec U (C c) q (min p n) ∧ UpperBoundSpec U (C c) 2 true q ∧
      LowerBoundSpec U (C c) 0 q ∧ NextToothSpec U (C c) q ∧
      UpperBoundSpec U (C (otherCounter c)) 1 false q ∧ LowerBoundSpec U (C (otherCounter c)) 1 q
  | .choice l r =>
    BranchSpec U q (min l n) (min r n) ∧
      UpperBoundSpec U (C 0) 1 false q ∧ LowerBoundSpec U (C 0) 1 q ∧
      UpperBoundSpec U (C 1) 1 false q ∧ LowerBoundSpec U (C 1) 1 q

/-- No step is in two different states `r < q < n`. -/
def UniquenessSpecs (U : Tree) (n : ℕ) : Prop :=
  ∀ r q, r < q → q < n → HaltUniqueSpec U r q

/-- The specifications of all clauses of the recurrence sentence, mirroring `AllClauses`. -/
def AllSpecs (P : NProgram) (C : Fin 2 → Tree) (U : Tree) : Prop :=
  (∀ q ins, P[q]? = some ins → InstructionSpecs P.length C U q ins) ∧
    UniquenessSpecs U P.length ∧ RecurrenceSpec U

variable {c : TreeClass} {top : Bool} {C : Fin 2 → Tree} {U : Tree}

/-! ## Values of the universal variables -/

/-- Universal values with the seed `y₁` and the bound `g₁`, and bottom elsewhere. -/
def seedBound (y g : Tree) : Universals Tree :=
  ⟨y, bot, bot, g, bot, bot, bot, bot, bot, bot, bot, bot, bot, bot⟩

theorem seedBound_topFree {y g : Tree} (hy : y.TopFree) (hg : g.TopFree) :
    (seedBound y g).Forall Tree.TopFree :=
  ⟨hy, topFree_bot, topFree_bot, hg, topFree_bot, topFree_bot, topFree_bot, topFree_bot,
    topFree_bot, topFree_bot, topFree_bot, topFree_bot, topFree_bot, topFree_bot⟩

/-- Over arbitrary trees the admissible values are the top-free ones. -/
theorem admissible_arbitrary_iff (t : Tree) : Admissible .arbitrary top t ↔ t.TopFree :=
  ⟨fun h => h.2, fun h => ⟨domain_arbitrary_of_topFree h, h⟩⟩

/-! ## The branch clause -/

/-- If the branch clause holds for all admissible values, a step from state `q` reaches `l` or
`r`: otherwise the path to a stub `1ʲ 0` of state `q` and the cocone of that stub refute it. -/
theorem branchClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {q l r : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      BranchClause (Existentials.standard C U) v q l r) :
    BranchSpec U q l r := by
  intro j hs
  by_contra hn
  obtain ⟨hl, hr⟩ := not_or.mp hn
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 0 (stub j) (stub j) (stub j)
    (stub j) (stub j) (stub j))
  exact not_path_le_cocone (stub j) (hcl ⟨pack_path_le (w := stub j) hU hs,
    le_stateContext_cocone_stub hU hl, le_stateContext_cocone_stub hU hr,
    rightRay_le_cocone_tooth j 0⟩)

/-- The branch specification sends every seed stub into the bound of one of the targets. -/
theorem branchClause_complete (hU : U.TopFree) {q l r : ℕ} (hshape : StubShaped U q)
    (hspec : BranchSpec U q l r) {v : Universals Tree} (hv : v.Forall Tree.TopFree) :
    BranchClause (Existentials.standard C U) v q l r := by
  obtain ⟨hy₁, -, -, hg₁, -⟩ := hv
  rintro ⟨hpack, hl, hr, hsp⟩
  apply (le_iff_constructorPaths_subset hy₁ hg₁).mpr
  intro w hw
  have hu := ((pack_le_iff hy₁ hU q).mp hpack).2 w hw
  rcases hshape w hu with hs | ⟨j, rfl⟩
  · exact (le_iff_constructorPaths_subset topFree_rightRay hg₁).mp hsp
      ((mem_constructorPaths_rightRay _).mpr hs)
  · rcases hspec j hu with h | h
    · exact (le_stateContext_iff hU hg₁ l).mp hl _ h
    · exact (le_stateContext_iff hU hg₁ r).mp hr _ h

/-! ## The recurrence clause -/

/-- The addresses `v` such that `0 1ᵃ v` is an address of `U` for some `a`: the comb of
state `0` with any number of leading ones removed. -/
def stateZeroTails (U : Tree) : Set Word :=
  {w | ∃ a, 0 :: (ones a ++ w) ∈ U.constructorPaths}

theorem prefixClosed_stateZeroTails (U : Tree) : PrefixClosed (stateZeroTails U) := by
  rintro p s ⟨a, ha⟩
  refine ⟨a, constructorPaths_prefix (r := s) ?_⟩
  simpa [List.append_assoc] using ha

/-- The least tree containing the comb of state `0` and closed under removing leading ones. -/
noncomputable def stateZeroTree (U : Tree) : Tree :=
  ofConstructorPaths (stateZeroTails U) (prefixClosed_stateZeroTails U)

/-- Over arbitrary trees the recurrence clause implies that state `0` occurs at arbitrarily
late steps. The bound refuting the clause is `stateZeroTree U`, which need not be regular. -/
theorem recurrenceClause_sound (hU : U.TopFree)
    (h : ∀ v : Universals Tree, v.Forall (Admissible .arbitrary top) →
      RecurrenceClause (Existentials.standard C U) v) :
    RecurrenceSpec U := by
  intro j
  have hg : (stateZeroTree U).TopFree := ofConstructorPaths_topFree _ _
  have hpaths : (stateZeroTree U).constructorPaths = stateZeroTails U :=
    ofConstructorPaths_constructorPaths _ _
  have hv : (seedBound (path (stub j)) (stateZeroTree U)).Forall (Admissible .arbitrary top) :=
    (seedBound_topFree (topFree_path _) hg).imp fun t ht => (admissible_arbitrary_iff t).mpr ht
  have hcl := h _ hv
  have h₁ : U ≤ f (stateZeroTree U) full := by
    rw [le_f_iff hg topFree_full hU]
    refine ⟨fun w hw => ?_, fun w _ => mem_constructorPaths_full w⟩
    rw [hpaths]
    exact ⟨0, by simpa using hw⟩
  have h₂ : stateZeroTree U ≤ f full (stateZeroTree U) := by
    rw [le_f_iff topFree_full hg hg]
    refine ⟨fun w _ => mem_constructorPaths_full w, fun w hw => ?_⟩
    rw [hpaths] at hw ⊢
    obtain ⟨a, ha⟩ := hw
    refine ⟨a + 1, ?_⟩
    rw [ones_succ', List.append_assoc]
    exact ha
  have h₃ : path (stub j) ≤ stubComb :=
    (path_le_iff topFree_stubComb _).mpr ((mem_constructorPaths_stubComb _).mpr (.inr ⟨j, rfl⟩))
  have hmem := (path_le_iff hg (stub j)).mp (hcl ⟨h₁, h₂, h₃⟩)
  rw [hpaths] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a + j, Nat.le_add_left j a, ?_⟩
  simpa [StubAt, ones_append_stub] using ha

/-- If state `0` occurs at arbitrarily late steps, every stub lies in each bound containing the
comb of state `0` and closed under removing leading ones. -/
theorem recurrenceClause_complete (hU : U.TopFree) (hspec : RecurrenceSpec U)
    {v : Universals Tree} (hv : v.Forall Tree.TopFree) :
    RecurrenceClause (Existentials.standard C U) v := by
  obtain ⟨hy₁, -, -, hg₁, -⟩ := hv
  rintro ⟨hUg, hgg, hyT⟩
  have hzero := ((le_f_iff hg₁ topFree_full hU).mp hUg).1
  have hstrip := ((le_f_iff topFree_full hg₁ hg₁).mp hgg).2
  have hstub : ∀ j, stub j ∈ v.g₁.constructorPaths := by
    intro j
    obtain ⟨j', hj', hs⟩ := hspec j
    have h' : stub j' ∈ v.g₁.constructorPaths := hzero _ (by simpa [StubAt] using hs)
    apply mem_of_ones_append_mem hstrip (j' - j)
    rwa [ones_append_stub, Nat.sub_add_cancel hj']
  apply (le_iff_constructorPaths_subset hy₁ hg₁).mpr
  intro w hw
  rcases (mem_constructorPaths_stubComb w).mp
      ((le_iff_constructorPaths_subset hy₁ topFree_stubComb).mp hyT hw) with hs | ⟨j, rfl⟩
  · obtain ⟨i, rfl⟩ := (isOnes_iff w).mp hs
    exact mem_constructorPaths_of_prefix (List.prefix_append _ _) (hstub i)
  · exact hstub j

/-! ## Assembling the specifications -/

private theorem forall_admissible {X : Universals Tree → Prop}
    (h : ∀ v : Universals Tree, v.Forall Tree.TopFree → X v) :
    ∀ v : Universals Tree, v.Forall (Admissible .arbitrary false) → X v :=
  fun v hv => h v (hv.imp fun _ ha => ha.2)

/-- Over arbitrary trees the clauses of an instruction imply their specifications. -/
theorem instructionSpecs_of_clauses (hU : U.TopFree) (hC : ∀ i, (C i).TopFree) {n q : ℕ}
    {ins : NInstr}
    (h : ∀ v : Universals Tree, v.Forall Tree.TopFree →
      InstructionClauses (Existentials.standard C U) v n q ins) :
    InstructionSpecs n C U q ins := by
  have hc : TreeClass.arbitrary ≠ .finite := by decide
  have h' := forall_admissible h
  cases ins with
  | inc d r =>
    exact ⟨transitionClause_sound hc hU fun v hv => (h' v hv).1,
      upperBoundClause_sound hc hU (hC d) fun v hv => (h' v hv).2.1,
      lowerBoundClause_sound hc hU (hC d) fun v hv => (h' v hv).2.2.1,
      upperBoundClause_sound hc hU (hC _) fun v hv => (h' v hv).2.2.2.1,
      lowerBoundClause_sound hc hU (hC _) fun v hv => (h' v hv).2.2.2.2⟩
  | jzdec d z p =>
    exact ⟨zeroTestClause_sound hc hU (hC d) fun v hv => (h' v hv).1,
      positiveTestClause_sound hc hU (hC d) fun v hv => (h' v hv).2.1,
      upperBoundClause_sound hc hU (hC d) fun v hv => (h' v hv).2.2.1,
      lowerBoundClause_sound hc hU (hC d) fun v hv => (h' v hv).2.2.2.1,
      nextToothClause_sound hc hU (hC d) fun v hv => (h' v hv).2.2.2.2.1,
      upperBoundClause_sound hc hU (hC _) fun v hv => (h' v hv).2.2.2.2.2.1,
      lowerBoundClause_sound hc hU (hC _) fun v hv => (h' v hv).2.2.2.2.2.2⟩
  | choice l r =>
    exact ⟨branchClause_sound hc hU fun v hv => (h' v hv).1,
      upperBoundClause_sound hc hU (hC 0) fun v hv => (h' v hv).2.1,
      lowerBoundClause_sound hc hU (hC 0) fun v hv => (h' v hv).2.2.1,
      upperBoundClause_sound hc hU (hC 1) fun v hv => (h' v hv).2.2.2.1,
      lowerBoundClause_sound hc hU (hC 1) fun v hv => (h' v hv).2.2.2.2⟩

/-- Over arbitrary trees the uniqueness clauses imply their specifications. -/
theorem uniquenessSpecs_of_clauses (hU : U.TopFree) {n : ℕ}
    (h : ∀ v : Universals Tree, v.Forall Tree.TopFree →
      UniquenessClauses (Existentials.standard C U) v n) :
    UniquenessSpecs U n := fun r q hrq hq =>
  haltUniqueClause_sound (by decide : TreeClass.arbitrary ≠ .finite) hU
    fun v hv => forall_admissible h v hv r q hrq hq

/-- Over arbitrary trees all clauses of the recurrence sentence imply their specifications. -/
theorem allSpecs_of_clauses {P : NProgram} (hU : U.TopFree) (hC : ∀ i, (C i).TopFree)
    (h : ∀ v : Universals Tree, v.Forall Tree.TopFree →
      AllClauses (Existentials.standard C U) v P) :
    AllSpecs P C U :=
  ⟨fun q ins hq => instructionSpecs_of_clauses hU hC fun v hv => (h v hv).1 q ins hq,
    uniquenessSpecs_of_clauses hU fun v hv => (h v hv).2.1,
    recurrenceClause_sound hU (forall_admissible fun v hv => (h v hv).2.2)⟩

variable {v : Universals Tree}

/-- The specifications of an instruction imply its clauses. -/
theorem instructionClauses_of_specs (hU : U.TopFree) (hC : ∀ i, (C i).TopFree)
    (hcomb : ∀ i, IsComb (C i)) {n q : ℕ} (hshape : StubShaped U q) {ins : NInstr}
    (h : InstructionSpecs n C U q ins) (hv : v.Forall Tree.TopFree) :
    InstructionClauses (Existentials.standard C U) v n q ins := by
  cases ins with
  | inc d r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨transitionClause_complete hU hshape h1 hv,
      upperBoundClause_complete hU (hC d) hshape (hcomb d) h2 hv,
      lowerBoundClause_complete hU (hC d) hshape (hcomb d) h3 hv,
      upperBoundClause_complete hU (hC _) hshape (hcomb _) h4 hv,
      lowerBoundClause_complete hU (hC _) hshape (hcomb _) h5 hv⟩
  | jzdec d z p =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨zeroTestClause_complete hU (hC d) hshape h1 hv,
      positiveTestClause_complete hU (hC d) hshape h2 hv,
      upperBoundClause_complete hU (hC d) hshape (hcomb d) h3 hv,
      lowerBoundClause_complete hU (hC d) hshape (hcomb d) h4 hv,
      nextToothClause_complete hU (hC d) hshape h5 hv,
      upperBoundClause_complete hU (hC _) hshape (hcomb _) h6 hv,
      lowerBoundClause_complete hU (hC _) hshape (hcomb _) h7 hv⟩
  | choice l r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨branchClause_complete hU hshape h1 hv,
      upperBoundClause_complete hU (hC 0) hshape (hcomb 0) h2 hv,
      lowerBoundClause_complete hU (hC 0) hshape (hcomb 0) h3 hv,
      upperBoundClause_complete hU (hC 1) hshape (hcomb 1) h4 hv,
      lowerBoundClause_complete hU (hC 1) hshape (hcomb 1) h5 hv⟩

/-- The uniqueness specifications imply the uniqueness clauses for a stub-shaped state tree. -/
theorem uniquenessClauses_of_specs (hU : U.TopFree) {n : ℕ} (hshape : ∀ q, StubShaped U q)
    (h : UniquenessSpecs U n) (hv : v.Forall Tree.TopFree) :
    UniquenessClauses (Existentials.standard C U) v n := fun r q hrq hq =>
  haltUniqueClause_complete hU (hshape q) (h r q hrq hq) hv

/-- For combs and a stub-shaped state tree, the specifications imply all clauses. -/
theorem allClauses_of_specs {P : NProgram} (hU : U.TopFree) (hC : ∀ i, (C i).TopFree)
    (hcomb : ∀ i, IsComb (C i)) (hshape : ∀ q, StubShaped U q) (h : AllSpecs P C U)
    (hv : v.Forall Tree.TopFree) :
    AllClauses (Existentials.standard C U) v P :=
  ⟨fun q ins hq => instructionClauses_of_specs hU hC hcomb (hshape q) (h.1 q ins hq) hv,
    uniquenessClauses_of_specs hU hshape h.2.1 hv, recurrenceClause_complete hU h.2.2 hv⟩

end Recurrence

end UndeciSigma2
