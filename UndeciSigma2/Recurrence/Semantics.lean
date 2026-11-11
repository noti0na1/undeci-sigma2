import UndeciSigma2.Sentence.Semantics
import UndeciSigma2.Recurrence.Definition

/-! # Semantics of the recurrence sentence

Each additional clause and each clause list of the recurrence sentence has a semantic
counterpart, and the formulas realize their counterparts. Over arbitrary trees the helper
equations have their standard solutions, every top-free tree is a value of a universal
variable, and the sentence reduces to `RecurrenceConditions`: two counter trees and a state
tree satisfying the initial conditions and all clauses for all top-free values.
-/

namespace UndeciSigma2

open UndeciSigma2.Tree Sentence

namespace Recurrence

/-! ## Semantic clauses -/

section Clauses
variable (x : Existentials Tree) (v : Universals Tree)

/-- Semantic counterpart of `branchClause`. -/
def BranchClause (q l r : ℕ) : Prop :=
  pack q v.y₁ ≤ x.states ∧ x.states ≤ stateContext x.full l v.g₁ ∧
      x.states ≤ stateContext x.full r v.g₁ ∧ x.rightRay ≤ v.g₁ →
    v.y₁ ≤ v.g₁

/-- Semantic counterpart of `recurrenceClause`. -/
def RecurrenceClause : Prop :=
  x.states ≤ f v.g₁ x.full ∧ v.g₁ ≤ f x.full v.g₁ ∧ v.y₁ ≤ x.stubComb → v.y₁ ≤ v.g₁

/-- Semantic counterpart of `instructionClauses`. -/
def InstructionClauses (n q : ℕ) : NInstr → Prop
  | .inc c r =>
    TransitionClause x v q (min r n) ∧
      UpperBoundClause x v 0 false q c ∧ LowerBoundClause x v 2 q c ∧
      UpperBoundClause x v 1 false q (otherCounter c) ∧ LowerBoundClause x v 1 q (otherCounter c)
  | .jzdec c z p =>
    ZeroTestClause x v q (min z n) c ∧
      PositiveTestClause x v q (min p n) c ∧ UpperBoundClause x v 2 true q c ∧
      LowerBoundClause x v 0 q c ∧ NextToothClause x v q c ∧
      UpperBoundClause x v 1 false q (otherCounter c) ∧ LowerBoundClause x v 1 q (otherCounter c)
  | .choice l r =>
    BranchClause x v q (min l n) (min r n) ∧
      UpperBoundClause x v 1 false q 0 ∧ LowerBoundClause x v 1 q 0 ∧
      UpperBoundClause x v 1 false q 1 ∧ LowerBoundClause x v 1 q 1

/-- Semantic counterpart of `programClauses`. -/
def ProgramClauses (P : NProgram) : Prop :=
  ∀ q i, P[q]? = some i → InstructionClauses x v P.length q i

/-- Semantic counterpart of `uniquenessClauses`. -/
def UniquenessClauses (n : ℕ) : Prop :=
  ∀ r q, r < q → q < n → HaltUniqueClause x v r q

/-- Semantic counterpart of `allClauses`. -/
def AllClauses (P : NProgram) : Prop :=
  ProgramClauses x v P ∧ UniquenessClauses x v P.length ∧ RecurrenceClause x v

end Clauses

/-- Semantic counterpart of `rootConditions`. -/
def RootConditions (x : Existentials Tree) (n : ℕ) : Prop :=
  (x.full ≤ f x.full x.full ∧ f x.full x.full ≤ x.full) ∧
  (x.rightRay ≤ f bot x.rightRay ∧ f bot x.rightRay ≤ x.rightRay) ∧
  (x.stubComb ≤ f e x.stubComb ∧ f e x.stubComb ≤ x.stubComb) ∧
  (x.leftRay ≤ f x.leftRay bot ∧ f x.leftRay bot ≤ x.leftRay) ∧
  (x.combUniverse ≤ f x.leftRay x.combUniverse ∧ f x.leftRay x.combUniverse ≤ x.combUniverse) ∧
  (x.shortCombs ≤ f (f e bot) x.shortCombs ∧ f (f e bot) x.shortCombs ≤ x.shortCombs) ∧
  x.counter 0 ≤ x.full ∧ x.counter 1 ≤ x.full ∧ x.states ≤ x.full ∧
  f e bot ≤ x.counter 0 ∧ x.counter 0 ≤ f e x.full ∧
  f e bot ≤ x.counter 1 ∧ x.counter 1 ≤ f e x.full ∧
  pack 0 (f e bot) ≤ x.states ∧ x.states ≤ haltContext x.full x.rightRay n

/-- Semantic counterpart of `matrix`. -/
def MatrixHolds (x : Existentials Tree) (v : Universals Tree) (P : NProgram) : Prop :=
  RootConditions x P.length ∧ (Guards x v → AllClauses x v P)

/-! ## Realization -/

section Realize
variable {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)
variable (x : Existentials (Term top n)) (v : Universals (Term top n))

theorem realize_branchClause (q l r : ℕ) :
    (branchClause x v q l r).Realize M ρ ↔ BranchClause (x.eval M ρ) (v.eval M ρ) q l r := by
  simp only [branchClause, BranchClause, Formula.imp, Formula.Realize, Term.eval_pack,
    Term.eval_stateContext, Existentials.eval, Universals.eval, Existentials.map,
    Universals.map, imp_iff_not_or]

theorem realize_recurrenceClause :
    (recurrenceClause x v).Realize M ρ ↔ RecurrenceClause (x.eval M ρ) (v.eval M ρ) := by
  simp only [recurrenceClause, RecurrenceClause, Formula.imp, Formula.Realize, Term.eval_f,
    Existentials.eval, Universals.eval, Existentials.map, Universals.map, imp_iff_not_or]

theorem realize_instructionClauses (k q : ℕ) (i : NInstr) :
    (instructionClauses x v k q i).Realize M ρ ↔
      InstructionClauses (x.eval M ρ) (v.eval M ρ) k q i := by
  cases i <;>
    simp only [instructionClauses, InstructionClauses, Formula.Realize, realize_branchClause,
      realize_upperBoundClause, realize_lowerBoundClause, realize_transitionClause,
      realize_nextToothClause, realize_zeroTestClause, realize_positiveTestClause]

theorem realize_programClauses (P : NProgram) :
    (programClauses x v P).Realize M ρ ↔ ProgramClauses (x.eval M ρ) (v.eval M ρ) P := by
  rw [programClauses, realize_allOf]
  constructor
  · intro h q i hq
    have hlt : q < P.length := (List.getElem?_eq_some_iff.mp hq).1
    have hi := h _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hlt, rfl⟩)
    rw [hq] at hi
    exact (realize_instructionClauses M ρ x v _ q i).mp hi
  · intro h φ hφ
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
    cases hq : P[q]? with
    | none => exact _root_.le_refl Tree.bot
    | some i => exact (realize_instructionClauses M ρ x v _ q i).mpr (h q i hq)

theorem realize_uniquenessClauses (k : ℕ) :
    (uniquenessClauses x v k).Realize M ρ ↔ UniquenessClauses (x.eval M ρ) (v.eval M ρ) k := by
  rw [uniquenessClauses, realize_allOf]
  constructor
  · intro h r q hrq hq
    have hi := h _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
    rw [realize_allOf] at hi
    exact (realize_haltUniqueClause M ρ x v r q).mp
      (hi _ (List.mem_map.mpr ⟨r, List.mem_range.mpr hrq, rfl⟩))
  · intro h φ hφ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hφ
    rw [realize_allOf]
    intro ψ hψ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hψ
    exact (realize_haltUniqueClause M ρ x v r q).mpr
      (h r q (List.mem_range.mp hr) (List.mem_range.mp hq))

theorem realize_allClauses (P : NProgram) :
    (allClauses x v P).Realize M ρ ↔ AllClauses (x.eval M ρ) (v.eval M ρ) P := by
  simp only [allClauses, AllClauses, Formula.Realize, realize_programClauses,
    realize_uniquenessClauses, realize_recurrenceClause]

theorem realize_rootConditions (k : ℕ) :
    (rootConditions x k).Realize M ρ ↔ RootConditions (x.eval M ρ) k := by
  simp only [rootConditions, RootConditions, equation, Formula.Realize, Term.eval_f,
    Term.eval_bot, Term.eval_e, Term.eval_pack, Term.eval_haltContext, Existentials.eval,
    Existentials.map, Function.comp_apply]

theorem realize_matrix (P : NProgram) :
    (matrix x v P).Realize M ρ ↔ MatrixHolds (x.eval M ρ) (v.eval M ρ) P := by
  simp only [matrix, MatrixHolds, Formula.Realize, Formula.imp, realize_rootConditions,
    realize_guards, realize_allClauses, imp_iff_not_or]

end Realize

/-- The sentence holds when nine elements satisfy the semantic matrix for all fourteen. -/
theorem recurrenceSentence_holds_iff_exists {top : Bool} (M : Structure top) (P : NProgram) :
    (recurrenceSentence top P).Holds M ↔
      ∃ x : Fin 9 → M.Elem, ∀ y : Fin 14 → M.Elem,
        MatrixHolds (Existentials.ofFn fun i => (x i : Tree))
          (Universals.ofFn fun i => (y i : Tree)) P := by
  simp only [recurrenceSentence, Formula.Holds, realize_exs, realize_alls, realize_matrix,
    eval_existentialVars, eval_universalVars]

/-! ## Standard helpers -/

/-- The root conditions on the counter trees `C` and the state tree `U`, with the standard
helpers: no top, both counters zero and the state zero at step zero, and no stub in the comb
of state `n`. -/
def InitialConditions (n : ℕ) (C : Fin 2 → Tree) (U : Tree) : Prop :=
  (∀ i, (C i).TopFree) ∧ U.TopFree ∧ (∀ i, f e bot ≤ C i ∧ C i ≤ f e full) ∧
    pack 0 (f e bot) ≤ U ∧ U ≤ haltContext full rightRay n

/-- The semantic content of the recurrence sentence over arbitrary trees: counter trees and
a state tree satisfying the initial conditions and all clauses for all top-free values of the
universal variables. -/
def RecurrenceConditions (P : NProgram) : Prop :=
  ∃ (C : Fin 2 → Tree) (U : Tree), InitialConditions P.length C U ∧
    ∀ v : Universals Tree, v.Forall Tree.TopFree → AllClauses (Existentials.standard C U) v P

/-- The root conditions force the standard helpers. -/
theorem eq_standard_of_rootConditions {x : Existentials Tree} {n : ℕ}
    (h : RootConditions x n) : x = Existentials.standard x.counter x.states := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h
  exact eq_standard_of_helperEquations ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

theorem rootConditions_standard_iff (n : ℕ) (C : Fin 2 → Tree) (U : Tree) :
    RootConditions (Existentials.standard C U) n ↔ InitialConditions n C U := by
  simp only [RootConditions, InitialConditions, Existentials.standard,
    helperEquations_standard, true_and]
  simp only [le_full_iff, Fin.forall_fin_two]
  tauto

/-- Over arbitrary trees, the recurrence sentence states `RecurrenceConditions`. -/
theorem recurrenceSentence_holds_iff_recurrenceConditions (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).Holds (Structure.ofClass .arbitrary top) ↔
      RecurrenceConditions P := by
  rw [recurrenceSentence_holds_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    have hroot := (hx default).1
    have hstd := eq_standard_of_rootConditions hroot
    refine ⟨![(x 0 : Tree), (x 1 : Tree)], (x 2 : Tree), ?_, ?_⟩
    · rw [hstd] at hroot
      exact (rootConditions_standard_iff _ _ _).mp hroot
    · intro v hv
      have hy := hx fun i => ⟨v.toFn i,
        domain_arbitrary_of_topFree ((Universals.forall_iff_toFn _ v).mp hv i)⟩
      rw [hstd] at hy
      refine hy.2 ?_
      exact hv.imp fun t ht => (le_full_iff t).mpr ht
  · rintro ⟨C, U, hinit, hcl⟩
    have hd : ∀ {t : Tree}, t.TopFree → Domain .arbitrary top t :=
      fun ht => domain_arbitrary_of_topFree ht
    refine ⟨![⟨C 0, hd (hinit.1 0)⟩, ⟨C 1, hd (hinit.1 1)⟩, ⟨U, hd hinit.2.1⟩,
      ⟨full, hd topFree_full⟩, ⟨rightRay, hd topFree_rightRay⟩, ⟨stubComb, hd topFree_stubComb⟩,
      ⟨leftRay, hd topFree_leftRay⟩, ⟨combUniverse, hd topFree_combUniverse⟩,
      ⟨shortCombs, hd topFree_shortCombs⟩], fun y => ?_⟩
    have hX : Existentials.ofFn (fun i => ((![⟨C 0, hd (hinit.1 0)⟩, ⟨C 1, hd (hinit.1 1)⟩,
        ⟨U, hd hinit.2.1⟩, ⟨full, hd topFree_full⟩, ⟨rightRay, hd topFree_rightRay⟩,
        ⟨stubComb, hd topFree_stubComb⟩, ⟨leftRay, hd topFree_leftRay⟩,
        ⟨combUniverse, hd topFree_combUniverse⟩, ⟨shortCombs, hd topFree_shortCombs⟩] :
          Fin 9 → (Structure.ofClass .arbitrary top).Elem) i : Tree)) =
        Existentials.standard C U := by
      unfold Existentials.ofFn Existentials.standard
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hX]
    refine ⟨(rootConditions_standard_iff _ _ _).mpr hinit, fun hg => hcl _ ?_⟩
    simp only [Guards] at hg
    rw [Universals.forall_iff_toFn, Universals.toFn_ofFn] at hg ⊢
    intro i
    exact (le_full_iff _).mp (hg i)

end Recurrence

end UndeciSigma2
