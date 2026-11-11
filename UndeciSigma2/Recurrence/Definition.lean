import UndeciSigma2.Sentence.Definition
import UndeciSigma2.Recurrence.Machine

/-! # The recurrence sentence

For a nondeterministic two-counter program `P` with `n` instructions, the recurrence sentence
has the same prefix `∃⁹ ∀¹⁴` and the same variables as the machine sentence. Its matrix is
`rootConditions ∧ (guards → allClauses)`.

The root conditions state the helper equations, that the counters and the state tree contain
no top, that both counters are zero and the state is zero at step zero, and, as a positive
atom, that no step is in a state at least `n`: the comb of state `n` has no stub.

The clauses are the clauses of every instruction, uniqueness of the state at each step for
every pair of states `r < q < n`, and the recurrence clause. The clauses of `inc` and `jzdec`
are those of the machine sentence without the uniqueness clause of the halting state. The
clauses of `choice l r` are a branch clause, stating that a step from state `q` reaches `l` or
`r`, and the clauses copying both counters. The recurrence clause states that state `0` occurs
at arbitrarily late steps. Jump targets are clipped to `n`.
-/

namespace UndeciSigma2

open Sentence

namespace Recurrence

variable {top : Bool} {m : ℕ}

/-! ## Clauses -/

section Clauses
variable (x : Existentials (Term top m)) (v : Universals (Term top m))

/-- A step from state `q` reaches state `l` or state `r`:
`pack q y₁ ≤ U ∧ U ≤ stateContext Z l g₁ ∧ U ≤ stateContext Z r g₁ ∧ S ≤ g₁ → y₁ ≤ g₁`. -/
def branchClause (q l r : ℕ) : Formula top m :=
  Formula.imp
    (.and (.le (Term.pack q v.y₁) x.states)
      (.and (.le x.states (Term.stateContext x.full l v.g₁))
        (.and (.le x.states (Term.stateContext x.full r v.g₁)) (.le x.rightRay v.g₁))))
    (.le v.y₁ v.g₁)

/-- State `0` occurs at arbitrarily late steps:
`U ≤ f(g₁, Z) ∧ g₁ ≤ f(Z, g₁) ∧ y₁ ≤ T → y₁ ≤ g₁`. A bound `g₁` containing the comb of
state `0` and closed under removing leading ones contains every stub. -/
def recurrenceClause : Formula top m :=
  Formula.imp
    (.and (.le x.states (.f v.g₁ x.full))
      (.and (.le v.g₁ (.f x.full v.g₁)) (.le v.y₁ x.stubComb)))
    (.le v.y₁ v.g₁)

/-- The clauses for instruction `q` of a nondeterministic program with `n` instructions. -/
def instructionClauses (n q : ℕ) : NInstr → Formula top m
  | .inc c r =>
    .and (transitionClause x v q (min r n))
    (.and (upperBoundClause x v 0 false q c) (.and (lowerBoundClause x v 2 q c)
    (.and (upperBoundClause x v 1 false q (otherCounter c))
      (lowerBoundClause x v 1 q (otherCounter c)))))
  | .jzdec c z p =>
    .and (zeroTestClause x v q (min z n) c)
    (.and (positiveTestClause x v q (min p n) c) (.and (upperBoundClause x v 2 true q c)
    (.and (lowerBoundClause x v 0 q c) (.and (nextToothClause x v q c)
    (.and (upperBoundClause x v 1 false q (otherCounter c))
      (lowerBoundClause x v 1 q (otherCounter c)))))))
  | .choice l r =>
    .and (branchClause x v q (min l n) (min r n))
    (.and (upperBoundClause x v 1 false q 0) (.and (lowerBoundClause x v 1 q 0)
    (.and (upperBoundClause x v 1 false q 1) (lowerBoundClause x v 1 q 1))))

/-- The clauses of all instructions of a program. -/
def programClauses (P : NProgram) : Formula top m :=
  allOf ((List.range P.length).map fun q =>
    (P[q]?).elim trueAtom (instructionClauses x v P.length q))

/-- No step is both in state `r` and in state `q`, for all states `r < q < n`. -/
def uniquenessClauses (n : ℕ) : Formula top m :=
  allOf ((List.range n).map fun q =>
    allOf ((List.range q).map fun r => haltUniqueClause x v r q))

/-- The clauses of the matrix: the clauses of every instruction, the uniqueness clauses and
the recurrence clause. -/
def allClauses (P : NProgram) : Formula top m :=
  .and (programClauses x v P) (.and (uniquenessClauses x v P.length) (recurrenceClause x v))

end Clauses

/-- The root conditions for a program with `n` instructions: the six helper equations, the
guards of the counters and the state tree, both counters zero and state zero at step zero,
and no step in a state at least `n` (the comb of state `n` lies on the right ray). -/
def rootConditions (x : Existentials (Term top m)) (n : ℕ) : Formula top m :=
  .and (equation x.full (.f x.full x.full))
  (.and (equation x.rightRay (.f .bot x.rightRay))
  (.and (equation x.stubComb (.f Term.e x.stubComb))
  (.and (equation x.leftRay (.f x.leftRay .bot))
  (.and (equation x.combUniverse (.f x.leftRay x.combUniverse))
  (.and (equation x.shortCombs (.f (.f Term.e .bot) x.shortCombs))
  (.and (.le (x.counter 0) x.full) (.and (.le (x.counter 1) x.full) (.and (.le x.states x.full)
  (.and (.le (.f Term.e .bot) (x.counter 0)) (.and (.le (x.counter 0) (.f Term.e x.full))
  (.and (.le (.f Term.e .bot) (x.counter 1)) (.and (.le (x.counter 1) (.f Term.e x.full))
  (.and (.le (Term.pack 0 (.f Term.e .bot)) x.states)
    (.le x.states (Term.haltContext x.full x.rightRay n)))))))))))))))

/-- The quantifier-free matrix: the root conditions, and all clauses under the guards. -/
def matrix (x : Existentials (Term top m)) (v : Universals (Term top m)) (P : NProgram) :
    Formula top m :=
  .and (rootConditions x P.length) (.imp (guards x v) (allClauses x v P))

/-! ## Syntactic class of the matrix -/

section Syntax
variable (x : Existentials (Term top m)) (v : Universals (Term top m))

theorem isMatrix_instructionClauses (n q : ℕ) (i : NInstr) :
    (instructionClauses x v n q i).isMatrix = true := by
  cases i <;>
    simp [instructionClauses, branchClause, upperBoundClause, lowerBoundClause,
      transitionClause, nextToothClause, zeroTestClause, positiveTestClause, alignBlock,
      isMatrix_popBlock, Formula.imp, Formula.isMatrix]

theorem isLeOnly_instructionClauses (n q : ℕ) (i : NInstr) :
    (instructionClauses x v n q i).IsLeOnly := by
  cases i <;>
    simp [instructionClauses, branchClause, upperBoundClause, lowerBoundClause,
      transitionClause, nextToothClause, zeroTestClause, positiveTestClause, alignBlock,
      isLeOnly_popBlock, Formula.imp, Formula.IsLeOnly]

theorem isMatrix_uniquenessClauses (n : ℕ) : (uniquenessClauses x v n).isMatrix = true := by
  apply isMatrix_allOf
  intro φ hφ
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
  apply isMatrix_allOf
  intro ψ hψ
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hψ
  simp [haltUniqueClause, Formula.imp, Formula.isMatrix]

theorem isLeOnly_uniquenessClauses (n : ℕ) : (uniquenessClauses x v n).IsLeOnly := by
  apply isLeOnly_allOf
  intro φ hφ
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
  apply isLeOnly_allOf
  intro ψ hψ
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hψ
  simp [haltUniqueClause, Formula.imp, Formula.IsLeOnly]

theorem isMatrix_programClauses (P : NProgram) : (programClauses x v P).isMatrix = true := by
  apply isMatrix_allOf
  intro φ hφ
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
  cases P[q]? with
  | none => rfl
  | some i => exact isMatrix_instructionClauses x v _ q i

theorem isLeOnly_programClauses (P : NProgram) : (programClauses x v P).IsLeOnly := by
  apply isLeOnly_allOf
  intro φ hφ
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
  cases P[q]? with
  | none => trivial
  | some i => exact isLeOnly_instructionClauses x v _ q i

theorem isMatrix_matrix (P : NProgram) : (matrix x v P).isMatrix = true := by
  simp [matrix, allClauses, rootConditions, guards, equation, recurrenceClause, Formula.imp,
    Formula.isMatrix, isMatrix_programClauses, isMatrix_uniquenessClauses]

theorem isLeOnly_matrix (P : NProgram) : (matrix x v P).IsLeOnly := by
  simp [matrix, allClauses, rootConditions, guards, equation, recurrenceClause, Formula.imp,
    Formula.IsLeOnly, isLeOnly_programClauses, isLeOnly_uniquenessClauses]

end Syntax

end Recurrence

open Recurrence

/-- The Σ₂ sentence with prefix `∃⁹ ∀¹⁴` expressing that a nondeterministic two-counter
program has an infinite run visiting state `0` infinitely often. -/
def recurrenceSentence (top : Bool) (P : NProgram) : Formula top 0 :=
  exs 9 (alls 14 (Recurrence.matrix (existentialVars top) (universalVars top) P))

theorem recurrenceSentence_quantifiers (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).quantifiers =
      some (List.replicate 9 true ++ List.replicate 14 false) := by
  simp [recurrenceSentence, quantifiers_exs, quantifiers_alls,
    (Formula.quantifiers_eq_nil_iff _).mpr (Recurrence.isMatrix_matrix _ _ P)]

/-- The recurrence sentence is syntactically Σ₂. -/
theorem recurrenceSentence_isSigma (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).IsSigma 2 := by
  rw [Formula.IsSigma, recurrenceSentence_quantifiers]
  simp [List.replicate_succ, Formula.blocks]

/-- The recurrence sentence uses inequality as its only kind of atom. -/
theorem recurrenceSentence_isLeOnly (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).IsLeOnly := by
  simp only [recurrenceSentence, isLeOnly_exs, isLeOnly_alls]
  exact Recurrence.isLeOnly_matrix _ _ P

end UndeciSigma2
