import UndeciSigma2.Sentence.Definition
import UndeciSigma2.Trees.Contexts

/-! # Semantics of the machine sentence

Each block and clause of the matrix has a semantic counterpart, a proposition
about trees with the same shape, and the formulas realize their counterparts.
The machine sentence holds in a structure exactly when nine elements satisfy the
semantic matrix for all fourteen elements.

In the regular and arbitrary domains the helper equations have their standard
solutions, the guards say that values contain no top, and the sentence reduces to
`MachineConditions`: two counter trees and a state tree satisfying the initial
conditions and the clauses of every instruction for all admissible values.
-/

namespace UndeciSigma2

open UndeciSigma2.Tree

/-! ## Evaluation of the contexts -/

namespace Term
variable {top : Bool} {n : ℕ}

@[simp] theorem eval_e (M : Structure top) (ρ : Fin n → M.Elem) :
    ((e : Term top n).eval M ρ : Tree) = Tree.e := rfl

@[simp] theorem eval_f (M : Structure top) (ρ : Fin n → M.Elem) (s t : Term top n) :
    ((Term.f s t).eval M ρ : Tree) = Tree.f (s.eval M ρ) (t.eval M ρ) := rfl

@[simp] theorem eval_bot (M : Structure top) (ρ : Fin n → M.Elem) :
    ((Term.bot : Term top n).eval M ρ : Tree) = Tree.bot := rfl

@[simp] theorem eval_pack (M : Structure top) (ρ : Fin n → M.Elem) (q : ℕ) (y : Term top n) :
    ((pack q y).eval M ρ : Tree) = Tree.pack q (y.eval M ρ) := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [pack, Tree.pack, eval_f, eval_bot, ih]

@[simp] theorem eval_stateContext (M : Structure top) (ρ : Fin n → M.Elem) (z : Term top n)
    (r : ℕ) (g : Term top n) :
    ((stateContext z r g).eval M ρ : Tree) = Tree.stateContext (z.eval M ρ) r (g.eval M ρ) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [stateContext, Tree.stateContext, eval_f, ih]

@[simp] theorem eval_haltContext (M : Structure top) (ρ : Fin n → M.Elem) (z s : Term top n)
    (k : ℕ) :
    ((haltContext z s k).eval M ρ : Tree) = Tree.haltContext (z.eval M ρ) (s.eval M ρ) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [haltContext, Tree.haltContext, eval_f, ih]

@[simp] theorem eval_popContext (M : Structure top) (ρ : Fin n → M.Elem) (z : Term top n)
    (δ : ℕ) (k : Term top n) :
    ((popContext z δ k).eval M ρ : Tree) = Tree.popContext (z.eval M ρ) δ (k.eval M ρ) := by
  induction δ with
  | zero => rfl
  | succ δ ih => simp only [popContext, Tree.popContext, eval_f, ih]

end Term

namespace Sentence

/-- Evaluate the existential terms. -/
def Existentials.eval {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)
    (x : Existentials (Term top n)) : Existentials Tree :=
  x.map fun s => (s.eval M ρ : Tree)

/-- Evaluate the universal terms. -/
def Universals.eval {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)
    (v : Universals (Term top n)) : Universals Tree :=
  v.map fun s => (s.eval M ρ : Tree)

/-! ## Semantic blocks and clauses -/

/-- Semantic counterpart of `alignBlock`. -/
def AlignBlock (z y g d p : Tree) : Prop :=
  y ≤ f z d ∧ d ≤ f z d ∧ d ≤ g ∧ f bot y ≤ p ∧ f bot p ≤ p ∧ p ≤ g

/-- Semantic counterpart of `popBlock`. -/
def PopBlock (z : Tree) : ℕ → (y g k k₀ kd kp : Tree) → Prop
  | 0, y, g, _, _, _, _ => y ≤ g
  | δ + 1, y, g, k, k₀, kd, kp =>
    y ≤ k ∧ k ≤ f k₀ k ∧ k₀ ≤ popContext z (δ + 1) kd ∧ f kd bot ≤ kp ∧ f bot kp ≤ kp ∧ kp ≤ g

section Clauses
variable (x : Existentials Tree) (v : Universals Tree)

/-- Semantic counterpart of `upperBoundClause`. -/
def UpperBoundClause (δ : ℕ) (trunc : Bool) (q : ℕ) (c : Fin 2) : Prop :=
  v.y₁ ≤ x.combUniverse ∧ x.counter c ≤ v.g₁ ∧ x.rightRay ≤ v.g₁ ∧ f bot v.y₂ ≤ x.counter c ∧
      PopBlock x.full δ v.y₁ v.g₂ v.k v.k₀ v.kd v.kp ∧
      (if trunc then x.stubComb else x.rightRay) ≤ v.g₂ ∧ pack q v.y₃ ≤ x.states ∧
      AlignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁ ∧ AlignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂ →
    v.y₁ ≤ v.g₁ ∨ v.y₂ ≤ v.g₂ ∨ v.y₃ ≤ v.g₃

/-- Semantic counterpart of `lowerBoundClause`. -/
def LowerBoundClause (δ q : ℕ) (c : Fin 2) : Prop :=
  v.y₁ ≤ x.counter c ∧ PopBlock x.full δ v.y₂ v.g₁ v.k v.k₀ v.kd v.kp ∧ x.rightRay ≤ v.g₁ ∧
      v.y₂ ≤ x.combUniverse ∧ x.counter c ≤ f x.full v.g₂ ∧ x.rightRay ≤ v.g₂ ∧
      pack q v.y₃ ≤ x.states ∧
      AlignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁ ∧ AlignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂ →
    v.y₁ ≤ v.g₁ ∨ v.y₂ ≤ v.g₂ ∨ v.y₃ ≤ v.g₃

/-- Semantic counterpart of `transitionClause`. -/
def TransitionClause (q r : ℕ) : Prop :=
  pack q v.y₁ ≤ x.states ∧ x.states ≤ stateContext x.full r v.g₁ ∧ x.rightRay ≤ v.g₁ →
    v.y₁ ≤ v.g₁

/-- Semantic counterpart of `nextToothClause`. -/
def NextToothClause (q : ℕ) (c : Fin 2) : Prop :=
  pack q v.y₁ ≤ x.states ∧ x.counter c ≤ f x.full v.g₁ ∧ x.rightRay ≤ v.g₁ → v.y₁ ≤ v.g₁

/-- Semantic counterpart of `haltUniqueClause`. -/
def HaltUniqueClause (n q : ℕ) : Prop :=
  pack q v.y₁ ≤ x.states ∧ pack n v.y₁ ≤ x.states → v.y₁ ≤ x.rightRay

/-- Semantic counterpart of `zeroTestClause`. -/
def ZeroTestClause (q r : ℕ) (c : Fin 2) : Prop :=
  v.y₁ ≤ x.shortCombs ∧ x.counter c ≤ v.g₁ ∧ x.stubComb ≤ v.g₁ ∧ pack q v.y₃ ≤ x.states ∧
      x.states ≤ stateContext x.full r v.g₃ ∧ AlignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁ →
    v.y₁ ≤ v.g₁ ∨ v.y₃ ≤ v.g₃

/-- Semantic counterpart of `positiveTestClause`. -/
def PositiveTestClause (q r : ℕ) (c : Fin 2) : Prop :=
  v.y₂ ≤ x.counter c ∧ v.y₂ ≤ x.combUniverse ∧ pack q v.y₃ ≤ x.states ∧
      x.states ≤ stateContext x.full r v.g₃ ∧ AlignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂ →
    v.y₂ ≤ x.stubComb ∨ v.y₃ ≤ v.g₃

/-- Semantic counterpart of `instructionClauses`. -/
def InstructionClauses (n q : ℕ) : Instr → Prop
  | .inc c r =>
    HaltUniqueClause x v n q ∧ TransitionClause x v q (min r n) ∧
      UpperBoundClause x v 0 false q c ∧ LowerBoundClause x v 2 q c ∧
      UpperBoundClause x v 1 false q (otherCounter c) ∧ LowerBoundClause x v 1 q (otherCounter c)
  | .jzdec c z p =>
    HaltUniqueClause x v n q ∧ ZeroTestClause x v q (min z n) c ∧
      PositiveTestClause x v q (min p n) c ∧ UpperBoundClause x v 2 true q c ∧
      LowerBoundClause x v 0 q c ∧ NextToothClause x v q c ∧
      UpperBoundClause x v 1 false q (otherCounter c) ∧ LowerBoundClause x v 1 q (otherCounter c)

/-- Semantic counterpart of `programClauses`. -/
def ProgramClauses (P : Program) : Prop :=
  ∀ q i, P[q]? = some i → InstructionClauses x v P.length q i

/-- Semantic counterpart of `guards`. -/
def Guards : Prop := v.Forall (· ≤ x.full)

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
  pack 0 (f e bot) ≤ x.states ∧ ¬x.states ≤ haltContext x.full x.rightRay n

/-- Semantic counterpart of `matrix`. -/
def MatrixHolds (x : Existentials Tree) (v : Universals Tree) (P : Program) : Prop :=
  RootConditions x P.length ∧ (Guards x v → ProgramClauses x v P)

/-! ## Realization -/

section Realize
variable {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)
variable (x : Existentials (Term top n)) (v : Universals (Term top n))

theorem realize_alignBlock (z y g d p : Term top n) :
    (alignBlock z y g d p).Realize M ρ ↔
      AlignBlock (z.eval M ρ) (y.eval M ρ) (g.eval M ρ) (d.eval M ρ) (p.eval M ρ) := Iff.rfl

theorem realize_popBlock (z : Term top n) (δ : ℕ) (y g k k₀ kd kp : Term top n) :
    (popBlock z δ y g k k₀ kd kp).Realize M ρ ↔
      PopBlock (z.eval M ρ) δ (y.eval M ρ) (g.eval M ρ) (k.eval M ρ) (k₀.eval M ρ)
        (kd.eval M ρ) (kp.eval M ρ) := by
  cases δ with
  | zero => rfl
  | succ δ =>
    simp only [popBlock, PopBlock, Formula.Realize, Term.eval_f, Term.eval_bot,
      Term.eval_popContext]

theorem realize_allOf (ps : List (Formula top n)) :
    (allOf ps).Realize M ρ ↔ ∀ φ ∈ ps, φ.Realize M ρ := by
  induction ps with
  | nil => simp only [allOf, List.foldr_nil, List.not_mem_nil, false_imp_iff, imp_true_iff,
      iff_true]; exact _root_.le_refl Tree.bot
  | cons φ ps ih =>
    simp only [allOf, List.foldr_cons, Formula.Realize, List.mem_cons, forall_eq_or_imp]
    exact and_congr_right fun _ => ih

theorem realize_upperBoundClause (δ : ℕ) (trunc : Bool) (q : ℕ) (c : Fin 2) :
    (upperBoundClause x v δ trunc q c).Realize M ρ ↔
      UpperBoundClause (x.eval M ρ) (v.eval M ρ) δ trunc q c := by
  cases trunc <;>
    simp only [upperBoundClause, UpperBoundClause, Bool.false_eq_true, ↓reduceIte, Formula.imp,
      Formula.Realize, realize_popBlock, realize_alignBlock, Term.eval_f, Term.eval_bot,
      Term.eval_pack, Existentials.eval, Universals.eval, Existentials.map, Universals.map,
      Function.comp_apply, imp_iff_not_or]

theorem realize_lowerBoundClause (δ q : ℕ) (c : Fin 2) :
    (lowerBoundClause x v δ q c).Realize M ρ ↔
      LowerBoundClause (x.eval M ρ) (v.eval M ρ) δ q c := by
  simp only [lowerBoundClause, LowerBoundClause, Formula.imp, Formula.Realize, realize_popBlock,
    realize_alignBlock, Term.eval_f, Term.eval_pack, Existentials.eval, Universals.eval,
    Existentials.map, Universals.map, Function.comp_apply, imp_iff_not_or]

theorem realize_transitionClause (q r : ℕ) :
    (transitionClause x v q r).Realize M ρ ↔ TransitionClause (x.eval M ρ) (v.eval M ρ) q r := by
  simp only [transitionClause, TransitionClause, Formula.imp, Formula.Realize, Term.eval_pack,
    Term.eval_stateContext, Existentials.eval, Universals.eval, Existentials.map,
    Universals.map, imp_iff_not_or]

theorem realize_nextToothClause (q : ℕ) (c : Fin 2) :
    (nextToothClause x v q c).Realize M ρ ↔ NextToothClause (x.eval M ρ) (v.eval M ρ) q c := by
  simp only [nextToothClause, NextToothClause, Formula.imp, Formula.Realize, Term.eval_f,
    Term.eval_pack, Existentials.eval, Universals.eval, Existentials.map, Universals.map,
    Function.comp_apply, imp_iff_not_or]

theorem realize_haltUniqueClause (k q : ℕ) :
    (haltUniqueClause x v k q).Realize M ρ ↔ HaltUniqueClause (x.eval M ρ) (v.eval M ρ) k q := by
  simp only [haltUniqueClause, HaltUniqueClause, Formula.imp, Formula.Realize, Term.eval_pack,
    Existentials.eval, Universals.eval, Existentials.map, Universals.map, imp_iff_not_or]

theorem realize_zeroTestClause (q r : ℕ) (c : Fin 2) :
    (zeroTestClause x v q r c).Realize M ρ ↔ ZeroTestClause (x.eval M ρ) (v.eval M ρ) q r c := by
  simp only [zeroTestClause, ZeroTestClause, Formula.imp, Formula.Realize, realize_alignBlock,
    Term.eval_pack, Term.eval_stateContext, Existentials.eval, Universals.eval,
    Existentials.map, Universals.map, Function.comp_apply, imp_iff_not_or]

theorem realize_positiveTestClause (q r : ℕ) (c : Fin 2) :
    (positiveTestClause x v q r c).Realize M ρ ↔
      PositiveTestClause (x.eval M ρ) (v.eval M ρ) q r c := by
  simp only [positiveTestClause, PositiveTestClause, Formula.imp, Formula.Realize,
    realize_alignBlock, Term.eval_pack, Term.eval_stateContext, Existentials.eval,
    Universals.eval, Existentials.map, Universals.map, Function.comp_apply, imp_iff_not_or]

theorem realize_instructionClauses (k q : ℕ) (i : Instr) :
    (instructionClauses x v k q i).Realize M ρ ↔
      InstructionClauses (x.eval M ρ) (v.eval M ρ) k q i := by
  cases i <;>
    simp only [instructionClauses, InstructionClauses, Formula.Realize, realize_upperBoundClause,
      realize_lowerBoundClause, realize_transitionClause, realize_nextToothClause,
      realize_haltUniqueClause, realize_zeroTestClause, realize_positiveTestClause]

theorem realize_programClauses (P : Program) :
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

theorem realize_guards : (guards x v).Realize M ρ ↔ Guards (x.eval M ρ) (v.eval M ρ) := by
  simp only [guards, Guards, Universals.Forall, Formula.Realize, Existentials.eval,
    Universals.eval, Existentials.map, Universals.map]

theorem realize_rootConditions (k : ℕ) :
    (rootConditions x k).Realize M ρ ↔ RootConditions (x.eval M ρ) k := by
  simp only [rootConditions, RootConditions, equation, Formula.Realize, Term.eval_f,
    Term.eval_bot, Term.eval_e, Term.eval_pack, Term.eval_haltContext, Existentials.eval,
    Existentials.map, Function.comp_apply]

theorem realize_matrix (P : Program) :
    (matrix x v P).Realize M ρ ↔ MatrixHolds (x.eval M ρ) (v.eval M ρ) P := by
  simp only [matrix, MatrixHolds, Formula.Realize, Formula.imp, realize_rootConditions,
    realize_guards, realize_programClauses, imp_iff_not_or]

end Realize

private theorem env_existential {α : Type*} (x : Fin 9 → α) (y : Fin 14 → α) (i : Fin 9) :
    env y (env x (Fin.elim0 : Fin 0 → α)) (i.addNat 14) = x i :=
  (env_back y (env x Fin.elim0) (i : Fin (0 + 9))).trans (env_front x Fin.elim0 i)

private theorem env_universal {α : Type*} (x : Fin 9 → α) (y : Fin 14 → α) (i : Fin 14) :
    env y (env x (Fin.elim0 : Fin 0 → α)) (i.castAdd 9) = y i :=
  env_front y _ i

theorem eval_existentialVars {top : Bool} (M : Structure top) (x : Fin 9 → M.Elem)
    (y : Fin 14 → M.Elem) :
    (existentialVars top).eval M (env y (env x Fin.elim0)) =
      Existentials.ofFn fun i => (x i : Tree) := by
  unfold existentialVars Existentials.eval Existentials.map Existentials.ofFn
  congr 1
  · funext i
    fin_cases i
    · exact congrArg Subtype.val (env_existential x y 0)
    · exact congrArg Subtype.val (env_existential x y 1)

theorem eval_universalVars {top : Bool} (M : Structure top) (x : Fin 9 → M.Elem)
    (y : Fin 14 → M.Elem) :
    (universalVars top).eval M (env y (env x Fin.elim0)) =
      Universals.ofFn fun i => (y i : Tree) := by
  simp only [universalVars, Universals.eval, Universals.map, Universals.ofFn, Term.eval,
    env_universal]

/-- The sentence holds when nine elements satisfy the semantic matrix for all fourteen. -/
theorem machineSentence_holds_iff_exists {top : Bool} (M : Structure top) (P : Program) :
    (machineSentence top P).Holds M ↔
      ∃ x : Fin 9 → M.Elem, ∀ y : Fin 14 → M.Elem,
        MatrixHolds (Existentials.ofFn fun i => (x i : Tree))
          (Universals.ofFn fun i => (y i : Tree)) P := by
  simp only [machineSentence, Formula.Holds, realize_exs, realize_alls, realize_matrix,
    eval_existentialVars, eval_universalVars]

/-! ## Standard helpers -/

/-- The existential values with the standard helper trees. -/
def Existentials.standard (C : Fin 2 → Tree) (U : Tree) : Existentials Tree :=
  ⟨C, U, Tree.full, Tree.rightRay, Tree.stubComb, Tree.leftRay, Tree.combUniverse,
    Tree.shortCombs⟩

@[simp] theorem Existentials.standard_counter (C : Fin 2 → Tree) (U : Tree) :
    (Existentials.standard C U).counter = C := rfl
@[simp] theorem Existentials.standard_states (C : Fin 2 → Tree) (U : Tree) :
    (Existentials.standard C U).states = U := rfl

/-- An admissible value of a universal variable: an element of the domain without top. -/
def Admissible (c : TreeClass) (top : Bool) (t : Tree) : Prop :=
  Domain c top t ∧ t.TopFree

/-- The root conditions on the counter trees `C` and the state tree `U`, with the standard
helpers: no top, both counters zero and the state zero at step zero, and the halting state
`n` at some step. -/
def InitialConditions (n : ℕ) (C : Fin 2 → Tree) (U : Tree) : Prop :=
  (∀ i, (C i).TopFree) ∧ U.TopFree ∧ (∀ i, f e bot ≤ C i ∧ C i ≤ f e full) ∧
    pack 0 (f e bot) ≤ U ∧ ¬U ≤ haltContext full rightRay n

/-- The semantic content of the machine sentence in the domain of class `c`. -/
def MachineConditions (c : TreeClass) (top : Bool) (P : Program) : Prop :=
  ∃ (C : Fin 2 → Tree) (U : Tree), (∀ i, Domain c top (C i)) ∧ Domain c top U ∧
    InitialConditions P.length C U ∧
    ∀ v : Universals Tree, v.Forall (Admissible c top) →
      ProgramClauses (Existentials.standard C U) v P

/-- The six helper equations, each written as two inequalities, force the standard
helpers. -/
theorem eq_standard_of_helperEquations {x : Existentials Tree}
    (h : (x.full ≤ f x.full x.full ∧ f x.full x.full ≤ x.full) ∧
      (x.rightRay ≤ f bot x.rightRay ∧ f bot x.rightRay ≤ x.rightRay) ∧
      (x.stubComb ≤ f e x.stubComb ∧ f e x.stubComb ≤ x.stubComb) ∧
      (x.leftRay ≤ f x.leftRay bot ∧ f x.leftRay bot ≤ x.leftRay) ∧
      (x.combUniverse ≤ f x.leftRay x.combUniverse ∧
        f x.leftRay x.combUniverse ≤ x.combUniverse) ∧
      (x.shortCombs ≤ f (f e bot) x.shortCombs ∧ f (f e bot) x.shortCombs ≤ x.shortCombs)) :
    x = Existentials.standard x.counter x.states := by
  obtain ⟨⟨hz₁, hz₂⟩, ⟨hs₁, hs₂⟩, ⟨ht₁, ht₂⟩, ⟨hl₁, hl₂⟩, ⟨hg₁, hg₂⟩, ⟨hh₁, hh₂⟩⟩ := h
  have hl := eq_leftRay_of_eq (_root_.le_antisymm hl₁ hl₂)
  have hg : x.combUniverse = f leftRay x.combUniverse := hl ▸ _root_.le_antisymm hg₁ hg₂
  cases x
  simp only [Existentials.standard, Existentials.mk.injEq, true_and]
  exact ⟨eq_full_of_eq (_root_.le_antisymm hz₁ hz₂),
    eq_rightRay_of_eq (_root_.le_antisymm hs₁ hs₂),
    eq_stubComb_of_eq (_root_.le_antisymm ht₁ ht₂), hl, eq_combUniverse_of_eq hg,
    eq_shortCombs_of_eq (_root_.le_antisymm hh₁ hh₂)⟩

/-- The standard helpers satisfy the six helper equations. -/
theorem helperEquations_standard :
    (full ≤ f full full ∧ f full full ≤ full) ∧
      (rightRay ≤ f bot rightRay ∧ f bot rightRay ≤ rightRay) ∧
      (stubComb ≤ f e stubComb ∧ f e stubComb ≤ stubComb) ∧
      (leftRay ≤ f leftRay bot ∧ f leftRay bot ≤ leftRay) ∧
      (combUniverse ≤ f leftRay combUniverse ∧ f leftRay combUniverse ≤ combUniverse) ∧
      (shortCombs ≤ f (f e bot) shortCombs ∧ f (f e bot) shortCombs ≤ shortCombs) :=
  ⟨⟨full_eq.le, full_eq.ge⟩, ⟨rightRay_eq.le, rightRay_eq.ge⟩,
    ⟨stubComb_eq.le, stubComb_eq.ge⟩, ⟨leftRay_eq.le, leftRay_eq.ge⟩,
    ⟨combUniverse_eq.le, combUniverse_eq.ge⟩, ⟨shortCombs_eq.le, shortCombs_eq.ge⟩⟩

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

/-- Outside the finite domain, the machine sentence states `MachineConditions`. -/
theorem machineSentence_holds_iff_machineConditions (top : Bool) (P : Program) {c : TreeClass}
    (hc : c ≠ .finite) :
    (machineSentence top P).Holds (Structure.ofClass c top) ↔ MachineConditions c top P := by
  rw [machineSentence_holds_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    have hroot := (hx default).1
    have hstd := eq_standard_of_rootConditions hroot
    refine ⟨![(x 0 : Tree), (x 1 : Tree)], (x 2 : Tree), ?_, (x 2).2, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact (x 0).2
      · exact (x 1).2
    · rw [hstd] at hroot
      exact (rootConditions_standard_iff _ _ _).mp hroot
    · intro v hv
      have hy := hx fun i => ⟨v.toFn i, ((Universals.forall_iff_toFn _ v).mp hv i).1⟩
      rw [hstd] at hy
      refine hy.2 ?_
      exact hv.imp fun t ht => (le_full_iff t).mpr ht.2
  · rintro ⟨C, U, hC, hU, hinit, hcl⟩
    have hd : ∀ {t : Tree}, t.IsRegular → t.TopFree → Domain c top t :=
      fun hr ht => domain_of_isRegular hc hr ht
    refine ⟨![⟨C 0, hC 0⟩, ⟨C 1, hC 1⟩, ⟨U, hU⟩, ⟨full, hd regular_full topFree_full⟩,
      ⟨rightRay, hd regular_rightRay topFree_rightRay⟩,
      ⟨stubComb, hd regular_stubComb topFree_stubComb⟩,
      ⟨leftRay, hd regular_leftRay topFree_leftRay⟩,
      ⟨combUniverse, hd regular_combUniverse topFree_combUniverse⟩,
      ⟨shortCombs, hd regular_shortCombs topFree_shortCombs⟩], fun y => ?_⟩
    have hX : Existentials.ofFn (fun i => ((![⟨C 0, hC 0⟩, ⟨C 1, hC 1⟩, ⟨U, hU⟩,
        ⟨full, hd regular_full topFree_full⟩, ⟨rightRay, hd regular_rightRay topFree_rightRay⟩,
        ⟨stubComb, hd regular_stubComb topFree_stubComb⟩,
        ⟨leftRay, hd regular_leftRay topFree_leftRay⟩,
        ⟨combUniverse, hd regular_combUniverse topFree_combUniverse⟩,
        ⟨shortCombs, hd regular_shortCombs topFree_shortCombs⟩] :
          Fin 9 → (Structure.ofClass c top).Elem) i : Tree)) = Existentials.standard C U := by
      unfold Existentials.ofFn Existentials.standard
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hX]
    refine ⟨(rootConditions_standard_iff _ _ _).mpr hinit, fun hg => hcl _ ?_⟩
    simp only [Guards] at hg
    rw [Universals.forall_iff_toFn, Universals.toFn_ofFn] at hg ⊢
    intro i
    exact ⟨(y i).2, (le_full_iff _).mp (hg i)⟩

end Sentence

end UndeciSigma2
