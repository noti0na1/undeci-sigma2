import UndeciSigma2.Clock.Definition
import UndeciSigma2.Clock.Trees
import UndeciSigma2.Sentence.Semantics

/-! # Semantics of the clock sentence

Each atom, block and clause description has a semantic counterpart, a proposition about
trees, and the formulas realize their counterparts. The clock sentence holds in one of the
six structures exactly when twenty-one trees of the domain satisfy the guards and the root
conditions, and every clause holds for all values of the universal variables in the domain
(`clockSentence_holds_iff_clockConditions`). Nothing is assumed about the universal values:
in the signature with top they may contain top.
-/

namespace UndeciSigma2

open UndeciSigma2.Tree Clock

/-! ## Evaluation of the contexts -/

namespace Term
variable {top : Bool} {n : ℕ}

/-- Evaluation commutes with selection contexts. -/
@[simp] theorem eval_select (M : Structure top) (ρ : Fin n → M.Elem) (k : ℕ)
    (a : ℕ → Term top n) (t : Term top n) :
    ((select k a t).eval M ρ : Tree) = Tree.select k (fun l => (a l).eval M ρ) (t.eval M ρ) := by
  unfold select Tree.select
  induction List.range k with
  | nil => rfl
  | cons l ls ih => simp only [List.foldr_cons, eval_f, ih]

@[simp] theorem eval_componentContext (M : Structure top) (ρ : Fin n → M.Elem) (k : ℕ)
    (z : Term top n) (sel : ℕ → Bool) (g : Term top n) :
    ((componentContext k z sel g).eval M ρ : Tree) =
      Tree.componentContext k (z.eval M ρ) sel (g.eval M ρ) := by
  simp only [componentContext, Tree.componentContext, eval_select]
  congr 1
  funext l
  split <;> rfl

@[simp] theorem eval_tailContext (M : Structure top) (ρ : Fin n → M.Elem) (k : ℕ)
    (z : Term top n) (sel : ℕ → Bool) (g : Term top n) :
    ((tailContext k z sel g).eval M ρ : Tree) =
      Tree.tailContext k (z.eval M ρ) sel (g.eval M ρ) := by
  simp only [tailContext, Tree.tailContext, eval_select]
  congr 1
  funext l
  split <;> rfl

end Term

/-! ## Semantic atoms and clauses -/

namespace Clock

/-- Semantic counterpart of `SeedAtom.formula`. -/
def SeedAtom.Holds (y : Tree) : SeedAtom Tree → Prop
  | .le X => y ≤ X
  | .rightLe X => f bot y ≤ X
  | .component L l => pack l y ≤ L
  | .componentRight L l => pack l (f bot y) ≤ L

/-- Semantic counterpart of `BoundAtom.formula`. -/
def BoundAtom.Holds (z g : Tree) : BoundAtom Tree → Prop
  | .le X => X ≤ g
  | .rightLe X => X ≤ f z g
  | .components L m sel => L ≤ componentContext m z sel g
  | .tails L m sel => L ≤ tailContext m z sel g

/-- Semantic counterpart of `SeedShape.formulas`. -/
def SeedShape.Holds (y k k₀ : Tree) : SeedShape → Prop
  | .any => True
  | .spineOrStub => y ≤ k ∧ k ≤ f e k
  | .atMostOneZero => y ≤ k ∧ k ≤ f k₀ k ∧ k₀ ≤ f bot k₀

/-- Semantic counterpart of `dropBlock`. -/
def DropBlock (z y d : Tree) (gs : List Tree) : Prop :=
  y ≤ d ∧ d ≤ f z d ∧ ∀ g ∈ gs, d ≤ g

/-- Semantic counterpart of `strictDropBlock`. -/
def StrictDropBlock (z y e : Tree) (gs : List Tree) : Prop :=
  y ≤ f z e ∧ e ≤ f z e ∧ ∀ g ∈ gs, e ≤ g

end Clock

/-- Semantic counterpart of `ClockClause.formula`: the clause holds for the values `v` of the
universal variables. -/
def ClockClause.Holds (v : ClockUniversals Tree) : ClockClause Tree → Prop
  | .oneSeed seeds bounds sh =>
    (∀ a ∈ seeds, a.Holds v.y₁) → (∀ b ∈ bounds, b.Holds v.z v.g₁) →
      sh.Holds v.y₁ v.k v.k₀ → v.y₁ ≤ v.g₁
  | .window X E =>
    f bot v.y₁ ≤ X → f bot v.y₂ ≤ X → E ≤ v.g₁ → E ≤ v.g₂ → DropBlock v.z v.y₁ v.d₁ [v.g₂] →
      StrictDropBlock v.z v.y₂ v.e₂ [v.g₁] → v.y₁ ≤ v.g₁ ∨ v.y₂ ≤ v.g₂
  | .window3 X E =>
    f bot v.y₁ ≤ X → f bot v.y₂ ≤ X → f bot v.y₃ ≤ X → E ≤ v.g₁ → E ≤ v.g₂ → E ≤ v.g₃ →
      DropBlock v.z v.y₁ v.d₁ [v.g₂, v.g₃] → DropBlock v.z v.y₂ v.d₂ [v.g₃] →
      StrictDropBlock v.z v.y₂ v.e₂ [v.g₁] → StrictDropBlock v.z v.y₃ v.e₃ [v.g₁, v.g₂] →
      v.y₁ ≤ v.g₁ ∨ v.y₂ ≤ v.g₂ ∨ v.y₃ ≤ v.g₃
  | .chain B => v.y₁ ≤ B → v.y₂ ≤ B → v.y₁ ≤ v.y₂ ∨ v.y₂ ≤ v.y₁
  | .unwindBound N U => v.y₁ ≤ N → U ≤ v.k → v.k ≤ f v.g₁ v.k → v.y₁ ≤ v.g₁

namespace Clock

/-- Semantic counterpart of `guards`: the ray, the comb bound and the sink satisfy their
loops, and every other variable lies below the sink. -/
def Guarded (x : ClockExistentials Tree) : Prop :=
  x.ray ≤ f bot x.ray ∧ x.combBound ≤ f x.ray x.combBound ∧ x.sink ≤ f x.combBound x.sink ∧
    ∀ t ∈ x.guarded, t ≤ x.sink

/-- Semantic counterpart of `rootConditions`, for `m` labels. -/
structure RootConditions (m : ℕ) (x : ClockExistentials Tree) : Prop where
  /-- `f(e, ⊥) ≤ D`. -/
  clock_lower : f e bot ≤ x.clock
  /-- `D ≤ f(e, K₂)`. -/
  clock_upper : x.clock ≤ f e x.sink
  /-- The start label has the stub at stamp `0`. -/
  labels_start : pack startLabel (f e bot) ≤ x.labels
  /-- Every component lies below the clock, and `L` has no address `1ᵐ`. -/
  labels_clock : x.labels ≤ select m (fun _ => x.clock) bot
  /-- Only the start label has a tooth at stamp `0`. -/
  labels_left : x.labels ≤ select m (fun l => if l = startLabel then x.sink else f bot x.sink) bot
  chain_le_loop : x.chain ≤ x.chainLoop
  chainLoop_le : x.chainLoop ≤ f x.chain x.chainLoop
  /-- The head of the chain lies below the component of the end label. -/
  labels_end : pack endLabel x.chainHead ≤ x.labels
  counter_lower : ∀ i, f e bot ≤ x.counter i
  counter_upper : ∀ i, x.counter i ≤ f e x.sink
  clock_le_counter : ∀ i, x.clock ≤ x.counter i
  plusClass_le : ∀ i, x.plusClass i ≤ f bot x.sink
  zeroClass_le : ∀ i, x.zeroClass i ≤ f bot x.sink
  unwind_lower : f e bot ≤ x.unwind
  unwind_upper : x.unwind ≤ f e x.sink
  unwindPart_le : x.unwindPart ≤ f bot x.sink
  /-- The unwinding part lies below the component of the unwinding label. -/
  labels_unwind : pack unwindLabel x.unwindPart ≤ x.labels
  /-- The component of the build-up label lies below the build-up loop. -/
  labels_build : x.labels ≤ f x.sink (f x.buildLoop x.sink)
  buildLoop_le : x.buildLoop ≤ f x.buildRay x.buildLoop
  chain_not_le_head : ¬x.chain ≤ x.chainHead

/-- Semantic counterpart of `matrix`. -/
def MatrixHolds (P : Program) (x : ClockExistentials Tree) (v : ClockUniversals Tree) : Prop :=
  (Guarded x ∧ RootConditions (labelCount P) x) ∧ ∀ cl ∈ clauses P x, cl.Holds v

/-! ## Realization -/

section Realize

variable {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)

/-- The value of a term, as a tree. -/
abbrev evalTree (t : Term top n) : Tree := (t.eval M ρ : Tree)

/-- A conjunction holds exactly when all its members hold. -/
theorem realize_conj (ps : List (Formula top n)) :
    (conj ps).Realize M ρ ↔ ∀ φ ∈ ps, φ.Realize M ρ := by
  induction ps with
  | nil => exact iff_of_true (_root_.le_refl Tree.bot) (by simp)
  | cons φ ps ih =>
    cases ps with
    | nil => simp [conj]
    | cons ψ ψs =>
      simp only [conj, Formula.Realize] at ih ⊢
      rw [ih]; simp only [List.forall_mem_cons]

/-- A seed atom realizes its semantic counterpart. -/
theorem realize_seedAtom (y : Term top n) (a : SeedAtom (Term top n)) :
    (a.formula y).Realize M ρ ↔ (a.map (evalTree M ρ)).Holds (evalTree M ρ y) := by
  cases a <;> simp [SeedAtom.formula, SeedAtom.map, SeedAtom.Holds, Formula.Realize]

/-- A bound atom realizes its semantic counterpart. -/
theorem realize_boundAtom (z g : Term top n) (b : BoundAtom (Term top n)) :
    (b.formula z g).Realize M ρ ↔
      (b.map (evalTree M ρ)).Holds (evalTree M ρ z) (evalTree M ρ g) := by
  cases b <;> simp [BoundAtom.formula, BoundAtom.map, BoundAtom.Holds, Formula.Realize]

/-- The shape atoms realize their semantic counterpart. -/
theorem realize_seedShape (y k k₀ : Term top n) (sh : SeedShape) :
    (∀ φ ∈ sh.formulas y k k₀, φ.Realize M ρ) ↔
      sh.Holds (evalTree M ρ y) (evalTree M ρ k) (evalTree M ρ k₀) := by
  cases sh <;> simp [SeedShape.formulas, SeedShape.Holds, Formula.Realize]

/-- A clause formula realizes the semantic clause of the evaluated description. -/
theorem realize_formula (v : ClockUniversals (Term top n)) (c : ClockClause (Term top n)) :
    (c.formula v).Realize M ρ ↔ (c.map (evalTree M ρ)).Holds (v.map (evalTree M ρ)) := by
  cases c with
  | oneSeed seeds bounds sh =>
    simp only [ClockClause.formula, ClockClause.map, ClockClause.Holds, Formula.imp,
      Formula.Realize, realize_conj, List.forall_mem_append, List.forall_mem_map,
      ClockUniversals.map, evalTree, realize_seedAtom, realize_boundAtom, realize_seedShape]
    tauto
  | window X E =>
    simp only [ClockClause.formula, ClockClause.map, ClockClause.Holds, Formula.imp,
      Formula.Realize, realize_conj, List.forall_mem_append, List.forall_mem_cons,
      List.forall_mem_map, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, dropBlock,
      strictDropBlock, DropBlock, StrictDropBlock, Term.eval_f, Term.eval_bot, ClockUniversals.map,
      evalTree]
    tauto
  | window3 X E =>
    simp only [ClockClause.formula, ClockClause.map, ClockClause.Holds, Formula.imp,
      Formula.Realize, realize_conj, List.forall_mem_append, List.forall_mem_cons,
      List.forall_mem_map, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, dropBlock,
      strictDropBlock, DropBlock, StrictDropBlock, Term.eval_f, Term.eval_bot, ClockUniversals.map,
      evalTree]
    tauto
  | chain B =>
    simp only [ClockClause.formula, ClockClause.map, ClockClause.Holds, Formula.imp,
      Formula.Realize, ClockUniversals.map, evalTree]
    tauto
  | unwindBound N U =>
    simp only [ClockClause.formula, ClockClause.map, ClockClause.Holds, Formula.imp,
      Formula.Realize, Term.eval_f, ClockUniversals.map, evalTree]
    tauto

/-- The guards realize `Guarded`. -/
theorem realize_guards (x : ClockExistentials (Term top n)) :
    (guards x).Realize M ρ ↔ Guarded (x.map (evalTree M ρ)) := by
  rw [guards, realize_conj, Guarded, ClockExistentials.guarded_map]
  simp [ClockExistentials.map, Formula.Realize, evalTree]

/-- The root conditions realize `RootConditions`. -/
theorem realize_rootConditions (x : ClockExistentials (Term top n)) (m : ℕ) :
    (rootConditions x m).Realize M ρ ↔ RootConditions m (x.map (evalTree M ρ)) := by
  have hleft : (fun l => evalTree M ρ
      (if l = startLabel then x.sink else Term.f Term.bot x.sink)) =
      (fun l => if l = startLabel then evalTree M ρ x.sink
        else f bot (evalTree M ρ x.sink)) := by
    funext l
    split <;> simp [evalTree]
  simp only [rootConditions, realize_conj, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, forall_const,
    and_true,
    List.forall_mem_flatMap, List.mem_finRange, Formula.Realize,
    Term.eval_f, Term.eval_e, Term.eval_bot, Term.eval_pack, Term.eval_select]
  change _ ↔ RootConditions m (x.map (evalTree M ρ))
  simp only [hleft]
  constructor
  · rintro ⟨⟨⟨hclock, hupper, hstart, hlabels, hleft, hchain, hloop, hend⟩,
      hcounters⟩, hunwind, huupper, hpart, hulabel, hbuild, hbloop, hne⟩
    exact ⟨hclock, hupper, hstart, hlabels, hleft, hchain, hloop, hend,
      fun i => (hcounters i).1, fun i => (hcounters i).2.1,
      fun i => (hcounters i).2.2.1, fun i => (hcounters i).2.2.2.1,
      fun i => (hcounters i).2.2.2.2, hunwind, huupper, hpart, hulabel, hbuild, hbloop, hne⟩
  · intro h
    exact ⟨⟨⟨h.clock_lower, h.clock_upper, h.labels_start, h.labels_clock, h.labels_left,
      h.chain_le_loop, h.chainLoop_le, h.labels_end⟩,
      fun i => ⟨h.counter_lower i, h.counter_upper i, h.clock_le_counter i,
        h.plusClass_le i, h.zeroClass_le i⟩⟩,
      h.unwind_lower, h.unwind_upper, h.unwindPart_le, h.labels_unwind,
      h.labels_build, h.buildLoop_le, h.chain_not_le_head⟩

end Realize

/-- The clause descriptions commute with renaming the witnesses. -/
theorem clauses_map {α β : Type*} (g : α → β) (P : Program) (x : ClockExistentials α) :
    (clauses P x).map (ClockClause.map g) = clauses P (x.map g) := by
  simp only [clauses, uniqueClauses, transitionClauses, counterClauses, zeroTestClauses,
    List.map_append, List.map_cons, List.map_nil, List.map_flatMap, List.map_map,
    List.map_filterMap, Option.map_map]
  rfl

/-- The matrix realizes `MatrixHolds`. -/
theorem realize_matrix {top : Bool} {n : ℕ} (M : Structure top) (ρ : Fin n → M.Elem)
    (P : Program) (x : ClockExistentials (Term top n)) (v : ClockUniversals (Term top n)) :
    (matrix x P v).Realize M ρ ↔
      MatrixHolds P (x.map (evalTree M ρ)) (v.map (evalTree M ρ)) := by
  simp only [matrix, MatrixHolds, Formula.Realize, realize_guards, realize_rootConditions,
    Sentence.realize_allOf, List.forall_mem_map, realize_formula]
  rw [← clauses_map, List.forall_mem_map]

/-! ## Variables -/

theorem ClockExistentials.ofFn_toFn {α : Type*} (x : ClockExistentials α) :
    ClockExistentials.ofFn x.toFn = x := by
  have h : ∀ C : Fin 3 → α, ![C 0, C 1, C 2] = C := fun C => by
    funext i
    fin_cases i <;> rfl
  cases x
  simp only [ClockExistentials.ofFn, ClockExistentials.toFn, ClockExistentials.mk.injEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, h _, h _, h _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ClockExistentials.toList_eq_ofFn {α : Type*} (x : ClockExistentials α) :
    x.toList = List.ofFn x.toFn := rfl

theorem ClockExistentials.forall_iff_toFn {α : Type*} (p : α → Prop) (x : ClockExistentials α) :
    x.Forall p ↔ ∀ i, p (x.toFn i) := by
  rw [ClockExistentials.Forall, ClockExistentials.toList_eq_ofFn, List.forall_mem_ofFn_iff]

/-- The existential variables evaluate to the values of the existential block. -/
theorem eval_existentialVars {top : Bool} (M : Structure top) (x : Fin 21 → M.Elem)
    (y : Fin 13 → M.Elem) :
    (existentialVars top).map (evalTree M (Sentence.env y (Sentence.env x Fin.elim0))) =
      ClockExistentials.ofFn fun i => (x i : Tree) := by
  have h (i : Fin 21) :
      Sentence.env y (Sentence.env x Fin.elim0) (i.addNat 13) = x i :=
    (Sentence.env_back y (Sentence.env x Fin.elim0) (i : Fin (0 + 21))).trans
      (Sentence.env_front x Fin.elim0 i)
  unfold existentialVars ClockExistentials.map ClockExistentials.ofFn
  simp only [Function.comp_def, evalTree, Term.eval, h, ClockExistentials.mk.injEq, true_and,
    and_true]
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

/-- The universal variables evaluate to the values of the universal block. -/
theorem eval_universalVars {top : Bool} (M : Structure top) (x : Fin 21 → M.Elem)
    (y : Fin 13 → M.Elem) :
    (universalVars top).map (evalTree M (Sentence.env y (Sentence.env x Fin.elim0))) =
      ClockUniversals.ofFn fun i => (y i : Tree) := by
  have h (i : Fin 13) :
      Sentence.env y (Sentence.env x Fin.elim0) (i.castAdd 21) = y i :=
    Sentence.env_front y _ i
  simp only [universalVars, ClockUniversals.map, ClockUniversals.ofFn,
    evalTree, Term.eval, h]

/-- The sentence holds when twenty-one elements satisfy the semantic matrix for all thirteen. -/
theorem clockSentence_holds_iff_exists {top : Bool} (M : Structure top) (P : Program) :
    (clockSentence top P).Holds M ↔
      ∃ x : Fin 21 → M.Elem, ∀ y : Fin 13 → M.Elem,
        MatrixHolds P (ClockExistentials.ofFn fun i => (x i : Tree))
          (ClockUniversals.ofFn fun i => (y i : Tree)) := by
  simp only [clockSentence, Formula.Holds, Sentence.realize_exs, Sentence.realize_alls,
    realize_matrix, eval_existentialVars, eval_universalVars]

/-! ## The semantic content in the six structures -/

/-- The semantic content of the clock sentence in the domain of class `c`: twenty-one trees
of the domain satisfying the guards and the root conditions, such that every clause holds
for all values of the universal variables in the domain. -/
def ClockConditions (c : TreeClass) (top : Bool) (P : Program) : Prop :=
  ∃ x : ClockExistentials Tree, x.Forall (Domain c top) ∧ Guarded x ∧
    RootConditions (labelCount P) x ∧
    ∀ cl ∈ clauses P x, ∀ v : ClockUniversals Tree, v.Forall (Domain c top) → cl.Holds v

/-- In each of the six structures, the clock sentence states `ClockConditions`. -/
theorem clockSentence_holds_iff_clockConditions (top : Bool) (P : Program) (c : TreeClass) :
    (clockSentence top P).Holds (Structure.ofClass c top) ↔ ClockConditions c top P := by
  rw [clockSentence_holds_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨ClockExistentials.ofFn (fun i => (x i : Tree)), ?_,
      (hx default).1.1, (hx default).1.2, ?_⟩
    · rw [ClockExistentials.forall_iff_toFn, ClockExistentials.toFn_ofFn]
      exact fun i => (x i).property
    · intro cl hcl v hv
      have h := (hx (fun i => ⟨v.toFn i, hv i⟩)).2 cl hcl
      simpa only [ClockUniversals.ofFn_toFn] using h
  · rintro ⟨x, hx, hg, hr, hclauses⟩
    refine ⟨fun i => ⟨x.toFn i, (ClockExistentials.forall_iff_toFn _ x).mp hx i⟩, ?_⟩
    intro y
    simp only [ClockExistentials.ofFn_toFn]
    refine ⟨⟨hg, hr⟩, fun cl hcl => hclauses cl hcl _ ?_⟩
    change ∀ i, Domain c top ((ClockUniversals.ofFn (fun j => (y j : Tree))).toFn i)
    rw [ClockUniversals.toFn_ofFn]
    exact fun i => (y i).property

end Clock

end UndeciSigma2
