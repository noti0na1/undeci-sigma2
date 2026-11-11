import Mathlib

/-! # Binary trees and their finite presentations

Trees are partial labelings of binary paths by bottom, a binary constructor,
and top. Finite terms and finite graphs represent finite and regular trees.
The three tree classes, with or without top, give the six structures.
-/

namespace UndeciSigma2

/-- The three tree labels, ordered as bottom, constructor and top. -/
inductive Sym where
  | bot | f | top
  deriving DecidableEq, Repr

namespace Sym

/-- The rank of a label in the order `⊥ < f < ⊤`. -/
def rank : Sym → Nat
  | bot => 0
  | f => 1
  | top => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder Sym := LinearOrder.lift' rank rank_injective

@[simp] theorem bot_le (a : Sym) : bot ≤ a := by cases a <;> decide
@[simp] theorem le_top (a : Sym) : a ≤ top := by cases a <;> decide

@[simp] theorem le_bot_iff (a : Sym) : a ≤ bot ↔ a = bot := by
  cases a <;> decide

@[simp] theorem top_le_iff (a : Sym) : top ≤ a ↔ a = top := by
  cases a <;> decide

end Sym

end UndeciSigma2

/-! # Finite and infinite trees

Trees are partial labelings of paths over `Fin 2`: the root exists, and exactly
constructor nodes have children. The covariant order compares labels at shared
paths. Bottom and top are leaves.
-/

namespace UndeciSigma2

/-- A finite or infinite tree represented by a well-formed partial labeling of paths. -/
structure Tree where
  /-- The label at each path, or `none` outside the tree domain. -/
  fn : List (Fin 2) → Option Sym
  /-- The root exists, and a path has children if and only if it is labeled `f`. -/
  wf : fn [] ≠ none ∧ ∀ π i, (fn (π ++ [i])).isSome ↔ fn π = some Sym.f

namespace Tree


@[ext] theorem ext {t u : Tree} (h : t.fn = u.fn) : t = u := by
  cases t
  cases u
  cases h
  rfl

theorem root_isSome (t : Tree) : (t.fn []).isSome :=
  Option.isSome_iff_ne_none.mpr t.wf.1

theorem child_isSome_iff (t : Tree) (π : List (Fin 2)) (i : Fin 2) :
    (t.fn (π ++ [i])).isSome ↔ t.fn π = some Sym.f := t.wf.2 π i

/-- Removing any suffix preserves membership in the domain. -/
theorem domain_append_left (t : Tree) (π ρ : List (Fin 2))
    (h : (t.fn (π ++ ρ)).isSome) : (t.fn π).isSome := by
  induction ρ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton ρ i ih =>
    have hf : t.fn (π ++ ρ) = some Sym.f :=
      (t.child_isSome_iff (π ++ ρ) i).mp (by simpa [List.append_assoc] using h)
    exact ih (by simp [hf])

/-- Every proper prefix of a path in the domain is labeled `f`. -/
theorem label_eq_f_of_proper_prefix (t : Tree) {π ρ : List (Fin 2)}
    (hprefix : π.IsPrefix ρ) (hne : π ≠ ρ) (h : (t.fn ρ).isSome) :
    t.fn π = some Sym.f := by
  obtain ⟨σ, rfl⟩ := hprefix
  cases σ with
  | nil => simp at hne
  | cons i σ =>
    apply (t.child_isSome_iff π i).mp
    exact t.domain_append_left (π ++ [i]) σ (by simpa [List.append_assoc] using h)

/-- The least tree, consisting of a single bottom leaf. -/
def bot : Tree where
  fn
    | [] => some Sym.bot
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp

/-- The greatest tree, consisting of a single top leaf. -/
def top : Tree where
  fn
    | [] => some Sym.top
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp

/-- The constructor applied to its indexed family of children. -/
def node (a : Fin 2 → Tree) : Tree where
  fn
    | [] => some Sym.f
    | i :: w => (a i).fn w
  wf := by
    constructor
    · simp
    · intro w i
      cases w with
      | nil => simpa using (a i).root_isSome
      | cons j w => exact (a j).child_isSome_iff w i

@[simp] theorem bot_fn_nil : (bot : Tree).fn [] = some Sym.bot := rfl
@[simp] theorem bot_fn_cons (i : Fin 2) (π : List (Fin 2)) :
    (bot : Tree).fn (i :: π) = none := rfl
@[simp] theorem top_fn_nil : (top : Tree).fn [] = some Sym.top := rfl
@[simp] theorem top_fn_cons (i : Fin 2) (π : List (Fin 2)) :
    (top : Tree).fn (i :: π) = none := rfl
@[simp] theorem node_fn_nil (a : Fin 2 → Tree) : (node a).fn [] = some Sym.f := rfl
@[simp] theorem node_fn_cons (a : Fin 2 → Tree) (i : Fin 2) (w : List (Fin 2)) :
    (node a).fn (i :: w) = (a i).fn w := rfl

/-- Restrict a tree to the descendants of a path in its domain. -/
def subtree (t : Tree) (π : List (Fin 2)) : Option (Tree) :=
  if h : (t.fn π).isSome then
    some {
      fn := fun ρ => t.fn (π ++ ρ)
      wf := by
        constructor
        · simpa using Option.isSome_iff_ne_none.mp h
        · intro ρ i
          simpa [List.append_assoc] using t.child_isSome_iff (π ++ ρ) i
    }
  else none

@[simp] theorem subtree_isSome_iff (t : Tree) (π : List (Fin 2)) :
    (t.subtree π).isSome ↔ (t.fn π).isSome := by
  unfold subtree
  split <;> simp_all

/-- A subtree reads the labels of its parent after the defining path. -/
theorem subtree_fn {t u : Tree} {π : List (Fin 2)} (h : t.subtree π = some u)
    (ρ : List (Fin 2)) : u.fn ρ = t.fn (π ++ ρ) := by
  unfold subtree at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- A bottom or top root has no nonempty paths in its domain. -/
theorem fn_cons_eq_none_of_root_ne_f (t : Tree) (h : t.fn [] ≠ some Sym.f)
    (i : Fin 2) (π : List (Fin 2)) : t.fn (i :: π) = none := by
  by_contra hsome
  apply h
  apply (t.child_isSome_iff [] i).mp
  exact t.domain_append_left [i] π (Option.isSome_iff_ne_none.mpr hsome)

@[simp] theorem root_eq_bot_iff (t : Tree) : t.fn [] = some Sym.bot ↔ t = bot := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

@[simp] theorem root_eq_top_iff (t : Tree) : t.fn [] = some Sym.top ↔ t = top := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

/-- A child of a tree whose root is the constructor. -/
def branch (t : Tree) (i : Fin 2) (h : t.fn [] = some Sym.f) : Tree where
  fn := fun π => t.fn (i :: π)
  wf := by
    constructor
    · exact Option.isSome_iff_ne_none.mp ((t.child_isSome_iff [] i).mpr h)
    · intro π j
      exact t.child_isSome_iff (i :: π) j

theorem eq_node_of_root_eq_f (t : Tree) (h : t.fn [] = some Sym.f) :
    t = node (fun i => t.branch i h) := by
  apply ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => rfl

theorem eq_bot_or_eq_top_or_node (t : Tree) :
    t = bot ∨ t = top ∨ ∃ a, t = node a := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  cases s with
  | bot => exact Or.inl ((root_eq_bot_iff t).mp hs)
  | top => exact Or.inr (Or.inl ((root_eq_top_iff t).mp hs))
  | f => exact Or.inr (Or.inr ⟨_, t.eq_node_of_root_eq_f hs⟩)

@[simp] theorem node_eq_node_iff (a b : Fin 2 → Tree) :
    node a = node b ↔ a = b := by
  constructor
  · intro h
    funext i
    apply ext
    funext w
    exact congrArg (fun t : Tree => t.fn (i :: w)) h
  · rintro rfl; rfl

@[simp] theorem bot_ne_top : (bot : Tree) ≠ top := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem node_ne_bot (a : Fin 2 → Tree) : node a ≠ bot := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem node_ne_top (a : Fin 2 → Tree) : node a ≠ top := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem top_ne_bot : (top : Tree) ≠ bot := bot_ne_top.symm
@[simp] theorem bot_ne_node (a : Fin 2 → Tree) : bot ≠ node a := (node_ne_bot a).symm
@[simp] theorem top_ne_node (a : Fin 2 → Tree) : top ≠ node a := (node_ne_top a).symm

end Tree
end UndeciSigma2

namespace UndeciSigma2
/-- Finite terms over bottom, top and one constructor of arity two. -/
inductive FTree where
  | bot
  | top
  | node (children : Fin 2 → FTree)

namespace FTree

/-- Embed a finite term as a well-formed partial labeling of paths. -/
def toTree : FTree → Tree
  | bot => Tree.bot
  | top => Tree.top
  | node a => Tree.node (fun i => toTree (a i))

@[simp] theorem toTree_bot : toTree (bot : FTree) = Tree.bot := rfl
@[simp] theorem toTree_top : toTree (top : FTree) = Tree.top := rfl
@[simp] theorem toTree_node (a : Fin 2 → FTree) :
    toTree (node a) = Tree.node (fun i => toTree (a i)) := rfl

/-- Distinct finite terms represent distinct path trees. -/
theorem toTree_injective : Function.Injective (@toTree) := by
  intro a b h
  induction a generalizing b with
  | bot => cases b <;> simp_all [toTree]
  | top => cases b <;> simp_all [toTree]
  | node a ih =>
    cases b with
    | bot => simp [toTree] at h
    | top => simp [toTree] at h
    | node b =>
      apply congrArg node
      funext i
      exact ih i (congrFun ((Tree.node_eq_node_iff ..).mp h) i)

end FTree
end UndeciSigma2

namespace UndeciSigma2

/-- A deterministic labeled graph. Only constructor states have outgoing edges. -/
structure Graph (Q : Type) where
  label : Q → Sym
  child : Q → Fin 2 → Q

namespace Graph
variable {Q R : Type}

/-- Follow a path, stopping at either kind of leaf. -/
def walk (g : Graph Q) (q : Q) : List (Fin 2) → Option Q
  | [] => some q
  | i :: p => if g.label q = .f then g.walk (g.child q i) p else none

theorem walk_append (g : Graph Q) (q : Q) (p r : List (Fin 2)) :
    g.walk q (p ++ r) = (g.walk q p).bind (fun q => g.walk q r) := by
  induction p generalizing q with
  | nil => rfl
  | cons i p ih => simp only [List.cons_append, walk]; split <;> simp_all

/-- The tree obtained by unfolding a graph from a state. -/
def unfold (g : Graph Q) (q : Q) : Tree where
  fn p := (g.walk q p).map g.label
  wf := by
    constructor
    · simp [walk]
    · intro p i
      rw [walk_append]
      cases h : g.walk q p with
      | none => simp
      | some q => by_cases hf : g.label q = .f <;> simp [walk, hf]

@[simp] theorem unfold_nil (g : Graph Q) (q : Q) :
    (g.unfold q).fn [] = some (g.label q) := rfl

@[simp] theorem unfold_cons (g : Graph Q) (q : Q) (i : Fin 2) (p : List (Fin 2)) :
    (g.unfold q).fn (i :: p) =
      if g.label q = .f then (g.unfold (g.child q i)).fn p else none := by
  simp only [unfold, walk]; split <;> rfl

/-- A graph map preserving labels and transitions preserves unfolding. -/
theorem unfold_map (g : Graph Q) (h : Graph R) (e : Q → R)
    (hl : ∀ q, h.label (e q) = g.label q)
    (hc : ∀ q i, h.child (e q) i = e (g.child q i)) (q : Q) :
    h.unfold (e q) = g.unfold q := by
  apply Tree.ext
  funext p
  induction p generalizing q with
  | nil => simp [hl]
  | cons i p ih => simp only [unfold_cons, hl, hc]; split <;> simp_all
end Graph

/-- A finite graph presentation; the finite state type need not be numbered. -/
structure RGraph where
  State : Type
  states : Fintype State
  graph : Graph State
  root : State

attribute [instance] RGraph.states

namespace RGraph
/-- Embed a finite graph by unfolding; different presentations may coincide. -/
def toTree (g : RGraph) : Tree := g.graph.unfold g.root

/-- A graph with one state labeled `s` and both transitions returning to that state. -/
def constant (s : Sym) : RGraph where
  State := Unit
  states := inferInstance
  graph := ⟨fun _ => s, fun _ _ => ()⟩
  root := ()

@[simp] theorem constant_bot : (constant .bot).toTree = Tree.bot := by
  apply Tree.ext
  funext p
  cases p <;> simp [toTree, constant, Graph.unfold_cons]

@[simp] theorem constant_top : (constant .top).toTree = Tree.top := by
  apply Tree.ext
  funext p
  cases p <;> simp [toTree, constant, Graph.unfold_cons]

/-- Disjoint union of two presentations, with a new constructor root. -/
def node (a : Fin 2 → RGraph) : RGraph where
  State := Option ((i : Fin 2) × (a i).State)
  states := inferInstance
  graph := {
    label := fun q => match q with
      | none => .f
      | some ⟨i, q⟩ => (a i).graph.label q
    child := fun q j => match q with
      | none => some ⟨j, (a j).root⟩
      | some ⟨i, q⟩ => some ⟨i, (a i).graph.child q j⟩ }
  root := none

@[simp] theorem node_toTree (a : Fin 2 → RGraph) :
    (node a).toTree = Tree.node (fun i => (a i).toTree) := by
  apply Tree.ext
  funext p
  cases p with
  | nil => rfl
  | cons i p =>
    change ((node a).graph.unfold (node a).root).fn (i :: p) = ((a i).toTree).fn p
    rw [Graph.unfold_cons]
    simp only [node, ↓reduceIte]
    exact congrArg (fun t : Tree => t.fn p)
      (Graph.unfold_map (a i).graph (node a).graph (fun q => some ⟨i, q⟩)
        (fun _ => rfl) (fun _ _ => rfl) (a i).root)

/-- The full infinite constructor tree has a one-state presentation. -/
def omega : RGraph := constant .f

@[simp] theorem omega_fn (p : List (Fin 2)) : omega.toTree.fn p = some .f := by
  induction p with
  | nil => rfl
  | cons i p ih => simpa [omega, toTree, constant, Graph.unfold_cons] using ih
end RGraph

namespace FTree
/-- Every finite tree has a finite graph presentation. -/
def toGraph : FTree → RGraph
  | bot => RGraph.constant .bot
  | top => RGraph.constant .top
  | node a => RGraph.node (fun i => (a i).toGraph)

@[simp] theorem toGraph_toTree (t : FTree) : t.toGraph.toTree = t.toTree := by
  induction t with
  | bot => simp [toGraph]
  | top => simp [toGraph]
  | node a ih => simp [toGraph, ih]
end FTree

namespace Tree
/-- No address carries the greatest label. -/
def TopFree (t : Tree) : Prop := ∀ p, t.fn p ≠ some .top
/-- Membership in the finite-tree domain. -/
def IsFinite (t : Tree) : Prop := ∃ a : FTree, a.toTree = t
/-- Membership in the regular-tree domain, using finite graph presentations. -/
def IsRegular (t : Tree) : Prop := ∃ g : RGraph, g.toTree = t

theorem IsFinite.isRegular {t : Tree} (h : t.IsFinite) : t.IsRegular := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a.toGraph, a.toGraph_toTree⟩

@[simp] theorem topFree_bot : bot.TopFree := by intro p; cases p <;> simp
@[simp] theorem topFree_node (a : Fin 2 → Tree) :
    (node a).TopFree ↔ ∀ i, (a i).TopFree := by
  constructor
  · intro h i p; exact h (i :: p)
  · intro h p; cases p with
    | nil => simp
    | cons i p => exact h i p

@[simp] theorem finite_bot : bot.IsFinite := ⟨.bot, rfl⟩
@[simp] theorem finite_top : top.IsFinite := ⟨.top, rfl⟩
theorem finite_node {a : Fin 2 → Tree} (h : ∀ i, (a i).IsFinite) :
    (node a).IsFinite := by
  choose b hb using h
  exact ⟨.node b, by simp [hb]⟩
@[simp] theorem regular_bot : bot.IsRegular := finite_bot.isRegular
@[simp] theorem regular_top : top.IsRegular := finite_top.isRegular

theorem regular_node {a : Fin 2 → Tree} (h : ∀ i, (a i).IsRegular) :
    (node a).IsRegular := by
  choose b hb using h
  exact ⟨RGraph.node b, by simp [hb]⟩

/-- Binary constructor notation for use in formulas. -/
def f (a b : Tree) : Tree := node ![a, b]
end Tree

/-- The three ambient classes of trees. -/
inductive TreeClass where
  | finite | regular | arbitrary
  deriving DecidableEq, Repr

/-- A domain predicate for each of the six structures. -/
def Domain (c : TreeClass) (withTop : Bool) (t : Tree) : Prop :=
  (match c with
   | .finite => t.IsFinite
   | .regular => t.IsRegular
   | .arbitrary => True) ∧ (withTop = true ∨ t.TopFree)

/-- The carrier of one of the six structures. -/
abbrev Carrier (c : TreeClass) (withTop : Bool) := {t : Tree // Domain c withTop t}

@[simp] theorem domain_bot (c : TreeClass) (withTop : Bool) : Domain c withTop Tree.bot := by
  constructor
  · cases c <;> simp [Tree.finite_bot, Tree.regular_bot]
  · exact Or.inr Tree.topFree_bot

instance (c : TreeClass) (withTop : Bool) : Inhabited (Carrier c withTop) :=
  ⟨⟨Tree.bot, domain_bot c withTop⟩⟩

theorem domain_node {c : TreeClass} {withTop : Bool} {a : Fin 2 → Tree}
    (h : ∀ i, Domain c withTop (a i)) : Domain c withTop (Tree.node a) := by
  constructor
  · cases c with
    | finite => exact Tree.finite_node (fun i => (h i).1)
    | regular => exact Tree.regular_node (fun i => (h i).1)
    | arbitrary => trivial
  · cases withTop with
    | true => exact Or.inl rfl
    | false => exact Or.inr ((Tree.topFree_node a).mpr (fun i => (h i).2.resolve_left (by decide)))

end UndeciSigma2
