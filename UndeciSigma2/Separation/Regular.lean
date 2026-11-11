import UndeciSigma2.Separation.Sentence

/-! # The separating sentence over regular and over finite trees

Over finite trees the sentence fails at once: the equation `Z = f(Z, Z)` has only the full
tree as a solution, and the full tree is not finite.

Over regular trees, let `x` be a regular top-free tree whose addresses are pairwise
comparable by prefix, the unfolding of a finite graph. The subtrees of `x` are the unfoldings
at the reachable states. Their addresses are again pairwise comparable, so each of them has
at most one address of each length. Let `d` be the join of `f(⊥, ⊥)` and these finitely many
subtrees. Then `d` is regular and top-free, `x ≤ d`, and the addresses of `d` contain the
empty word and are closed under removing the first letter, so `d = f(h, k)` for its two
children `h ≤ d` and `k ≤ d`. For each length `ℓ ≥ 1`, `d` has at most as many addresses of
length `ℓ` as the graph has states. Choosing `2^ℓ` larger than that number, some word of
length `ℓ` is not an address of `d`, so `d` is not the full tree.
-/

namespace UndeciSigma2

open UndeciSigma2.Tree

namespace Separation

/-! ## The suffix closure of a regular tree -/

section SuffixClosure
variable (g : RGraph)

/-- A state is reachable when some path leads to it from the root. -/
def Reachable (q : g.State) : Prop := ∃ p, g.graph.walk g.root p = some q

theorem reachable_root : Reachable g g.root := ⟨[], rfl⟩

theorem Reachable.child {g : RGraph} {q : g.State} (hq : Reachable g q)
    (hl : g.graph.label q = .f) (i : Fin 2) : Reachable g (g.graph.child q i) := by
  obtain ⟨p, hp⟩ := hq
  exact ⟨p ++ [i], by simp [Graph.walk_append, hp, Graph.walk, hl]⟩

/-- An address of the unfolding at a state reached by `p`, preceded by `p`, is an address of
the presented tree. -/
theorem append_mem_of_walk_eq {g : RGraph} {p r : Word} {q : g.State}
    (hp : g.graph.walk g.root p = some q) (hr : r ∈ (g.graph.unfold q).constructorPaths) :
    p ++ r ∈ g.toTree.constructorPaths := by
  change (g.graph.walk g.root (p ++ r)).map g.graph.label = some .f
  rw [Graph.walk_append, hp]
  exact hr

/-- The tree `f(⊥, ⊥)` together with the unfoldings at the reachable states. -/
def suffixTrees : Set Tree := insert e (g.graph.unfold '' {q | Reachable g q})

/-- The join of `suffixTrees g`. Its addresses are the empty word and the suffixes of the
addresses of the presented tree. -/
noncomputable def suffixClosure : Tree := sjoin (suffixTrees g)

theorem regular_suffixClosure : (suffixClosure g).IsRegular := by
  refine regular_sjoin (((Set.toFinite _).image _).insert _) ?_
  rintro t (rfl | ⟨q, -, rfl⟩)
  · exact finite_e.isRegular
  · exact ⟨⟨g.State, g.states, g.graph, q⟩, rfl⟩

theorem topFree_suffixClosure : (suffixClosure g).TopFree := topFree_sjoin _

theorem mem_suffixClosure_iff (r : Word) :
    r ∈ (suffixClosure g).constructorPaths ↔
      r = [] ∨ ∃ q, Reachable g q ∧ r ∈ (g.graph.unfold q).constructorPaths := by
  change r ∈ (sjoin (suffixTrees g)).constructorPaths ↔ _
  rw [sjoin_constructorPaths]
  constructor
  · rintro ⟨t, (rfl | ⟨q, hq, rfl⟩), hr⟩
    · exact Or.inl ((mem_constructorPaths_e r).mp hr)
    · exact Or.inr ⟨q, hq, hr⟩
  · rintro (rfl | ⟨q, hq, hr⟩)
    · exact ⟨e, Set.mem_insert _ _, nil_mem_constructorPaths_e⟩
    · exact ⟨_, Set.mem_insert_of_mem _ ⟨q, hq, rfl⟩, hr⟩

theorem nil_mem_suffixClosure : [] ∈ (suffixClosure g).constructorPaths :=
  (mem_suffixClosure_iff g []).mpr (Or.inl rfl)

theorem le_suffixClosure (hx : g.toTree.TopFree) : g.toTree ≤ suffixClosure g :=
  le_sjoin (Set.mem_insert_of_mem _ ⟨g.root, reachable_root g, rfl⟩) hx

/-- The addresses of the suffix closure are closed under removing the first letter. -/
theorem mem_suffixClosure_of_cons_mem {i : Fin 2} {r : Word}
    (h : i :: r ∈ (suffixClosure g).constructorPaths) :
    r ∈ (suffixClosure g).constructorPaths := by
  rw [mem_suffixClosure_iff] at h ⊢
  rcases h with h | ⟨q, hq, hr⟩
  · exact absurd h (List.cons_ne_nil i r)
  · change (g.graph.unfold q).fn (i :: r) = some .f at hr
    rw [Graph.unfold_cons] at hr
    split_ifs at hr with hl
    exact Or.inr ⟨_, hq.child hl i, hr⟩

/-- If the addresses of the presented tree are pairwise comparable by prefix, some word is
not an address of the suffix closure: each reachable state contributes at most one address
of each length. -/
theorem exists_not_mem_suffixClosure
    (hchain : ∀ a ∈ g.toTree.constructorPaths, ∀ b ∈ g.toTree.constructorPaths,
      a <+: b ∨ b <+: a) :
    ∃ w, w ∉ (suffixClosure g).constructorPaths := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hex : ∀ w : Fin (Fintype.card g.State + 1) → Fin 2,
      ∃ q, Reachable g q ∧ List.ofFn w ∈ (g.graph.unfold q).constructorPaths := by
    intro w
    rcases (mem_suffixClosure_iff g (List.ofFn w)).mp (hall _) with h | h
    · exact absurd (congrArg List.length h) (by simp)
    · exact h
  choose F hF hmem using hex
  have hinj : Function.Injective F := by
    intro w w' hww'
    obtain ⟨p, hp⟩ := hF w
    have h₁ := append_mem_of_walk_eq hp (hmem w)
    have h₂ := append_mem_of_walk_eq hp (by rw [hww']; exact hmem w')
    have hlen : (List.ofFn w).length = (List.ofFn w').length := by simp
    apply List.ofFn_injective
    rcases hchain _ h₁ _ h₂ with h | h
    · exact ((List.prefix_append_right_inj p).mp h).eq_of_length hlen
    · exact (((List.prefix_append_right_inj p).mp h).eq_of_length hlen.symm).symm
  have hcard := Fintype.card_le_of_injective F hinj
  have hlt : Fintype.card g.State + 1 < 2 ^ (Fintype.card g.State + 1) := Nat.lt_two_pow_self
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  omega

end SuffixClosure

end Separation

open Separation

/-- The separating sentence fails over regular trees, with or without top. -/
theorem separatingSentence_not_holds_regular (top : Bool) :
    ¬(separatingSentence top).Holds (Structure.ofClass .regular top) := by
  rw [separatingSentence_holds_ofClass_iff]
  rintro ⟨-, x, hx, hxT, hchain, hclosed⟩
  obtain ⟨g, rfl⟩ := hx.1
  have hroot : (suffixClosure g).fn [] = some .f := nil_mem_suffixClosure g
  have hdT := topFree_suffixClosure g
  have hdR := regular_suffixClosure g
  have hdf : suffixClosure g =
      f ((suffixClosure g).branch 0 hroot) ((suffixClosure g).branch 1 hroot) := by
    refine ((suffixClosure g).eq_node_of_root_eq_f hroot).trans ?_
    unfold f
    congr 1
    funext i
    fin_cases i <;> rfl
  have hbT : ∀ i, ((suffixClosure g).branch i hroot).TopFree := fun i p => hdT (i :: p)
  have hbd : ∀ i, (suffixClosure g).branch i hroot ≤ suffixClosure g := fun i =>
    le_of_subset (hbT i) fun r hr => mem_suffixClosure_of_cons_mem g (i := i) (r := r) hr
  have hreg : TreeClass.regular ≠ .finite := by decide
  have hfull := hclosed _ _ _ (domain_of_isRegular hreg hdR hdT) hdT
    (domain_of_isRegular hreg (hdR.branch hroot 0) (hbT 0)) (hbT 0)
    (domain_of_isRegular hreg (hdR.branch hroot 1) (hbT 1)) (hbT 1)
    (le_suffixClosure g hxT) (le_of_eq hdf) (ge_of_eq hdf) (hbd 0) (hbd 1)
  obtain ⟨w, hw⟩ := exists_not_mem_suffixClosure g
    fun a ha b hb => prefix_or_prefix_of_comparable hchain ha hb
  exact hw ((le_iff_constructorPaths_subset topFree_full hdT).mp hfull
    (mem_constructorPaths_full w))

/-- The separating sentence fails over finite trees, with or without top, only because the
equation `Z = f(Z, Z)` has no finite solution: the full tree is not finite. This says little
about the finite structures, since already the Σ₁ sentence `∃ Z. Z ≤ f(Z, Z) ∧ f(Z, Z) ≤ Z`
holds over regular and arbitrary trees and fails over finite trees. -/
theorem separatingSentence_not_holds_finite (top : Bool) :
    ¬(separatingSentence top).Holds (Structure.ofClass .finite top) := by
  rw [separatingSentence_holds_ofClass_iff]
  rintro ⟨hfull, -⟩
  exact not_isFinite_full hfull.1

end UndeciSigma2
