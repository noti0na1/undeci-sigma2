import UndeciSigma2.Tree

/-! # Non-structural subtyping

The subtype order compares labels at shared paths. On trees without top, it
is inclusion of constructor addresses. Intersection and union of these sets
preserve finite and regular trees and give lattice operations.
-/

namespace UndeciSigma2
namespace Tree
/-- The non-structural order compares labels at all shared paths. -/
def CovLe (t u : Tree) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → a ≤ b

instance : LE Tree := ⟨Tree.CovLe⟩

theorem le_refl (t : Tree) : t ≤ t := by
  intro π a b ha hb
  have : a = b := Option.some.inj (ha.symm.trans hb)
  exact this.le

/-- A path shared by the endpoints of two comparisons also occurs in the middle. -/
theorem middle_isSome {t u v : Tree} (htu : t ≤ u) (huv : u ≤ v)
    (π : List (Fin 2)) (ht : (t.fn π).isSome) (hv : (v.fn π).isSome) :
    (u.fn π).isSome := by
  induction π using List.reverseRecOn with
  | nil => exact u.root_isSome
  | append_singleton π i ih =>
    have ht' := (t.child_isSome_iff π i).mp ht
    have hv' := (v.child_isSome_iff π i).mp hv
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih (by simp [ht']) (by simp [hv']))
    have hb' : b = Sym.f := _root_.le_antisymm (huv π b Sym.f hb hv')
      (htu π Sym.f b ht' hb)
    exact (u.child_isSome_iff π i).mpr (by simpa [hb'] using hb)

theorem le_trans {t u v : Tree} (htu : t ≤ u) (huv : u ≤ v) : t ≤ v := by
  intro π a c ha hc
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (middle_isSome htu huv π (by simp [ha]) (by simp [hc]))
  exact _root_.le_trans (htu π a b ha hb) (huv π b c hb hc)

theorem le_antisymm {t u : Tree} (htu : t ≤ u) (hut : u ≤ t) : t = u := by
  have labels : ∀ π a b, t.fn π = some a → u.fn π = some b → a = b := by
    intro π a b ha hb
    exact _root_.le_antisymm (htu π a b ha hb) (hut π b a hb ha)
  apply ext
  funext π
  induction π using List.reverseRecOn with
  | nil =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp t.root_isSome
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    rw [ha, hb, labels [] a b ha hb]
  | append_singleton π i ih =>
    have hd : (t.fn (π ++ [i])).isSome ↔ (u.fn (π ++ [i])).isSome := by
      rw [child_isSome_iff, child_isSome_iff, ih]
    cases ht : t.fn (π ++ [i]) <;> cases hu : u.fn (π ++ [i])
    · rfl
    · simp [ht, hu] at hd
    · simp [ht, hu] at hd
    · exact congrArg some (labels _ _ _ ht hu)

instance : PartialOrder Tree where
  le := Tree.CovLe
  le_refl := Tree.le_refl
  le_trans := fun _ _ _ => Tree.le_trans
  le_antisymm := fun _ _ => Tree.le_antisymm

@[simp] theorem bot_le (t : Tree) : bot ≤ t := by
  intro π a b ha hb
  cases π with
  | nil => simp only [bot_fn_nil, Option.some.injEq] at ha; subst a; exact Sym.bot_le b
  | cons i π => simp at ha

@[simp] theorem le_top (t : Tree) : t ≤ top := by
  intro π a b ha hb
  cases π with
  | nil => simp only [top_fn_nil, Option.some.injEq] at hb; subst b; exact Sym.le_top a
  | cons i π => simp at hb

@[simp] theorem le_bot_iff (t : Tree) : t ≤ bot ↔ t = bot :=
  ⟨fun h => le_antisymm h (bot_le t), fun h => h ▸ le_refl bot⟩

@[simp] theorem top_le_iff (t : Tree) : top ≤ t ↔ t = top :=
  ⟨fun h => le_antisymm (le_top t) h, fun h => h ▸ le_refl top⟩

@[simp] theorem node_le_node_iff (a b : Fin 2 → Tree) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w x y hx hy
    exact h (i :: w) x y hx hy
  · intro h w x y hx hy
    cases w with
    | nil => exact (Option.some.inj (hx.symm.trans hy)).le
    | cons i w => exact h i w x y hx hy

theorem le_iff_root_cases (t u : Tree) :
    t ≤ u ↔ t = bot ∨ u = top ∨
      ∃ a b, t = node a ∧ u = node b ∧ ∀ i, a i ≤ b i := by
  constructor
  · intro h
    rcases t.eq_bot_or_eq_top_or_node with ht | ht | ⟨a, rfl⟩
    · exact Or.inl ht
    · subst t; exact Or.inr (Or.inl ((top_le_iff u).mp h))
    · rcases u.eq_bot_or_eq_top_or_node with hu | hu | ⟨b, rfl⟩
      · subst u; exact False.elim (node_ne_bot a ((le_bot_iff _).mp h))
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, (node_le_node_iff ..).mp h⟩)
  · rintro (rfl | rfl | ⟨a, b, rfl, rfl, h⟩)
    · exact bot_le u
    · exact le_top t
    · exact (node_le_node_iff ..).mpr h

end Tree

end UndeciSigma2

namespace UndeciSigma2

instance : PartialOrder FTree := PartialOrder.lift FTree.toTree FTree.toTree_injective

namespace Tree
/-- Constructor addresses, excluding leaf addresses. -/
def constructorPaths (t : Tree) : Set (List (Fin 2)) := {p | t.fn p = some .f}

theorem constructorPaths_prefix {t : Tree} {p r : List (Fin 2)} (h : p ++ r ∈ t.constructorPaths) : p ∈ t.constructorPaths := by
  cases r with
  | nil => simpa using h
  | cons i r =>
    apply (t.child_isSome_iff p i).mp
    exact t.domain_append_left (p ++ [i]) r (by simp only [constructorPaths, Set.mem_ofPred_eq] at h; simpa [List.append_assoc] using Option.isSome_iff_ne_none.mpr (by rw [h]; simp))

/-- If `a ≤ b` and `b` contains no top, every path in the domain of `a` is in the domain of `b`. -/
theorem right_isSome {a b : Tree} (h : a ≤ b) (hb : b.TopFree)
    (p : List (Fin 2)) (hp : (a.fn p).isSome) : (b.fn p).isSome := by
  induction p using List.reverseRecOn with
  | nil => exact b.root_isSome
  | append_singleton p i ih =>
    have ha := (a.child_isSome_iff p i).mp hp
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (ih (by simp [ha]))
    have hh := h p .f s ha hs
    have : s = .f := by
      cases s with
      | bot => contradiction
      | f => rfl
      | top => exact False.elim (hb p hs)
    exact (b.child_isSome_iff p i).mpr (this ▸ hs)

/-- The top-free part is a lower set, even in the signature with top. -/
theorem TopFree.of_le {a b : Tree} (hb : b.TopFree) (h : a ≤ b) : a.TopFree := by
  intro p hp
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (right_isSome h hb p (by simp [hp]))
  have ht := (Sym.top_le_iff s).mp (h p .top s hp hs)
  exact hb p (ht ▸ hs)

/-- On top-free trees, order is exactly inclusion of constructor addresses. -/
theorem le_iff_constructorPaths_subset {a b : Tree} (ha : a.TopFree) (hb : b.TopFree) :
    a ≤ b ↔ a.constructorPaths ⊆ b.constructorPaths := by
  constructor
  · intro h p hp
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
      (right_isSome h hb p (by simp [constructorPaths] at hp; simp [hp]))
    have hh := h p .f s hp hs
    cases s with
    | bot => contradiction
    | f => exact hs
    | top => exact False.elim (hb p hs)
  · intro h p s t hs ht
    cases s with
    | bot => exact Sym.bot_le _
    | top => exact False.elim (ha p hs)
    | f =>
      have hf := h hs
      have : t = .f := Option.some.inj (ht.symm.trans hf)
      subst t
      exact le_rfl

theorem topFree_ext {a b : Tree} (ha : a.TopFree) (hb : b.TopFree)
    (h : a.constructorPaths = b.constructorPaths) : a = b :=
  le_antisymm ((le_iff_constructorPaths_subset ha hb).mpr (h ▸ Set.Subset.rfl))
    ((le_iff_constructorPaths_subset hb ha).mpr (h ▸ Set.Subset.rfl))

/-- Prefix closure, including the empty address when the set is nonempty. -/
def PrefixClosed (S : Set (List (Fin 2))) : Prop :=
  ∀ p r, p ++ r ∈ S → p ∈ S

/-- Recover a top-free tree from its constructor addresses, placing bottom on
its frontier. The empty set represents bottom. -/
noncomputable def ofConstructorPaths (S : Set (List (Fin 2))) (hS : PrefixClosed S) : Tree := by
  classical
  refine ⟨fun p => if p ∈ S then some .f
    else if p = [] ∨ p.dropLast ∈ S then some .bot else none, ?_⟩
  have parent : ∀ p i, p ++ [i] ∈ S → p ∈ S := fun p i h => hS p [i] h
  constructor
  · split <;> simp_all
  · intro p i
    by_cases hp : p ∈ S
    · simp only [hp, ite_true, List.dropLast_append_cons]; split <;> simp_all
    · have hn := mt (parent p i) hp
      simp [hp, hn]

@[simp] theorem ofConstructorPaths_constructorPaths (S : Set (List (Fin 2))) (hS : PrefixClosed S) :
    (ofConstructorPaths S hS).constructorPaths = S := by
  classical
  ext p
  simp only [constructorPaths, ofConstructorPaths, Set.mem_ofPred_eq]
  split <;> simp_all

@[simp] theorem ofConstructorPaths_topFree (S : Set (List (Fin 2))) (hS : PrefixClosed S) :
    (ofConstructorPaths S hS).TopFree := by
  classical
  intro p
  simp only [ofConstructorPaths]
  split <;> simp_all

/-- Binary meet of top-free trees, defined by intersection of addresses. -/
noncomputable def meet (a b : Tree) : Tree :=
  ofConstructorPaths (a.constructorPaths ∩ b.constructorPaths) (fun _ _ h => ⟨constructorPaths_prefix h.1, constructorPaths_prefix h.2⟩)

/-- Binary join of top-free trees, defined by union of addresses. -/
noncomputable def join (a b : Tree) : Tree :=
  ofConstructorPaths (a.constructorPaths ∪ b.constructorPaths) (fun _ _ h => h.elim (fun h => Or.inl (constructorPaths_prefix h))
    (fun h => Or.inr (constructorPaths_prefix h)))

@[simp] theorem meet_constructorPaths (a b : Tree) : (meet a b).constructorPaths = a.constructorPaths ∩ b.constructorPaths := ofConstructorPaths_constructorPaths _ _
@[simp] theorem join_constructorPaths (a b : Tree) : (join a b).constructorPaths = a.constructorPaths ∪ b.constructorPaths := ofConstructorPaths_constructorPaths _ _
@[simp] theorem meet_topFree (a b : Tree) : (meet a b).TopFree := ofConstructorPaths_topFree _ _
@[simp] theorem join_topFree (a b : Tree) : (join a b).TopFree := ofConstructorPaths_topFree _ _

theorem meet_le_left {a b : Tree} (ha : a.TopFree) : meet a b ≤ a :=
  (le_iff_constructorPaths_subset (meet_topFree _ _) ha).mpr (by simp)
theorem meet_le_right {a b : Tree} (hb : b.TopFree) : meet a b ≤ b :=
  (le_iff_constructorPaths_subset (meet_topFree _ _) hb).mpr (by simp)

theorem le_meet {a b x : Tree} (ha : a.TopFree) (hb : b.TopFree)
    (hxa : x ≤ a) (hxb : x ≤ b) : x ≤ meet a b := by
  have hx := ha.of_le hxa
  apply (le_iff_constructorPaths_subset hx (meet_topFree _ _)).mpr
  rw [meet_constructorPaths]
  exact Set.subset_inter ((le_iff_constructorPaths_subset hx ha).mp hxa) ((le_iff_constructorPaths_subset hx hb).mp hxb)

theorem le_join_left {a b : Tree} (ha : a.TopFree) : a ≤ join a b :=
  (le_iff_constructorPaths_subset ha (join_topFree _ _)).mpr (by simp)
theorem le_join_right {a b : Tree} (hb : b.TopFree) : b ≤ join a b :=
  (le_iff_constructorPaths_subset hb (join_topFree _ _)).mpr (by simp)

/-- The union is below every common upper bound, including ones containing top. -/
theorem join_le {a b x : Tree} (hax : a ≤ x) (hbx : b ≤ x) : join a b ≤ x := by
  intro p s t hs ht
  cases s with
  | bot => exact Sym.bot_le _
  | top => exact False.elim (join_topFree a b p hs)
  | f =>
    have hp : p ∈ (join a b).constructorPaths := hs
    rw [join_constructorPaths] at hp
    exact hp.elim (fun h => hax p .f t h ht) (fun h => hbx p .f t h ht)

/-- Arbitrary unions are available in the arbitrary-tree domain. -/
noncomputable def sjoin (S : Set Tree) : Tree :=
  ofConstructorPaths {p | ∃ t ∈ S, p ∈ t.constructorPaths} (by
    rintro p r ⟨t, ht, hp⟩
    exact ⟨t, ht, constructorPaths_prefix hp⟩)

@[simp] theorem sjoin_constructorPaths (S : Set Tree) :
    (sjoin S).constructorPaths = {p | ∃ t ∈ S, p ∈ t.constructorPaths} := ofConstructorPaths_constructorPaths _ _

theorem le_sjoin {S : Set Tree} {t : Tree} (ht : t ∈ S) (hf : t.TopFree) :
    t ≤ sjoin S := by
  apply (le_iff_constructorPaths_subset hf (ofConstructorPaths_topFree _ _)).mpr
  intro p hp
  exact (sjoin_constructorPaths S).symm ▸ ⟨t, ht, hp⟩

theorem sjoin_le {S : Set Tree} {u : Tree} (h : ∀ t ∈ S, t ≤ u) : sjoin S ≤ u := by
  intro p s v hs hv
  cases s with
  | bot => exact Sym.bot_le _
  | top => exact False.elim (ofConstructorPaths_topFree _ _ p hs)
  | f =>
    have hp : p ∈ (sjoin S).constructorPaths := hs
    rw [sjoin_constructorPaths] at hp
    obtain ⟨t, ht, hp⟩ := hp
    exact h t ht p .f v hp hv
end Tree
end UndeciSigma2

namespace UndeciSigma2
namespace FTree
/-- A bound on the depth of every constructor in a finite term. -/
def height : FTree → Nat
  | bot | top => 0
  | node a => (Finset.univ.sup fun i => (a i).height) + 1

theorem length_lt_height (t : FTree) (p : List (Fin 2)) (h : p ∈ t.toTree.constructorPaths) :
    p.length < t.height := by
  induction t generalizing p with
  | bot => cases p <;> simp [Tree.constructorPaths, toTree] at h
  | top => cases p <;> simp [Tree.constructorPaths, toTree] at h
  | node a ih =>
    cases p with
    | nil => simp [height]
    | cons i p =>
      have hp := ih i p h
      have hm : (a i).height ≤ Finset.univ.sup (fun j => (a j).height) :=
        Finset.le_sup (f := fun j => (a j).height) (Finset.mem_univ i)
      simp only [List.length_cons, height]
      omega
end FTree

namespace Tree
/-- A top-free tree with bounded constructor depth is a finite term. -/
theorem finite_of_bounded {t : Tree} (ht : t.TopFree) (n : Nat)
    (h : ∀ p ∈ t.constructorPaths, p.length < n) : t.IsFinite := by
  induction n generalizing t with
  | zero =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · exact finite_bot
    · exact False.elim (ht [] rfl)
    · have := h [] rfl; simp at this
  | succ n ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · exact finite_bot
    · exact False.elim (ht [] rfl)
    · apply finite_node
      intro i
      apply ih ((topFree_node a).mp ht i)
      intro p hp
      have := h (i :: p) hp
      simpa using this

theorem finite_iff_bounded {t : Tree} (ht : t.TopFree) :
    t.IsFinite ↔ ∃ n, ∀ p ∈ t.constructorPaths, p.length < n := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.height, a.length_lt_height⟩
  · rintro ⟨n, hn⟩
    exact finite_of_bounded ht n hn

/-- Finiteness is downward closed below a finite top-free tree. -/
theorem IsFinite.of_le {a b : Tree} (hb : b.IsFinite) (hf : b.TopFree) (h : a ≤ b) :
    a.IsFinite := by
  obtain ⟨n, hn⟩ := (finite_iff_bounded hf).mp hb
  exact finite_of_bounded (hf.of_le h) n
    (fun p hp => hn p ((le_iff_constructorPaths_subset (hf.of_le h) hf).mp h hp))

theorem finite_meet {a b : Tree} (ha : a.IsFinite) (hf : a.TopFree) :
    (meet a b).IsFinite := ha.of_le hf (meet_le_left hf)

theorem finite_join {a b : Tree} (ha : a.IsFinite) (hb : b.IsFinite) :
    (join a b).IsFinite := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  apply finite_of_bounded (join_topFree _ _) (max a.height b.height)
  intro p hp
  rw [join_constructorPaths] at hp
  rcases hp with hp | hp
  · exact lt_of_lt_of_le (a.length_lt_height p hp) (le_max_left _ _)
  · exact lt_of_lt_of_le (b.length_lt_height p hp) (le_max_right _ _)
end Tree

namespace Graph
variable {Q R : Type}

/-- Complete the transition system with a dead state after leaves. -/
def next (g : Graph Q) : Option Q → Fin 2 → Option Q
  | none, _ => none
  | some q, i => if g.label q = .f then some (g.child q i) else none

/-- Total traversal of the completed graph. -/
def run (g : Graph Q) : Option Q → List (Fin 2) → Option Q
  | q, [] => q
  | q, i :: p => g.run (g.next q i) p

/-- Constructor-labeled states are the accepting states. -/
def Active (g : Graph Q) (q : Option Q) : Prop :=
  ∃ r, q = some r ∧ g.label r = .f

@[simp] theorem active_none (g : Graph Q) : ¬g.Active none := by simp [Active]
@[simp] theorem active_some (g : Graph Q) (q : Q) : g.Active (some q) ↔ g.label q = .f := by
  simp [Active]
@[simp] theorem run_none (g : Graph Q) (p : List (Fin 2)) : g.run none p = none := by
  induction p with
  | nil => rfl
  | cons i p ih => exact ih

theorem active_next (g : Graph Q) (q : Option Q) (i : Fin 2)
    (h : g.Active (g.next q i)) : g.Active q := by
  cases q with
  | none => exact False.elim (g.active_none h)
  | some q =>
    simp only [next] at h
    split at h
    · exact (active_some g q).mpr (by assumption)
    · exact False.elim (g.active_none h)

theorem active_run (g : Graph Q) (q : Option Q) (p : List (Fin 2))
    (h : g.Active (g.run q p)) : g.Active q := by
  induction p generalizing q with
  | nil => exact h
  | cons i p ih => exact g.active_next q i (ih _ h)

theorem active_run_iff (g : Graph Q) (q : Q) (p : List (Fin 2)) :
    g.Active (g.run (some q) p) ↔ (g.unfold q).fn p = some .f := by
  induction p generalizing q with
  | nil => simp [run]
  | cons i p ih =>
    simp only [run, next, unfold_cons]
    split <;> simp_all

/-- Select union or intersection of two constructor-address languages. -/
def combine (union : Bool) (a b : Prop) : Prop := if union then a ∨ b else a ∧ b

theorem combine_mono (union : Bool) {a b c d : Prop} (hac : a → c) (hbd : b → d) :
    combine union a b → combine union c d := by
  cases union <;> simp only [combine, Bool.false_eq_true, ↓reduceIte] <;> tauto

/-- The finite product automaton for intersection or union. Dead states are
necessary for union when one input stops earlier than the other. -/
noncomputable def product (union : Bool) (g : Graph Q) (h : Graph R) :
    Graph (Option Q × Option R) := by
  classical
  exact {
    label := fun q => if combine union (g.Active q.1) (h.Active q.2) then .f else .bot
    child := fun q i => (g.next q.1 i, h.next q.2 i) }

theorem product_topFree (union : Bool) (g : Graph Q) (h : Graph R)
    (q : Option Q × Option R) : ((product union g h).unfold q).TopFree := by
  intro p
  change ((product union g h).walk q p).map (product union g h).label ≠ some Sym.top
  cases hw : (product union g h).walk q p with
  | none => simp
  | some r =>
    simp only [Option.map_some, product]
    split <;> simp

theorem product_constructorPaths (union : Bool) (g : Graph Q) (h : Graph R)
    (q : Option Q × Option R) (p : List (Fin 2)) :
    ((product union g h).unfold q).fn p = some .f ↔
      combine union (g.Active (g.run q.1 p)) (h.Active (h.run q.2 p)) := by
  classical
  induction p generalizing q with
  | nil => simp only [unfold_nil, product, run]; split <;> simp_all
  | cons i p ih =>
    rw [unfold_cons]
    change (if (if combine union (g.Active q.1) (h.Active q.2) then Sym.f else Sym.bot) = Sym.f
      then ((product union g h).unfold (g.next q.1 i, h.next q.2 i)).fn p else none) = some .f ↔ _
    by_cases hc : combine union (g.Active q.1) (h.Active q.2)
    · simp only [hc, ↓reduceIte, ih, run]
    · have hn : ¬ combine union (g.Active (g.run q.1 (i :: p)))
          (h.Active (h.run q.2 (i :: p))) := by
        intro hh
        exact hc (combine_mono union (g.active_run _ _) (h.active_run _ _) hh)
      simp [hc, hn]
end Graph

namespace RGraph
/-- A finite graph presenting the union or intersection of constructor addresses. -/
noncomputable def product (union : Bool) (g h : RGraph) : RGraph where
  State := Option g.State × Option h.State
  states := inferInstance
  graph := Graph.product union g.graph h.graph
  root := (some g.root, some h.root)

theorem product_toTree (union : Bool) (g h : RGraph) :
    (product union g h).toTree = if union then Tree.join g.toTree h.toTree
      else Tree.meet g.toTree h.toTree := by
  apply Tree.topFree_ext (Graph.product_topFree _ _ _ _)
  · cases union <;> simp
  · ext p
    change ((Graph.product union g.graph h.graph).unfold (some g.root, some h.root)).fn p = some .f ↔ _
    rw [Graph.product_constructorPaths, Graph.active_run_iff, Graph.active_run_iff]
    change Graph.combine union (p ∈ g.toTree.constructorPaths) (p ∈ h.toTree.constructorPaths) ↔ _
    cases union <;> simp [Graph.combine]
end RGraph

namespace Tree
theorem regular_meet {a b : Tree} (ha : a.IsRegular) (hb : b.IsRegular) :
    (meet a b).IsRegular := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  exact ⟨RGraph.product false g h, RGraph.product_toTree false g h⟩

theorem regular_join {a b : Tree} (ha : a.IsRegular) (hb : b.IsRegular) :
    (join a b).IsRegular := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  exact ⟨RGraph.product true g h, RGraph.product_toTree true g h⟩
end Tree

/-- Domain closure of the top-free meet in every one of the six structures. -/
theorem domain_meet {c : TreeClass} {top : Bool} {a b : Tree}
    (ha : Domain c top a) (hb : Domain c top b) (hf : a.TopFree) :
    Domain c top (Tree.meet a b) := by
  constructor
  · cases c with
    | finite => exact Tree.finite_meet ha.1 hf
    | regular => exact Tree.regular_meet ha.1 hb.1
    | arbitrary => trivial
  · exact Or.inr (Tree.meet_topFree _ _)

/-- Domain closure of the top-free join in every one of the six structures. -/
theorem domain_join {c : TreeClass} {top : Bool} {a b : Tree}
    (ha : Domain c top a) (hb : Domain c top b) :
    Domain c top (Tree.join a b) := by
  constructor
  · cases c with
    | finite => exact Tree.finite_join ha.1 hb.1
    | regular => exact Tree.regular_join ha.1 hb.1
    | arbitrary => trivial
  · exact Or.inr (Tree.join_topFree _ _)

end UndeciSigma2

namespace UndeciSigma2

/-- All three top-free carriers are lattices with constructor-address
intersection and union. Their order is the inherited non-structural order. -/
noncomputable instance (c : TreeClass) : Lattice (Carrier c false) where
  sup a b := ⟨Tree.join a b, domain_join a.2 b.2⟩
  inf a b := ⟨Tree.meet a b, domain_meet a.2 b.2 (a.2.2.resolve_left (by decide))⟩
  le_sup_left a b := Tree.le_join_left (a.2.2.resolve_left (by decide))
  le_sup_right a b := Tree.le_join_right (b.2.2.resolve_left (by decide))
  sup_le a b x ha hb := Tree.join_le ha hb
  inf_le_left a b := Tree.meet_le_left (a.2.2.resolve_left (by decide))
  inf_le_right a b := Tree.meet_le_right (b.2.2.resolve_left (by decide))
  le_inf a b x ha hb := Tree.le_meet (b.2.2.resolve_left (by decide))
    (x.2.2.resolve_left (by decide)) ha hb

end UndeciSigma2
