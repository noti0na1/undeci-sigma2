import UndeciSigma2.Order
import UndeciSigma2.Words

/-! # Top-free trees as prefix-closed sets of words

On top-free trees the order is inclusion of constructor addresses. This file
collects the address sets of the basic trees used by the reduction:

* `Tree.e = f(⊥, ⊥)` and the full tree `Tree.full`, whose addresses are all words;
* `Tree.path w`, the least tree containing `w`, whose addresses are the prefixes of `w`;
* `Tree.cocone w`, the greatest top-free tree avoiding `w`, whose addresses are the
  words without `w` as a prefix;
* `Tree.nestRight a j t = f(a, f(a, … f(a, t)))`, with `j` constructors on the right spine.

It also shows that the full tree is not finite, that finite joins and the children of
regular trees are regular, and that top-free trees belong to the arbitrary domains, regular
top-free trees to the regular ones, and finite top-free trees to every domain.
-/

namespace UndeciSigma2

open Word

namespace Tree

/-- The tree `f(⊥, ⊥)` with one constructor node. -/
def e : Tree := f bot bot

/-- The full binary tree: every address carries the constructor. -/
def full : Tree := RGraph.omega.toTree

/-! ## Addresses of bottom and of the constructor -/

@[simp] theorem not_mem_constructorPaths_bot (w : Word) : w ∉ bot.constructorPaths := by
  cases w <;> simp [constructorPaths]

@[simp] theorem nil_mem_constructorPaths_f (a b : Tree) : [] ∈ (f a b).constructorPaths := rfl

@[simp] theorem zero_cons_mem_constructorPaths_f (a b : Tree) (w : Word) :
    0 :: w ∈ (f a b).constructorPaths ↔ w ∈ a.constructorPaths := Iff.rfl

@[simp] theorem one_cons_mem_constructorPaths_f (a b : Tree) (w : Word) :
    1 :: w ∈ (f a b).constructorPaths ↔ w ∈ b.constructorPaths := Iff.rfl

@[simp] theorem nil_mem_constructorPaths_e : [] ∈ e.constructorPaths := rfl

theorem mem_constructorPaths_e (w : Word) : w ∈ e.constructorPaths ↔ w = [] := by
  rcases w with _ | ⟨i, w⟩
  · simp
  · fin_cases i <;> simp [e]

@[simp] theorem mem_constructorPaths_full (w : Word) : w ∈ full.constructorPaths :=
  RGraph.omega_fn w

/-- Constructor addresses are closed under prefixes. -/
theorem mem_constructorPaths_of_prefix {t : Tree} {v w : Word} (h : v <+: w)
    (hw : w ∈ t.constructorPaths) : v ∈ t.constructorPaths := by
  obtain ⟨r, rfl⟩ := h
  exact constructorPaths_prefix hw

/-! ## Top-freeness, finiteness and regularity of the constructor -/

@[simp] theorem topFree_f (a b : Tree) : (f a b).TopFree ↔ a.TopFree ∧ b.TopFree := by
  simp [f, topFree_node, Fin.forall_fin_two]

@[simp] theorem topFree_e : e.TopFree := by simp [e]

@[simp] theorem topFree_full : full.TopFree := by
  intro w
  simp [full]

theorem finite_f {a b : Tree} (ha : a.IsFinite) (hb : b.IsFinite) : (f a b).IsFinite := by
  apply finite_node
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem regular_f {a b : Tree} (ha : a.IsRegular) (hb : b.IsRegular) : (f a b).IsRegular := by
  apply regular_node
  intro i
  fin_cases i
  · exact ha
  · exact hb

@[simp] theorem finite_e : e.IsFinite := finite_f finite_bot finite_bot

theorem regular_full : full.IsRegular := ⟨RGraph.omega, rfl⟩

/-- The full tree is not finite. -/
theorem not_isFinite_full : ¬full.IsFinite := by
  rw [finite_iff_bounded topFree_full]
  rintro ⟨n, hn⟩
  have := hn (List.replicate n 0) (mem_constructorPaths_full _)
  simp at this

@[simp] theorem f_le_f_iff (a b c d : Tree) : f a b ≤ f c d ↔ a ≤ c ∧ b ≤ d := by
  simp [f, Fin.forall_fin_two]

/-- The full tree is the unique solution of `X = f(X, X)`. -/
theorem full_eq : full = f full full := by
  apply ext
  funext p
  cases p with
  | nil => rfl
  | cons i p => fin_cases i <;> simp [f, full]

/-- Every solution of `X = f(X, X)` is the full tree, even in the signature with top. -/
theorem eq_full_of_eq {x : Tree} (h : x = f x x) : x = full := by
  have hx : ∀ p, x.fn p = some .f := by
    intro p
    induction p with
    | nil => rw [h]; rfl
    | cons i p ih =>
      have hc : x.fn (i :: p) = x.fn p := by
        conv_lhs => rw [h]
        fin_cases i <;> rfl
      rw [hc, ih]
  apply ext
  funext p
  rw [hx p]
  exact (RGraph.omega_fn p).symm

/-! ## Order and address inclusion -/

/-- A top-free tree is below every tree containing its addresses. -/
theorem le_of_subset {a b : Tree} (ha : a.TopFree)
    (h : a.constructorPaths ⊆ b.constructorPaths) : a ≤ b := by
  intro p s t hs ht
  cases s with
  | bot => exact Sym.bot_le _
  | top => exact absurd hs (ha p)
  | f =>
    have hb : b.fn p = some .f := h (show p ∈ a.constructorPaths from hs)
    have : t = .f := Option.some.inj (ht.symm.trans hb)
    subst this
    exact le_rfl

/-- Comparison with the full tree is the absence of top. -/
theorem le_full_iff (t : Tree) : t ≤ full ↔ t.TopFree := by
  constructor
  · exact fun h => topFree_full.of_le h
  · exact fun h => le_of_subset h fun p _ => mem_constructorPaths_full p

/-- For top-free trees, failure of the order is witnessed by an address. -/
theorem not_le_iff_exists {a b : Tree} (ha : a.TopFree) (hb : b.TopFree) :
    ¬a ≤ b ↔ ∃ w ∈ a.constructorPaths, w ∉ b.constructorPaths := by
  rw [le_iff_constructorPaths_subset ha hb, Set.not_subset]

/-- A constructor is below a top-free tree when its root and both children embed. -/
theorem f_le_iff {a b C : Tree} (ha : a.TopFree) (hb : b.TopFree) (hC : C.TopFree) :
    f a b ≤ C ↔ [] ∈ C.constructorPaths ∧ (∀ w ∈ a.constructorPaths, 0 :: w ∈ C.constructorPaths) ∧
      ∀ w ∈ b.constructorPaths, 1 :: w ∈ C.constructorPaths := by
  rw [le_iff_constructorPaths_subset ((topFree_f a b).mpr ⟨ha, hb⟩) hC]
  constructor
  · intro h
    exact ⟨h (nil_mem_constructorPaths_f a b),
      fun w hw => h ((zero_cons_mem_constructorPaths_f a b w).mpr hw),
      fun w hw => h ((one_cons_mem_constructorPaths_f a b w).mpr hw)⟩
  · rintro ⟨h₀, ha', hb'⟩ w hw
    rcases w with _ | ⟨i, w⟩
    · exact h₀
    · fin_cases i
      · exact ha' w hw
      · exact hb' w hw

/-- A top-free tree is below a constructor when its two subtrees embed. -/
theorem le_f_iff {a b C : Tree} (ha : a.TopFree) (hb : b.TopFree) (hC : C.TopFree) :
    C ≤ f a b ↔ (∀ w, 0 :: w ∈ C.constructorPaths → w ∈ a.constructorPaths) ∧
      ∀ w, 1 :: w ∈ C.constructorPaths → w ∈ b.constructorPaths := by
  rw [le_iff_constructorPaths_subset hC ((topFree_f a b).mpr ⟨ha, hb⟩)]
  constructor
  · intro h
    exact ⟨fun w hw => (zero_cons_mem_constructorPaths_f a b w).mp (h hw),
      fun w hw => (one_cons_mem_constructorPaths_f a b w).mp (h hw)⟩
  · rintro ⟨h₀, h₁⟩ w hw
    rcases w with _ | ⟨i, w⟩
    · exact nil_mem_constructorPaths_f a b
    · fin_cases i
      · exact h₀ w hw
      · exact h₁ w hw

/-! ## Paths -/

/-- The least tree whose addresses contain `w`: its addresses are the prefixes of `w`. -/
def path : Word → Tree
  | [] => e
  | i :: w => node fun k => if k = i then path w else bot

@[simp] theorem mem_constructorPaths_path (w v : Word) :
    v ∈ (path w).constructorPaths ↔ v <+: w := by
  induction w generalizing v with
  | nil => simp [path, mem_constructorPaths_e]
  | cons i w ih =>
    cases v with
    | nil => simp [path, constructorPaths]
    | cons j v =>
      change (if j = i then path w else bot).fn v = some .f ↔ _
      by_cases h : j = i
      · subst j
        simpa [constructorPaths] using ih v
      · simp only [h, ite_false, List.cons_prefix_cons, false_and, iff_false]
        exact not_mem_constructorPaths_bot v

@[simp] theorem topFree_path (w : Word) : (path w).TopFree := by
  induction w with
  | nil => exact topFree_e
  | cons i w ih =>
    apply (topFree_node _).mpr
    intro k
    split
    · exact ih
    · exact topFree_bot

theorem finite_path (w : Word) : (path w).IsFinite := by
  induction w with
  | nil => exact finite_e
  | cons i w ih =>
    apply finite_node
    intro k
    split
    · exact ih
    · exact finite_bot

/-- A path is below a tree exactly when the tree contains its end. -/
theorem path_le_iff {X : Tree} (hX : X.TopFree) (w : Word) :
    path w ≤ X ↔ w ∈ X.constructorPaths := by
  rw [le_iff_constructorPaths_subset (topFree_path w) hX]
  constructor
  · exact fun h => h ((mem_constructorPaths_path w w).mpr List.prefix_rfl)
  · exact fun hw v hv => mem_constructorPaths_of_prefix ((mem_constructorPaths_path w v).mp hv) hw

/-- A path is below every tree containing its end, even one with top. -/
theorem path_le_of_mem {X : Tree} {w : Word} (h : w ∈ X.constructorPaths) : path w ≤ X := by
  exact le_of_subset (topFree_path w) fun v hv =>
    mem_constructorPaths_of_prefix ((mem_constructorPaths_path w v).mp hv) h

/-- The tree `f(⊥, path w)` is the path to `1 w`. -/
theorem f_bot_path (w : Word) : f bot (path w) = path (1 :: w) := by
  apply topFree_ext ((topFree_f _ _).mpr ⟨topFree_bot, topFree_path w⟩) (topFree_path _)
  ext v
  rcases v with _ | ⟨i, v⟩
  · simp
  · obtain rfl | rfl := letter_eq_zero_or_eq_one i <;> simp

/-- The tree `f(e, ⊥)` is the path to the word `0`. -/
theorem f_e_bot_eq_path : f e bot = path [0] := by
  apply topFree_ext ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩) (topFree_path _)
  ext w
  rcases w with _ | ⟨i, w⟩
  · simp
  · rcases letter_eq_zero_or_eq_one i with rfl | rfl
    · simp [mem_constructorPaths_e]
    · simp

/-! ## Cocones -/

/-- The greatest top-free tree avoiding `w`: its addresses are the words without
`w` as a prefix. -/
def cocone : Word → Tree
  | [] => bot
  | i :: w => node fun k => if k = i then cocone w else full

@[simp] theorem mem_constructorPaths_cocone (w v : Word) :
    v ∈ (cocone w).constructorPaths ↔ ¬w <+: v := by
  induction w generalizing v with
  | nil => simp [cocone]
  | cons i w ih =>
    cases v with
    | nil => simp [cocone, constructorPaths]
    | cons j v =>
      change (if j = i then cocone w else full).fn v = some .f ↔ _
      by_cases h : j = i
      · subst j
        simpa [constructorPaths] using ih v
      · simp [h, Ne.symm h, full]

@[simp] theorem topFree_cocone (w : Word) : (cocone w).TopFree := by
  induction w with
  | nil => exact topFree_bot
  | cons i w ih =>
    apply (topFree_node _).mpr
    intro k
    split
    · exact ih
    · exact topFree_full

theorem regular_cocone (w : Word) : (cocone w).IsRegular := by
  induction w with
  | nil => exact regular_bot
  | cons i w ih =>
    apply regular_node
    intro k
    split
    · exact ih
    · exact regular_full

/-- A top-free tree is below the cocone of `w` exactly when it avoids `w`. -/
theorem le_cocone_iff {X : Tree} (hX : X.TopFree) (w : Word) :
    X ≤ cocone w ↔ w ∉ X.constructorPaths := by
  rw [le_iff_constructorPaths_subset hX (topFree_cocone w)]
  constructor
  · exact fun h hw => (mem_constructorPaths_cocone w w).mp (h hw) List.prefix_rfl
  · intro hw v hv
    rw [mem_constructorPaths_cocone]
    exact fun hp => hw (mem_constructorPaths_of_prefix hp hv)

/-- The path to `w` is below the cocone of `u` exactly when `u` is not a prefix of `w`. -/
theorem path_le_cocone_iff (w u : Word) : path w ≤ cocone u ↔ ¬u <+: w := by
  rw [path_le_iff (topFree_cocone u), mem_constructorPaths_cocone]

/-- The path to `w` is not below the cocone of `w`. -/
theorem not_path_le_cocone (w : Word) : ¬path w ≤ cocone w :=
  fun h => (path_le_cocone_iff w w).mp h List.prefix_rfl

/-! ## Right nests -/

/-- `nestRight a j t = f(a, f(a, … f(a, t)))` with `j` constructors on the right spine. -/
def nestRight (a : Tree) : ℕ → Tree → Tree
  | 0, t => t
  | j + 1, t => f a (nestRight a j t)

@[simp] theorem nestRight_zero (a t : Tree) : nestRight a 0 t = t := rfl
@[simp] theorem nestRight_succ (a t : Tree) (j : ℕ) :
    nestRight a (j + 1) t = f a (nestRight a j t) := rfl

theorem mem_constructorPaths_nestRight (a t : Tree) (j : ℕ) (w : Word) :
    w ∈ (nestRight a j t).constructorPaths ↔
      (∃ i < j, w = ones i) ∨ (∃ i < j, ∃ v ∈ a.constructorPaths, w = ones i ++ 0 :: v) ∨
        ∃ v ∈ t.constructorPaths, w = ones j ++ v := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (Or.inl ⟨0, Nat.succ_pos j, rfl⟩)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [nestRight_succ, zero_cons_mem_constructorPaths_f]
        constructor
        · intro hw
          exact Or.inr (Or.inl ⟨0, Nat.succ_pos j, w, hw, rfl⟩)
        · rintro (⟨i, -, h⟩ | ⟨i, -, v, hv, h⟩ | ⟨v, -, h⟩)
          · exact absurd h (zero_cons_ne_ones w i)
          · obtain ⟨-, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
            exact hv
          · rw [ones_succ, List.cons_append, List.cons.injEq] at h
            exact absurd h.1 (by decide)
      · rw [nestRight_succ, one_cons_mem_constructorPaths_f, ih]
        constructor
        · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
          · exact Or.inl ⟨i + 1, by omega, rfl⟩
          · exact Or.inr (Or.inl ⟨i + 1, by omega, v, hv, rfl⟩)
          · exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
        · rintro (⟨i, hi, h⟩ | ⟨i, hi, v, hv, h⟩ | ⟨v, hv, h⟩)
          · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_iff.mp h
            exact Or.inl ⟨k, by omega, rfl⟩
          · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_append_iff.mp h
            exact Or.inr (Or.inl ⟨k, by omega, v, hv, rfl⟩)
          · rw [ones_succ, List.cons_append, List.cons.injEq] at h
            exact Or.inr (Or.inr ⟨v, hv, h.2⟩)

@[simp] theorem topFree_nestRight {a t : Tree} (ha : a.TopFree) (ht : t.TopFree) (j : ℕ) :
    (nestRight a j t).TopFree := by
  induction j with
  | zero => exact ht
  | succ j ih => exact (topFree_f _ _).mpr ⟨ha, ih⟩

theorem regular_nestRight {a t : Tree} (ha : a.IsRegular) (ht : t.IsRegular) (j : ℕ) :
    (nestRight a j t).IsRegular := by
  induction j with
  | zero => exact ht
  | succ j ih => exact regular_f ha ih

/-- Finite trees are closed under right nests. -/
theorem finite_nestRight {a t : Tree} (ha : a.IsFinite) (ht : t.IsFinite) (j : ℕ) :
    (nestRight a j t).IsFinite := by
  induction j with
  | zero => exact ht
  | succ j ih => exact finite_f ha ih

/-- A right nest over `⊥` grows when one more copy of its left child is added. -/
theorem nestRight_bot_le_f (a : Tree) (j : ℕ) :
    nestRight a j bot ≤ f a (nestRight a j bot) := by
  induction j with
  | zero => exact bot_le _
  | succ j ih => exact (f_le_f_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

/-! ## Joins and children -/

/-- The join of a set of trees, the union of their address sets, is top-free. -/
theorem topFree_sjoin (S : Set Tree) : (sjoin S).TopFree := ofConstructorPaths_topFree _ _

/-- The join of no trees is bottom. -/
theorem sjoin_empty : sjoin ∅ = bot :=
  topFree_ext (topFree_sjoin _) topFree_bot (by ext p; simp)

/-- Adding a tree to a set joins it with the join of the set. -/
theorem sjoin_insert (a : Tree) (S : Set Tree) : sjoin (insert a S) = join a (sjoin S) :=
  topFree_ext (topFree_sjoin _) (join_topFree _ _) (by ext p; simp)

/-- The join of finitely many regular trees is regular. -/
theorem regular_sjoin {S : Set Tree} (hS : S.Finite) (h : ∀ t ∈ S, t.IsRegular) :
    (sjoin S).IsRegular := by
  induction S, hS using Set.Finite.induction_on with
  | empty => rw [sjoin_empty]; exact regular_bot
  | @insert a S _ _ ih =>
    rw [sjoin_insert]
    exact regular_join (h a (Set.mem_insert a S))
      (ih fun t ht => h t (Set.mem_insert_of_mem a ht))

/-- The children of a regular tree are regular. -/
theorem IsRegular.branch {t : Tree} (ht : t.IsRegular) (hf : t.fn [] = some .f) (i : Fin 2) :
    (t.branch i hf).IsRegular := by
  obtain ⟨g, rfl⟩ := ht
  have hl : g.graph.label g.root = .f := Option.some.inj hf
  refine ⟨⟨g.State, g.states, g.graph, g.graph.child g.root i⟩, Tree.ext ?_⟩
  funext p
  change (g.graph.unfold (g.graph.child g.root i)).fn p = (g.graph.unfold g.root).fn (i :: p)
  rw [Graph.unfold_cons]
  simp only [hl, ↓reduceIte]

end Tree

/-! ## Membership in the domains -/

/-- Regular top-free trees belong to the regular and arbitrary domains, with or without top. -/
theorem domain_of_isRegular {c : TreeClass} {top : Bool} (hc : c ≠ .finite) {t : Tree}
    (hr : t.IsRegular) (ht : t.TopFree) : Domain c top t := by
  cases c with
  | finite => exact absurd rfl hc
  | regular => exact ⟨hr, Or.inr ht⟩
  | arbitrary => exact ⟨trivial, Or.inr ht⟩

/-- Top-free trees belong to the arbitrary domain, with or without top. -/
theorem domain_arbitrary_of_topFree {top : Bool} {t : Tree} (ht : t.TopFree) :
    Domain .arbitrary top t :=
  ⟨trivial, Or.inr ht⟩

/-- Finite top-free trees belong to every domain. -/
theorem domain_of_isFinite {c : TreeClass} {top : Bool} {t : Tree}
    (hf : t.IsFinite) (ht : t.TopFree) : Domain c top t := by
  cases c with
  | finite => exact ⟨hf, Or.inr ht⟩
  | regular => exact ⟨hf.isRegular, Or.inr ht⟩
  | arbitrary => exact ⟨trivial, Or.inr ht⟩

/-- Paths belong to every domain. -/
theorem domain_path {c : TreeClass} {top : Bool} (w : Word) : Domain c top (Tree.path w) :=
  domain_of_isFinite (Tree.finite_path w) (Tree.topFree_path w)

end UndeciSigma2
