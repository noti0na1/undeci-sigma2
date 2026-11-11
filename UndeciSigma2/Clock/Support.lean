import UndeciSigma2.Trees.Basic

/-! # Supports and top paths

The order on trees with top is not inclusion of constructor addresses. Its monotone
replacement is the support: the constructor addresses together with every address at or
below a top. For trees `a ≤ b` the support of `a` is contained in the support of `b`, and a
top-free tree lies below `g` exactly when its constructor addresses lie in the support of
`g`, whether or not `g` contains top. These facts let the clauses of the clock sentence be
read as statements about address sets for universal values with or without top.

A tree `t` with `t ≤ f(a, t)` and `a` top-free is top-free: a shortest address at or below a
top of `t` would be `1 w` with `w` a shorter one. Below such a loop the support of `t` is
closed under removing leading ones, and removing a leading zero leads into the support of `a`.
-/

namespace UndeciSigma2

open Word

namespace Tree

/-- The addresses at or below a top of `t`. -/
def topPaths (t : Tree) : Set Word := {p | ∃ q, q <+: p ∧ t.fn q = some .top}

/-- The support of `t`: its constructor addresses and the addresses at or below a top. -/
def support (t : Tree) : Set Word := t.constructorPaths ∪ t.topPaths

theorem constructorPaths_subset_support (t : Tree) : t.constructorPaths ⊆ t.support :=
  Set.subset_union_left

theorem topPaths_subset_support (t : Tree) : t.topPaths ⊆ t.support :=
  Set.subset_union_right

/-- A tree is top-free exactly when it has no top paths. -/
theorem topPaths_eq_empty_iff (t : Tree) : t.topPaths = ∅ ↔ t.TopFree := by
  constructor
  · intro h p hp
    have : p ∈ t.topPaths := ⟨p, List.prefix_rfl, hp⟩
    rw [h] at this
    exact this
  · intro h
    ext p
    simp only [topPaths, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and]
    exact fun q _ hq => h q hq

/-- The support of a top-free tree is its set of constructor addresses. -/
theorem support_eq {t : Tree} (ht : t.TopFree) : t.support = t.constructorPaths := by
  rw [support, (topPaths_eq_empty_iff t).mpr ht, Set.union_empty]

/-- The support is closed under prefixes. -/
theorem mem_support_of_prefix {t : Tree} {v w : Word} (h : v <+: w) (hw : w ∈ t.support) :
    v ∈ t.support := by
  rcases hw with hw | ⟨q, hq, ht⟩
  · exact Or.inl (mem_constructorPaths_of_prefix h hw)
  · rcases h with ⟨r, rfl⟩
    rcases List.prefix_or_prefix_of_prefix hq (List.prefix_append v r) with hq | hq
    · exact Or.inr ⟨q, hq, ht⟩
    · by_cases he : v = q
      · exact Or.inr ⟨q, he ▸ List.prefix_rfl, ht⟩
      · exact Or.inl (t.label_eq_f_of_proper_prefix hq he (by simp [ht]))

@[simp] theorem support_bot : bot.support = ∅ := by
  rw [support_eq topFree_bot]
  ext w
  simp

@[simp] theorem support_top : top.support = Set.univ := by
  ext w
  simp only [Set.mem_univ, iff_true]
  exact Or.inr ⟨[], List.nil_prefix, rfl⟩

@[simp] theorem nil_mem_support_f (a b : Tree) : [] ∈ (f a b).support :=
  Or.inl (nil_mem_constructorPaths_f a b)

@[simp] theorem nil_not_mem_topPaths_node (a : Fin 2 → Tree) :
    [] ∉ (node a).topPaths := by
  rintro ⟨q, hq, ht⟩
  have : q = [] := List.eq_nil_of_prefix_nil hq
  subst q
  simp at ht

@[simp] theorem cons_mem_topPaths_node (a : Fin 2 → Tree) (i : Fin 2) (w : Word) :
    i :: w ∈ (node a).topPaths ↔ w ∈ (a i).topPaths := by
  constructor
  · rintro ⟨q, hq, ht⟩
    cases q with
    | nil => simp at ht
    | cons j q =>
      obtain ⟨rfl, hp⟩ := List.cons_prefix_cons.mp hq
      exact ⟨q, hp, ht⟩
  · rintro ⟨q, hq, ht⟩
    exact ⟨i :: q, List.cons_prefix_cons.mpr ⟨rfl, hq⟩, ht⟩

@[simp] theorem cons_mem_support_node (a : Fin 2 → Tree) (i : Fin 2) (w : Word) :
    i :: w ∈ (node a).support ↔ w ∈ (a i).support := by
  simp only [support, Set.mem_union, cons_mem_topPaths_node]
  rfl

@[simp] theorem zero_cons_mem_support_f (a b : Tree) (w : Word) :
    0 :: w ∈ (f a b).support ↔ w ∈ a.support := by
  simp [f]

@[simp] theorem one_cons_mem_support_f (a b : Tree) (w : Word) :
    1 :: w ∈ (f a b).support ↔ w ∈ b.support := by
  simp [f]

/-- The support of a constructor: the root, and the supports of the children below `0` and `1`. -/
theorem support_f (a b : Tree) :
    (f a b).support = {[]} ∪ List.cons 0 '' a.support ∪ List.cons 1 '' b.support := by
  ext w
  rcases w with _ | ⟨i, w⟩
  · simp
  · obtain rfl | rfl := letter_eq_zero_or_eq_one i <;> simp

/-- Supports are monotone. -/
theorem support_mono {a b : Tree} (h : a ≤ b) : a.support ⊆ b.support := by
  intro w
  induction w generalizing a b with
  | nil =>
    intro hw
    rcases (le_iff_root_cases a b).mp h with rfl | rfl | ⟨a, b, rfl, rfl, hab⟩
    · simp at hw
    · simp
    · exact Or.inl rfl
  | cons i w ih =>
    intro hw
    rcases (le_iff_root_cases a b).mp h with rfl | rfl | ⟨a, b, rfl, rfl, hab⟩
    · simp at hw
    · simp
    · exact (cons_mem_support_node b i w).mpr
        (ih (hab i) ((cons_mem_support_node a i w).mp hw))

/-- Top paths are monotone. -/
theorem topPaths_mono {a b : Tree} (h : a ≤ b) : a.topPaths ⊆ b.topPaths := by
  intro w
  induction w generalizing a b with
  | nil =>
    rintro ⟨q, hq, ht⟩
    have : q = [] := List.eq_nil_of_prefix_nil hq
    subst q
    have ha : a = top := (root_eq_top_iff a).mp ht
    have hb : b = top := (top_le_iff b).mp (ha ▸ h)
    exact ⟨[], List.prefix_rfl, hb ▸ rfl⟩
  | cons i w ih =>
    intro hw
    rcases (le_iff_root_cases a b).mp h with rfl | rfl | ⟨a, b, rfl, rfl, hab⟩
    · rw [(topPaths_eq_empty_iff bot).mpr topFree_bot] at hw
      exact hw.elim
    · exact ⟨[], List.nil_prefix, rfl⟩
    · exact (cons_mem_topPaths_node b i w).mpr
        (ih (hab i) ((cons_mem_topPaths_node a i w).mp hw))

/-- A top-free tree lies below `b` exactly when its constructor addresses lie in the support
of `b`, also when `b` contains top. -/
theorem le_iff_subset_support {a b : Tree} (ha : a.TopFree) :
    a ≤ b ↔ a.constructorPaths ⊆ b.support := by
  constructor
  · intro h
    exact (constructorPaths_subset_support a).trans (support_mono h)
  · intro h p x y hx hy
    cases x with
    | bot => exact Sym.bot_le _
    | top => exact False.elim (ha p hx)
    | f =>
      rcases h hx with hf | ⟨q, hq, htop⟩
      · have : y = .f := Option.some.inj (hy.symm.trans hf)
        subst y
        exact le_rfl
      · by_cases he : q = p
        · subst q
          have : y = .top := Option.some.inj (hy.symm.trans htop)
          subst y
          exact Sym.le_top _
        · have hf := b.label_eq_f_of_proper_prefix hq he (by simp [hy])
          simp [htop] at hf

/-- A tree `t` with `t ≤ f(a, t)` and `a` top-free is top-free. -/
theorem topFree_of_le_f {a t : Tree} (h : t ≤ f a t) (ha : a.TopFree) : t.TopFree := by
  have hempty : ∀ w : Word, w ∉ t.topPaths := by
    intro w
    induction w with
    | nil =>
      intro hw
      exact nil_not_mem_topPaths_node _ (topPaths_mono h hw)
    | cons i w ih =>
      intro hw
      have hh := topPaths_mono h hw
      obtain rfl | rfl := letter_eq_zero_or_eq_one i
      · have hh : w ∈ a.topPaths := (cons_mem_topPaths_node _ 0 w).mp hh
        rw [(topPaths_eq_empty_iff a).mpr ha] at hh
        exact hh
      · exact ih ((cons_mem_topPaths_node _ 1 w).mp hh)
  intro w hw
  exact hempty w ⟨w, List.prefix_rfl, hw⟩

/-! ## Supports below loops -/

/-- If `k ≤ f(a, k)`, the support of `k` is closed under removing a leading one. -/
theorem mem_support_of_one_cons_mem {a k : Tree} (h : k ≤ f a k) {u : Word}
    (hu : 1 :: u ∈ k.support) : u ∈ k.support :=
  (one_cons_mem_support_f a k u).mp (support_mono h hu)

/-- If `k ≤ f(a, k)`, removing a leading zero from a word of the support of `k` gives a word of
the support of `a`. -/
theorem mem_support_of_zero_cons_mem {a k : Tree} (h : k ≤ f a k) {u : Word}
    (hu : 0 :: u ∈ k.support) : u ∈ a.support :=
  (zero_cons_mem_support_f a k u).mp (support_mono h hu)

/-- If `k ≤ f(a, k)`, the support of `k` is closed under removing leading ones. -/
theorem mem_support_of_ones_append_mem {a k : Tree} (h : k ≤ f a k) (j : ℕ) {u : Word}
    (hu : ones j ++ u ∈ k.support) : u ∈ k.support :=
  mem_of_ones_append_mem (fun _ hw => mem_support_of_one_cons_mem h hw) j hu

end Tree

end UndeciSigma2
