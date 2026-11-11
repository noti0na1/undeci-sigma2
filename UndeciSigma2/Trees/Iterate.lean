import UndeciSigma2.Trees.Basic

/-! # Infinite spines

The equation `X = f(a, X)` has exactly one solution `rightSpine a`, an infinite
right spine with a copy of `a` as each left child. Symmetrically `X = f(X, b)`
has exactly one solution `leftSpine b`. Both are top-free and regular when the
given tree is, and neither is finite.
-/

namespace UndeciSigma2

open Word

namespace Tree

/-- Labels of the right spine with left children `a`. -/
def rightSpineFn (a : Tree) : Word → Option Sym
  | [] => some .f
  | i :: w => if i = 0 then a.fn w else rightSpineFn a w

/-- Labels of the left spine with right children `b`. -/
def leftSpineFn (b : Tree) : Word → Option Sym
  | [] => some .f
  | i :: w => if i = 0 then leftSpineFn b w else b.fn w

/-- The solution of `X = f(a, X)`: an infinite right spine whose left children are `a`. -/
def rightSpine (a : Tree) : Tree where
  fn := rightSpineFn a
  wf := by
    refine ⟨by simp [rightSpineFn], ?_⟩
    intro π i
    induction π with
    | nil =>
      simp only [List.nil_append, rightSpineFn]
      split
      · simpa using a.root_isSome
      · simp
    | cons j π ih =>
      simp only [List.cons_append, rightSpineFn]
      split
      · exact a.child_isSome_iff π i
      · exact ih

/-- The solution of `X = f(X, b)`: an infinite left spine whose right children are `b`. -/
def leftSpine (b : Tree) : Tree where
  fn := leftSpineFn b
  wf := by
    refine ⟨by simp [leftSpineFn], ?_⟩
    intro π i
    induction π with
    | nil =>
      simp only [List.nil_append, leftSpineFn]
      split
      · simp
      · simpa using b.root_isSome
    | cons j π ih =>
      simp only [List.cons_append, leftSpineFn]
      split
      · exact ih
      · exact b.child_isSome_iff π i

theorem rightSpine_eq (a : Tree) : rightSpine a = f a (rightSpine a) := by
  apply ext
  funext p
  cases p with
  | nil => rfl
  | cons i p => fin_cases i <;> rfl

theorem leftSpine_eq (b : Tree) : leftSpine b = f (leftSpine b) b := by
  apply ext
  funext p
  cases p with
  | nil => rfl
  | cons i p => fin_cases i <;> rfl

/-- `rightSpine a` is the only solution of `X = f(a, X)`, in every signature. -/
theorem eq_rightSpine_of_eq {a x : Tree} (h : x = f a x) : x = rightSpine a := by
  apply ext
  funext p
  induction p with
  | nil => rw [h]; rfl
  | cons i p ih =>
    have hc : x.fn (i :: p) = if i = 0 then a.fn p else x.fn p := by
      conv_lhs => rw [h]
      fin_cases i <;> rfl
    rw [hc, ih]
    rfl

/-- `leftSpine b` is the only solution of `X = f(X, b)`, in every signature. -/
theorem eq_leftSpine_of_eq {b x : Tree} (h : x = f x b) : x = leftSpine b := by
  apply ext
  funext p
  induction p with
  | nil => rw [h]; rfl
  | cons i p ih =>
    have hc : x.fn (i :: p) = if i = 0 then x.fn p else b.fn p := by
      conv_lhs => rw [h]
      fin_cases i <;> rfl
    rw [hc, ih]
    rfl

theorem mem_constructorPaths_rightSpine (a : Tree) (w : Word) :
    w ∈ (rightSpine a).constructorPaths ↔
      IsOnes w ∨ ∃ i, ∃ v ∈ a.constructorPaths, w = ones i ++ 0 :: v := by
  induction w with
  | nil => exact iff_of_true rfl (Or.inl isOnes_nil)
  | cons b w ih =>
    rw [rightSpine_eq]
    obtain rfl | rfl := letter_eq_zero_or_eq_one b
    · rw [zero_cons_mem_constructorPaths_f]
      constructor
      · intro hw
        exact Or.inr ⟨0, w, hw, rfl⟩
      · rintro (h | ⟨i, v, hv, h⟩)
        · exact absurd ((isOnes_cons _ _).mp h).1 (by decide)
        · obtain ⟨-, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
          exact hv
    · rw [one_cons_mem_constructorPaths_f, ih, isOnes_cons]
      constructor
      · rintro (h | ⟨i, v, hv, rfl⟩)
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨i + 1, v, hv, rfl⟩
      · rintro (⟨-, h⟩ | ⟨i, v, hv, h⟩)
        · exact Or.inl h
        · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_append_iff.mp h
          exact Or.inr ⟨k, v, hv, rfl⟩

theorem mem_constructorPaths_leftSpine (b : Tree) (w : Word) :
    w ∈ (leftSpine b).constructorPaths ↔
      (∃ x, w = zeros x) ∨ ∃ x, ∃ v ∈ b.constructorPaths, w = zeros x ++ 1 :: v := by
  induction w with
  | nil => exact iff_of_true rfl (Or.inl ⟨0, rfl⟩)
  | cons c w ih =>
    rw [leftSpine_eq]
    obtain rfl | rfl := letter_eq_zero_or_eq_one c
    · rw [zero_cons_mem_constructorPaths_f, ih]
      constructor
      · rintro (⟨x, rfl⟩ | ⟨x, v, hv, rfl⟩)
        · exact Or.inl ⟨x + 1, rfl⟩
        · exact Or.inr ⟨x + 1, v, hv, rfl⟩
      · rintro (⟨x, h⟩ | ⟨x, v, hv, h⟩)
        · rcases x with _ | x
          · simp at h
          · rw [zeros_succ, List.cons.injEq] at h
            exact Or.inl ⟨x, h.2⟩
        · rcases x with _ | x
          · simp at h
          · rw [zeros_succ, List.cons_append, List.cons.injEq] at h
            exact Or.inr ⟨x, v, hv, h.2⟩
    · rw [one_cons_mem_constructorPaths_f]
      constructor
      · intro hw
        exact Or.inr ⟨0, w, hw, rfl⟩
      · rintro (⟨x, h⟩ | ⟨x, v, hv, h⟩)
        · rcases x with _ | x
          · simp at h
          · rw [zeros_succ, List.cons.injEq] at h
            exact absurd h.1 (by decide)
        · rcases x with _ | x
          · rw [zeros_zero, List.nil_append, List.cons.injEq] at h
            exact h.2 ▸ hv
          · rw [zeros_succ, List.cons_append, List.cons.injEq] at h
            exact absurd h.1 (by decide)

theorem topFree_rightSpine {a : Tree} (ha : a.TopFree) : (rightSpine a).TopFree := by
  intro p
  induction p with
  | nil => simp [rightSpine, rightSpineFn]
  | cons i p ih =>
    change rightSpineFn a (i :: p) ≠ _
    simp only [rightSpineFn]
    split
    · exact ha p
    · exact ih

theorem topFree_leftSpine {b : Tree} (hb : b.TopFree) : (leftSpine b).TopFree := by
  intro p
  induction p with
  | nil => simp [leftSpine, leftSpineFn]
  | cons i p ih =>
    change leftSpineFn b (i :: p) ≠ _
    simp only [leftSpineFn]
    split
    · exact ih
    · exact hb p

/-- The graph of `rightSpine` over a presentation `g` of its left children: one new
constructor state, `none`, whose left child is the root of `g` and whose right child is itself. -/
def rightSpineGraph (g : RGraph) : Graph (Option g.State) where
  label q := q.elim .f g.graph.label
  child q i := q.elim (if i = 0 then some g.root else none) fun q => some (g.graph.child q i)

/-- The graph of `leftSpine` over a presentation `g` of its right children. -/
def leftSpineGraph (g : RGraph) : Graph (Option g.State) where
  label q := q.elim .f g.graph.label
  child q i := q.elim (if i = 0 then none else some g.root) fun q => some (g.graph.child q i)

theorem rightSpineGraph_unfold (g : RGraph) :
    (rightSpineGraph g).unfold none = rightSpine g.toTree := by
  have hs : (rightSpineGraph g).unfold (some g.root) = g.toTree :=
    Graph.unfold_map g.graph (rightSpineGraph g) some (fun _ => rfl) (fun _ _ => rfl) g.root
  apply eq_rightSpine_of_eq
  apply ext
  funext p
  cases p with
  | nil => rfl
  | cons i p =>
    obtain rfl | rfl := letter_eq_zero_or_eq_one i
    · change ((rightSpineGraph g).unfold (some g.root)).fn p = g.toTree.fn p
      rw [hs]
    · rfl

theorem leftSpineGraph_unfold (g : RGraph) :
    (leftSpineGraph g).unfold none = leftSpine g.toTree := by
  have hs : (leftSpineGraph g).unfold (some g.root) = g.toTree :=
    Graph.unfold_map g.graph (leftSpineGraph g) some (fun _ => rfl) (fun _ _ => rfl) g.root
  apply eq_leftSpine_of_eq
  apply ext
  funext p
  cases p with
  | nil => rfl
  | cons i p =>
    obtain rfl | rfl := letter_eq_zero_or_eq_one i
    · rfl
    · change ((leftSpineGraph g).unfold (some g.root)).fn p = g.toTree.fn p
      rw [hs]

theorem regular_rightSpine {a : Tree} (ha : a.IsRegular) : (rightSpine a).IsRegular := by
  obtain ⟨g, rfl⟩ := ha
  exact ⟨⟨Option g.State, inferInstance, rightSpineGraph g, none⟩, rightSpineGraph_unfold g⟩

theorem regular_leftSpine {b : Tree} (hb : b.IsRegular) : (leftSpine b).IsRegular := by
  obtain ⟨g, rfl⟩ := hb
  exact ⟨⟨Option g.State, inferInstance, leftSpineGraph g, none⟩, leftSpineGraph_unfold g⟩

end Tree

end UndeciSigma2
