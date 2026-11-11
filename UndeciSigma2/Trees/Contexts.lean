import UndeciSigma2.Trees.Helpers

/-! # Contexts reading combs out of the state tree

The state tree `U` stores the comb of state `q` as its subtree at `1^q 0`. Four
contexts compare a tree with such a comb:

* `pack q y = f(⊥, … f(⊥, f(y, ⊥)))` places `y` at `1^q 0`;
* `stateContext z r g = f(z, … f(f(z, g), z))` bounds the tail of the comb of
  state `r`, the subtree at `1^r 0 1`, by `g`;
* `haltContext z s n = f(z, … f(s, z))` bounds the comb of state `n` by `s`;
* `popContext z δ k = f(… f(k, z) …, z)` bounds the subtree at `0^δ` by `k`.

The parameters `z` and `s` stand for the values of the helper variables; with the
full tree and the right ray the comparisons become statements about addresses.
-/

namespace UndeciSigma2

open Word

namespace Tree

/-- `pack q y = f(⊥, … f(⊥, f(y, ⊥)))`, placing `y` at the address `1^q 0`. -/
def pack : ℕ → Tree → Tree
  | 0, y => f y bot
  | q + 1, y => f bot (pack q y)

/-- `stateContext z r g = f(z, … f(f(z, g), z))`, with `g` at the address `1^r 0 1`. -/
def stateContext (z : Tree) : ℕ → Tree → Tree
  | 0, g => f (f z g) z
  | r + 1, g => f z (stateContext z r g)

/-- `haltContext z s n = f(z, … f(s, z))`, with `s` at the address `1^n 0`. -/
def haltContext (z s : Tree) : ℕ → Tree
  | 0 => f s z
  | n + 1 => f z (haltContext z s n)

/-- `popContext z δ k = f(… f(k, z) …, z)`, with `k` at the address `0^δ`. -/
def popContext (z : Tree) : ℕ → Tree → Tree
  | 0, k => k
  | δ + 1, k => f (popContext z δ k) z

@[simp] theorem topFree_pack {y : Tree} (hy : y.TopFree) (q : ℕ) : (pack q y).TopFree := by
  induction q with
  | zero => exact (topFree_f _ _).mpr ⟨hy, topFree_bot⟩
  | succ q ih => exact (topFree_f _ _).mpr ⟨topFree_bot, ih⟩

/-- If `pack l y` is top-free, so is `y`. -/
theorem topFree_of_topFree_pack {l : ℕ} {y : Tree} (h : (pack l y).TopFree) : y.TopFree := by
  induction l with
  | zero => exact ((topFree_f _ _).mp h).1
  | succ l ih => exact ih ((topFree_f _ _).mp h).2

@[simp] theorem topFree_stateContext {z g : Tree} (hz : z.TopFree) (hg : g.TopFree) (r : ℕ) :
    (stateContext z r g).TopFree := by
  induction r with
  | zero => exact (topFree_f _ _).mpr ⟨(topFree_f _ _).mpr ⟨hz, hg⟩, hz⟩
  | succ r ih => exact (topFree_f _ _).mpr ⟨hz, ih⟩

@[simp] theorem topFree_haltContext {z s : Tree} (hz : z.TopFree) (hs : s.TopFree) (n : ℕ) :
    (haltContext z s n).TopFree := by
  induction n with
  | zero => exact (topFree_f _ _).mpr ⟨hs, hz⟩
  | succ n ih => exact (topFree_f _ _).mpr ⟨hz, ih⟩

@[simp] theorem topFree_popContext {z k : Tree} (hz : z.TopFree) (hk : k.TopFree) (δ : ℕ) :
    (popContext z δ k).TopFree := by
  induction δ with
  | zero => exact hk
  | succ δ ih => exact (topFree_f _ _).mpr ⟨ih, hz⟩

theorem mem_constructorPaths_pack (q : ℕ) (y : Tree) (w : Word) :
    w ∈ (pack q y).constructorPaths ↔
      (∃ i ≤ q, w = ones i) ∨ ∃ v ∈ y.constructorPaths, w = ones q ++ 0 :: v := by
  induction q generalizing w with
  | zero =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (Or.inl ⟨0, le_rfl, rfl⟩)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [pack, zero_cons_mem_constructorPaths_f]
        constructor
        · intro hw
          exact Or.inr ⟨w, hw, rfl⟩
        · rintro (⟨i, -, h⟩ | ⟨v, hv, h⟩)
          · exact absurd h (zero_cons_ne_ones w i)
          · obtain ⟨-, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
            exact hv
      · rw [pack, one_cons_mem_constructorPaths_f]
        refine iff_of_false (not_mem_constructorPaths_bot w) ?_
        rintro (⟨i, hi, h⟩ | ⟨v, -, h⟩)
        · obtain ⟨k, rfl, -⟩ := one_cons_eq_ones_iff.mp h
          omega
        · obtain ⟨k, hk, -⟩ := one_cons_eq_ones_append_iff.mp h
          omega
  | succ q ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (Or.inl ⟨0, Nat.zero_le _, rfl⟩)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [pack, zero_cons_mem_constructorPaths_f]
        refine iff_of_false (not_mem_constructorPaths_bot w) ?_
        rintro (⟨i, -, h⟩ | ⟨v, -, h⟩)
        · exact zero_cons_ne_ones w i h
        · have := (zero_cons_eq_ones_append_iff.mp h).1
          omega
      · rw [pack, one_cons_mem_constructorPaths_f, ih]
        constructor
        · rintro (⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩)
          · exact Or.inl ⟨i + 1, by omega, rfl⟩
          · exact Or.inr ⟨v, hv, rfl⟩
        · rintro (⟨i, hi, h⟩ | ⟨v, hv, h⟩)
          · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_iff.mp h
            exact Or.inl ⟨k, by omega, rfl⟩
          · obtain ⟨k, hk, rfl⟩ := one_cons_eq_ones_append_iff.mp h
            obtain rfl : q = k := by omega
            exact Or.inr ⟨v, hv, rfl⟩

/-- The addresses of `stateContext full r g`: all words except `1^r 0 1 v` with `v ∉ g`. -/
theorem mem_constructorPaths_stateContext (r : ℕ) (g : Tree) (w : Word) :
    w ∈ (stateContext full r g).constructorPaths ↔
      ∀ v, w = ones r ++ 0 :: 1 :: v → v ∈ g.constructorPaths := by
  induction r generalizing w with
  | zero =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [stateContext, zero_cons_mem_constructorPaths_f]
        rcases w with _ | ⟨c, w⟩
        · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
        · obtain rfl | rfl := letter_eq_zero_or_eq_one c
          · rw [zero_cons_mem_constructorPaths_f]
            refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
            simp at h
          · rw [one_cons_mem_constructorPaths_f]
            constructor
            · rintro hw v h
              simp only [ones_zero, List.nil_append, List.cons.injEq, true_and] at h
              exact h ▸ hw
            · intro h
              exact h w rfl
      · rw [stateContext, one_cons_mem_constructorPaths_f]
        refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
        simp at h
  | succ r ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [stateContext, zero_cons_mem_constructorPaths_f]
        refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
        simp at h
      · rw [stateContext, one_cons_mem_constructorPaths_f, ih]
        simp only [ones_succ, List.cons_append, List.cons.injEq, true_and]

/-- The addresses of `haltContext full s n`: all words except `1^n 0 v` with `v ∉ s`. -/
theorem mem_constructorPaths_haltContext (s : Tree) (n : ℕ) (w : Word) :
    w ∈ (haltContext full s n).constructorPaths ↔
      ∀ v, w = ones n ++ 0 :: v → v ∈ s.constructorPaths := by
  induction n generalizing w with
  | zero =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [haltContext, zero_cons_mem_constructorPaths_f]
        constructor
        · rintro hw v h
          simp only [ones_zero, List.nil_append, List.cons.injEq, true_and] at h
          exact h ▸ hw
        · intro h
          exact h w rfl
      · rw [haltContext, one_cons_mem_constructorPaths_f]
        refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
        simp at h
  | succ n ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [haltContext, zero_cons_mem_constructorPaths_f]
        refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
        simp at h
      · rw [haltContext, one_cons_mem_constructorPaths_f, ih]
        simp only [ones_succ, List.cons_append, List.cons.injEq, true_and]

/-- The addresses of `popContext full δ k`: all words except `0^δ v` with `v ∉ k`. -/
theorem mem_constructorPaths_popContext (δ : ℕ) (k : Tree) (w : Word) :
    w ∈ (popContext full δ k).constructorPaths ↔
      ∀ v, w = zeros δ ++ v → v ∈ k.constructorPaths := by
  induction δ generalizing w with
  | zero =>
    simp only [popContext, zeros_zero, List.nil_append]
    exact ⟨fun hw v h => h ▸ hw, fun h => h w rfl⟩
  | succ δ ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (nil_mem_constructorPaths_f _ _) (fun v h => by simp at h)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [popContext, zero_cons_mem_constructorPaths_f, ih]
        simp only [zeros_succ, List.cons_append, List.cons.injEq, true_and]
      · rw [popContext, one_cons_mem_constructorPaths_f]
        refine iff_of_true (mem_constructorPaths_full w) (fun v h => ?_)
        simp at h

/-- `pack q y ≤ U`: the spine of `U` reaches `q` and `y` embeds at `1^q 0`. -/
theorem pack_le_iff {y U : Tree} (hy : y.TopFree) (hU : U.TopFree) (q : ℕ) :
    pack q y ≤ U ↔ (∀ i ≤ q, ones i ∈ U.constructorPaths) ∧
      ∀ w ∈ y.constructorPaths, ones q ++ 0 :: w ∈ U.constructorPaths := by
  rw [le_iff_constructorPaths_subset (topFree_pack hy q) hU]
  constructor
  · intro h
    exact ⟨fun i hi => h ((mem_constructorPaths_pack q y _).mpr (Or.inl ⟨i, hi, rfl⟩)),
      fun w hw => h ((mem_constructorPaths_pack q y _).mpr (Or.inr ⟨w, hw, rfl⟩))⟩
  · rintro ⟨h₁, h₂⟩ w hw
    rcases (mem_constructorPaths_pack q y w).mp hw with ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
    · exact h₁ i hi
    · exact h₂ v hv

/-- If `pack q y ≤ U` for top-free `y` and `U`, every address `w` of `y` gives the address
`1^q 0 w` of `U`. -/
theorem mem_of_pack_le {y U : Tree} (hy : y.TopFree) (hU : U.TopFree) {q : ℕ}
    (h : pack q y ≤ U) {w : Word} (hw : w ∈ y.constructorPaths) :
    ones q ++ 0 :: w ∈ U.constructorPaths :=
  ((pack_le_iff hy hU q).mp h).2 w hw

/-- If `1^q 0 w` is an address of `U`, the path to `w` packed at state `q` is below `U`. -/
theorem pack_path_le {U : Tree} {q : ℕ} {w : Word} (hU : U.TopFree)
    (h : ones q ++ 0 :: w ∈ U.constructorPaths) : pack q (path w) ≤ U := by
  rw [pack_le_iff (topFree_path w) hU]
  refine ⟨fun i hi => mem_constructorPaths_of_prefix ?_ h, fun v hv =>
    mem_constructorPaths_of_prefix ?_ h⟩
  · exact (ones_prefix_ones_iff.mpr hi).trans (List.prefix_append _ _)
  · rw [mem_constructorPaths_path] at hv
    exact (List.prefix_append_right_inj _).mpr (List.cons_prefix_cons.mpr ⟨rfl, hv⟩)

/-- `U ≤ stateContext full r g`: the tail of the comb of state `r` embeds in `g`. -/
theorem le_stateContext_iff {U g : Tree} (hU : U.TopFree) (hg : g.TopFree) (r : ℕ) :
    U ≤ stateContext full r g ↔
      ∀ w, ones r ++ 0 :: 1 :: w ∈ U.constructorPaths → w ∈ g.constructorPaths := by
  rw [le_iff_constructorPaths_subset hU (topFree_stateContext topFree_full hg r)]
  constructor
  · intro h w hw
    exact (mem_constructorPaths_stateContext r g _).mp (h hw) w rfl
  · intro h w hw
    exact (mem_constructorPaths_stateContext r g w).mpr fun v hv => h v (hv ▸ hw)

/-- `U ≤ haltContext full rightRay n`: the comb of state `n` has no tooth. -/
theorem le_haltContext_iff {U : Tree} (hU : U.TopFree) (n : ℕ) :
    U ≤ haltContext full rightRay n ↔
      ∀ w, ones n ++ 0 :: w ∈ U.constructorPaths → IsOnes w := by
  rw [le_iff_constructorPaths_subset hU (topFree_haltContext topFree_full topFree_rightRay n)]
  constructor
  · intro h w hw
    exact (mem_constructorPaths_rightRay w).mp
      ((mem_constructorPaths_haltContext rightRay n _).mp (h hw) w rfl)
  · intro h w hw
    exact (mem_constructorPaths_haltContext rightRay n w).mpr fun v hv =>
      (mem_constructorPaths_rightRay v).mpr (h v (hv ▸ hw))

/-- `k ≤ popContext full δ kd`: the subtree of `k` at `0^δ` embeds in `kd`. -/
theorem le_popContext_iff {k kd : Tree} (hk : k.TopFree) (hkd : kd.TopFree) (δ : ℕ) :
    k ≤ popContext full δ kd ↔
      ∀ w, zeros δ ++ w ∈ k.constructorPaths → w ∈ kd.constructorPaths := by
  rw [le_iff_constructorPaths_subset hk (topFree_popContext topFree_full hkd δ)]
  constructor
  · intro h w hw
    exact (mem_constructorPaths_popContext δ kd _).mp (h hw) w rfl
  · intro h w hw
    exact (mem_constructorPaths_popContext δ kd w).mpr fun v hv => h v (hv ▸ hw)

/-- `f(⊥, y) ≤ C`: the root of `C` is a constructor and `y` embeds in its right child. -/
theorem f_bot_le_iff {y C : Tree} (hy : y.TopFree) (hC : C.TopFree) :
    f bot y ≤ C ↔ [] ∈ C.constructorPaths ∧
      ∀ w ∈ y.constructorPaths, 1 :: w ∈ C.constructorPaths := by
  rw [f_le_iff topFree_bot hy hC]
  constructor
  · rintro ⟨h₀, -, h₁⟩
    exact ⟨h₀, h₁⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, fun w hw => absurd hw (not_mem_constructorPaths_bot w), h₁⟩

/-- `C ≤ f(full, g)`: the right child of `C` embeds in `g`. -/
theorem le_f_full_iff {C g : Tree} (hC : C.TopFree) (hg : g.TopFree) :
    C ≤ f full g ↔ ∀ w, 1 :: w ∈ C.constructorPaths → w ∈ g.constructorPaths := by
  rw [le_f_iff topFree_full hg hC]
  exact ⟨fun h => h.2, fun h => ⟨fun w _ => mem_constructorPaths_full w, h⟩⟩

/-! ## Examples -/

example (y : Tree) : pack 2 y = f bot (f bot (f y bot)) := rfl
example (z g : Tree) : stateContext z 1 g = f z (f (f z g) z) := rfl
example (z s : Tree) : haltContext z s 1 = f z (f s z) := rfl
example (z k : Tree) : popContext z 2 k = f (f k z) z := rfl

end Tree

end UndeciSigma2
