import UndeciSigma2.Clock.Support
import UndeciSigma2.Trees.Contexts

/-! # Trees for the clock sentence

The combs of the clock sentence are read to the right: the word `toothWord s x = 1^s 0 1^x`
is depth `x` of the tooth at stamp `s`. This file proves the basic facts about tooth words and
collects the constructions on top-free trees used to refute or to satisfy the clauses; `F(t)`
denotes the set of addresses of `t`:

* the residual `t.residual p`, with addresses `{u | p u ∈ F(t)}`;
* the spine join `spineJoin t`, with addresses `{u | ∃ a, 1^a u ∈ F(t)}`, and its left child
  `tails t`, with addresses `{v | ∃ a, 1^a 0 v ∈ F(t)}`;
* the finite union `unionTree ts` and the prefix closure `prefixTree W` of a set of words;
* the finite trees `shapeTree n` (spine words and stubs), `oneZeroTree n` (spine words and
  teeth), `dropTree w` and `strictDropTree w` (the words obtained from prefixes of `w` by
  removing leading ones);
* the contexts `select k a t = f(a 0, f(a 1, … f(a (k - 1), t)))`, `componentContext` and
  `tailContext`, which compare the components of a label tree with a bound.

It also proves the facts about the loop `t ≤ f(a, t)`: for top-free `a` and `t`, the
addresses of `t` are spine words and words `1^j 0 u` with `u` an address of `a`.

Finally, each tree class is closed under the constructions used: residuals of top-free trees,
finite unions, and spine joins (an infinite union in general, but a finite one for finite and
for regular trees).
-/

namespace UndeciSigma2

open Word

namespace Clock

/-! ## Words -/

/-- The word `1^s 0 1^x`: depth `x` of the tooth at stamp `s` of a comb read to the right. -/
def toothWord (s x : ℕ) : Word := ones s ++ 0 :: ones x

@[simp] theorem toothWord_zero_right (s : ℕ) : toothWord s 0 = stub s := rfl

@[simp] theorem length_toothWord (s x : ℕ) : (toothWord s x).length = s + 1 + x := by
  simp [toothWord]; omega

/-- A tooth word determines its stamp and its depth. -/
theorem toothWord_inj {s x s' x' : ℕ} : toothWord s x = toothWord s' x' ↔ s = s' ∧ x = x' := by
  simp only [toothWord, ones_append_zero_cons_inj]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa using congrArg List.length h⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The prefixes of a tooth word: spine words up to the stamp and shorter tooth words. -/
theorem prefix_toothWord_iff {w : Word} {s x : ℕ} :
    w <+: toothWord s x ↔ (∃ i ≤ s, w = ones i) ∨ ∃ y ≤ x, w = toothWord s y := by
  rw [toothWord, prefix_ones_append_zero_cons_iff]
  constructor
  · rintro (h | ⟨v, hv, rfl⟩)
    · exact Or.inl h
    · obtain ⟨y, hy, rfl⟩ := prefix_ones_iff.mp hv
      exact Or.inr ⟨y, hy, rfl⟩
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ones y, ones_prefix_ones_iff.mpr hy, rfl⟩

/-- Leading ones move the stamp of a tooth word. -/
theorem ones_append_toothWord (c s x : ℕ) : ones c ++ toothWord s x = toothWord (c + s) x := by
  simp [toothWord, ones_add, List.append_assoc]

/-- A shorter tooth word of the same stamp is a prefix. -/
theorem toothWord_prefix_toothWord {s x y : ℕ} (h : x ≤ y) : toothWord s x <+: toothWord s y :=
  (List.prefix_append_right_inj _).mpr
    (List.cons_prefix_cons.mpr ⟨rfl, ones_prefix_ones_iff.mpr h⟩)

/-- The stub of a stamp is a prefix of its tooth words. -/
theorem stub_prefix_toothWord (s y : ℕ) : stub s <+: toothWord s y :=
  toothWord_prefix_toothWord (Nat.zero_le y)

/-- A tooth word is not a spine word. -/
theorem not_isOnes_toothWord (s y : ℕ) : ¬IsOnes (toothWord s y) :=
  not_isOnes_ones_append_zero_cons s (ones y)

/-- A tooth word is not a word of ones. -/
theorem toothWord_ne_ones (s y i : ℕ) : toothWord s y ≠ ones i := fun h =>
  not_isOnes_toothWord s y (h ▸ isOnes_ones i)

/-- A tooth word has exactly one zero. -/
theorem count_zero_toothWord (s y : ℕ) : (toothWord s y).count 0 = 1 := by
  rw [toothWord, count_zero_ones_append_zero_cons, count_zero_eq_zero_of_isOnes (isOnes_ones y)]

/-- A tree containing a tooth word contains the shorter tooth words of the same stamp. -/
theorem toothWord_mem_of_le {X : Tree} {s y y' : ℕ} (h : y ≤ y')
    (hX : toothWord s y' ∈ X.constructorPaths) : toothWord s y ∈ X.constructorPaths :=
  Tree.mem_constructorPaths_of_prefix (toothWord_prefix_toothWord h) hX

/-- A tree containing a tooth word contains its stub. -/
theorem stub_mem_of_toothWord_mem {X : Tree} {s y : ℕ}
    (hX : toothWord s y ∈ X.constructorPaths) : stub s ∈ X.constructorPaths :=
  Tree.mem_constructorPaths_of_prefix (stub_prefix_toothWord s y) hX

/-- The words `v` such that `1ᵃ v` is a prefix of `w` for some `a`. -/
def dropOnes (w : Word) : Set Word := {v | ∃ a, ones a ++ v <+: w}

/-- The words `v` such that `1ᵃ v` is a prefix of `w` for some `a ≥ 1`. -/
def dropOnesStrict (w : Word) : Set Word := {v | ∃ a, ones (a + 1) ++ v <+: w}

end Clock

open Clock

namespace Tree

/-! ## Residuals -/

/-- The residual of `t` at `p`: the top-free tree with addresses `{u | p u ∈ F(t)}`. For a
top-free tree and an address `p` it is the subtree at `p`. -/
noncomputable def residual (t : Tree) (p : Word) : Tree :=
  ofConstructorPaths {u | p ++ u ∈ t.constructorPaths} fun u r h =>
    constructorPaths_prefix (p := p ++ u) (r := r) (by simpa [List.append_assoc] using h)

/-- The addresses of a residual. -/
@[simp] theorem mem_residual (t : Tree) (p u : Word) :
    u ∈ (t.residual p).constructorPaths ↔ p ++ u ∈ t.constructorPaths := by
  exact Set.ext_iff.mp (ofConstructorPaths_constructorPaths _ _) u

@[simp] theorem topFree_residual (t : Tree) (p : Word) : (t.residual p).TopFree :=
  ofConstructorPaths_topFree _ _

theorem residual_nil {t : Tree} (ht : t.TopFree) : t.residual [] = t :=
  topFree_ext (topFree_residual t []) ht (by ext u; simp)

theorem residual_residual (t : Tree) (p q : Word) :
    (t.residual p).residual q = t.residual (p ++ q) :=
  topFree_ext (topFree_residual _ _) (topFree_residual _ _) (by ext u; simp [List.append_assoc])

/-- Residuals are monotone. -/
theorem residual_mono {a b : Tree} (h : a ≤ b) (hb : b.TopFree) (p : Word) :
    a.residual p ≤ b.residual p := by
  apply (le_iff_constructorPaths_subset (topFree_residual _ _) (topFree_residual _ _)).mpr
  intro u hu
  exact (mem_residual b p u).mpr
    ((le_iff_constructorPaths_subset (hb.of_le h) hb).mp h ((mem_residual a p u).mp hu))

/-- A top-free tree lies below `f(a, b)` exactly when its two residuals at `0` and `1` lie
below `a` and `b`; this includes the tree `⊥`, whose residuals are `⊥`. -/
theorem le_f_iff_residual {t a b : Tree} (ht : t.TopFree) :
    t ≤ f a b ↔ t.residual [0] ≤ a ∧ t.residual [1] ≤ b := by
  rw [le_iff_subset_support ht, le_iff_subset_support (topFree_residual _ _),
    le_iff_subset_support (topFree_residual _ _)]
  constructor
  · intro h
    exact ⟨fun u hu => (zero_cons_mem_support_f a b u).mp (h (by simpa using hu)),
      fun u hu => (one_cons_mem_support_f a b u).mp (h (by simpa using hu))⟩
  · rintro ⟨ha, hb⟩ w hw
    cases w with
    | nil => exact nil_mem_support_f a b
    | cons i w =>
      obtain rfl | rfl := letter_eq_zero_or_eq_one i
      · exact (zero_cons_mem_support_f a b w).mpr (ha (by simpa using hw))
      · exact (one_cons_mem_support_f a b w).mpr (hb (by simpa using hw))

/-- The residuals of `⊥` lie below every tree. -/
theorem residual_bot_le (q : Word) (U : Tree) : bot.residual q ≤ U :=
  le_of_subset (topFree_residual _ _) fun u hu => by simp at hu

/-- A top-free tree whose addresses are addresses of residuals of `X` lies below every `z` above
all residuals of `X`, also when `z` contains top. -/
theorem le_of_forall_mem_residual {t X z : Tree} (ht : t.TopFree) (hres : ∀ p, X.residual p ≤ z)
    (h : ∀ u ∈ t.constructorPaths, ∃ p, p ++ u ∈ X.constructorPaths) : t ≤ z := by
  rw [le_iff_subset_support ht]
  intro u hu
  obtain ⟨p, hp⟩ := h u hu
  exact support_mono (hres p)
    (constructorPaths_subset_support _ ((mem_residual X p u).mpr hp))

/-! ## Spine joins and tails -/

/-- The spine join of `t`: the top-free tree with addresses `{u | ∃ a, 1^a u ∈ F(t)}`, the
union of the residuals of `t` along its right spine. -/
noncomputable def spineJoin (t : Tree) : Tree :=
  ofConstructorPaths {u | ∃ a, ones a ++ u ∈ t.constructorPaths} fun u r ⟨a, h⟩ =>
    ⟨a, constructorPaths_prefix (p := ones a ++ u) (r := r) (by simpa [List.append_assoc] using h)⟩

/-- The addresses of a spine join. -/
@[simp] theorem mem_spineJoin (t : Tree) (u : Word) :
    u ∈ (spineJoin t).constructorPaths ↔ ∃ a, ones a ++ u ∈ t.constructorPaths := by
  exact Set.ext_iff.mp (ofConstructorPaths_constructorPaths _ _) u

@[simp] theorem topFree_spineJoin (t : Tree) : (spineJoin t).TopFree :=
  ofConstructorPaths_topFree _ _

/-- The tails of `t`: the top-free tree with addresses `{v | ∃ a, 1^a 0 v ∈ F(t)}`, the left
child of the spine join. -/
noncomputable def tails (t : Tree) : Tree := (spineJoin t).residual [0]

/-- The addresses of the tails. -/
@[simp] theorem mem_tails (t : Tree) (v : Word) :
    v ∈ (tails t).constructorPaths ↔ ∃ a, ones a ++ 0 :: v ∈ t.constructorPaths := by
  simp [tails]

@[simp] theorem topFree_tails (t : Tree) : (tails t).TopFree := topFree_residual _ _

/-! ## Unions and prefix closures -/

/-- The union of a finite list of top-free trees: the join of its elements and `⊥`. -/
noncomputable def unionTree (ts : List Tree) : Tree := ts.foldr join bot

/-- The addresses of a finite union. -/
@[simp] theorem mem_unionTree (ts : List Tree) (w : Word) :
    w ∈ (unionTree ts).constructorPaths ↔ ∃ t ∈ ts, w ∈ t.constructorPaths := by
  induction ts with
  | nil => simp [unionTree]
  | cons t ts ih =>
    simp only [unionTree, List.foldr_cons, join_constructorPaths, Set.mem_union, List.mem_cons,
      exists_eq_or_imp] at ih ⊢
    rw [ih]

theorem topFree_unionTree (ts : List Tree) : (unionTree ts).TopFree := by
  cases ts with
  | nil => exact topFree_bot
  | cons t ts => exact join_topFree _ _

/-- A top-free tree of a list lies below the union of the list. -/
theorem le_unionTree_of_mem {t : Tree} {ts : List Tree} (ht : t ∈ ts) (htf : t.TopFree) :
    t ≤ unionTree ts :=
  le_of_subset htf fun u hu => (mem_unionTree ts u).mpr ⟨t, ht, hu⟩

/-- The path to `w` lies below a finite union exactly when some tree of the union contains
`w`. -/
theorem path_le_unionTree_iff (w : Word) (ts : List Tree) :
    path w ≤ unionTree ts ↔ ∃ t ∈ ts, w ∈ t.constructorPaths := by
  rw [path_le_iff (topFree_unionTree ts), mem_unionTree]

/-- The least top-free tree containing a set of words: its addresses are their prefixes. -/
noncomputable def prefixTree (W : Set Word) : Tree :=
  ofConstructorPaths {u | ∃ w ∈ W, u <+: w} fun u r ⟨w, hw, h⟩ =>
    ⟨w, hw, (List.prefix_append u r).trans h⟩

/-- The addresses of a prefix closure. -/
@[simp] theorem mem_prefixTree (W : Set Word) (u : Word) :
    u ∈ (prefixTree W).constructorPaths ↔ ∃ w ∈ W, u <+: w := by
  exact Set.ext_iff.mp (ofConstructorPaths_constructorPaths _ _) u

@[simp] theorem topFree_prefixTree (W : Set Word) : (prefixTree W).TopFree :=
  ofConstructorPaths_topFree _ _

/-! ## Finite trees for the refuting values -/

/-- The tree with the spine words `1ⁱ` and the stubs `1ⁱ 0` for `i < n`. -/
def shapeTree (n : ℕ) : Tree := nestRight e n bot

/-- The addresses of `shapeTree n`. -/
theorem mem_shapeTree (n : ℕ) (w : Word) :
    w ∈ (shapeTree n).constructorPaths ↔ ∃ i < n, w = ones i ∨ w = stub i := by
  simp only [shapeTree, mem_constructorPaths_nestRight, mem_constructorPaths_e,
    not_mem_constructorPaths_bot, false_and, exists_false, or_false]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, v, rfl, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, [], rfl, rfl⟩

/-- The tree `shapeTree n` satisfies the loop `k ≤ f(e, k)`. -/
theorem shapeTree_le (n : ℕ) : shapeTree n ≤ f e (shapeTree n) := by
  exact nestRight_bot_le_f e n

/-- The tree with the spine words `1ⁱ` and the tooth words `1ⁱ 0 1ˣ` for `i < n`, `x ≤ n`. -/
def oneZeroTree (n : ℕ) : Tree := nestRight (path (ones n)) n bot

/-- The addresses of `oneZeroTree n`. -/
theorem mem_oneZeroTree (n : ℕ) (w : Word) :
    w ∈ (oneZeroTree n).constructorPaths ↔
      ∃ i < n, w = ones i ∨ ∃ x ≤ n, w = toothWord i x := by
  simp only [oneZeroTree, mem_constructorPaths_nestRight, mem_constructorPaths_path,
    prefix_ones_iff, not_mem_constructorPaths_bot, false_and, exists_false, or_false]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, v, ⟨x, hx, rfl⟩, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr ⟨x, hx, rfl⟩⟩
  · rintro ⟨i, hi, rfl | ⟨x, hx, rfl⟩⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, ones x, ⟨x, hx, rfl⟩, rfl⟩

/-- The tree `oneZeroTree n` satisfies the loop `k ≤ f(1ⁿ, k)`. -/
theorem oneZeroTree_le (n : ℕ) : oneZeroTree n ≤ f (path (ones n)) (oneZeroTree n) := by
  exact nestRight_bot_le_f (path (ones n)) n

/-- The path to `1ⁿ` satisfies the loop `k₀ ≤ f(⊥, k₀)`. -/
theorem path_ones_le (n : ℕ) : path (ones n) ≤ f bot (path (ones n)) := by
  apply path_le_of_mem
  cases n with
  | zero => exact nil_mem_constructorPaths_f _ _
  | succ n =>
    rw [ones_succ, one_cons_mem_constructorPaths_f, mem_constructorPaths_path]
    exact (ones_prefix_ones_iff (i := n) (j := n + 1)).mpr (by omega)

/-- The tree with the addresses `dropOnes w`. -/
noncomputable def dropTree (w : Word) : Tree := spineJoin (path w)

/-- The addresses of a drop tree. -/
@[simp] theorem mem_dropTree (w v : Word) :
    v ∈ (dropTree w).constructorPaths ↔ v ∈ dropOnes w := by
  simp [dropTree, dropOnes]

/-- The tree with the addresses `dropOnesStrict w`; it is `⊥` if `w` does not start with `1`. -/
noncomputable def strictDropTree (w : Word) : Tree := spineJoin ((path w).residual [1])

/-- The addresses of a strict drop tree. -/
@[simp] theorem mem_strictDropTree (w v : Word) :
    v ∈ (strictDropTree w).constructorPaths ↔ v ∈ dropOnesStrict w := by
  simp [strictDropTree, dropOnesStrict, ones_succ]

/-! ## Loops `t ≤ f(a, t)` -/

/-- If `t ≤ f(a, t)` for top-free `a` and `t`, every address of `t` is a spine word or a word
`1^j 0 u` with `u` an address of `a`. -/
theorem mem_of_le_f_self {a t : Tree} (h : t ≤ f a t) (ha : a.TopFree) (ht : t.TopFree)
    {w : Word} (hw : w ∈ t.constructorPaths) :
    IsOnes w ∨ ∃ j u, u ∈ a.constructorPaths ∧ w = ones j ++ 0 :: u := by
  have hsub := (le_iff_constructorPaths_subset ht ((topFree_f _ _).mpr ⟨ha, ht⟩)).mp h
  induction w with
  | nil => exact Or.inl isOnes_nil
  | cons i w ih =>
    obtain rfl | rfl := letter_eq_zero_or_eq_one i
    · exact Or.inr ⟨0, w, (zero_cons_mem_constructorPaths_f _ _ _).mp (hsub hw), rfl⟩
    · rcases ih ((one_cons_mem_constructorPaths_f _ _ _).mp (hsub hw)) with hw | ⟨j, u, hu, rfl⟩
      · exact Or.inl (isOnes_cons _ _ |>.mpr ⟨rfl, hw⟩)
      · exact Or.inr ⟨j + 1, u, hu, rfl⟩

/-- If `t ≤ f(a, t)` for top-free `a` and `t`, the residuals of `t` along its spine lie
below `t`. -/
theorem residual_ones_le_of_le_f_self {a t : Tree} (h : t ≤ f a t) (ha : a.TopFree)
    (ht : t.TopFree) (j : ℕ) : t.residual (ones j) ≤ t := by
  have hright := ((le_f_iff_residual (topFree_of_le_f h ha)).mp h).2
  induction j with
  | zero => simp [residual_nil ht]
  | succ j ih =>
    have hh := (residual_mono hright ht (ones j)).trans ih
    simpa [residual_residual, ones_succ] using hh

/-- If `t ≤ f(a, t)` for top-free `a` and `t`, the residual of `t` at `1^j 0 p` lies below
the residual of `a` at `p`. -/
theorem residual_ones_zero_le_of_le_f_self {a t : Tree} (h : t ≤ f a t) (ha : a.TopFree)
    (ht : t.TopFree) (j : ℕ) (p : Word) : t.residual (ones j ++ 0 :: p) ≤ a.residual p := by
  have hleft := ((le_f_iff_residual ht).mp h).1
  have hj := residual_ones_le_of_le_f_self h ha ht j
  have hh := (residual_mono hj ht [0]).trans hleft
  have hp := residual_mono hh ha p
  simpa [residual_residual, List.append_assoc] using hp

/-- If `t ≤ f(a, t)` for top-free `a` and `t`, every residual of `t` lies below a bound `U` of
`t` and of the residuals of `a`. -/
theorem residual_le_of_le_f_self {a t U : Tree} (h : t ≤ f a t) (ha : a.TopFree)
    (ht : t.TopFree) (htU : t ≤ U) (haU : ∀ q, a.residual q ≤ U) (p : Word) :
    t.residual p ≤ U := by
  by_cases hp : IsOnes p
  · obtain ⟨j, rfl⟩ := (isOnes_iff p).mp hp
    exact (residual_ones_le_of_le_f_self h ha ht j).trans htU
  · obtain ⟨j, q, rfl⟩ := (not_isOnes_iff p).mp hp
    exact (residual_ones_zero_le_of_le_f_self h ha ht j q).trans (haU q)

/-- If `t ≤ f(a, t)` for top-free `a` and `t`, an address `1ʲ 0 w` of `t` gives the address `w`
of `a`. -/
theorem mem_of_ones_append_zero_cons_mem {a t : Tree} (h : t ≤ f a t) (ha : a.TopFree)
    (ht : t.TopFree) (j : ℕ) {w : Word} (hw : ones j ++ 0 :: w ∈ t.constructorPaths) :
    w ∈ a.constructorPaths := by
  have hsub := (le_iff_constructorPaths_subset ht ((topFree_f _ _).mpr ⟨ha, ht⟩)).mp h
  induction j with
  | zero => exact hsub hw
  | succ j ih => exact ih (hsub hw)

/-! ## Selection contexts -/

/-- `select k a t = f(a 0, f(a 1, … f(a (k - 1), t)))`: the tree `a l` sits at `1ˡ 0` for
`l < k` and `t` sits at `1ᵏ`. -/
def select (k : ℕ) (a : ℕ → Tree) (t : Tree) : Tree :=
  (List.range k).foldr (fun l acc => f (a l) acc) t

/-- `g` at `1ˡ 0` for the selected `l < k`, and `z` at the other `1ˡ 0` and at `1ᵏ`. -/
def componentContext (k : ℕ) (z : Tree) (sel : ℕ → Bool) (g : Tree) : Tree :=
  select k (fun l => if sel l then g else z) z

/-- `f(z, g)` at `1ˡ 0` for the selected `l < k`, and `z` at the other `1ˡ 0` and at `1ᵏ`. -/
def tailContext (k : ℕ) (z : Tree) (sel : ℕ → Bool) (g : Tree) : Tree :=
  select k (fun l => if sel l then f z g else z) z

example (a : ℕ → Tree) (t : Tree) : select 2 a t = f (a 0) (f (a 1) t) := rfl

@[simp] theorem select_zero (a : ℕ → Tree) (t : Tree) : select 0 a t = t := rfl

@[simp] theorem select_succ (k : ℕ) (a : ℕ → Tree) (t : Tree) :
    select (k + 1) a t = f (a 0) (select k (fun l => a (l + 1)) t) := by
  simp [select, List.range_succ_eq_map, List.foldr_map]

/-- A selection of top-free trees is top-free. -/
theorem topFree_select {k : ℕ} {a : ℕ → Tree} {t : Tree} (ha : ∀ l, (a l).TopFree)
    (ht : t.TopFree) : (select k a t).TopFree := by
  induction k generalizing a with
  | zero => simpa using ht
  | succ k ih =>
    rw [select_succ]
    exact (topFree_f _ _).mpr ⟨ha 0, ih fun l => ha (l + 1)⟩

/-- A top-free tree lies below `select k a t` exactly when its residual at `1ˡ 0` lies below
`a l` for `l < k` and its residual at `1ᵏ` lies below `t`. -/
theorem le_select_iff {L t : Tree} {a : ℕ → Tree} (hL : L.TopFree) (k : ℕ) :
    L ≤ select k a t ↔ (∀ l < k, L.residual (ones l ++ [0]) ≤ a l) ∧ L.residual (ones k) ≤ t := by
  induction k generalizing L a with
  | zero => simp [residual_nil hL]
  | succ k ih =>
    rw [select_succ, le_f_iff_residual hL, ih (topFree_residual _ _)]
    simp only [residual_residual, List.singleton_append]
    constructor
    · rintro ⟨hzero, hrest, htail⟩
      refine ⟨?_, htail⟩
      intro l hl
      cases l with
      | zero => simpa using hzero
      | succ l => exact hrest l (by omega)
    · rintro ⟨hparts, htail⟩
      refine ⟨by simpa using hparts 0 (by omega), ?_, htail⟩
      intro l hl
      exact hparts (l + 1) (by omega)

/-- The support of `select k a t`: the spine words `1ˡ` for `l < k`, the words `1ˡ 0 u` with
`u` in the support of `a l` for `l < k`, and the words `1ᵏ u` with `u` in the support of `t`. -/
theorem mem_support_select (k : ℕ) (a : ℕ → Tree) (t : Tree) (w : Word) :
    w ∈ (select k a t).support ↔ (∃ l < k, w = ones l) ∨
      (∃ l < k, ∃ u ∈ (a l).support, w = ones l ++ 0 :: u) ∨ ∃ u ∈ t.support, w = ones k ++ u := by
  induction k generalizing a w with
  | zero => simp
  | succ k ih =>
    rcases w with _ | ⟨b, w⟩
    · exact iff_of_true (by simp) (Or.inl ⟨0, Nat.succ_pos k, rfl⟩)
    · obtain rfl | rfl := letter_eq_zero_or_eq_one b
      · rw [select_succ, zero_cons_mem_support_f]
        constructor
        · intro hw
          exact Or.inr (Or.inl ⟨0, Nat.succ_pos k, w, hw, rfl⟩)
        · rintro (⟨i, -, h⟩ | ⟨i, -, v, hv, h⟩ | ⟨v, -, h⟩)
          · exact absurd h (zero_cons_ne_ones w i)
          · obtain ⟨rfl, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
            exact hv
          · rw [ones_succ, List.cons_append, List.cons.injEq] at h
            exact absurd h.1 (by decide)
      · rw [select_succ, one_cons_mem_support_f, ih]
        constructor
        · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
          · exact Or.inl ⟨i + 1, by omega, rfl⟩
          · exact Or.inr (Or.inl ⟨i + 1, by omega, v, hv, rfl⟩)
          · exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
        · rintro (⟨i, hi, h⟩ | ⟨i, hi, v, hv, h⟩ | ⟨v, hv, h⟩)
          · obtain ⟨j, rfl, rfl⟩ := one_cons_eq_ones_iff.mp h
            exact Or.inl ⟨j, by omega, rfl⟩
          · obtain ⟨j, rfl, rfl⟩ := one_cons_eq_ones_append_iff.mp h
            exact Or.inr (Or.inl ⟨j, by omega, v, hv, rfl⟩)
          · rw [ones_succ, List.cons_append, List.cons.injEq] at h
            exact Or.inr (Or.inr ⟨v, hv, h.2⟩)

/-- The addresses of `select k a t` for top-free `a l` and `t`. -/
theorem mem_constructorPaths_select {k : ℕ} {a : ℕ → Tree} {t : Tree} (ha : ∀ l, (a l).TopFree)
    (ht : t.TopFree) (w : Word) :
    w ∈ (select k a t).constructorPaths ↔ (∃ l < k, w = ones l) ∨
      (∃ l < k, ∃ u ∈ (a l).constructorPaths, w = ones l ++ 0 :: u) ∨
        ∃ u ∈ t.constructorPaths, w = ones k ++ u := by
  have h := mem_support_select k a t w
  have hs : ∀ l, (a l).support = (a l).constructorPaths := fun l => support_eq (ha l)
  rw [support_eq (topFree_select ha ht), support_eq ht] at h
  simp only [hs] at h
  exact h

/-- The words `1ˡ 0 u` in the support of `select k a t` with `l < k` are those with `u` in the
support of `a l`. -/
theorem mem_support_select_component {k l : ℕ} (hl : l < k) {a : ℕ → Tree} {t : Tree}
    {u : Word} (h : ones l ++ 0 :: u ∈ (select k a t).support) : u ∈ (a l).support := by
  rcases (mem_support_select k a t _).mp h with ⟨l', -, he⟩ | ⟨l', -, u', hu', he⟩ |
      ⟨u', -, he⟩
  · have : IsOnes (ones l ++ 0 :: u) := he ▸ isOnes_ones l'
    exact absurd this (not_isOnes_ones_append_zero_cons l u)
  · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp he
    exact hu'
  · exact absurd he (ones_append_zero_cons_ne_ones_append hl u u')

/-- An address `1ˡ 0 w` of a top-free tree below `select k a ⊥` has `l < k` and `w` in
`a l`. -/
theorem mem_of_le_select_bot {L : Tree} {a : ℕ → Tree} {k l : ℕ} {w : Word}
    (hL : L.TopFree) (h : L ≤ select k a bot) (ha : (a l).TopFree)
    (hw : ones l ++ 0 :: w ∈ L.constructorPaths) : l < k ∧ w ∈ (a l).constructorPaths := by
  have hs := support_mono h (by rw [support_eq hL]; exact hw)
  rcases (mem_support_select k a bot _).mp hs with ⟨l', -, he⟩ | ⟨l', hl', u, hu, he⟩ |
      ⟨u, hu, -⟩
  · exact absurd (isOnes_ones l') (he ▸ not_isOnes_ones_append_zero_cons l w)
  · obtain ⟨hl, hw⟩ := ones_append_zero_cons_inj.mp he
    rw [hl, hw]
    exact ⟨hl', by rwa [support_eq (hl ▸ ha)] at hu⟩
  · simp at hu

end Tree

/-! ## Closure of the tree classes -/

section Closure

open UndeciSigma2.Tree

variable {c : TreeClass} {top : Bool}

/-- Residuals of finite top-free trees are finite. -/
theorem finite_residual {t : Tree} (ht : t.IsFinite) (htf : t.TopFree) (p : Word) :
    (t.residual p).IsFinite := by
  obtain ⟨n, hn⟩ := (finite_iff_bounded htf).mp ht
  apply finite_of_bounded (topFree_residual _ _) n
  intro u hu
  have hh := hn (p ++ u) ((mem_residual t p u).mp hu)
  simp only [List.length_append] at hh
  omega

/-- Residuals of regular top-free trees are regular. -/
theorem regular_residual {t : Tree} (ht : t.IsRegular) (htf : t.TopFree) (p : Word) :
    (t.residual p).IsRegular := by
  induction p generalizing t with
  | nil => simpa [residual_nil htf] using ht
  | cons i p ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · have he : bot.residual (i :: p) = bot :=
        topFree_ext (topFree_residual _ _) topFree_bot (by ext u; simp)
      rw [he]
      exact finite_bot.isRegular
    · exact False.elim (htf [] rfl)
    · have hr : (a i).IsRegular := ht.branch rfl i
      have hf := (topFree_node a).mp htf i
      have he : (node a).residual (i :: p) = (a i).residual p :=
        topFree_ext (topFree_residual _ _) (topFree_residual _ _) (by ext u; rfl)
      rw [he]
      exact ih hr hf

/-- Residuals of top-free trees stay in the domain. -/
theorem domain_residual {t : Tree} (h : Domain c top t) (ht : t.TopFree) (p : Word) :
    Domain c top (t.residual p) := by
  refine ⟨?_, Or.inr (topFree_residual _ _)⟩
  cases c with
  | finite => exact finite_residual h.1 ht p
  | regular => exact regular_residual h.1 ht p
  | arbitrary => trivial

/-- Finite unions stay in the domain. -/
theorem domain_unionTree {ts : List Tree} (h : ∀ t ∈ ts, Domain c top t) :
    Domain c top (unionTree ts) := by
  induction ts with
  | nil => exact domain_bot c top
  | cons t ts ih =>
    exact domain_join (h t (by simp)) (ih fun u hu => h u (by simp [hu]))

/-- Spine joins of finite top-free trees are finite. -/
theorem finite_spineJoin {t : Tree} (ht : t.IsFinite) (htf : t.TopFree) :
    (spineJoin t).IsFinite := by
  obtain ⟨n, hn⟩ := (finite_iff_bounded htf).mp ht
  apply finite_of_bounded (topFree_spineJoin _) n
  intro u hu
  obtain ⟨a, ha⟩ := (mem_spineJoin t u).mp hu
  have hh := hn (ones a ++ u) ha
  simp only [List.length_append, length_ones] at hh
  omega

/-- A regular tree has finitely many residuals along its spine, so its spine join is a finite
join of regular trees. -/
theorem regular_spineJoin {t : Tree} (ht : t.IsRegular) :
    (spineJoin t).IsRegular := by
  obtain ⟨g, rfl⟩ := ht
  let S : Set Tree := g.graph.unfold '' {q | ∃ n, g.graph.walk g.root (ones n) = some q}
  have hS : S.Finite := (Set.toFinite _).image _
  have hreg : (sjoin S).IsRegular := regular_sjoin hS (by
    rintro u ⟨q, _, rfl⟩
    exact ⟨⟨g.State, g.states, g.graph, q⟩, rfl⟩)
  have he : spineJoin g.toTree = sjoin S := by
    apply topFree_ext (topFree_spineJoin _) (topFree_sjoin _)
    ext u
    simp only [mem_spineJoin, sjoin_constructorPaths, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      change (g.graph.walk g.root (ones n ++ u)).map g.graph.label = some .f at hn
      rw [Graph.walk_append] at hn
      cases hq : g.graph.walk g.root (ones n) with
      | none => simp [hq] at hn
      | some q =>
        refine ⟨g.graph.unfold q, ⟨q, ⟨n, hq⟩, rfl⟩, ?_⟩
        change (g.graph.walk q u).map g.graph.label = some .f
        simpa only [hq, Option.bind_some] using hn
    · rintro ⟨v, ⟨q, ⟨n, hq⟩, rfl⟩, hu⟩
      refine ⟨n, ?_⟩
      change (g.graph.walk g.root (ones n ++ u)).map g.graph.label = some .f
      rw [Graph.walk_append, hq]
      exact hu
  rw [he]
  exact hreg

/-- Spine joins of top-free trees stay in the domain. -/
theorem domain_spineJoin {t : Tree} (h : Domain c top t) (ht : t.TopFree) :
    Domain c top (spineJoin t) := by
  refine ⟨?_, Or.inr (topFree_spineJoin _)⟩
  cases c with
  | finite => exact finite_spineJoin h.1 ht
  | regular => exact regular_spineJoin h.1
  | arbitrary => trivial

/-- Tails of top-free trees of the domain stay in the domain. -/
theorem domain_tails {t : Tree} (h : Domain c top t) (ht : t.TopFree) :
    Domain c top (tails t) :=
  domain_residual (domain_spineJoin h ht) (topFree_spineJoin t) [0]

/-- The prefix closure of a finite set of words is finite. -/
theorem finite_prefixTree {W : Set Word} (hW : W.Finite) : (prefixTree W).IsFinite := by
  obtain ⟨n, hn⟩ := (hW.image List.length).bddAbove
  apply finite_of_bounded (topFree_prefixTree _) (n + 1)
  intro u hu
  obtain ⟨w, hw, hup⟩ := (mem_prefixTree W u).mp hu
  have hwlen : w.length ≤ n := hn (Set.mem_image_of_mem _ hw)
  have hulen := hup.length_le
  omega

theorem finite_shapeTree (n : ℕ) : (shapeTree n).IsFinite := by
  induction n with
  | zero => exact finite_bot
  | succ n ih => exact finite_f finite_e ih

/-- A selection of finite trees is finite. -/
theorem finite_select {k : ℕ} {a : ℕ → Tree} {t : Tree} (ha : ∀ l, (a l).IsFinite)
    (ht : t.IsFinite) : (select k a t).IsFinite := by
  induction k generalizing a with
  | zero => simpa using ht
  | succ k ih =>
    rw [select_succ]
    exact finite_f (ha 0) (ih fun l => ha (l + 1))

theorem finite_oneZeroTree (n : ℕ) : (oneZeroTree n).IsFinite := by
  exact finite_nestRight (finite_path _) finite_bot n

theorem finite_dropTree (w : Word) : (dropTree w).IsFinite :=
  finite_spineJoin (finite_path w) (topFree_path w)

theorem finite_strictDropTree (w : Word) : (strictDropTree w).IsFinite :=
  finite_spineJoin (finite_residual (finite_path w) (topFree_path w) [1]) (topFree_residual _ _)

@[simp] theorem topFree_shapeTree (n : ℕ) : (shapeTree n).TopFree :=
  topFree_nestRight topFree_e topFree_bot n

@[simp] theorem topFree_oneZeroTree (n : ℕ) : (oneZeroTree n).TopFree :=
  topFree_nestRight (topFree_path _) topFree_bot n

@[simp] theorem topFree_dropTree (w : Word) : (dropTree w).TopFree := topFree_spineJoin _

@[simp] theorem topFree_strictDropTree (w : Word) : (strictDropTree w).TopFree :=
  topFree_spineJoin _

/-- Drop trees lie in every domain. -/
theorem domain_dropTree (w : Word) : Domain c top (dropTree w) :=
  domain_of_isFinite (finite_dropTree w) (topFree_dropTree w)

/-- Strict drop trees lie in every domain. -/
theorem domain_strictDropTree (w : Word) : Domain c top (strictDropTree w) :=
  domain_of_isFinite (finite_strictDropTree w) (topFree_strictDropTree w)

end Closure

end UndeciSigma2
