import UndeciSigma2.Clock.Semantics

/-! # Readings of the guards and of the atoms

**The guards.** If the ray `R`, the comb bound `K` and the sink `K₂` satisfy `R ≤ f(⊥, R)`,
`K ≤ f(R, K)` and `K₂ ≤ f(K, K₂)`, and every other existential lies below `K₂`, then all
twenty-one witnesses are top-free, the addresses of `R` are words of ones, those of `K` have at
most one zero and those of `K₂` at most two, and every residual of every witness lies below the
universe `R ⊔ K ⊔ K₂`. The universe is the value of the sink `z` in the refutations of the
one-seed and window clauses.

**The atoms.** Each seed atom has a reading, a set of words: if the atom holds and its witness
is top-free, the addresses of the seed lie in the reading; conversely, the path to a word of
the reading satisfies the atom. Each bound atom has a reading: if it holds, the
reading lies in the support of the bound; conversely it holds for the union of the trees making
up its reading, with the universe as sink. Each seed shape has a language: the seed lies in it,
and every word of the language is a seed for suitable finite auxiliaries.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

variable {c : TreeClass} {top : Bool}

/-! ## The guards -/

/-- The universe `R ⊔ K ⊔ K₂` of the three guards. -/
noncomputable def universeTree (x : ClockExistentials Tree) : Tree :=
  join (join x.ray x.combBound) x.sink

@[simp] theorem topFree_universeTree (x : ClockExistentials Tree) : (universeTree x).TopFree :=
  join_topFree _ _

/-- The universe lies in the domain. -/
theorem domain_universeTree {x : ClockExistentials Tree} (h : x.Forall (Domain c top)) :
    Domain c top (universeTree x) := by
  have hm : x.ray ∈ x.toList ∧ x.combBound ∈ x.toList ∧ x.sink ∈ x.toList := by
    simp [ClockExistentials.toList]
  exact domain_join (domain_join (h _ hm.1) (h _ hm.2.1)) (h _ hm.2.2)

/-- A witness usable in a refutation with sink value `z`: in the domain, top-free, and with
every residual below `z`. -/
def IsWitness (c : TreeClass) (top : Bool) (z t : Tree) : Prop :=
  Domain c top t ∧ t.TopFree ∧ ∀ p, t.residual p ≤ z

variable {x : ClockExistentials Tree}

/-- The ray is top-free. -/
theorem Guarded.topFree_ray (h : Guarded x) : x.ray.TopFree := topFree_of_le_f h.1 topFree_bot

/-- The comb bound is top-free. -/
theorem Guarded.topFree_combBound (h : Guarded x) : x.combBound.TopFree :=
  topFree_of_le_f h.2.1 h.topFree_ray

/-- The sink is top-free. -/
theorem Guarded.topFree_sink (h : Guarded x) : x.sink.TopFree :=
  topFree_of_le_f h.2.2.1 h.topFree_combBound

/-- The guards make every witness top-free. -/
theorem Guarded.topFree (h : Guarded x) : ∀ t ∈ x.toList, t.TopFree := by
  intro t ht
  simp only [ClockExistentials.toList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ht | rfl | rfl | rfl
  · exact h.topFree_sink.of_le (h.2.2.2 t ht)
  · exact h.topFree_ray
  · exact h.topFree_combBound
  · exact h.topFree_sink

/-- The addresses of the ray are words of ones. -/
theorem Guarded.isOnes_of_mem_ray (h : Guarded x) {w : Word} (hw : w ∈ x.ray.constructorPaths) :
    IsOnes w := by
  rcases mem_of_le_f_self h.1 topFree_bot h.topFree_ray hw with hw | ⟨j, u, hu, -⟩
  · exact hw
  · exact absurd hu (not_mem_constructorPaths_bot u)

/-- The addresses of the comb bound have at most one zero. -/
theorem Guarded.count_le_of_mem_combBound (h : Guarded x) {w : Word}
    (hw : w ∈ x.combBound.constructorPaths) : w.count 0 ≤ 1 := by
  rcases mem_of_le_f_self h.2.1 h.topFree_ray h.topFree_combBound hw with hw | ⟨j, u, hu, rfl⟩
  · rw [count_zero_eq_zero_of_isOnes hw]
    omega
  · rw [count_zero_ones_append_zero_cons, count_zero_eq_zero_of_isOnes (h.isOnes_of_mem_ray hu)]

/-- The addresses of the sink have at most two zeros. -/
theorem Guarded.count_le_of_mem_sink (h : Guarded x) {w : Word}
    (hw : w ∈ x.sink.constructorPaths) : w.count 0 ≤ 2 := by
  rcases mem_of_le_f_self h.2.2.1 h.topFree_combBound h.topFree_sink hw with hw | ⟨j, u, hu, rfl⟩
  · rw [count_zero_eq_zero_of_isOnes hw]
    omega
  · rw [count_zero_ones_append_zero_cons]
    have := h.count_le_of_mem_combBound hu
    omega

/-- The addresses of the sink, and hence of every witness, have at most two zeros. -/
theorem Guarded.count_le_of_mem (h : Guarded x) {t : Tree} (ht : t ∈ x.toList) {w : Word}
    (hw : w ∈ t.constructorPaths) : w.count 0 ≤ 2 := by
  simp only [ClockExistentials.toList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ht | rfl | rfl | rfl
  · exact h.count_le_of_mem_sink ((le_iff_constructorPaths_subset
      (h.topFree_sink.of_le (h.2.2.2 t ht)) h.topFree_sink).mp (h.2.2.2 t ht) hw)
  · rw [count_zero_eq_zero_of_isOnes (h.isOnes_of_mem_ray hw)]
    omega
  · have := h.count_le_of_mem_combBound hw
    omega
  · exact h.count_le_of_mem_sink hw

/-- Every residual of every witness lies below the universe. -/
theorem Guarded.residual_le_universe (h : Guarded x) {t : Tree} (ht : t ∈ x.toList) (p : Word) :
    t.residual p ≤ universeTree x := by
  have hR := h.topFree_ray
  have hK := h.topFree_combBound
  have hK₂ := h.topFree_sink
  have hRU : x.ray ≤ universeTree x :=
    (le_join_left hR).trans (le_join_left (join_topFree _ _))
  have hKU : x.combBound ≤ universeTree x :=
    (le_join_right hK).trans (le_join_left (join_topFree _ _))
  have hK₂U : x.sink ≤ universeTree x := le_join_right hK₂
  have hR' : ∀ q, x.ray.residual q ≤ universeTree x :=
    residual_le_of_le_f_self h.1 topFree_bot hR hRU fun q => residual_bot_le q _
  have hK' : ∀ q, x.combBound.residual q ≤ universeTree x :=
    residual_le_of_le_f_self h.2.1 hR hK hKU hR'
  have hK₂' : ∀ q, x.sink.residual q ≤ universeTree x :=
    residual_le_of_le_f_self h.2.2.1 hK hK₂ hK₂U hK'
  simp only [ClockExistentials.toList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ht | rfl | rfl | rfl
  · exact (residual_mono (h.2.2.2 t ht) hK₂ p).trans (hK₂' p)
  · exact hR' p
  · exact hK' p
  · exact hK₂' p

/-- The witnesses of guarded trees of the domain are usable in refutations with the universe as
sink value. -/
theorem Guarded.isWitness (h : Guarded x) (hd : x.Forall (Domain c top)) {t : Tree}
    (ht : t ∈ x.toList) : IsWitness c top (universeTree x) t :=
  ⟨hd t ht, h.topFree t ht, h.residual_le_universe ht⟩

/-- A family of thirteen values satisfies a property when each value does. -/
theorem ClockUniversals.forall_of_each {α : Type*} {p : α → Prop} {v : ClockUniversals α}
    (h₁ : p v.y₁) (h₂ : p v.y₂) (h₃ : p v.y₃) (h₄ : p v.g₁) (h₅ : p v.g₂) (h₆ : p v.g₃)
    (h₇ : p v.k) (h₈ : p v.k₀) (h₉ : p v.d₁) (h₁₀ : p v.d₂) (h₁₁ : p v.e₂) (h₁₂ : p v.e₃)
    (h₁₃ : p v.z) : v.Forall p := by
  intro i
  fin_cases i <;> assumption

/-! ## Seed atoms -/

/-- The reading of a seed atom: the set containing the addresses of every seed satisfying the
atom, for a top-free witness (`SeedAtom.subset_reading`). -/
def SeedAtom.reading : SeedAtom Tree → Set Word
  | .le X => X.constructorPaths
  | .rightLe X => {u | 1 :: u ∈ X.constructorPaths}
  | .component L l => {u | ones l ++ 0 :: u ∈ L.constructorPaths}
  | .componentRight L l => {u | ones l ++ 0 :: 1 :: u ∈ L.constructorPaths}

/-- A seed below a top-free witness is top-free. -/
theorem SeedAtom.topFree_of_holds {a : SeedAtom Tree} {y : Tree} (hX : a.witness.TopFree)
    (h : a.Holds y) : y.TopFree := by
  cases a with
  | le X => exact TopFree.of_le hX h
  | rightLe X => exact ((topFree_f _ _).mp (TopFree.of_le hX h)).2
  | component L l => exact topFree_of_topFree_pack (TopFree.of_le hX h)
  | componentRight L l =>
    exact ((topFree_f _ _).mp (topFree_of_topFree_pack (TopFree.of_le hX h))).2

/-- The addresses of a seed below a top-free witness lie in the reading. -/
theorem SeedAtom.subset_reading {a : SeedAtom Tree} {y : Tree} (hX : a.witness.TopFree)
    (h : a.Holds y) : y.constructorPaths ⊆ a.reading := by
  have hy := SeedAtom.topFree_of_holds hX h
  have hfy : (f bot y).TopFree := (topFree_f _ _).mpr ⟨topFree_bot, hy⟩
  intro u hu
  cases a with
  | le X => exact (le_iff_constructorPaths_subset hy hX).mp h hu
  | rightLe X =>
    exact (le_iff_constructorPaths_subset hfy hX).mp h
      ((one_cons_mem_constructorPaths_f _ _ _).mpr hu)
  | component L l => exact mem_of_pack_le hy hX h hu
  | componentRight L l =>
    exact mem_of_pack_le hfy hX h ((one_cons_mem_constructorPaths_f _ _ _).mpr hu)

/-- A path is a seed exactly when its end lies in the reading. -/
theorem SeedAtom.holds_path_iff {a : SeedAtom Tree} (hX : a.witness.TopFree) (w : Word) :
    a.Holds (path w) ↔ w ∈ a.reading := by
  refine ⟨fun h => SeedAtom.subset_reading hX h ((mem_constructorPaths_path w w).mpr
    List.prefix_rfl), fun hw => ?_⟩
  cases a with
  | le X => exact path_le_of_mem hw
  | rightLe X =>
    show f bot (path w) ≤ X
    rw [f_bot_path]
    exact path_le_of_mem hw
  | component L l => exact pack_path_le hX hw
  | componentRight L l =>
    show pack l (f bot (path w)) ≤ L
    rw [f_bot_path]
    exact pack_path_le hX hw

/-! ## Bound atoms -/

/-- The reading of a bound atom: the words that the bound must contain. -/
def BoundAtom.reading : BoundAtom Tree → Set Word
  | .le X => X.constructorPaths
  | .rightLe X => {u | 1 :: u ∈ X.constructorPaths}
  | .components L m sel => {u | ∃ l < m, sel l = true ∧ ones l ++ 0 :: u ∈ L.constructorPaths}
  | .tails L m sel => {u | ∃ l < m, sel l = true ∧ ones l ++ 0 :: 1 :: u ∈ L.constructorPaths}

/-- The trees whose union is the reading of a bound atom: the witness, its right child, or the
selected components or their right children. -/
noncomputable def BoundAtom.trees : BoundAtom Tree → List Tree
  | .le X => [X]
  | .rightLe X => [X.residual [1]]
  | .components L m sel => ((List.range m).filter sel).map fun l => L.residual (ones l ++ [0])
  | .tails L m sel => ((List.range m).filter sel).map fun l => L.residual (ones l ++ [0, 1])

/-- If a bound atom holds, its reading lies in the support of the bound, whatever the sink. -/
theorem BoundAtom.reading_subset_support {b : BoundAtom Tree} {z g : Tree} (h : b.Holds z g) :
    b.reading ⊆ g.support := by
  cases b with
  | le X => exact (constructorPaths_subset_support X).trans (support_mono h)
  | rightLe X =>
    intro u hu
    exact (one_cons_mem_support_f z g u).mp (support_mono h (constructorPaths_subset_support X hu))
  | components L m sel =>
    rintro u ⟨l, hl, hsel, hu⟩
    have := mem_support_select_component hl (support_mono h (constructorPaths_subset_support L hu))
    simpa [hsel] using this
  | tails L m sel =>
    rintro u ⟨l, hl, hsel, hu⟩
    have := mem_support_select_component hl (support_mono h (constructorPaths_subset_support L hu))
    simp only [hsel, ite_true] at this
    exact (one_cons_mem_support_f z g u).mp this

/-- The reading of a bound atom is the union of the addresses of its trees. -/
theorem BoundAtom.mem_reading_iff {b : BoundAtom Tree} (w : Word) :
    w ∈ b.reading ↔ ∃ t ∈ b.trees, w ∈ t.constructorPaths := by
  cases b with
  | le X => simp [BoundAtom.reading, BoundAtom.trees]
  | rightLe X => simp [BoundAtom.reading, BoundAtom.trees]
  | components L m sel => simp [BoundAtom.reading, BoundAtom.trees, and_assoc]
  | tails L m sel => simp [BoundAtom.reading, BoundAtom.trees, and_assoc]

/-- A bound atom holds for every bound containing its trees, if every residual of the witness
lies below the sink. -/
theorem BoundAtom.holds_unionTree {b : BoundAtom Tree} {z : Tree} {ts : List Tree}
    (hX : b.witness.TopFree) (hres : ∀ p, b.witness.residual p ≤ z)
    (hts : ∀ t ∈ b.trees, t ∈ ts) : b.Holds z (unionTree ts) := by
  have hmem : ∀ t ∈ b.trees, t.TopFree → t ≤ unionTree ts := fun t ht htf =>
    le_unionTree_of_mem (hts t ht) htf
  cases b with
  | le X => exact hmem X (by simp [BoundAtom.trees]) hX
  | rightLe X =>
    simp only [BoundAtom.witness] at hX hres
    show X ≤ f z (unionTree ts)
    rw [le_f_iff_residual hX]
    exact ⟨hres [0], hmem _ (by simp [BoundAtom.trees]) (topFree_residual _ _)⟩
  | components L m sel =>
    simp only [BoundAtom.witness] at hX hres
    show L ≤ componentContext m z sel (unionTree ts)
    rw [componentContext, le_select_iff hX]
    refine ⟨fun l hl => ?_, hres _⟩
    by_cases hs : sel l = true
    · have ht : L.residual (ones l ++ [0]) ∈ (BoundAtom.components L m sel).trees := by
        simp only [BoundAtom.trees, List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨l, ⟨hl, hs⟩, rfl⟩
      simp only [hs, ite_true]
      exact hmem _ ht (topFree_residual _ _)
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact hres _
  | tails L m sel =>
    simp only [BoundAtom.witness] at hX hres
    show L ≤ tailContext m z sel (unionTree ts)
    rw [tailContext, le_select_iff hX]
    refine ⟨fun l hl => ?_, hres _⟩
    by_cases hs : sel l = true
    · have ht : L.residual (ones l ++ [0] ++ [1]) ∈ (BoundAtom.tails L m sel).trees := by
        simp only [BoundAtom.trees, List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨l, ⟨hl, hs⟩, by simp [List.append_assoc]⟩
      simp only [hs, ite_true]
      rw [le_f_iff_residual (topFree_residual _ _), residual_residual, residual_residual]
      exact ⟨hres _, hmem _ ht (topFree_residual _ _)⟩
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact hres _

/-- The trees of a bound atom with a top-free witness of the domain lie in the domain. -/
theorem BoundAtom.domain_of_mem_trees {b : BoundAtom Tree} (hX : Domain c top b.witness)
    (hXt : b.witness.TopFree) {t : Tree} (ht : t ∈ b.trees) : Domain c top t := by
  cases b with
  | le X =>
    simp only [BoundAtom.trees, List.mem_singleton] at ht
    subst ht
    exact hX
  | rightLe X =>
    simp only [BoundAtom.trees, List.mem_singleton] at ht
    subst ht
    exact domain_residual hX hXt _
  | components L m sel =>
    simp only [BoundAtom.trees, List.mem_map] at ht
    obtain ⟨l, -, rfl⟩ := ht
    exact domain_residual hX hXt _
  | tails L m sel =>
    simp only [BoundAtom.trees, List.mem_map] at ht
    obtain ⟨l, -, rfl⟩ := ht
    exact domain_residual hX hXt _

/-! ## Seed shapes -/

/-- The language of a seed shape: all words, spine words and stubs, or words with at most one
zero. -/
def SeedShape.language : SeedShape → Set Word
  | .any => Set.univ
  | .spineOrStub => {w | IsOnes w ∨ ∃ j, w = stub j}
  | .atMostOneZero => {w | IsOnes w ∨ ∃ j i, w = toothWord j i}

/-- If `k ≤ f(e, k)`, the support of `k` consists of spine words and stubs. -/
theorem mem_support_of_le_f_e {k : Tree} (h : k ≤ f e k) :
    ∀ u ∈ k.support, IsOnes u ∨ ∃ j, u = stub j := by
  intro u
  induction u with
  | nil => exact fun _ => Or.inl isOnes_nil
  | cons i u ih =>
    intro hu
    obtain rfl | rfl := letter_eq_zero_or_eq_one i
    · have hu' := mem_support_of_zero_cons_mem h hu
      rw [support_eq topFree_e, mem_constructorPaths_e] at hu'
      subst hu'
      exact Or.inr ⟨0, rfl⟩
    · rcases ih (mem_support_of_one_cons_mem h hu) with hu' | ⟨j, rfl⟩
      · exact Or.inl ((isOnes_cons _ _).mpr ⟨rfl, hu'⟩)
      · exact Or.inr ⟨j + 1, rfl⟩

/-- If `k₀ ≤ f(⊥, k₀)`, the support of `k₀` consists of spine words. -/
theorem isOnes_of_mem_support_of_le_f_bot {k₀ : Tree} (h : k₀ ≤ f bot k₀) :
    ∀ u ∈ k₀.support, IsOnes u := by
  intro u
  induction u with
  | nil => exact fun _ => isOnes_nil
  | cons i u ih =>
    intro hu
    obtain rfl | rfl := letter_eq_zero_or_eq_one i
    · have hu' := mem_support_of_zero_cons_mem h hu
      simp at hu'
    · exact (isOnes_cons _ _).mpr ⟨rfl, ih (mem_support_of_one_cons_mem h hu)⟩

/-- If `k ≤ f(k₀, k)` and `k₀ ≤ f(⊥, k₀)`, the support of `k` consists of spine words and tooth
words. -/
theorem mem_support_of_le_f_of_le_f_bot {k k₀ : Tree} (h : k ≤ f k₀ k) (h₀ : k₀ ≤ f bot k₀) :
    ∀ u ∈ k.support, IsOnes u ∨ ∃ j i, u = toothWord j i := by
  intro u
  induction u with
  | nil => exact fun _ => Or.inl isOnes_nil
  | cons a u ih =>
    intro hu
    obtain rfl | rfl := letter_eq_zero_or_eq_one a
    · obtain ⟨i, rfl⟩ := (isOnes_iff u).mp
        (isOnes_of_mem_support_of_le_f_bot h₀ u (mem_support_of_zero_cons_mem h hu))
      exact Or.inr ⟨0, i, rfl⟩
    · rcases ih (mem_support_of_one_cons_mem h hu) with hu' | ⟨j, i, rfl⟩
      · exact Or.inl ((isOnes_cons _ _).mpr ⟨rfl, hu'⟩)
      · exact Or.inr ⟨j + 1, i, rfl⟩

/-- The addresses of a seed satisfying a shape lie in its language, whatever the
auxiliaries. -/
theorem SeedShape.subset_language {sh : SeedShape} {y k k₀ : Tree} (h : sh.Holds y k k₀) :
    y.constructorPaths ⊆ sh.language := by
  intro u hu
  have hu' : u ∈ y.support := constructorPaths_subset_support y hu
  cases sh with
  | any => trivial
  | spineOrStub => exact mem_support_of_le_f_e h.2 u (support_mono h.1 hu')
  | atMostOneZero => exact mem_support_of_le_f_of_le_f_bot h.2.1 h.2.2 u (support_mono h.1 hu')

/-- Auxiliaries `(k, k₀)` making the path to a word of the language satisfy the shape. -/
noncomputable def SeedShape.auxiliaries (w : Word) : SeedShape → Tree × Tree
  | .any => (bot, bot)
  | .spineOrStub => (shapeTree (w.length + 1), bot)
  | .atMostOneZero => (oneZeroTree (w.length + 1), path (ones (w.length + 1)))

/-- The path to a word of the language satisfies the shape with its auxiliaries. -/
theorem SeedShape.holds_auxiliaries {sh : SeedShape} {w : Word} (hw : w ∈ sh.language) :
    sh.Holds (path w) (sh.auxiliaries w).1 (sh.auxiliaries w).2 := by
  cases sh with
  | any => trivial
  | spineOrStub =>
    show path w ≤ shapeTree (w.length + 1) ∧
      shapeTree (w.length + 1) ≤ f e (shapeTree (w.length + 1))
    refine ⟨path_le_of_mem ((mem_shapeTree _ w).mpr ?_), shapeTree_le _⟩
    rcases hw with hw | ⟨j, rfl⟩
    · obtain ⟨i, rfl⟩ := (isOnes_iff w).mp hw
      exact ⟨i, by simp, Or.inl rfl⟩
    · exact ⟨j, by simp [stub], Or.inr rfl⟩
  | atMostOneZero =>
    show path w ≤ oneZeroTree (w.length + 1) ∧
      oneZeroTree (w.length + 1) ≤ f (path (ones (w.length + 1))) (oneZeroTree (w.length + 1)) ∧
      path (ones (w.length + 1)) ≤ f bot (path (ones (w.length + 1)))
    refine ⟨path_le_of_mem ((mem_oneZeroTree _ w).mpr ?_), oneZeroTree_le _, path_ones_le _⟩
    rcases hw with hw | ⟨j, i, rfl⟩
    · obtain ⟨i, rfl⟩ := (isOnes_iff w).mp hw
      exact ⟨i, by simp, Or.inl rfl⟩
    · exact ⟨j, by simp; omega, Or.inr ⟨i, by simp; omega, rfl⟩⟩

/-- The auxiliaries of a shape are finite and top-free, hence in every domain. -/
theorem SeedShape.finite_auxiliaries (sh : SeedShape) (w : Word) :
    (sh.auxiliaries w).1.IsFinite ∧ (sh.auxiliaries w).1.TopFree ∧
      (sh.auxiliaries w).2.IsFinite ∧ (sh.auxiliaries w).2.TopFree := by
  cases sh with
  | any => exact ⟨finite_bot, topFree_bot, finite_bot, topFree_bot⟩
  | spineOrStub => exact ⟨finite_shapeTree _, topFree_shapeTree _, finite_bot, topFree_bot⟩
  | atMostOneZero =>
    exact ⟨finite_oneZeroTree _, topFree_oneZeroTree _, finite_path _, topFree_path _⟩

/-! ## Blocks -/

/-- The drop block makes the words obtained from the addresses of `y` by removing leading ones
lie in the support of every bound in the list. -/
theorem DropBlock.dropOnes_subset {z y d : Tree} {gs : List Tree} (h : DropBlock z y d gs)
    {w : Word} (hw : w ∈ y.constructorPaths) {g : Tree} (hg : g ∈ gs) :
    dropOnes w ⊆ g.support := by
  rintro v ⟨a, hv⟩
  have h₁ : ones a ++ v ∈ d.support :=
    support_mono h.1 (constructorPaths_subset_support y (mem_constructorPaths_of_prefix hv hw))
  exact support_mono (h.2.2 g hg) (mem_support_of_ones_append_mem h.2.1 a h₁)

/-- The strict drop block makes the words obtained from the addresses of `y` by removing at
least one leading one lie in the support of every bound in the list. -/
theorem StrictDropBlock.dropOnesStrict_subset {z y e : Tree} {gs : List Tree}
    (h : StrictDropBlock z y e gs) {w : Word} (hw : w ∈ y.constructorPaths) {g : Tree}
    (hg : g ∈ gs) : dropOnesStrict w ⊆ g.support := by
  rintro v ⟨a, hv⟩
  have h₁ : 1 :: (ones a ++ v) ∈ (f z e).support :=
    support_mono h.1 (constructorPaths_subset_support y (mem_constructorPaths_of_prefix hv hw))
  exact support_mono (h.2.2 g hg)
    (mem_support_of_ones_append_mem h.2.1 a ((one_cons_mem_support_f z e _).mp h₁))

/-- The drop block holds for the path to an address `w` of the right child of `X`, with the
drop tree of `w`, when every residual of `X` lies below the sink. -/
theorem dropBlock_path {X z : Tree} {w : Word} (hres : ∀ p, X.residual p ≤ z)
    (hw : 1 :: w ∈ X.constructorPaths) {gs : List Tree} (hgs : ∀ g ∈ gs, dropTree w ≤ g) :
    DropBlock z (path w) (dropTree w) gs := by
  refine ⟨path_le_of_mem ((mem_dropTree w w).mpr ⟨0, List.prefix_rfl⟩), ?_, hgs⟩
  rw [le_f_iff_residual (topFree_dropTree w)]
  constructor
  · apply le_of_forall_mem_residual (topFree_residual _ _) hres
    intro u hu
    rw [Tree.mem_residual, mem_dropTree] at hu
    obtain ⟨a, ha⟩ := hu
    refine ⟨ones (a + 1) ++ [0], mem_constructorPaths_of_prefix ?_ hw⟩
    have he : ones (a + 1) ++ [0] ++ u = 1 :: (ones a ++ ([0] ++ u)) := by
      simp [List.append_assoc]
    rw [he]
    exact List.cons_prefix_cons.mpr ⟨rfl, ha⟩
  · apply le_of_subset (topFree_residual _ _)
    intro u hu
    rw [Tree.mem_residual, mem_dropTree] at hu
    rw [mem_dropTree]
    obtain ⟨a, ha⟩ := hu
    exact ⟨a + 1, by rwa [ones_succ', List.append_assoc]⟩

/-- The strict drop block holds for the path to an address `w` of the right child of `X`, with
the strict drop tree of `w`, when every residual of `X` lies below the sink. -/
theorem strictDropBlock_path {X z : Tree} {w : Word} (hres : ∀ p, X.residual p ≤ z)
    (hw : 1 :: w ∈ X.constructorPaths) {gs : List Tree} (hgs : ∀ g ∈ gs, strictDropTree w ≤ g) :
    StrictDropBlock z (path w) (strictDropTree w) gs := by
  refine ⟨?_, ?_, hgs⟩
  · rw [le_f_iff_residual (topFree_path w)]
    constructor
    · apply le_of_forall_mem_residual (topFree_residual _ _) hres
      intro u hu
      rw [Tree.mem_residual, mem_constructorPaths_path] at hu
      exact ⟨[1, 0], mem_constructorPaths_of_prefix (List.cons_prefix_cons.mpr ⟨rfl, hu⟩) hw⟩
    · apply le_of_subset (topFree_residual _ _)
      intro u hu
      rw [Tree.mem_residual, mem_constructorPaths_path] at hu
      rw [mem_strictDropTree]
      exact ⟨0, hu⟩
  · rw [le_f_iff_residual (topFree_strictDropTree w)]
    constructor
    · apply le_of_forall_mem_residual (topFree_residual _ _) hres
      intro u hu
      rw [Tree.mem_residual, mem_strictDropTree] at hu
      obtain ⟨a, ha⟩ := hu
      refine ⟨ones (a + 2) ++ [0], mem_constructorPaths_of_prefix ?_ hw⟩
      have he : ones (a + 2) ++ [0] ++ u = 1 :: (ones (a + 1) ++ ([0] ++ u)) := by
        simp [List.append_assoc]
      rw [he]
      exact List.cons_prefix_cons.mpr ⟨rfl, ha⟩
    · apply le_of_subset (topFree_residual _ _)
      intro u hu
      rw [Tree.mem_residual, mem_strictDropTree] at hu
      rw [mem_strictDropTree]
      obtain ⟨a, ha⟩ := hu
      exact ⟨a + 1, by rwa [ones_succ' (a + 1), List.append_assoc]⟩

end Clock

end UndeciSigma2
