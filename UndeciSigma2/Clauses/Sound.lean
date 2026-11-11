import UndeciSigma2.Clauses.Specs

/-! # Sound direction of the clauses

If a clause holds for all admissible values of the universal variables, its
specification holds. If the specification fails, the proofs refute the clause by
explicit regular top-free values of the universal variables: paths of teeth and stubs
as seeds, cocones of the same words as bounds, right nests for the alignment blocks,
and left paths with their right spines for the comparison blocks. Several of these
values, such as the cocones and the right spines, are infinite: they exist in the
regular and arbitrary domains but not in the finite one.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Sentence

variable {c : TreeClass} {top : Bool} {C : Fin 2 → Tree} {U : Tree}

/-- Values of the universal variables refuting a clause, used by all sound proofs. The
two alignment pairs are equal: `d = nestRight full j bot`, the words with fewer than `j`
leading ones, and `p = nestRight bot (j + 1) full`, the words `1ⁱ` for `i ≤ j` and all
words below `1^(j+1)`. For the comparison block with offset `δ` and a seed tooth of
depth `x`: `k₀ = path (zeros x)`, `kd = path (zeros (x - δ))` (or `⊥` if `x < δ`),
`k = rightSpine k₀` and `kp = rightSpine kd`. -/
noncomputable def refutingValues (j δ x : ℕ) (y₁ y₂ y₃ g₁ g₂ g₃ : Tree) : Universals Tree where
  y₁ := y₁
  y₂ := y₂
  y₃ := y₃
  g₁ := g₁
  g₂ := g₂
  g₃ := g₃
  k := rightSpine (path (zeros x))
  k₀ := path (zeros x)
  kd := if δ ≤ x then path (zeros (x - δ)) else bot
  kp := rightSpine (if δ ≤ x then path (zeros (x - δ)) else bot)
  d₁ := nestRight full j bot
  p₁ := nestRight bot (j + 1) full
  d₂ := nestRight full j bot
  p₂ := nestRight bot (j + 1) full

/-- The refuting values are admissible when their seeds and bounds are regular and top-free. -/
theorem refutingValues_admissible (hc : c ≠ .finite) (j δ x : ℕ) {y₁ y₂ y₃ g₁ g₂ g₃ : Tree}
    (h : ∀ t ∈ [y₁, y₂, y₃, g₁, g₂, g₃], t.IsRegular ∧ t.TopFree) :
    (refutingValues j δ x y₁ y₂ y₃ g₁ g₂ g₃).Forall (Admissible c top) := by
  have hd : ∀ {t : Tree}, t.IsRegular → t.TopFree → Admissible c top t :=
    fun hr ht => ⟨domain_of_isRegular hc hr ht, ht⟩
  have hk₀ : (path (zeros x)).IsRegular := (finite_path _).isRegular
  have hkd : (if δ ≤ x then path (zeros (x - δ)) else bot).IsRegular ∧
      (if δ ≤ x then path (zeros (x - δ)) else bot).TopFree := by
    split
    · exact ⟨(finite_path _).isRegular, topFree_path _⟩
    · exact ⟨regular_bot, topFree_bot⟩
  have hd₁ := regular_nestRight regular_full regular_bot j
  have hp₁ := regular_nestRight regular_bot regular_full (j + 1)
  have ht₁ := topFree_nestRight topFree_full topFree_bot j
  have ht₂ := topFree_nestRight topFree_bot topFree_full (j + 1)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨hd h₁.1 h₁.2, hd h₂.1 h₂.2, hd h₃.1 h₃.2, hd h₄.1 h₄.2, hd h₅.1 h₅.2, hd h₆.1 h₆.2,
    hd (regular_rightSpine hk₀) (topFree_rightSpine (topFree_path _)), hd hk₀ (topFree_path _),
    hd hkd.1 hkd.2, hd (regular_rightSpine hkd.1) (topFree_rightSpine hkd.2),
    hd hd₁ ht₁, hd hp₁ ht₂, hd hd₁ ht₁, hd hp₁ ht₂⟩

/-- The refuting values with paths as seeds and cocones as bounds are admissible. -/
theorem refutingValues_path_cocone_admissible (hc : c ≠ .finite) (j δ x : ℕ)
    (w₁ w₂ w₃ u₁ u₂ u₃ : Word) :
    (refutingValues j δ x (path w₁) (path w₂) (path w₃) (cocone u₁) (cocone u₂)
      (cocone u₃)).Forall (Admissible c top) := by
  apply refutingValues_admissible hc
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro t (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact ⟨(finite_path _).isRegular, topFree_path _⟩
    | exact ⟨regular_cocone _, topFree_cocone _⟩

/-! ## Addresses used by the refuting values -/

private theorem zeros_prefix_zeros_iff_le {x y : ℕ} : zeros x <+: zeros y ↔ x ≤ y := by
  constructor
  · intro h
    simpa using h.length_le
  · intro h
    exact ⟨zeros (y - x), by rw [← zeros_add, Nat.add_sub_cancel' h]⟩

/-- The spine word `1^(j+1)` is not a prefix of a word with a zero after `1ʲ`. -/
private theorem not_ones_succ_prefix_ones_append_zero (j : ℕ) (v : Word) :
    ¬ones (j + 1) <+: ones j ++ 0 :: v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ones_succ (j + 1), ones_succ j, List.cons_append, List.cons_prefix_cons]
    exact fun h => ih h.2

private theorem not_ones_succ_prefix_tooth (j x : ℕ) : ¬ones (j + 1) <+: tooth j x :=
  not_ones_succ_prefix_ones_append_zero j (zeros x)

private theorem ones_prefix_tooth (j x : ℕ) : ones j <+: tooth j x :=
  List.prefix_append _ _

/-- Prepending a one to both words preserves the prefix order. -/
private theorem one_cons_prefix {v w : Word} (h : v <+: w) : (1 : Fin 2) :: v <+: 1 :: w :=
  List.cons_prefix_cons.mpr ⟨rfl, h⟩

private theorem ones_succ_prefix_one_cons {j : ℕ} {w : Word} (h : ones j <+: w) :
    ones (j + 1) <+: 1 :: w := by
  rw [ones_succ]
  exact one_cons_prefix h

private theorem path_tooth_le_cocone_tooth_iff (j x x' : ℕ) :
    path (tooth j x) ≤ cocone (tooth j x') ↔ x < x' := by
  rw [path_le_cocone_iff, tooth, tooth, List.prefix_append_right_inj, List.cons_prefix_cons,
    zeros_prefix_zeros_iff_le]
  simp

/-- A tooth of a right spine is a tooth of its left children. -/
private theorem tooth_mem_rightSpine_iff (a : Tree) (j x : ℕ) :
    tooth j x ∈ (rightSpine a).constructorPaths ↔ zeros x ∈ a.constructorPaths := by
  induction j with
  | zero =>
    rw [rightSpine_eq, tooth_zero_left]
    exact zero_cons_mem_constructorPaths_f _ _ _
  | succ j ih =>
    rw [rightSpine_eq, tooth_succ_left, one_cons_mem_constructorPaths_f]
    exact ih

private theorem zeros_mem_leftSpine (b : Tree) (x : ℕ) :
    zeros x ∈ (leftSpine b).constructorPaths := by
  induction x with
  | zero =>
    rw [leftSpine_eq]
    exact nil_mem_constructorPaths_f _ _
  | succ x ih =>
    rw [leftSpine_eq, zeros_succ, zero_cons_mem_constructorPaths_f]
    exact ih

private theorem tooth_mem_combUniverse (j x : ℕ) :
    tooth j x ∈ combUniverse.constructorPaths :=
  (tooth_mem_rightSpine_iff _ j x).mpr (zeros_mem_leftSpine _ x)

private theorem tooth_not_mem_rightRay (j x : ℕ) : tooth j x ∉ rightRay.constructorPaths :=
  fun h => not_mem_constructorPaths_bot _ ((tooth_mem_rightSpine_iff _ j x).mp h)

private theorem tooth_mem_stubComb_iff (j x : ℕ) :
    tooth j x ∈ stubComb.constructorPaths ↔ x = 0 := by
  rw [stubComb, tooth_mem_rightSpine_iff, mem_constructorPaths_e]
  cases x <;> simp

private theorem tooth_one_mem_shortCombs (j : ℕ) : tooth j 1 ∈ shortCombs.constructorPaths :=
  (tooth_mem_rightSpine_iff _ j 1).mpr nil_mem_constructorPaths_e

/-- The right ray avoids every tooth, in particular every stub `tooth j 0`. -/
theorem rightRay_le_cocone_tooth (j x : ℕ) : rightRay ≤ cocone (tooth j x) :=
  (le_cocone_iff topFree_rightRay _).mpr (tooth_not_mem_rightRay j x)

/-- Addresses of `nestRight full j bot`: the words without the prefix `1ʲ`. -/
theorem mem_constructorPaths_nestRight_full_bot (j : ℕ) (w : Word) :
    w ∈ (nestRight full j bot).constructorPaths ↔ ¬ones j <+: w := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    rcases w with _ | ⟨i, w⟩
    · simp
    · fin_cases i
      · simp
      · simp [ih]

/-- Addresses of `nestRight bot j full`: the words comparable with `1ʲ`. -/
theorem mem_constructorPaths_nestRight_bot_full (j : ℕ) (w : Word) :
    w ∈ (nestRight bot j full).constructorPaths ↔ w <+: ones j ∨ ones j <+: w := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    rcases w with _ | ⟨i, w⟩
    · simp
    · fin_cases i
      · simp
      · simp [ih]

/-! ## Contexts at the refuting values -/

/-- If state `r` has no stub at step `j + 1`, the state tree lies below the context bounding
the tail of the comb of state `r` by the cocone of the stub `1ʲ 0`. -/
theorem le_stateContext_cocone_stub {r j : ℕ} (hU : U.TopFree)
    (h : ¬StubAt U r (j + 1)) : U ≤ stateContext full r (cocone (stub j)) := by
  rw [le_stateContext_iff hU (topFree_cocone _)]
  intro w hw
  rw [mem_constructorPaths_cocone]
  intro hp
  apply h
  refine mem_constructorPaths_of_prefix ?_ hw
  show ones r ++ 0 :: 1 :: stub j <+: ones r ++ 0 :: 1 :: w
  exact (List.prefix_append_right_inj _).mpr (List.cons_prefix_cons.mpr ⟨rfl, one_cons_prefix hp⟩)

private theorem le_f_full_cocone {D : Tree} {w : Word} (hD : D.TopFree)
    (h : 1 :: w ∉ D.constructorPaths) : D ≤ f full (cocone w) := by
  rw [le_f_iff topFree_full (topFree_cocone w) hD]
  refine ⟨fun _ _ => mem_constructorPaths_full _, fun v hv => ?_⟩
  rw [mem_constructorPaths_cocone]
  exact fun hp => h (mem_constructorPaths_of_prefix (one_cons_prefix hp) hv)

private theorem f_bot_path_le {D : Tree} {w : Word} (hD : D.TopFree)
    (h : 1 :: w ∈ D.constructorPaths) : f bot (path w) ≤ D := by
  rw [f_le_iff topFree_bot (topFree_path w) hD]
  refine ⟨mem_constructorPaths_of_prefix List.nil_prefix h,
    fun v hv => absurd hv (not_mem_constructorPaths_bot v), fun v hv => ?_⟩
  rw [mem_constructorPaths_path] at hv
  exact mem_constructorPaths_of_prefix (one_cons_prefix hv) h

/-! ## The two blocks at the refuting values -/

/-- The alignment block holds for a path into the tooth below spine node `j`, the
cocone of the stub `j`, and the right nests of the refuting values. -/
theorem alignBlock_nestRight (j x : ℕ) :
    AlignBlock full (path (tooth j x)) (cocone (stub j)) (nestRight full j bot)
      (nestRight bot (j + 1) full) := by
  have hd := topFree_nestRight topFree_full topFree_bot j
  have hp := topFree_nestRight topFree_bot topFree_full (j + 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_f_iff topFree_full hd (topFree_path _)]
    refine ⟨fun _ _ => mem_constructorPaths_full _, fun v hv => ?_⟩
    rw [mem_constructorPaths_path] at hv
    rw [mem_constructorPaths_nestRight_full_bot]
    exact fun h => not_ones_succ_prefix_tooth j x ((ones_succ_prefix_one_cons h).trans hv)
  · rw [le_f_iff topFree_full hd hd]
    refine ⟨fun _ _ => mem_constructorPaths_full _, fun v hv => ?_⟩
    rw [mem_constructorPaths_nestRight_full_bot] at hv ⊢
    exact fun h => hv ((ones_prefix_ones_iff.mpr (Nat.le_succ j)).trans
      (ones_succ_prefix_one_cons h))
  · rw [le_cocone_iff hd, mem_constructorPaths_nestRight_full_bot, not_not]
    exact ones_prefix_tooth j 0
  · rw [f_le_iff topFree_bot (topFree_path _) hp]
    refine ⟨(mem_constructorPaths_nestRight_bot_full _ _).mpr (Or.inl List.nil_prefix),
      fun v hv => absurd hv (not_mem_constructorPaths_bot v), fun v hv => ?_⟩
    rw [mem_constructorPaths_path] at hv
    rw [mem_constructorPaths_nestRight_bot_full, ones_succ, List.cons_prefix_cons,
      List.cons_prefix_cons]
    simp only [true_and]
    exact List.prefix_or_prefix_of_prefix hv (ones_prefix_tooth j x)
  · rw [f_le_iff topFree_bot hp hp]
    refine ⟨(mem_constructorPaths_nestRight_bot_full _ _).mpr (Or.inl List.nil_prefix),
      fun v hv => absurd hv (not_mem_constructorPaths_bot v), fun v hv => ?_⟩
    rw [mem_constructorPaths_nestRight_bot_full] at hv ⊢
    rcases hv with hv | hv
    · obtain ⟨i, -, rfl⟩ := prefix_ones_iff.mp hv
      rw [← ones_succ]
      rcases le_total (i + 1) (j + 1) with h | h
      · exact Or.inl (ones_prefix_ones_iff.mpr h)
      · exact Or.inr (ones_prefix_ones_iff.mpr h)
    · exact Or.inr ((ones_prefix_ones_iff.mpr (Nat.le_succ _)).trans
        (ones_succ_prefix_one_cons hv))
  · rw [le_cocone_iff hp, mem_constructorPaths_nestRight_bot_full]
    rintro (h | h)
    · exact not_stub_prefix_ones _ _ h
    · exact not_ones_succ_prefix_tooth j 0 h

/-- The comparison block with offset `δ` holds for a path into the tooth `1ʲ 0 0ˣ`, the
cocone of the tooth `1ʲ 0 0^x'`, and the auxiliaries of the refuting values exactly when
`x < x' + δ`. -/
theorem popBlock_rightSpine_iff (j δ x x' : ℕ) :
    PopBlock full δ (path (tooth j x)) (cocone (tooth j x')) (rightSpine (path (zeros x)))
        (path (zeros x)) (if δ ≤ x then path (zeros (x - δ)) else bot)
        (rightSpine (if δ ≤ x then path (zeros (x - δ)) else bot)) ↔ x < x' + δ := by
  cases δ with
  | zero =>
    simp only [PopBlock, Nat.add_zero]
    exact path_tooth_le_cocone_tooth_iff j x x'
  | succ δ =>
    set kd := if δ + 1 ≤ x then path (zeros (x - (δ + 1))) else bot with hkd_def
    have hkd : kd.TopFree := by
      rw [hkd_def]
      split
      · exact topFree_path _
      · exact topFree_bot
    have hA : path (tooth j x) ≤ rightSpine (path (zeros x)) := by
      rw [path_le_iff (topFree_rightSpine (topFree_path _)), tooth_mem_rightSpine_iff,
        mem_constructorPaths_path]
    have hB : rightSpine (path (zeros x)) ≤ f (path (zeros x)) (rightSpine (path (zeros x))) :=
      (rightSpine_eq _).le
    have hC : path (zeros x) ≤ popContext full (δ + 1) kd := by
      rw [le_popContext_iff (topFree_path _) hkd]
      intro w hw
      rw [mem_constructorPaths_path] at hw
      have hlen := hw.length_le
      simp only [List.length_append, length_zeros] at hlen
      have hle : δ + 1 ≤ x := by omega
      rw [hkd_def, ite_eq_left hle, mem_constructorPaths_path]
      rw [show zeros x = zeros (δ + 1) ++ zeros (x - (δ + 1)) by
        rw [← zeros_add, Nat.add_sub_cancel' hle]] at hw
      exact (List.prefix_append_right_inj _).mp hw
    have hD : f kd bot ≤ rightSpine kd := by
      conv_rhs => rw [rightSpine_eq]
      exact (f_le_f_iff _ _ _ _).mpr ⟨le_rfl, Tree.bot_le _⟩
    have hE : f bot (rightSpine kd) ≤ rightSpine kd := by
      conv_rhs => rw [rightSpine_eq]
      exact (f_le_f_iff _ _ _ _).mpr ⟨Tree.bot_le _, le_rfl⟩
    have hF : rightSpine kd ≤ cocone (tooth j x') ↔ x < x' + (δ + 1) := by
      rw [le_cocone_iff (topFree_rightSpine hkd), tooth_mem_rightSpine_iff, hkd_def]
      split_ifs with h
      · rw [mem_constructorPaths_path, zeros_prefix_zeros_iff_le]
        omega
      · simp only [not_mem_constructorPaths_bot, not_false_eq_true, true_iff]
        omega
    simp only [PopBlock]
    exact ⟨fun h => hF.mp h.2.2.2.2.2, fun h => ⟨hA, hB, hC, hD, hE, hF.mpr h⟩⟩

theorem upperBoundClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {i : Fin 2}
    (hC : (C i).TopFree) {δ : ℕ} {trunc : Bool} {q : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      UpperBoundClause (Existentials.standard C U) v δ trunc q i) :
    UpperBoundSpec U (C i) δ trunc q := by
  intro j x₁ x₂ hs hn ht htr
  by_contra hlt
  have hcl := h _ (refutingValues_path_cocone_admissible hc j δ x₁ (tooth j x₁) (tooth j x₂)
    (stub j) (tooth j x₁) (tooth j x₂) (stub j))
  have htrunc : (if trunc then stubComb else rightRay) ≤ cocone (tooth j x₂) := by
    cases trunc
    · exact rightRay_le_cocone_tooth j x₂
    · refine (le_cocone_iff topFree_stubComb _).mpr ?_
      rw [tooth_mem_stubComb_iff]
      have := htr rfl
      omega
  rcases hcl ⟨(path_le_iff topFree_combUniverse _).mpr (tooth_mem_combUniverse j x₁),
    (le_cocone_iff hC _).mpr hn, rightRay_le_cocone_tooth j x₁,
    f_bot_path_le (w := tooth j x₂) hC ht, (popBlock_rightSpine_iff j δ x₁ x₂).mpr (by omega),
    htrunc, pack_path_le (w := stub j) hU hs, alignBlock_nestRight j x₁,
    alignBlock_nestRight j x₂⟩ with h₁ | h₂ | h₃
  · exact not_path_le_cocone (tooth j x₁) h₁
  · exact not_path_le_cocone (tooth j x₂) h₂
  · exact not_path_le_cocone (stub j) h₃

theorem lowerBoundClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {i : Fin 2}
    (hC : (C i).TopFree) {δ q : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      LowerBoundClause (Existentials.standard C U) v δ q i) :
    LowerBoundSpec U (C i) δ q := by
  intro j x₁ x₂ hs ht hn
  by_contra hlt
  have hcl := h _ (refutingValues_path_cocone_admissible hc j δ x₂ (tooth j x₁) (tooth j x₂)
    (stub j) (tooth j x₁) (tooth j x₂) (stub j))
  rcases hcl ⟨(path_le_iff hC _).mpr ht, (popBlock_rightSpine_iff j δ x₂ x₁).mpr (by omega),
    rightRay_le_cocone_tooth j x₁,
    (path_le_iff topFree_combUniverse _).mpr (tooth_mem_combUniverse j x₂),
    le_f_full_cocone (w := tooth j x₂) hC hn, rightRay_le_cocone_tooth j x₂,
    pack_path_le (w := stub j) hU hs, alignBlock_nestRight j x₁,
    alignBlock_nestRight j x₂⟩ with h₁ | h₂ | h₃
  · exact not_path_le_cocone (tooth j x₁) h₁
  · exact not_path_le_cocone (tooth j x₂) h₂
  · exact not_path_le_cocone (stub j) h₃

theorem transitionClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {q r : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      TransitionClause (Existentials.standard C U) v q r) :
    TransitionSpec U q r := by
  intro j hs
  by_contra hn
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 0 (stub j) (stub j) (stub j)
    (stub j) (stub j) (stub j))
  exact not_path_le_cocone (stub j) (hcl ⟨pack_path_le (w := stub j) hU hs,
    le_stateContext_cocone_stub hU hn, rightRay_le_cocone_tooth j 0⟩)

theorem nextToothClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {i : Fin 2}
    (hC : (C i).TopFree) {q : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      NextToothClause (Existentials.standard C U) v q i) :
    NextToothSpec U (C i) q := by
  intro j hs
  by_contra hn
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 0 (stub j) (stub j) (stub j)
    (stub j) (stub j) (stub j))
  exact not_path_le_cocone (stub j) (hcl ⟨pack_path_le (w := stub j) hU hs,
    le_f_full_cocone (w := stub j) hC hn, rightRay_le_cocone_tooth j 0⟩)

theorem haltUniqueClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {n q : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      HaltUniqueClause (Existentials.standard C U) v n q) :
    HaltUniqueSpec U n q := by
  rintro j ⟨hq, hn⟩
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 0 (stub j) (stub j) (stub j)
    (stub j) (stub j) (stub j))
  have hS := hcl ⟨pack_path_le (w := stub j) hU hq, pack_path_le (w := stub j) hU hn⟩
  exact tooth_not_mem_rightRay j 0 ((path_le_iff topFree_rightRay (stub j)).mp hS)

theorem zeroTestClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {i : Fin 2}
    (hC : (C i).TopFree) {q r : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      ZeroTestClause (Existentials.standard C U) v q r i) :
    ZeroTestSpec U (C i) q r := by
  intro j hs hn₁
  by_contra hn
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 1 (tooth j 1) (tooth j 1)
    (stub j) (tooth j 1) (tooth j 1) (stub j))
  have hT : stubComb ≤ cocone (tooth j 1) := by
    refine (le_cocone_iff topFree_stubComb _).mpr ?_
    rw [tooth_mem_stubComb_iff]
    exact one_ne_zero
  rcases hcl ⟨(path_le_iff topFree_shortCombs _).mpr (tooth_one_mem_shortCombs j),
    (le_cocone_iff hC _).mpr hn₁, hT, pack_path_le (w := stub j) hU hs,
    le_stateContext_cocone_stub hU hn, alignBlock_nestRight j 1⟩ with h₁ | h₃
  · exact not_path_le_cocone (tooth j 1) h₁
  · exact not_path_le_cocone (stub j) h₃

theorem positiveTestClause_sound (hc : c ≠ .finite) (hU : U.TopFree) {i : Fin 2}
    (hC : (C i).TopFree) {q r : ℕ}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      PositiveTestClause (Existentials.standard C U) v q r i) :
    PositiveTestSpec U (C i) q r := by
  intro j hs hp₁
  by_contra hn
  have hcl := h _ (refutingValues_path_cocone_admissible hc j 0 1 (tooth j 1) (tooth j 1)
    (stub j) (tooth j 1) (tooth j 1) (stub j))
  rcases hcl ⟨(path_le_iff hC _).mpr hp₁,
    (path_le_iff topFree_combUniverse _).mpr (tooth_mem_combUniverse j 1),
    pack_path_le (w := stub j) hU hs, le_stateContext_cocone_stub hU hn,
    alignBlock_nestRight j 1⟩ with h₂ | h₃
  · exact one_ne_zero ((tooth_mem_stubComb_iff j 1).mp
      ((path_le_iff topFree_stubComb (tooth j 1)).mp h₂))
  · exact not_path_le_cocone (stub j) h₃

/-- The clauses of an instruction imply their specifications. -/
theorem instructionSpecs_of_clauses (hc : c ≠ .finite) (hU : U.TopFree)
    (hC : ∀ i, (C i).TopFree) {n q : ℕ} {ins : Instr}
    (h : ∀ v : Universals Tree, v.Forall (Admissible c top) →
      InstructionClauses (Existentials.standard C U) v n q ins) :
    InstructionSpecs n C U q ins := by
  cases ins with
  | inc d r =>
    exact ⟨haltUniqueClause_sound hc hU fun v hv => (h v hv).1,
      transitionClause_sound hc hU fun v hv => (h v hv).2.1,
      upperBoundClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.1,
      lowerBoundClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.2.1,
      upperBoundClause_sound hc hU (hC _) fun v hv => (h v hv).2.2.2.2.1,
      lowerBoundClause_sound hc hU (hC _) fun v hv => (h v hv).2.2.2.2.2⟩
  | jzdec d z p =>
    exact ⟨haltUniqueClause_sound hc hU fun v hv => (h v hv).1,
      zeroTestClause_sound hc hU (hC d) fun v hv => (h v hv).2.1,
      positiveTestClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.1,
      upperBoundClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.2.1,
      lowerBoundClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.2.2.1,
      nextToothClause_sound hc hU (hC d) fun v hv => (h v hv).2.2.2.2.2.1,
      upperBoundClause_sound hc hU (hC _) fun v hv => (h v hv).2.2.2.2.2.2.1,
      lowerBoundClause_sound hc hU (hC _) fun v hv => (h v hv).2.2.2.2.2.2.2⟩

end Sentence

end UndeciSigma2
