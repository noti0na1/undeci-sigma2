import UndeciSigma2.Clock.Readings

/-! # Window clauses

For a top-free source `X` and a top-free base `E` of the domain, both with all residuals below
a sink value of the domain, let `S` be the set of addresses of the right child of `X` outside
`E`. The window clause holds for all values of the universal variables exactly when no
two words `w₁, w₂ ∈ S` satisfy `w₂ ∉ dropOnes w₁` and `w₁ ∉ dropOnesStrict w₂`; the triple
window clause exactly when no three words `w₁, w₂, w₃ ∈ S` satisfy these conditions for every
pair `a < b` (`WindowSpec`).

* If the specification holds, the clause holds for arbitrary values: failing consequents give
  addresses `wᵢ` of the seeds outside the supports of the bounds; they lie in `S`, and the drop
  blocks put `dropOnes wₐ` and `dropOnesStrict w_b` into the supports of the other bounds.
* If the clause holds for all values of the domain, the specification holds: a forbidden tuple
  is refuted by the paths to its words, the drop trees, bounds made of `E` and the drop trees,
  and the sink value. These values lie in the domain of the witnesses.

For the tooth words `1^s 0 1^x`, at most `k - 1` new words share a stamp under `WindowSpec k`
(`WindowSpec.not_strictMono`); conversely, if `S` consists of tooth words whose lengths grow
with the stamp, this bound per stamp implies `WindowSpec k` (`windowSpec_of_onion`).
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

variable {c : TreeClass} {top : Bool}

/-- No `k` words of `S` are pairwise unrelated in order: `w b ∉ dropOnes (w a)` and
`w a ∉ dropOnesStrict (w b)` for `a < b`. -/
def WindowSpec (k : ℕ) (S : Set Word) : Prop :=
  ¬∃ w : Fin k → Word, (∀ i, w i ∈ S) ∧
    ∀ a b, a < b → w b ∉ dropOnes (w a) ∧ w a ∉ dropOnesStrict (w b)

/-- The addresses of the right child of `X` outside `E`. -/
def windowSet (X E : Tree) : Set Word := {w | 1 :: w ∈ X.constructorPaths ∧ w ∉ E.constructorPaths}

/-! ## Two and three words -/

/-- A relation on `Fin 2` holds for all `a < b` if it holds for `0 < 1`. -/
theorem forall_lt_fin_two {P : Fin 2 → Fin 2 → Prop} (h : P 0 1) : ∀ a b, a < b → P a b := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact h | exact absurd hab (by decide)

/-- A relation on `Fin 3` holds for all `a < b` if it holds for the three pairs. -/
theorem forall_lt_fin_three {P : Fin 3 → Fin 3 → Prop} (h₀₁ : P 0 1) (h₀₂ : P 0 2)
    (h₁₂ : P 1 2) : ∀ a b, a < b → P a b := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first | exact h₀₁ | exact h₀₂ | exact h₁₂ | exact absurd hab (by decide)

/-- Two words of `S`, unrelated in both directions, contradict `WindowSpec 2 S`. -/
theorem not_windowSpec_two {S : Set Word} {w₁ w₂ : Word} (h₁ : w₁ ∈ S) (h₂ : w₂ ∈ S)
    (h₁₂ : w₂ ∉ dropOnes w₁ ∧ w₁ ∉ dropOnesStrict w₂) : ¬WindowSpec 2 S := fun h =>
  h ⟨![w₁, w₂], fun i => by fin_cases i <;> assumption, forall_lt_fin_two h₁₂⟩

/-- Three words of `S`, pairwise unrelated in both directions, contradict `WindowSpec 3 S`. -/
theorem not_windowSpec_three {S : Set Word} {w₁ w₂ w₃ : Word} (h₁ : w₁ ∈ S) (h₂ : w₂ ∈ S)
    (h₃ : w₃ ∈ S) (h₁₂ : w₂ ∉ dropOnes w₁ ∧ w₁ ∉ dropOnesStrict w₂)
    (h₁₃ : w₃ ∉ dropOnes w₁ ∧ w₁ ∉ dropOnesStrict w₃)
    (h₂₃ : w₃ ∉ dropOnes w₂ ∧ w₂ ∉ dropOnesStrict w₃) : ¬WindowSpec 3 S := fun h =>
  h ⟨![w₁, w₂, w₃], fun i => by fin_cases i <;> assumption, forall_lt_fin_three h₁₂ h₁₃ h₂₃⟩

/-! ## The clauses hold under their specifications -/

/-- A seed `y` with `f(⊥, y) ≤ X` that does not lie below a bound `g ≥ E` has an address in
the window set outside the support of `g`. -/
theorem exists_mem_windowSet {X E y g : Tree} (hX : X.TopFree) (hy : f bot y ≤ X) (hE : E ≤ g)
    (hn : ¬y ≤ g) : ∃ w ∈ y.constructorPaths, w ∈ windowSet X E ∧ w ∉ g.support := by
  have hyt : y.TopFree := SeedAtom.topFree_of_holds (a := .rightLe X) hX hy
  rw [le_iff_subset_support hyt, Set.not_subset] at hn
  obtain ⟨w, hw, hwg⟩ := hn
  refine ⟨w, hw, ⟨SeedAtom.subset_reading (a := .rightLe X) hX hy hw, fun hwE => hwg ?_⟩, hwg⟩
  exact support_mono hE (constructorPaths_subset_support E hwE)

/-- If its specification holds, the window clause holds for all values of the universal
variables, with or without top. -/
theorem window_holds {X E : Tree} (hX : X.TopFree) (hspec : WindowSpec 2 (windowSet X E))
    (v : ClockUniversals Tree) : (ClockClause.window X E).Holds v := by
  intro h₁ h₂ hE₁ hE₂ hd₁ he₂
  by_contra hc
  rw [not_or] at hc
  obtain ⟨w₁, hw₁, hS₁, hn₁⟩ := exists_mem_windowSet hX h₁ hE₁ hc.1
  obtain ⟨w₂, hw₂, hS₂, hn₂⟩ := exists_mem_windowSet hX h₂ hE₂ hc.2
  refine not_windowSpec_two hS₁ hS₂ ⟨fun h => hn₂ ?_, fun h => hn₁ ?_⟩ hspec
  · exact DropBlock.dropOnes_subset hd₁ hw₁ (List.mem_singleton_self _) h
  · exact StrictDropBlock.dropOnesStrict_subset he₂ hw₂ (List.mem_singleton_self _) h

/-- If its specification holds, the triple window clause holds for all values of the universal
variables, with or without top. -/
theorem window3_holds {X E : Tree} (hX : X.TopFree) (hspec : WindowSpec 3 (windowSet X E))
    (v : ClockUniversals Tree) : (ClockClause.window3 X E).Holds v := by
  intro h₁ h₂ h₃ hE₁ hE₂ hE₃ hd₁ hd₂ he₂ he₃
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨w₁, hw₁, hS₁, hn₁⟩ := exists_mem_windowSet hX h₁ hE₁ hc.1
  obtain ⟨w₂, hw₂, hS₂, hn₂⟩ := exists_mem_windowSet hX h₂ hE₂ hc.2.1
  obtain ⟨w₃, hw₃, hS₃, hn₃⟩ := exists_mem_windowSet hX h₃ hE₃ hc.2.2
  refine not_windowSpec_three hS₁ hS₂ hS₃ ⟨fun h => hn₂ ?_, fun h => hn₁ ?_⟩
    ⟨fun h => hn₃ ?_, fun h => hn₁ ?_⟩ ⟨fun h => hn₃ ?_, fun h => hn₂ ?_⟩ hspec
  · exact DropBlock.dropOnes_subset hd₁ hw₁ (by simp) h
  · exact StrictDropBlock.dropOnesStrict_subset he₂ hw₂ (by simp) h
  · exact DropBlock.dropOnes_subset hd₁ hw₁ (by simp) h
  · exact StrictDropBlock.dropOnesStrict_subset he₃ hw₃ (by simp) h
  · exact DropBlock.dropOnes_subset hd₂ hw₂ (by simp) h
  · exact StrictDropBlock.dropOnesStrict_subset he₃ hw₃ (by simp) h

/-! ## The specifications follow from the clauses -/

/-- The values of the universal variables refuting a window clause with base `E` at the words
`w₁, w₂`, with sink value `z`. -/
noncomputable def windowValues (E z : Tree) (w₁ w₂ : Word) : ClockUniversals Tree where
  y₁ := path w₁
  y₂ := path w₂
  y₃ := bot
  g₁ := unionTree [E, strictDropTree w₂]
  g₂ := unionTree [E, dropTree w₁]
  g₃ := bot
  k := bot
  k₀ := bot
  d₁ := dropTree w₁
  d₂ := bot
  e₂ := strictDropTree w₂
  e₃ := bot
  z := z

/-- The values of the universal variables refuting a triple window clause with base `E` at the
words `w₁, w₂, w₃`, with sink value `z`. -/
noncomputable def window3Values (E z : Tree) (w₁ w₂ w₃ : Word) : ClockUniversals Tree where
  y₁ := path w₁
  y₂ := path w₂
  y₃ := path w₃
  g₁ := unionTree [E, strictDropTree w₂, strictDropTree w₃]
  g₂ := unionTree [E, dropTree w₁, strictDropTree w₃]
  g₃ := unionTree [E, dropTree w₁, dropTree w₂]
  k := bot
  k₀ := bot
  d₁ := dropTree w₁
  d₂ := dropTree w₂
  e₂ := strictDropTree w₂
  e₃ := strictDropTree w₃
  z := z

/-- The union of a tree of the domain with finitely many drop trees lies in the domain. -/
theorem domain_unionTree_cons {E : Tree} (hE : Domain c top E) {ts : List Tree}
    (hts : ∀ t ∈ ts, t.IsFinite ∧ t.TopFree) : Domain c top (unionTree (E :: ts)) :=
  domain_unionTree fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hE
    · exact domain_of_isFinite (hts t ht).1 (hts t ht).2

/-- The path to an address `w` of the right child of `X` satisfies `f(⊥, path w) ≤ X`. -/
theorem rightLe_path {X : Tree} {w : Word} (hw : 1 :: w ∈ X.constructorPaths) :
    f bot (path w) ≤ X := by
  rw [f_bot_path]
  exact path_le_of_mem hw

/-- If the window clause holds for all values of the domain, its specification holds. -/
theorem window_spec {X E z : Tree} (hz : Domain c top z) (hX : IsWitness c top z X)
    (hE : IsWitness c top z E)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) → (ClockClause.window X E).Holds v) :
    WindowSpec 2 (windowSet X E) := by
  rintro ⟨w, hwS, hw⟩
  obtain ⟨hX₁, hE₁⟩ := hwS 0
  obtain ⟨hX₂, hE₂⟩ := hwS 1
  obtain ⟨h₂₁, h₁₂⟩ := hw 0 1 (by decide)
  have hv : (windowValues E z (w 0) (w 1)).Forall (Domain c top) := by
    apply ClockUniversals.forall_of_each <;> simp only [windowValues]
    all_goals first
      | exact domain_bot c top | exact hz | exact domain_path _ | exact domain_dropTree _
      | exact domain_strictDropTree _
      | exact domain_unionTree_cons hE.1 (by simp [finite_dropTree, finite_strictDropTree])
  have hd₁ : ∀ g ∈ [unionTree [E, dropTree (w 0)]], dropTree (w 0) ≤ g := by
    intro g hg
    rw [List.mem_singleton] at hg
    exact hg ▸ le_unionTree_of_mem (by simp) (topFree_dropTree _)
  have he₂ : ∀ g ∈ [unionTree [E, strictDropTree (w 1)]], strictDropTree (w 1) ≤ g := by
    intro g hg
    rw [List.mem_singleton] at hg
    exact hg ▸ le_unionTree_of_mem (by simp) (topFree_strictDropTree _)
  have hc := h _ hv (rightLe_path hX₁) (rightLe_path hX₂)
    (le_unionTree_of_mem (by simp) hE.2.1) (le_unionTree_of_mem (by simp) hE.2.1)
    (dropBlock_path hX.2.2 hX₁ hd₁) (strictDropBlock_path hX.2.2 hX₂ he₂)
  simp only [windowValues, path_le_unionTree_iff, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, mem_dropTree, mem_strictDropTree] at hc
  tauto

/-- If the triple window clause holds for all values of the domain, its specification
holds. -/
theorem window3_spec {X E z : Tree} (hz : Domain c top z) (hX : IsWitness c top z X)
    (hE : IsWitness c top z E)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) →
      (ClockClause.window3 X E).Holds v) :
    WindowSpec 3 (windowSet X E) := by
  rintro ⟨w, hwS, hw⟩
  obtain ⟨hX₁, hE₁⟩ := hwS 0
  obtain ⟨hX₂, hE₂⟩ := hwS 1
  obtain ⟨hX₃, hE₃⟩ := hwS 2
  obtain ⟨h₂₁, h₁₂⟩ := hw 0 1 (by decide)
  obtain ⟨h₃₁, h₁₃⟩ := hw 0 2 (by decide)
  obtain ⟨h₃₂, h₂₃⟩ := hw 1 2 (by decide)
  have hv : (window3Values E z (w 0) (w 1) (w 2)).Forall (Domain c top) := by
    apply ClockUniversals.forall_of_each <;> simp only [window3Values]
    all_goals first
      | exact domain_bot c top | exact hz | exact domain_path _ | exact domain_dropTree _
      | exact domain_strictDropTree _
      | exact domain_unionTree_cons hE.1 (by simp [finite_dropTree, finite_strictDropTree])
  have hd₁ : ∀ g ∈ [unionTree [E, dropTree (w 0), strictDropTree (w 2)],
      unionTree [E, dropTree (w 0), dropTree (w 1)]], dropTree (w 0) ≤ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact le_unionTree_of_mem (by simp) (topFree_dropTree _)
  have hd₂ : ∀ g ∈ [unionTree [E, dropTree (w 0), dropTree (w 1)]], dropTree (w 1) ≤ g := by
    intro g hg
    rw [List.mem_singleton] at hg
    exact hg ▸ le_unionTree_of_mem (by simp) (topFree_dropTree _)
  have he₂ : ∀ g ∈ [unionTree [E, strictDropTree (w 1), strictDropTree (w 2)]],
      strictDropTree (w 1) ≤ g := by
    intro g hg
    rw [List.mem_singleton] at hg
    exact hg ▸ le_unionTree_of_mem (by simp) (topFree_strictDropTree _)
  have he₃ : ∀ g ∈ [unionTree [E, strictDropTree (w 1), strictDropTree (w 2)],
      unionTree [E, dropTree (w 0), strictDropTree (w 2)]], strictDropTree (w 2) ≤ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact le_unionTree_of_mem (by simp) (topFree_strictDropTree _)
  have hc := h _ hv (rightLe_path hX₁) (rightLe_path hX₂) (rightLe_path hX₃)
    (le_unionTree_of_mem (by simp) hE.2.1) (le_unionTree_of_mem (by simp) hE.2.1)
    (le_unionTree_of_mem (by simp) hE.2.1)
    (dropBlock_path hX.2.2 hX₁ hd₁) (dropBlock_path hX.2.2 hX₂ hd₂)
    (strictDropBlock_path hX.2.2 hX₂ he₂) (strictDropBlock_path hX.2.2 hX₃ he₃)
  simp only [window3Values, path_le_unionTree_iff, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, mem_dropTree, mem_strictDropTree] at hc
  tauto

/-! ## Tooth words -/

/-- A tooth word of a stamp `s' ≤ s` and depth `x' ≤ x` arises from `1^s 0 1^x` by removing
leading ones. -/
theorem toothWord_mem_dropOnes {s x s' x' : ℕ} (hs : s' ≤ s) (hx : x' ≤ x) :
    toothWord s' x' ∈ dropOnes (toothWord s x) :=
  ⟨s - s', by
    rw [ones_append_toothWord, Nat.sub_add_cancel hs]
    exact toothWord_prefix_toothWord hx⟩

/-- A tooth word of a stamp `s' < s` and depth `x' ≤ x` arises from `1^s 0 1^x` by removing at
least one leading one. -/
theorem toothWord_mem_dropOnesStrict {s x s' x' : ℕ} (hs : s' < s) (hx : x' ≤ x) :
    toothWord s' x' ∈ dropOnesStrict (toothWord s x) :=
  ⟨s - s' - 1, by
    rw [ones_append_toothWord, show s - s' - 1 + 1 + s' = s by omega]
    exact toothWord_prefix_toothWord hx⟩

/-- Removing leading ones from a tooth word does not make the tooth longer. -/
theorem toothWord_not_mem_dropOnes {s x x' : ℕ} (hx : x < x') :
    toothWord s x' ∉ dropOnes (toothWord s x) := by
  rintro ⟨c, hc⟩
  have := hc.length_le
  simp only [List.length_append, length_ones, length_toothWord] at this
  omega

/-- Removing at least one leading one from a tooth word never gives a tooth word of the same
stamp. -/
theorem toothWord_not_mem_dropOnesStrict {s x x' : ℕ} :
    toothWord s x ∉ dropOnesStrict (toothWord s x') := by
  rintro ⟨c, hc⟩
  rw [ones_append_toothWord] at hc
  rcases prefix_ones_append_zero_cons_iff.mp hc with ⟨i, -, hi⟩ | ⟨v, -, hv⟩
  · have : IsOnes (toothWord (c + 1 + s) x) := hi ▸ isOnes_ones i
    exact not_isOnes_ones_append_zero_cons _ _ this
  · have := (ones_append_zero_cons_inj.mp hv).1
    omega

/-- Under `WindowSpec k`, fewer than `k` words of `S` are tooth words of one stamp. -/
theorem WindowSpec.not_strictMono {k : ℕ} {S : Set Word} (h : WindowSpec k S) (s : ℕ)
    (xs : Fin k → ℕ) (hxs : StrictMono xs) : ¬∀ i, toothWord s (xs i) ∈ S := fun hS =>
  h ⟨fun i => toothWord s (xs i), hS, fun _ _ hab =>
    ⟨toothWord_not_mem_dropOnes (hxs hab), toothWord_not_mem_dropOnesStrict⟩⟩

/-- Two tooth words of a set satisfying the onion condition that are unrelated as in
`WindowSpec` share their stamp, and the later one is longer. -/
theorem eq_and_lt_of_onion {S : Set Word}
    (honion : ∀ s s' y y', s < s' → toothWord s y ∈ S → toothWord s' y' ∈ S → y ≤ y')
    {s s' y y' : ℕ} (h : toothWord s y ∈ S) (h' : toothWord s' y' ∈ S)
    (h₁ : toothWord s' y' ∉ dropOnes (toothWord s y))
    (h₂ : toothWord s y ∉ dropOnesStrict (toothWord s' y')) : s = s' ∧ y < y' := by
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact absurd (toothWord_mem_dropOnesStrict hlt (honion _ _ _ _ hlt h h')) h₂
  · exact ⟨heq, lt_of_not_ge fun hle => h₁ (toothWord_mem_dropOnes heq.ge hle)⟩
  · exact absurd (toothWord_mem_dropOnes hgt.le (honion _ _ _ _ hgt h' h)) h₁

/-- If `S` consists of tooth words, the tooth words of a smaller stamp are not longer than those
of a larger stamp, and fewer than `k` words of `S` share a stamp, then `WindowSpec k S`. -/
theorem windowSpec_of_onion {k : ℕ} {S : Set Word}
    (hS : ∀ w ∈ S, ∃ s y, w = toothWord s y)
    (honion : ∀ s s' y y', s < s' → toothWord s y ∈ S → toothWord s' y' ∈ S → y ≤ y')
    (hcard : ∀ s (xs : Fin k → ℕ), StrictMono xs → ¬∀ i, toothWord s (xs i) ∈ S) :
    WindowSpec k S := by
  rintro ⟨w, hwS, hw⟩
  choose st hst using fun i => hS (w i) (hwS i)
  choose y hy using hst
  have hmem : ∀ i, toothWord (st i) (y i) ∈ S := fun i => by
    rw [← hy i]
    exact hwS i
  have key : ∀ a b, a < b → st a = st b ∧ y a < y b := by
    intro a b hab
    obtain ⟨h₁, h₂⟩ := hw a b hab
    rw [hy a, hy b] at h₁ h₂
    exact eq_and_lt_of_onion honion (hmem a) (hmem b) h₁ h₂
  cases k with
  | zero => exact hcard 0 Fin.elim0 (fun a => a.elim0) fun i => i.elim0
  | succ k =>
    refine hcard (st 0) y (fun a b hab => (key a b hab).2) fun i => ?_
    rcases (Fin.zero_le i).eq_or_lt with h0 | h0
    · rw [← h0]
      exact hmem 0
    · rw [(key 0 i h0).1]
      exact hmem i

end Clock

end UndeciSigma2
