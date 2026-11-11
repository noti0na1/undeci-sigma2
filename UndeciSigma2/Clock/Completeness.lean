import UndeciSigma2.Clock.Specs

/-! # Completeness of the clock sentence

If the program halts, its label machine has a balanced exact run `λ₀, …, λ_E` with counters
`cᵢ(s)` (`exists_balanced_exactRun`). The honest witnesses are finite top-free trees built from
it. With `t : ℕ → ℤ` giving the tooth lengths (`-1` for no tooth), the comb `comb E t` has the
addresses `1ⁱ` for `i ≤ E` and `1^s 0 1^y` for `s ≤ E` and `y ≤ t(s)`. With `u(s)` the number
of unwinding labels up to `s`, `N` the number of build-up labels, `m` the number of labels and
`M = m + 3E + 3`:

| witness | value |
|---|---|
| clock | `comb E (s ↦ s)` |
| component of `l` | `comb E (s ↦ s if λ_s = l, else -1)` |
| labels | `select m (component) ⊥` |
| counter `i` | `comb E (s ↦ cᵢ(s) + s)` |
| increasing class of `i` | the counter comb at the stamps `s ≥ 1` whose label adds `1` to `i` |
| keeping class of `i` | the counter comb at the stamps `s ≥ 1` whose label keeps `i` |
| unwinding comb | `comb E u` |
| unwinding part | `comb E (s ↦ u(s) if λ_s` is the unwinding label`, else -1)` |
| chain, head, loop | the paths to `1^E 0 1^E 0` and `1^E 0 1^E`, the spine join of the chain |
| ray `N`, build-up loop | the path to `1^N`, the spine join of the build-up component |
| ray, comb bound, sink | the words of length at most `M` with at most `0`, `1`, `2` zeros |

They satisfy the guards and the root conditions, and the specification of every clause; the
balance of the run is used only for the unwinding bound. Being finite and top-free, they lie in
every domain, so the clock sentence holds in all six structures.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

/-- The comb with last stamp `E` and tooth lengths `t`: the addresses `1ⁱ` for `i ≤ E` and
`1^s 0 1^y` for `s ≤ E` and `y ≤ t s`; a negative `t s` means no tooth at `s`. -/
noncomputable def comb (E : ℕ) (t : ℕ → ℤ) : Tree :=
  prefixTree ({ones E} ∪ {w | ∃ s ≤ E, ∃ y : ℕ, (y : ℤ) ≤ t s ∧ w = toothWord s y})

/-- The addresses of a comb. -/
theorem mem_comb (E : ℕ) (t : ℕ → ℤ) (w : Word) :
    w ∈ (comb E t).constructorPaths ↔
      (∃ i ≤ E, w = ones i) ∨ ∃ s ≤ E, ∃ y : ℕ, (y : ℤ) ≤ t s ∧ w = toothWord s y := by
  rw [comb, mem_prefixTree]
  constructor
  · rintro ⟨v, hv, hwv⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hv
    rcases hv with rfl | ⟨s, hs, y, hy, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := prefix_ones_iff.mp hwv
      exact Or.inl ⟨i, hi, rfl⟩
    · rcases prefix_toothWord_iff.mp hwv with ⟨i, hi, rfl⟩ | ⟨y', hy', rfl⟩
      · exact Or.inl ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨s, hs, y', by omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩)
    · exact ⟨ones E, Or.inl rfl, ones_prefix_ones_iff.mpr hi⟩
    · exact ⟨toothWord s y, Or.inr ⟨s, hs, y, hy, rfl⟩, List.prefix_rfl⟩

/-- Combs are finite. -/
theorem finite_comb (E : ℕ) (t : ℕ → ℤ) : (comb E t).IsFinite := by
  apply finite_of_bounded (topFree_prefixTree _)
    (E + (∑ s ∈ Finset.range (E + 1), (t s).toNat) + 2)
  intro w hw
  rcases (mem_comb E t w).mp hw with ⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · simp only [length_ones]
    omega
  · have hle : (t s).toNat ≤ ∑ s ∈ Finset.range (E + 1), (t s).toNat :=
      Finset.single_le_sum (f := fun s => (t s).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (show s < E + 1 by omega))
    rw [length_toothWord]
    omega

@[simp] theorem topFree_comb (E : ℕ) (t : ℕ → ℤ) : (comb E t).TopFree := topFree_prefixTree _

/-- The tree of the words of length at most `M` with at most `k` zeros. -/
noncomputable def boundedTree (M k : ℕ) : Tree :=
  prefixTree {w | w.length ≤ M ∧ w.count 0 ≤ k}

/-- The addresses of a bounded tree. -/
theorem mem_boundedTree (M k : ℕ) (w : Word) :
    w ∈ (boundedTree M k).constructorPaths ↔ w.length ≤ M ∧ w.count 0 ≤ k := by
  rw [boundedTree, mem_prefixTree]
  constructor
  · rintro ⟨v, ⟨hvl, hvc⟩, hwv⟩
    exact ⟨hwv.length_le.trans hvl, (hwv.sublist.count_le 0).trans hvc⟩
  · intro h
    exact ⟨w, h, List.prefix_rfl⟩

/-- Bounded trees are finite. -/
theorem finite_boundedTree (M k : ℕ) : (boundedTree M k).IsFinite := by
  apply finite_of_bounded (topFree_prefixTree _) (M + 1)
  intro w hw
  have := ((mem_boundedTree M k w).mp hw).1
  omega

@[simp] theorem topFree_boundedTree (M k : ℕ) : (boundedTree M k).TopFree := topFree_prefixTree _

/-! ## Addresses of combs -/

/-- The spine words of a comb are those up to its last stamp. -/
theorem ones_mem_comb {E i : ℕ} {t : ℕ → ℤ} : ones i ∈ (comb E t).constructorPaths ↔ i ≤ E := by
  rw [mem_comb]
  constructor
  · rintro (⟨i', hi', h⟩ | ⟨s, -, y, -, h⟩)
    · have := congrArg List.length h
      simp only [length_ones] at this
      omega
    · exact absurd h.symm (toothWord_ne_ones s y i)
  · exact fun h => Or.inl ⟨i, h, rfl⟩

/-- The tooth words of a comb are those within its tooth lengths. -/
theorem toothWord_mem_comb {E s y : ℕ} {t : ℕ → ℤ} :
    toothWord s y ∈ (comb E t).constructorPaths ↔ s ≤ E ∧ (y : ℤ) ≤ t s := by
  rw [mem_comb]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨s', hs', y', hy', h⟩)
    · exact absurd h (toothWord_ne_ones s y i)
    · obtain ⟨rfl, rfl⟩ := toothWord_inj.mp h
      exact ⟨hs', hy'⟩
  · rintro ⟨hs, hy⟩
    exact Or.inr ⟨s, hs, y, hy, rfl⟩

/-- The addresses of the right child of a comb: the comb shifted by one stamp. -/
theorem one_cons_mem_comb {E : ℕ} {t : ℕ → ℤ} {w : Word} :
    1 :: w ∈ (comb E t).constructorPaths ↔
      (∃ i < E, w = ones i) ∨ ∃ s < E, ∃ y : ℕ, (y : ℤ) ≤ t (s + 1) ∧ w = toothWord s y := by
  rw [mem_comb]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨s, hs, y, hy, h⟩)
    · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_iff.mp h
      exact Or.inl ⟨k, by omega, rfl⟩
    · obtain ⟨k, rfl, rfl⟩ := one_cons_eq_ones_append_iff.mp h
      exact Or.inr ⟨k, by omega, y, hy, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩)
    · exact Or.inl ⟨i + 1, by omega, rfl⟩
    · exact Or.inr ⟨s + 1, by omega, y, hy, rfl⟩

/-- The addresses of the left child of a comb: the tooth at stamp `0`. -/
theorem zero_cons_mem_comb {E : ℕ} {t : ℕ → ℤ} {w : Word} :
    0 :: w ∈ (comb E t).constructorPaths ↔ ∃ y : ℕ, (y : ℤ) ≤ t 0 ∧ w = ones y := by
  rw [mem_comb]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨s, -, y, hy, h⟩)
    · exact absurd h (zero_cons_ne_ones w i)
    · obtain ⟨rfl, rfl⟩ := zero_cons_eq_ones_append_iff.mp h
      exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Or.inr ⟨0, Nat.zero_le _, y, hy, rfl⟩

/-- Combs grow with their tooth lengths. -/
theorem comb_subset {E : ℕ} {t t' : ℕ → ℤ} (h : ∀ s ≤ E, t s ≤ t' s) :
    (comb E t).constructorPaths ⊆ (comb E t').constructorPaths := by
  intro w hw
  rw [mem_comb] at hw ⊢
  rcases hw with hw | ⟨s, hs, y, hy, rfl⟩
  · exact Or.inl hw
  · exact Or.inr ⟨s, hs, y, hy.trans (h s hs), rfl⟩

/-- Combs are monotone in their tooth lengths. -/
theorem comb_mono {E : ℕ} {t t' : ℕ → ℤ} (h : ∀ s ≤ E, t s ≤ t' s) : comb E t ≤ comb E t' :=
  le_of_subset (topFree_comb E t) (comb_subset h)

/-- A comb with a tooth at stamp `0` lies above `f(e, ⊥)`. -/
theorem f_e_bot_le_comb {E : ℕ} {t : ℕ → ℤ} (h : 0 ≤ t 0) : f e bot ≤ comb E t := by
  rw [f_e_bot_eq_path]
  exact path_le_of_mem (toothWord_mem_comb (s := 0) (y := 0).mpr ⟨Nat.zero_le _, by simpa using h⟩)

/-! ## Bounded trees -/

/-- Bounded trees are closed under sublists of words. -/
theorem mem_boundedTree_of_sublist {M k : ℕ} {u w : Word} (h : u.Sublist w)
    (hw : w ∈ (boundedTree M k).constructorPaths) : u ∈ (boundedTree M k).constructorPaths := by
  rw [mem_boundedTree] at hw ⊢
  exact ⟨h.length_le.trans hw.1, (h.count_le 0).trans hw.2⟩

theorem mem_boundedTree_of_cons {M k : ℕ} {a : Fin 2} {w : Word}
    (h : a :: w ∈ (boundedTree M k).constructorPaths) : w ∈ (boundedTree M k).constructorPaths :=
  mem_boundedTree_of_sublist (List.sublist_cons_self a w) h

/-- A top-free tree whose addresses are short with few zeros lies below the bounded tree. -/
theorem le_boundedTree {t : Tree} {M k : ℕ} (ht : t.TopFree)
    (h : ∀ w ∈ t.constructorPaths, w.length ≤ M ∧ w.count 0 ≤ k) : t ≤ boundedTree M k :=
  le_of_subset ht fun w hw => (mem_boundedTree M k w).mpr (h w hw)

/-- The addresses of a tree below a bounded tree are addresses of the bounded tree. -/
theorem mem_boundedTree_of_le {t : Tree} {M k : ℕ} (h : t ≤ boundedTree M k) {w : Word}
    (hw : w ∈ t.constructorPaths) : w ∈ (boundedTree M k).constructorPaths :=
  (le_iff_constructorPaths_subset ((topFree_boundedTree M k).of_le h) (topFree_boundedTree M k)).mp
    h hw

/-- A spine join stays below a bounded tree. -/
theorem spineJoin_le_boundedTree {t : Tree} {M k : ℕ} (h : t ≤ boundedTree M k) :
    spineJoin t ≤ boundedTree M k :=
  le_of_subset (topFree_spineJoin _) fun u hu => by
    obtain ⟨a, ha⟩ := (mem_spineJoin t u).mp hu
    exact mem_boundedTree_of_sublist (List.sublist_append_right _ _) (mem_boundedTree_of_le h ha)

/-- A comb with teeth of length at most twice the stamp is a bounded tree. -/
theorem comb_le_boundedTree {E M k : ℕ} {t : ℕ → ℤ} (ht : ∀ s ≤ E, t s ≤ 2 * s)
    (hM : 3 * E + 1 ≤ M) (hk : 1 ≤ k) : comb E t ≤ boundedTree M k := by
  apply le_boundedTree (topFree_comb E t)
  intro w hw
  rcases (mem_comb E t w).mp hw with ⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · rw [length_ones, count_zero_eq_zero_of_isOnes (isOnes_ones i)]
    omega
  · have := ht s hs
    rw [length_toothWord, count_zero_toothWord]
    omega

/-- If every address of `X` lies in the bounded tree and the words below `0` lie in `a`, then
`X ≤ f(a, B)` for the bounded tree `B`. -/
theorem le_f_boundedTree {X a : Tree} {M k : ℕ} (hX : X.TopFree) (ha : a.TopFree)
    (hXB : X ≤ boundedTree M k) (h0 : ∀ w, 0 :: w ∈ X.constructorPaths → w ∈ a.constructorPaths) :
    X ≤ f a (boundedTree M k) := by
  rw [le_f_iff ha (topFree_boundedTree M k) hX]
  exact ⟨h0, fun w hw => mem_boundedTree_of_cons (mem_boundedTree_of_le hXB hw)⟩

/-- A bounded comb whose tooth at stamp `0` is the stub lies below `f(e, B)`. -/
theorem comb_le_f_e {E M k : ℕ} {t : ℕ → ℤ} (h : t 0 ≤ 0) (hB : comb E t ≤ boundedTree M k) :
    comb E t ≤ f e (boundedTree M k) := by
  apply le_f_boundedTree (topFree_comb E t) topFree_e hB
  intro w hw
  obtain ⟨y, hy, rfl⟩ := zero_cons_mem_comb.mp hw
  obtain rfl : y = 0 := by omega
  exact nil_mem_constructorPaths_e

/-- A bounded comb without tooth at stamp `0` lies below `f(⊥, B)`. -/
theorem comb_le_f_bot {E M k : ℕ} {t : ℕ → ℤ} (h : t 0 < 0) (hB : comb E t ≤ boundedTree M k) :
    comb E t ≤ f bot (boundedTree M k) := by
  apply le_f_boundedTree (topFree_comb E t) topFree_bot hB
  intro w hw
  obtain ⟨y, hy, rfl⟩ := zero_cons_mem_comb.mp hw
  omega

/-- The comb bound satisfies its guard. -/
theorem boundedTree_one_le (M : ℕ) : boundedTree M 1 ≤ f (path (ones M)) (boundedTree M 1) := by
  apply le_f_boundedTree (topFree_boundedTree M 1) (topFree_path _) le_rfl
  intro w hw
  rw [mem_boundedTree] at hw
  simp only [List.length_cons, List.count_cons_self] at hw
  obtain ⟨i, rfl⟩ := (isOnes_iff w).mp (isOnes_of_count_zero (by omega))
  rw [mem_constructorPaths_path]
  exact ones_prefix_ones_iff.mpr (by simp only [length_ones] at hw; omega)

/-- The sink satisfies its guard. -/
theorem boundedTree_two_le (M : ℕ) :
    boundedTree M 2 ≤ f (boundedTree M 1) (boundedTree M 2) := by
  apply le_f_boundedTree (topFree_boundedTree M 2) (topFree_boundedTree M 1) le_rfl
  intro w hw
  rw [mem_boundedTree] at hw ⊢
  simp only [List.length_cons, List.count_cons_self] at hw
  omega

/-! ## Selections -/

/-! ## Window clauses of combs -/

/-- The window set of a comb with tooth lengths `t` over a comb with tooth lengths `t'` consists
of the tooth words `1^s 0 1^y` with `t' s < y ≤ t (s + 1)`. If `t (s + 1)` is at most `t' s'` for
every later stamp `s'`, and `t (s + 1) - t' s < k` at every stamp, the window specification
`WindowSpec k` holds. -/
theorem windowSpec_comb {k E : ℕ} {t t' : ℕ → ℤ} (hk : 1 ≤ k)
    (honion : ∀ s s', s < s' → s' < E → t (s + 1) ≤ t' s')
    (hcard : ∀ s < E, t (s + 1) < t' s + k) :
    WindowSpec k (windowSet (comb E t) (comb E t')) := by
  have hmem : ∀ w ∈ windowSet (comb E t) (comb E t'),
      ∃ s < E, ∃ y : ℕ, (y : ℤ) ≤ t (s + 1) ∧ t' s < y ∧ w = toothWord s y := by
    rintro w ⟨h₁, h₂⟩
    rcases one_cons_mem_comb.mp h₁ with ⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
    · exact absurd (ones_mem_comb.mpr (by omega)) h₂
    · refine ⟨s, hs, y, hy, ?_, rfl⟩
      by_contra hn
      exact h₂ (toothWord_mem_comb.mpr ⟨by omega, by omega⟩)
  have htooth : ∀ s y, toothWord s y ∈ windowSet (comb E t) (comb E t') →
      s < E ∧ (y : ℤ) ≤ t (s + 1) ∧ t' s < y := by
    intro s y h
    obtain ⟨s', hs', y', hy', hlt, he⟩ := hmem _ h
    obtain ⟨rfl, rfl⟩ := toothWord_inj.mp he
    exact ⟨hs', hy', hlt⟩
  apply windowSpec_of_onion
  · intro w hw
    obtain ⟨s, -, y, -, -, rfl⟩ := hmem w hw
    exact ⟨s, y, rfl⟩
  · intro s s' y y' hss h h'
    obtain ⟨-, hy, -⟩ := htooth s y h
    obtain ⟨hs', -, hy'⟩ := htooth s' y' h'
    have := honion s s' hss hs'
    omega
  · intro s xs hxs hall
    have hstep : ∀ j (hj : j < k), xs ⟨0, by omega⟩ + j ≤ xs ⟨j, hj⟩ := by
      intro j
      induction j with
      | zero => intro hj; exact le_rfl
      | succ j ih =>
        intro hj
        have h₁ := ih (by omega)
        have h₂ : xs ⟨j, by omega⟩ < xs ⟨j + 1, hj⟩ := hxs (Fin.mk_lt_mk.mpr (by omega))
        omega
    obtain ⟨hs, -, h₀⟩ := htooth s _ (hall ⟨0, by omega⟩)
    obtain ⟨-, hlast, -⟩ := htooth s _ (hall ⟨k - 1, by omega⟩)
    have := hstep (k - 1) (by omega)
    have := hcard s hs
    omega

/-! ## Labels and occurrences -/

theorem startLabel_lt {P : Program} : startLabel < labelCount P := by
  simp only [labelCount, startLabel]
  omega

theorem buildLabel_lt {P : Program} : buildLabel < labelCount P := by
  simp only [labelCount, buildLabel]
  omega

theorem unwindLabel_lt {P : Program} : unwindLabel < labelCount P := by
  simp only [labelCount, unwindLabel]
  omega

theorem endLabel_lt {P : Program} : endLabel < labelCount P := by
  simp only [labelCount, endLabel]
  omega

/-- Every effect is at least `-1`. -/
theorem neg_one_le_effect {P : Program} (l : ℕ) (i : Fin 3) : -1 ≤ effect P l i := by
  rcases effect_mem (P := P) l i with h | h | h <;> omega

namespace ExactRun

variable {P : Program} (r : ExactRun P)

/-- The number of unwinding labels at the stamps `1, …, s`. -/
def unwound (s : ℕ) : ℕ := occurrences r.label unwindLabel s

/-- The number of build-up labels. -/
def builds : ℕ := occurrences r.label buildLabel r.last

/-- The length bound of the guards: every other honest witness has addresses of length at most
`m + 3E + 1`. -/
def guardLength : ℕ := labelCount P + 3 * r.last + 3

/-- The component of label `l`: the clock at the stamps with label `l`. -/
noncomputable def component (l : ℕ) : Tree :=
  comb r.last fun s => if r.label s = l then (s : ℤ) else -1

/-- The tooth length of counter `i` at stamp `s`. -/
def counterTooth (i : Fin 3) (s : ℕ) : ℤ := r.count s i + s

/-- The honest witnesses of the run. -/
noncomputable def honestWitnesses : ClockExistentials Tree where
  clock := comb r.last fun s => s
  chain := path (toothWord r.last r.last ++ [0])
  chainHead := path (toothWord r.last r.last)
  chainLoop := spineJoin (path (toothWord r.last r.last ++ [0]))
  labels := select (labelCount P) r.component bot
  counter i := comb r.last (r.counterTooth i)
  plusClass i := comb r.last fun s =>
    if 1 ≤ s ∧ effect P (r.label s) i = 1 then r.counterTooth i s else -1
  zeroClass i := comb r.last fun s =>
    if 1 ≤ s ∧ effect P (r.label s) i = 0 then r.counterTooth i s else -1
  unwind := comb r.last fun s => r.unwound s
  unwindPart := comb r.last fun s => if r.label s = unwindLabel then (r.unwound s : ℤ) else -1
  buildRay := path (ones r.builds)
  buildLoop := spineJoin (r.component buildLabel)
  ray := path (ones r.guardLength)
  combBound := boundedTree r.guardLength 1
  sink := boundedTree r.guardLength 2

/-! ## The values of the honest witnesses -/

theorem honestWitnesses_clock : r.honestWitnesses.clock = comb r.last fun s => (s : ℤ) := rfl

theorem honestWitnesses_chain :
    r.honestWitnesses.chain = path (toothWord r.last r.last ++ [0]) := rfl

theorem honestWitnesses_chainHead : r.honestWitnesses.chainHead = path (toothWord r.last r.last) :=
  rfl

theorem honestWitnesses_chainLoop :
    r.honestWitnesses.chainLoop = spineJoin (path (toothWord r.last r.last ++ [0])) := rfl

theorem honestWitnesses_labels :
    r.honestWitnesses.labels = select (labelCount P) r.component bot := rfl

theorem honestWitnesses_counter (i : Fin 3) :
    r.honestWitnesses.counter i = comb r.last (r.counterTooth i) := rfl

theorem honestWitnesses_plusClass (i : Fin 3) :
    r.honestWitnesses.plusClass i = comb r.last fun s =>
      if 1 ≤ s ∧ effect P (r.label s) i = 1 then r.counterTooth i s else -1 := rfl

theorem honestWitnesses_zeroClass (i : Fin 3) :
    r.honestWitnesses.zeroClass i = comb r.last fun s =>
      if 1 ≤ s ∧ effect P (r.label s) i = 0 then r.counterTooth i s else -1 := rfl

theorem honestWitnesses_unwind :
    r.honestWitnesses.unwind = comb r.last fun s => (r.unwound s : ℤ) := rfl

theorem honestWitnesses_unwindPart :
    r.honestWitnesses.unwindPart =
      comb r.last fun s => if r.label s = unwindLabel then (r.unwound s : ℤ) else -1 := rfl

theorem honestWitnesses_buildRay : r.honestWitnesses.buildRay = path (ones r.builds) := rfl

theorem honestWitnesses_buildLoop :
    r.honestWitnesses.buildLoop = spineJoin (r.component buildLabel) := rfl

theorem honestWitnesses_ray : r.honestWitnesses.ray = path (ones r.guardLength) := rfl

theorem honestWitnesses_combBound : r.honestWitnesses.combBound = boundedTree r.guardLength 1 := rfl

theorem honestWitnesses_sink : r.honestWitnesses.sink = boundedTree r.guardLength 2 := rfl

/-! ## Facts about the run -/

/-- The labels of an exact run are labels of the machine. -/
theorem label_lt {s : ℕ} (hs : s ≤ r.last) : r.label s < labelCount P :=
  label_lt_labelCount r.label_zero r.isSuccessor_label hs

/-- Only stamp `0` carries the start label. -/
theorem label_ne_startLabel {s : ℕ} (h1 : 1 ≤ s) (hs : s ≤ r.last) : r.label s ≠ startLabel := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  intro h
  have hn := r.isSuccessor_label s' (by omega)
  rw [h, isSuccessor_start] at hn
  exact Bool.false_ne_true hn

/-- The tooth of a counter comb grows by the effect of the next label plus one. -/
theorem counterTooth_succ (i : Fin 3) {s : ℕ} (hs : s < r.last) :
    r.counterTooth i (s + 1) = r.counterTooth i s + effect P (r.label (s + 1)) i + 1 := by
  unfold counterTooth
  have := r.count_succ s hs i
  push_cast
  omega

theorem counterTooth_nonneg (i : Fin 3) (s : ℕ) : 0 ≤ r.counterTooth i s := by
  unfold counterTooth
  omega

/-- The tooth of a counter comb at stamp `s` is at most `2s` long. -/
theorem counterTooth_le (i : Fin 3) {s : ℕ} (hs : s ≤ r.last) : r.counterTooth i s ≤ 2 * s := by
  unfold counterTooth
  have := r.count_le s i hs
  omega

/-- The counter teeth do not shrink: a counter decreases by at most one per stamp. -/
theorem counterTooth_mono (i : Fin 3) {s s' : ℕ} (h : s ≤ s') (hs' : s' ≤ r.last) :
    r.counterTooth i s ≤ r.counterTooth i s' := by
  induction s' with
  | zero =>
    obtain rfl : s = 0 := by omega
    exact le_rfl
  | succ s' ih =>
    rcases h.lt_or_eq with h | h
    · have h₁ := ih (by omega) (by omega)
      have h₂ := r.counterTooth_succ i (s := s') (by omega)
      have h₃ := neg_one_le_effect (P := P) (r.label (s' + 1)) i
      omega
    · rw [h]

theorem unwound_succ (s : ℕ) :
    r.unwound (s + 1) = r.unwound s + if r.label (s + 1) = unwindLabel then 1 else 0 :=
  occurrences_succ _ _ _

theorem unwound_zero : r.unwound 0 = 0 := rfl

theorem unwound_le (s : ℕ) : r.unwound s ≤ s := occurrences_le _ _ _

theorem unwound_mono {s s' : ℕ} (h : s ≤ s') : r.unwound s ≤ r.unwound s' :=
  occurrences_mono _ _ h

theorem builds_le : r.builds ≤ r.last := occurrences_le _ _ _

/-! ## Components and the label tree -/

theorem topFree_component (l : ℕ) : (r.component l).TopFree := topFree_comb _ _

theorem finite_component (l : ℕ) : (r.component l).IsFinite := finite_comb _ _

/-- The addresses of a component: the spine words and the teeth of the clock at the stamps with
the given label. -/
theorem mem_component (l : ℕ) (w : Word) :
    w ∈ (r.component l).constructorPaths ↔ (∃ i ≤ r.last, w = ones i) ∨
      ∃ s ≤ r.last, r.label s = l ∧ ∃ y ≤ s, w = toothWord s y := by
  rw [component, mem_comb]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨s, hs, y, hy, rfl⟩
    split_ifs at hy with h
    · exact ⟨s, hs, h, y, by omega, rfl⟩
    · omega
  · rintro ⟨s, hs, h, y, hy, rfl⟩
    refine ⟨s, hs, y, ?_, rfl⟩
    simp only [h, ↓reduceIte]
    omega

theorem ones_mem_component {l i : ℕ} (hi : i ≤ r.last) :
    ones i ∈ (r.component l).constructorPaths :=
  ones_mem_comb.mpr hi

/-- The tooth words of a component: those of the clock at the stamps with its label. -/
theorem toothWord_mem_component {l s y : ℕ} :
    toothWord s y ∈ (r.component l).constructorPaths ↔ s ≤ r.last ∧ r.label s = l ∧ y ≤ s := by
  rw [component, toothWord_mem_comb]
  split_ifs with h
  · constructor
    · rintro ⟨hs, hy⟩
      exact ⟨hs, h, by omega⟩
    · rintro ⟨hs, -, hy⟩
      exact ⟨hs, by omega⟩
  · constructor
    · rintro ⟨-, hy⟩
      omega
    · rintro ⟨-, hl, -⟩
      exact absurd hl h

/-- Every component lies in the clock. -/
theorem component_subset_clock (l : ℕ) :
    (r.component l).constructorPaths ⊆ r.honestWitnesses.clock.constructorPaths := by
  apply comb_subset
  intro s _
  split_ifs <;> omega

theorem component_le_boundedTree (l : ℕ) {M k : ℕ} (hM : 3 * r.last + 1 ≤ M) (hk : 1 ≤ k) :
    r.component l ≤ boundedTree M k :=
  comb_le_boundedTree (fun s _ => by split_ifs <;> omega) hM hk

/-- The addresses of the label tree: the spine words `1ˡ` and the words `1ˡ 0 u` with `u` an
address of the component of `l`, for `l < m`. -/
theorem mem_labels (w : Word) :
    w ∈ r.honestWitnesses.labels.constructorPaths ↔ (∃ l < labelCount P, w = ones l) ∨
      ∃ l < labelCount P, ∃ u ∈ (r.component l).constructorPaths, w = ones l ++ 0 :: u := by
  have h := mem_constructorPaths_select (k := labelCount P) (a := r.component) (t := bot)
    r.topFree_component topFree_bot w
  simp only [not_mem_constructorPaths_bot, false_and, exists_false, or_false] at h
  exact h

theorem ones_mem_labels {l : ℕ} (hl : l < labelCount P) :
    ones l ∈ r.honestWitnesses.labels.constructorPaths :=
  (r.mem_labels _).mpr (Or.inl ⟨l, hl, rfl⟩)

/-- The words `1ˡ 0 u` of the label tree are those with `l < m` and `u` an address of the
component of `l`. -/
theorem ones_append_zero_cons_mem_labels (l : ℕ) (u : Word) :
    ones l ++ 0 :: u ∈ r.honestWitnesses.labels.constructorPaths ↔
      l < labelCount P ∧ u ∈ (r.component l).constructorPaths := by
  rw [mem_labels]
  constructor
  · rintro (⟨l', -, h⟩ | ⟨l', hl', u', hu', h⟩)
    · exact absurd (h ▸ isOnes_ones l') (not_isOnes_ones_append_zero_cons l u)
    · obtain ⟨rfl, rfl⟩ := ones_append_zero_cons_inj.mp h
      exact ⟨hl', hu'⟩
  · rintro ⟨hl, hu⟩
    exact Or.inr ⟨l, hl, u, hu, rfl⟩

theorem topFree_labels : r.honestWitnesses.labels.TopFree :=
  topFree_select r.topFree_component topFree_bot

/-- The subtree of the label tree at `1ˡ 0` is the component of `l`. -/
theorem residual_labels {l : ℕ} (hl : l < labelCount P) :
    r.honestWitnesses.labels.residual (ones l ++ [0]) = r.component l := by
  apply topFree_ext (topFree_residual _ _) (r.topFree_component l)
  ext u
  rw [mem_residual, List.append_assoc, List.singleton_append, ones_append_zero_cons_mem_labels]
  exact and_iff_right hl

/-- The label tree has no address `1ᵐ`. -/
theorem residual_labels_le_bot : r.honestWitnesses.labels.residual (ones (labelCount P)) ≤ bot :=
  le_of_subset (topFree_residual _ _) fun u hu => by
    rw [mem_residual, mem_labels] at hu
    rcases hu with ⟨l, hl, h⟩ | ⟨l, hl, v, -, h⟩
    · have := congrArg List.length h
      simp only [List.length_append, length_ones] at this
      omega
    · exact absurd h.symm (ones_append_zero_cons_ne_ones_append hl v u)

/-! ## Bounds of the honest witnesses -/

theorem three_mul_last_add_one_le : 3 * r.last + 1 ≤ r.guardLength := by
  unfold guardLength; omega

/-- The chain word `1^E 0 1^E 0` has two zeros. -/
theorem count_zero_chainWord : (toothWord r.last r.last ++ [0]).count 0 = 2 := by
  rw [List.count_append, count_zero_toothWord]
  simp

theorem chainWord_mem_sink :
    toothWord r.last r.last ++ [0] ∈ (boundedTree r.guardLength 2).constructorPaths := by
  rw [mem_boundedTree, r.count_zero_chainWord]
  simp only [List.length_append, length_toothWord, List.length_singleton]
  unfold guardLength labelCount
  omega

/-- The clock lies below the sink. -/
theorem clock_le_sink : r.honestWitnesses.clock ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s _ => by omega) r.three_mul_last_add_one_le (by omega)

theorem counter_le_sink (i : Fin 3) : r.honestWitnesses.counter i ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s hs => r.counterTooth_le i hs) r.three_mul_last_add_one_le (by omega)

theorem plusClass_le_sink (i : Fin 3) :
    r.honestWitnesses.plusClass i ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s hs => by
    have := r.counterTooth_le i hs
    split_ifs <;> omega) r.three_mul_last_add_one_le (by omega)

theorem zeroClass_le_sink (i : Fin 3) :
    r.honestWitnesses.zeroClass i ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s hs => by
    have := r.counterTooth_le i hs
    split_ifs <;> omega) r.three_mul_last_add_one_le (by omega)

theorem unwind_le_sink : r.honestWitnesses.unwind ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s _ => by have := r.unwound_le s; omega) r.three_mul_last_add_one_le
    (by omega)

theorem unwindPart_le_sink : r.honestWitnesses.unwindPart ≤ boundedTree r.guardLength 2 :=
  comb_le_boundedTree (fun s _ => by
    have := r.unwound_le s
    split_ifs <;> omega) r.three_mul_last_add_one_le (by omega)

theorem labels_le_sink : r.honestWitnesses.labels ≤ boundedTree r.guardLength 2 := by
  apply le_boundedTree r.topFree_labels
  intro w hw
  rcases (r.mem_labels w).mp hw with ⟨l, hl, rfl⟩ | ⟨l, hl, u, hu, rfl⟩
  · rw [length_ones, count_zero_eq_zero_of_isOnes (isOnes_ones l)]
    unfold guardLength
    omega
  · have hu' := (mem_boundedTree _ _ _).mp
      (mem_boundedTree_of_le (r.component_le_boundedTree l (le_refl (3 * r.last + 1)) le_rfl) hu)
    rw [count_zero_ones_append_zero_cons]
    simp only [List.length_append, length_ones, List.length_cons]
    unfold guardLength
    omega

/-- Every honest witness other than the guards lies below the sink. -/
theorem honest_le_sink : ∀ t ∈ r.honestWitnesses.guarded, t ≤ boundedTree r.guardLength 2 := by
  have hchain := r.chainWord_mem_sink
  intro t ht
  simp only [ClockExistentials.guarded, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact r.clock_le_sink
  · exact path_le_of_mem hchain
  · exact path_le_of_mem (mem_constructorPaths_of_prefix (List.prefix_append _ _) hchain)
  · exact spineJoin_le_boundedTree (path_le_of_mem hchain)
  · exact r.labels_le_sink
  · exact r.counter_le_sink 0
  · exact r.counter_le_sink 1
  · exact r.counter_le_sink 2
  · exact r.plusClass_le_sink 0
  · exact r.plusClass_le_sink 1
  · exact r.plusClass_le_sink 2
  · exact r.zeroClass_le_sink 0
  · exact r.zeroClass_le_sink 1
  · exact r.zeroClass_le_sink 2
  · exact r.unwind_le_sink
  · exact r.unwindPart_le_sink
  · apply path_le_of_mem
    rw [mem_boundedTree, length_ones, count_zero_eq_zero_of_isOnes (isOnes_ones _)]
    have := r.builds_le
    have := r.three_mul_last_add_one_le
    omega
  · exact spineJoin_le_boundedTree (r.component_le_boundedTree _ r.three_mul_last_add_one_le
      (by omega))

/-- The loop of the chain: removing leading ones and then a zero from an address of the chain
gives an address of the chain. -/
theorem chainLoop_le_f :
    spineJoin (path (toothWord r.last r.last ++ [0])) ≤
      f (path (toothWord r.last r.last ++ [0]))
        (spineJoin (path (toothWord r.last r.last ++ [0]))) := by
  rw [le_f_iff (topFree_path _) (topFree_spineJoin _) (topFree_spineJoin _)]
  have hw : toothWord r.last r.last ++ [0] = ones r.last ++ 0 :: (ones r.last ++ [0]) := by
    simp [toothWord]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, ha⟩ := (mem_spineJoin _ _).mp hu
    rw [mem_constructorPaths_path, hw] at ha
    rw [mem_constructorPaths_path, hw]
    rcases prefix_ones_append_zero_cons_iff.mp ha with ⟨i, -, h⟩ | ⟨v, hv, h⟩
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons a u)
    · obtain ⟨-, rfl⟩ := ones_append_zero_cons_inj.mp h
      refine hv.trans ((List.prefix_append_right_inj (ones r.last)).mpr ?_)
      exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
  · obtain ⟨a, ha⟩ := (mem_spineJoin _ _).mp hu
    exact (mem_spineJoin _ _).mpr ⟨a + 1, by rwa [ones_succ', List.append_assoc]⟩

/-- The loop of the build-up component: the teeth of the build-up component are not longer than
the number of build-up labels. -/
theorem buildLoop_le_f :
    spineJoin (r.component buildLabel) ≤
      f (path (ones r.builds)) (spineJoin (r.component buildLabel)) := by
  rw [le_f_iff (topFree_path _) (topFree_spineJoin _) (topFree_spineJoin _)]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, ha⟩ := (mem_spineJoin _ _).mp hu
    rw [mem_component] at ha
    rcases ha with ⟨i, -, h⟩ | ⟨s, hs, hl, y, hy, h⟩
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_ones_append_zero_cons a u)
    · obtain ⟨-, rfl⟩ := ones_append_zero_cons_inj.mp h
      have := ((r.label_eq_buildLabel_iff hs).mp hl).2
      rw [mem_constructorPaths_path]
      exact ones_prefix_ones_iff.mpr (by unfold builds; omega)
  · obtain ⟨a, ha⟩ := (mem_spineJoin _ _).mp hu
    exact (mem_spineJoin _ _).mpr ⟨a + 1, by rwa [ones_succ', List.append_assoc]⟩

/-! ## Domain, guards and root conditions -/

/-- The honest witnesses are finite and top-free. -/
theorem honest_finite : ∀ t ∈ r.honestWitnesses.toList, t.IsFinite ∧ t.TopFree := by
  intro t ht
  simp only [ClockExistentials.toList, ClockExistentials.guarded, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  have hlabels : r.honestWitnesses.labels.IsFinite :=
    finite_select r.finite_component finite_bot
  rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
  all_goals first
    | exact ⟨finite_comb _ _, topFree_comb _ _⟩
    | exact ⟨finite_path _, topFree_path _⟩
    | exact ⟨finite_spineJoin (finite_path _) (topFree_path _), topFree_spineJoin _⟩
    | exact ⟨finite_spineJoin (finite_comb _ _) (topFree_comb _ _), topFree_spineJoin _⟩
    | exact ⟨hlabels, r.topFree_labels⟩
    | exact ⟨finite_boundedTree _ _, topFree_boundedTree _ _⟩

/-- The honest witnesses lie in every domain. -/
theorem honest_domain (c : TreeClass) (top : Bool) :
    r.honestWitnesses.Forall (Domain c top) := fun t ht =>
  domain_of_isFinite (r.honest_finite t ht).1 (r.honest_finite t ht).2

/-- The honest witnesses satisfy the guards. -/
theorem honest_guarded : Guarded r.honestWitnesses := by
  refine ⟨path_ones_le _, boundedTree_one_le _, boundedTree_two_le _, ?_⟩
  exact r.honest_le_sink

/-- The honest witnesses satisfy the root conditions. -/
theorem honest_root : RootConditions (labelCount P) r.honestWitnesses := by
  have hcomp (l : ℕ) : r.component l ≤ boundedTree r.guardLength 2 :=
    r.component_le_boundedTree l r.three_mul_last_add_one_le (by omega)
  exact {
    clock_lower := f_e_bot_le_comb (by simp)
    clock_upper := comb_le_f_e (by simp) r.clock_le_sink
    labels_start := by
      show pack startLabel (f e bot) ≤ r.honestWitnesses.labels
      rw [f_e_bot_eq_path]
      exact pack_path_le (w := toothWord 0 0) r.topFree_labels
        ((r.ones_append_zero_cons_mem_labels _ _).mpr ⟨startLabel_lt,
          r.toothWord_mem_component.mpr ⟨Nat.zero_le _, r.label_zero, le_rfl⟩⟩)
    labels_clock := by
      rw [le_select_iff r.topFree_labels]
      refine ⟨fun l hl => ?_, r.residual_labels_le_bot⟩
      rw [r.residual_labels hl]
      exact le_of_subset (r.topFree_component l) (r.component_subset_clock l)
    labels_left := by
      rw [le_select_iff r.topFree_labels]
      refine ⟨fun l hl => ?_, r.residual_labels_le_bot⟩
      rw [r.residual_labels hl]
      split_ifs with h
      · exact hcomp l
      · refine comb_le_f_bot ?_ (hcomp l)
        rw [r.label_zero]
        simp only [Ne.symm h, ↓reduceIte]
        omega
    chain_le_loop := le_of_subset (topFree_path _) fun u hu => (mem_spineJoin _ _).mpr ⟨0, hu⟩
    chainLoop_le := r.chainLoop_le_f
    labels_end := pack_path_le r.topFree_labels
      ((r.ones_append_zero_cons_mem_labels _ _).mpr ⟨endLabel_lt,
        r.toothWord_mem_component.mpr ⟨le_rfl, r.label_last, le_rfl⟩⟩)
    counter_lower := fun i => f_e_bot_le_comb (r.counterTooth_nonneg i 0)
    counter_upper := fun i =>
      comb_le_f_e (by simp [counterTooth, r.count_zero]) (r.counter_le_sink i)
    clock_le_counter := fun i => comb_mono fun s _ => by
      have := r.counterTooth_nonneg i s
      simp only [counterTooth]
      omega
    plusClass_le := fun i => comb_le_f_bot (by simp) (r.plusClass_le_sink i)
    zeroClass_le := fun i => comb_le_f_bot (by simp) (r.zeroClass_le_sink i)
    unwind_lower := f_e_bot_le_comb (by simp)
    unwind_upper := comb_le_f_e (by simp [r.unwound_zero]) r.unwind_le_sink
    unwindPart_le := comb_le_f_bot (by simp [r.label_zero]) r.unwindPart_le_sink
    labels_unwind := by
      rw [honestWitnesses_unwindPart, pack_le_iff (topFree_comb _ _) r.topFree_labels]
      refine ⟨fun i hi => r.ones_mem_labels (lt_of_le_of_lt hi unwindLabel_lt), fun w hw => ?_⟩
      refine (r.ones_append_zero_cons_mem_labels _ _).mpr ⟨unwindLabel_lt, comb_subset ?_ hw⟩
      intro s _
      have := r.unwound_le s
      split_ifs <;> omega
    labels_build := by
      apply le_of_subset r.topFree_labels
      intro w hw
      have hwB := mem_boundedTree_of_le r.labels_le_sink hw
      rcases w with _ | ⟨a, w⟩
      · exact nil_mem_constructorPaths_f _ _
      rcases letter_eq_zero_or_eq_one a with rfl | rfl
      · exact (zero_cons_mem_constructorPaths_f _ _ _).mpr (mem_boundedTree_of_cons hwB)
      rw [one_cons_mem_constructorPaths_f]
      rcases w with _ | ⟨b, v⟩
      · exact nil_mem_constructorPaths_f _ _
      rcases letter_eq_zero_or_eq_one b with rfl | rfl
      · rw [zero_cons_mem_constructorPaths_f, honestWitnesses_buildLoop, mem_spineJoin]
        have h1 : ones buildLabel ++ 0 :: v ∈ r.honestWitnesses.labels.constructorPaths := hw
        exact ⟨0, ((r.ones_append_zero_cons_mem_labels _ _).mp h1).2⟩
      · rw [one_cons_mem_constructorPaths_f]
        exact mem_boundedTree_of_cons (mem_boundedTree_of_cons hwB)
    buildLoop_le := r.buildLoop_le_f
    chain_not_le_head := by
      show ¬path (toothWord r.last r.last ++ [0]) ≤ path (toothWord r.last r.last)
      rw [path_le_iff (topFree_path _), mem_constructorPaths_path]
      intro h
      have := h.length_le
      simp at this }

/-! ## The specification of each clause family -/

/-- The spine words up to the last stamp lie in the ray. -/
theorem mem_ray_of_le {i : ℕ} (hi : i ≤ r.last) :
    ones i ∈ r.honestWitnesses.ray.constructorPaths := by
  rw [honestWitnesses_ray, mem_constructorPaths_path]
  exact ones_prefix_ones_iff.mpr (by unfold guardLength; omega)

/-- The chain is the set of prefixes of one word. -/
theorem honest_chain_spec : (chainClause r.honestWitnesses).Spec := by
  rw [chainClause_spec_iff]
  intro a ha b hb
  rw [honestWitnesses_chain, mem_constructorPaths_path] at ha hb
  exact List.prefix_or_prefix_of_prefix ha hb

/-- The words of the chain with at most one zero are the prefixes of `1^E 0 1^E`. -/
theorem honest_chainHead_spec : (chainHeadClause r.honestWitnesses).Spec := by
  rw [chainHeadClause_spec_iff]
  intro w hw hshape
  rw [honestWitnesses_chain, mem_constructorPaths_path] at hw
  rw [honestWitnesses_chainHead, mem_constructorPaths_path]
  rcases List.prefix_concat_iff.mp hw with h | h
  · exfalso
    have hc : w.count 0 = 2 := h ▸ r.count_zero_chainWord
    rcases hshape with h' | ⟨j, i, rfl⟩
    · rw [count_zero_eq_zero_of_isOnes h'] at hc
      omega
    · rw [count_zero_toothWord] at hc
      omega
  · exact h

/-- The tooth of the clock grows by one from each stamp to the next. -/
theorem honest_clock_spec : (clockClause r.honestWitnesses).Spec := by
  rw [clockClause_spec_iff, honestWitnesses_clock]
  apply windowSpec_comb (by norm_num)
  · intro s s' hss _
    push_cast
    omega
  · intro s _
    push_cast
    omega

/-- The spine words and stubs of the right child of the clock lie in the clock. -/
theorem honest_gap_spec : (gapClause r.honestWitnesses).Spec := by
  rw [gapClause_spec_iff]
  intro w hw hshape
  rw [honestWitnesses_clock] at hw ⊢
  rcases one_cons_mem_comb.mp hw with ⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact ones_mem_comb.mpr (by omega)
  · rcases hshape with h | ⟨j, hj⟩
    · exact absurd h (not_isOnes_toothWord s y)
    · rw [← toothWord_zero_right] at hj
      obtain ⟨rfl, rfl⟩ := toothWord_inj.mp hj
      exact toothWord_mem_comb.mpr ⟨by omega, by simp⟩

/-- The component of the end label and the right child of the clock share only spine words. -/
theorem honest_endLast_spec : (endLastClause r.honestWitnesses).Spec := by
  rw [endLastClause_spec_iff]
  intro w hL hD
  rw [r.ones_append_zero_cons_mem_labels, r.mem_component] at hL
  rw [honestWitnesses_clock, one_cons_mem_comb] at hD
  rcases hL with ⟨-, ⟨i, hi, rfl⟩ | ⟨s, hs, hl, y, -, rfl⟩⟩
  · exact r.mem_ray_of_le hi
  · have hsE : s = r.last := (r.label_eq_endLabel_iff hs).mp hl
    rcases hD with ⟨i, -, h⟩ | ⟨s', hs', y', -, h⟩
    · exact absurd h (toothWord_ne_ones s y i)
    · obtain ⟨rfl, -⟩ := toothWord_inj.mp h
      omega

/-- Every address of the clock lies in the component of the label of its stamp. -/
theorem honest_cover_spec : (coverClause P r.honestWitnesses).Spec := by
  rw [coverClause_spec_iff]
  intro w hw
  rw [honestWitnesses_clock, mem_comb] at hw
  rcases hw with ⟨i, hi, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact ⟨startLabel, startLabel_lt,
      (r.ones_append_zero_cons_mem_labels _ _).mpr ⟨startLabel_lt, r.ones_mem_component hi⟩⟩
  · refine ⟨r.label s, r.label_lt hs, (r.ones_append_zero_cons_mem_labels _ _).mpr
      ⟨r.label_lt hs, r.toothWord_mem_component.mpr ⟨hs, rfl, ?_⟩⟩⟩
    omega

/-- Two components share only spine words. -/
theorem honest_unique_spec {l l' : ℕ} (hl : l < l') :
    (uniqueClause r.honestWitnesses l l').Spec := by
  rw [uniqueClause_spec_iff]
  intro w h₁ h₂
  rw [r.ones_append_zero_cons_mem_labels, r.mem_component] at h₁ h₂
  rcases h₁ with ⟨-, ⟨i, hi, rfl⟩ | ⟨s, -, hls, y, -, rfl⟩⟩
  · exact r.mem_ray_of_le hi
  · rcases h₂ with ⟨-, ⟨i, -, h⟩ | ⟨s', -, hls', y', -, h⟩⟩
    · exact absurd h (toothWord_ne_ones s y i)
    · obtain ⟨rfl, rfl⟩ := toothWord_inj.mp h
      omega

/-- The teeth of the component of a label continue, one stamp later, in the component of the
next label. -/
theorem honest_transition_spec {l : ℕ} (hl : l < labelCount P) (hend : l ≠ endLabel) :
    (transitionClause P r.honestWitnesses l).Spec := by
  rw [transitionClause_spec_iff]
  intro w hw
  rw [r.ones_append_zero_cons_mem_labels, and_iff_right hl, r.mem_component] at hw
  rcases hw with ⟨i, hi, rfl⟩ | ⟨s, hs, hls, y, hy, rfl⟩
  · exact Or.inl (r.mem_ray_of_le hi)
  · right
    have hsE : s < r.last := by
      rcases hs.lt_or_eq with h | h
      · exact h
      · subst h
        exact absurd (hls ▸ r.label_last) hend
    refine ⟨r.label (s + 1), r.label_lt (by omega), hls ▸ r.isSuccessor_label s hsE, ?_⟩
    rw [r.ones_append_zero_cons_mem_labels]
    exact ⟨r.label_lt (by omega),
      r.toothWord_mem_component (s := s + 1).mpr ⟨by omega, rfl, by omega⟩⟩

/-- A new tooth word of a counter comb lies in the class comb of the effect of the label. -/
theorem honest_counterStep_spec (i : Fin 3) : (counterStepClause r.honestWitnesses i).Spec := by
  rw [counterStepClause_spec_iff]
  intro w hw
  rw [honestWitnesses_counter] at hw ⊢
  rw [honestWitnesses_plusClass, honestWitnesses_zeroClass]
  rcases one_cons_mem_comb.mp hw with ⟨j, hj, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact Or.inl (ones_mem_comb.mpr (by omega))
  · by_cases hys : (y : ℤ) ≤ r.counterTooth i s
    · exact Or.inl (toothWord_mem_comb.mpr ⟨by omega, hys⟩)
    · have hsucc := r.counterTooth_succ i hs
      right
      show toothWord (s + 1) y ∈ _ ∨ toothWord (s + 1) y ∈ _
      rw [toothWord_mem_comb, toothWord_mem_comb]
      rcases effect_mem (P := P) (r.label (s + 1)) i with he | he | he
      · omega
      · right
        simp only [he, le_add_iff_nonneg_left, zero_le, true_and, ↓reduceIte]
        exact ⟨by omega, hy⟩
      · left
        simp only [he, le_add_iff_nonneg_left, zero_le, true_and, ↓reduceIte]
        exact ⟨by omega, hy⟩

/-- The keeping class comb adds at most one tooth word per stamp. -/
theorem honest_zeroWindow_spec (i : Fin 3) : (zeroWindowClause r.honestWitnesses i).Spec := by
  rw [zeroWindowClause_spec_iff, honestWitnesses_zeroClass, honestWitnesses_counter]
  apply windowSpec_comb (by norm_num)
  · intro s s' hss hs'
    have hm := r.counterTooth_mono i (show s + 1 ≤ s' by omega) (by omega)
    have h₀ := r.counterTooth_nonneg i s'
    split_ifs <;> omega
  · intro s hs
    have hsucc := r.counterTooth_succ i hs
    have h₀ := r.counterTooth_nonneg i s
    split_ifs with h
    · rw [h.2] at hsucc
      push_cast
      omega
    · push_cast
      omega

/-- The increasing class comb adds at most two tooth words per stamp. -/
theorem honest_plusWindow_spec (i : Fin 3) : (plusWindowClause r.honestWitnesses i).Spec := by
  rw [plusWindowClause_spec_iff, honestWitnesses_plusClass, honestWitnesses_counter]
  apply windowSpec_comb (by norm_num)
  · intro s s' hss hs'
    have hm := r.counterTooth_mono i (show s + 1 ≤ s' by omega) (by omega)
    have h₀ := r.counterTooth_nonneg i s'
    split_ifs <;> omega
  · intro s hs
    have hsucc := r.counterTooth_succ i hs
    have h₀ := r.counterTooth_nonneg i s
    split_ifs with h
    · rw [h.2] at hsucc
      push_cast
      omega
    · push_cast
      omega

/-- The stubs of a class comb lie at stamps whose label changes the counter by `κ`. -/
theorem honest_classLabel_spec (i : Fin 3) (κ : ℤ) :
    (classLabelClause P r.honestWitnesses i κ (comb r.last fun s =>
      if 1 ≤ s ∧ effect P (r.label s) i = κ then r.counterTooth i s else -1)).Spec := by
  rw [classLabelClause_spec_iff]
  intro w hw hshape
  rw [mem_comb] at hw
  rcases hw with ⟨j, hj, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact Or.inl (r.mem_ray_of_le hj)
  · right
    split_ifs at hy with h
    · rcases hshape with h' | ⟨j, hj⟩
      · exact absurd h' (not_isOnes_toothWord s y)
      · rw [← toothWord_zero_right] at hj
        obtain ⟨rfl, rfl⟩ := toothWord_inj.mp hj
        refine ⟨r.label s, r.label_lt hs, ⟨r.label_ne_startLabel h.1 hs, h.2⟩, ?_⟩
        rw [r.ones_append_zero_cons_mem_labels]
        exact ⟨r.label_lt hs, r.toothWord_mem_component.mpr ⟨hs, rfl, Nat.zero_le _⟩⟩
    · omega

/-- The stubs of the increasing class comb lie at stamps whose label increases the counter. -/
theorem honest_plusClassLabel_spec (i : Fin 3) :
    (classLabelClause P r.honestWitnesses i 1 (r.honestWitnesses.plusClass i)).Spec := by
  exact r.honest_classLabel_spec i 1

/-- The stubs of the keeping class comb lie at stamps whose label keeps the counter. -/
theorem honest_zeroClassLabel_spec (i : Fin 3) :
    (classLabelClause P r.honestWitnesses i 0 (r.honestWitnesses.zeroClass i)).Spec := by
  exact r.honest_classLabel_spec i 0

/-- Before a zero branch testing counter `c`, the tooth of counter comb `c` is that of the
clock. -/
theorem honest_zeroTest_spec {μ : ℕ} {c : Fin 2} (hc : zeroTest P μ = some c) :
    (zeroTestClause r.honestWitnesses μ c).Spec := by
  rw [zeroTestClause_spec_iff]
  intro w hC hL
  rw [r.ones_append_zero_cons_mem_labels] at hL
  obtain ⟨-, hL⟩ := hL
  rw [honestWitnesses_counter, mem_comb] at hC
  rw [honestWitnesses_clock]
  rcases hC with ⟨j, hj, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact ones_mem_comb.mpr hj
  · have hL' : toothWord (s + 1) y ∈ (r.component μ).constructorPaths := hL
    obtain ⟨hs₁, hlab, hys⟩ := r.toothWord_mem_component.mp hL'
    have hz := r.count_eq_zero s (by omega) c (by rw [hlab]; exact hc)
    simp only [counterTooth, hz] at hy
    exact toothWord_mem_comb.mpr ⟨hs, by push_cast at hy ⊢; omega⟩

/-- A new tooth word of the unwinding comb lies in its unwinding part. -/
theorem honest_unwindStep_spec : (unwindStepClause r.honestWitnesses).Spec := by
  rw [unwindStepClause_spec_iff]
  intro w hw
  rw [honestWitnesses_unwind] at hw ⊢
  rw [honestWitnesses_unwindPart]
  rcases one_cons_mem_comb.mp hw with ⟨j, hj, rfl⟩ | ⟨s, hs, y, hy, rfl⟩
  · exact Or.inl (ones_mem_comb.mpr (by omega))
  · have hsucc := r.unwound_succ s
    by_cases hys : y ≤ r.unwound s
    · exact Or.inl (toothWord_mem_comb.mpr ⟨by omega, by exact_mod_cast hys⟩)
    · right
      show toothWord (s + 1) y ∈ _
      rw [toothWord_mem_comb]
      by_cases hl : r.label (s + 1) = unwindLabel
      · simp only [hl, ↓reduceIte]
        exact ⟨by omega, hy⟩
      · simp only [hl, ↓reduceIte] at hsucc
        omega

/-- The unwinding part adds at most one tooth word per stamp. -/
theorem honest_unwindWindow_spec : (unwindWindowClause r.honestWitnesses).Spec := by
  rw [unwindWindowClause_spec_iff, honestWitnesses_unwindPart, honestWitnesses_unwind]
  apply windowSpec_comb (by norm_num)
  · intro s s' hss _
    have hm := r.unwound_mono (show s + 1 ≤ s' by omega)
    split_ifs <;> omega
  · intro s _
    have hsucc := r.unwound_succ s
    split_ifs with h
    · simp only [h, ↓reduceIte] at hsucc
      push_cast
      omega
    · push_cast
      omega

/-- The unwinding bound uses the balance of the run: the ray `N` has the length of the number
of build-up labels, and the tails of the unwinding comb reach the number of unwinding
labels. -/
theorem honest_unwindBound_spec (hb : r.Balanced) :
    (unwindBoundClause r.honestWitnesses).Spec := by
  rw [unwindBoundClause_spec_iff]
  intro w hw
  rw [honestWitnesses_buildRay, mem_constructorPaths_path] at hw
  obtain ⟨j, hj, rfl⟩ := prefix_ones_iff.mp hw
  refine ⟨r.last, ?_⟩
  rw [honestWitnesses_unwind]
  have hbal : r.builds = r.unwound r.last := hb
  exact toothWord_mem_comb.mpr ⟨le_rfl, by omega⟩

/-- The honest witnesses of a balanced exact run satisfy the specifications of all clauses. -/
theorem honest_spec (hb : r.Balanced) : ∀ cl ∈ clauses P r.honestWitnesses, cl.Spec := by
  rw [forall_mem_clauses_iff]
  exact ⟨r.honest_chain_spec, r.honest_chainHead_spec, r.honest_clock_spec, r.honest_gap_spec,
    r.honest_endLast_spec, r.honest_cover_spec, fun _ _ _ hl => r.honest_unique_spec hl,
    fun _ hl hend => r.honest_transition_spec hl hend,
    fun i => ⟨r.honest_counterStep_spec i, r.honest_zeroWindow_spec i, r.honest_plusWindow_spec i,
      r.honest_plusClassLabel_spec i, r.honest_zeroClassLabel_spec i⟩,
    fun _ _ _ hc => r.honest_zeroTest_spec hc, r.honest_unwindStep_spec,
    r.honest_unwindWindow_spec, r.honest_unwindBound_spec hb⟩

/-- The honest witnesses of a balanced exact run satisfy the guards, the root conditions and
the specifications of all clauses. -/
theorem specConditions_honest (hb : r.Balanced) : SpecConditions P r.honestWitnesses :=
  ⟨r.honest_guarded, r.honest_root, r.honest_spec hb⟩

end ExactRun

/-- Completeness: if the program halts, the clock sentence holds in all six structures. -/
theorem clockConditions_of_halts {P : Program} {c : TreeClass} {top : Bool} (h : P.Halts) :
    ClockConditions c top P := by
  obtain ⟨r, hb⟩ := exists_balanced_exactRun h
  exact (clockConditions_iff c top P).mpr
    ⟨r.honestWitnesses, r.honest_domain c top, r.specConditions_honest hb⟩

end Clock

end UndeciSigma2
