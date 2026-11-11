import Mathlib

/-! # Words for combs

Addresses in binary trees are words over `Fin 2`, with `0` for the left child
and `1` for the right child. A comb is read along its right spine: the word
`ones j` reaches spine node `j`, and the tooth `tooth j x = 1ʲ 0 0ˣ` reaches
depth `x` of the tooth hanging below spine node `j`. The stub `stub j = 1ʲ 0`
is the root of that tooth. The last section counts the zeros of a word.
-/

namespace UndeciSigma2

/-- Binary words, read from the root of a tree. -/
abbrev Word := List (Fin 2)

namespace Word

/-- The word `1ʲ`. -/
def ones (j : ℕ) : Word := List.replicate j 1

/-- The word `0ˣ`. -/
def zeros (x : ℕ) : Word := List.replicate x 0

/-- The word `1ʲ 0 0ˣ`: depth `x` of the tooth below spine node `j`. -/
def tooth (j x : ℕ) : Word := ones j ++ 0 :: zeros x

/-- The word `1ʲ 0`: the root of the tooth below spine node `j`. -/
def stub (j : ℕ) : Word := tooth j 0

/-- The word consists of ones only, that is, it belongs to `1*`. -/
def IsOnes (w : Word) : Prop := ∀ a ∈ w, a = 1

@[simp] theorem ones_zero : ones 0 = [] := rfl
@[simp] theorem ones_succ (j : ℕ) : ones (j + 1) = 1 :: ones j := rfl
@[simp] theorem zeros_zero : zeros 0 = [] := rfl
@[simp] theorem zeros_succ (x : ℕ) : zeros (x + 1) = 0 :: zeros x := rfl
@[simp] theorem length_ones (j : ℕ) : (ones j).length = j := List.length_replicate
@[simp] theorem length_zeros (x : ℕ) : (zeros x).length = x := List.length_replicate

theorem ones_add (i j : ℕ) : ones (i + j) = ones i ++ ones j := by
  simp only [ones, List.replicate_add]

theorem zeros_add (x y : ℕ) : zeros (x + y) = zeros x ++ zeros y := by
  simp only [zeros, List.replicate_add]

theorem ones_succ' (j : ℕ) : ones (j + 1) = ones j ++ [1] := by
  simp [ones, List.replicate_succ']

/-- A set of words closed under removing a leading one contains `w` whenever it contains
`1ᵃ w`. -/
theorem mem_of_ones_append_mem {S : Set Word} (hS : ∀ w, (1 : Fin 2) :: w ∈ S → w ∈ S)
    (a : ℕ) {w : Word} (h : ones a ++ w ∈ S) : w ∈ S := by
  induction a with
  | zero => exact h
  | succ a ih => exact ih (hS _ h)

@[simp] theorem tooth_zero_left (x : ℕ) : tooth 0 x = 0 :: zeros x := rfl
@[simp] theorem tooth_succ_left (j x : ℕ) : tooth (j + 1) x = 1 :: tooth j x := rfl
theorem stub_eq (j : ℕ) : stub j = ones j ++ [0] := rfl
@[simp] theorem stub_zero : stub 0 = [0] := rfl
@[simp] theorem stub_succ (j : ℕ) : stub (j + 1) = 1 :: stub j := rfl
@[simp] theorem length_tooth (j x : ℕ) : (tooth j x).length = j + 1 + x := by
  simp [tooth]; omega

theorem tooth_add (j x y : ℕ) : tooth j (x + y) = tooth j x ++ zeros y := by
  simp only [tooth, zeros_add, List.cons_append, List.append_assoc]

theorem tooth_eq_stub_append (j x : ℕ) : tooth j x = stub j ++ zeros x := by
  rw [stub, ← tooth_add, Nat.zero_add]

theorem ones_append_tooth (i j x : ℕ) : ones i ++ tooth j x = tooth (i + j) x := by
  simp only [tooth, ones_add, List.append_assoc]

theorem ones_append_stub (i j : ℕ) : ones i ++ stub j = stub (i + j) :=
  ones_append_tooth i j 0

@[simp] theorem isOnes_nil : IsOnes [] := by simp [IsOnes]

@[simp] theorem isOnes_cons (a : Fin 2) (w : Word) : IsOnes (a :: w) ↔ a = 1 ∧ IsOnes w := by
  simp [IsOnes]

@[simp] theorem isOnes_ones (j : ℕ) : IsOnes (ones j) := by
  intro a ha
  exact List.eq_of_mem_replicate ha

theorem isOnes_iff (w : Word) : IsOnes w ↔ ∃ i, w = ones i := by
  constructor
  · intro h
    exact ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h⟩⟩
  · rintro ⟨i, rfl⟩
    exact isOnes_ones i

theorem IsOnes.of_prefix {v w : Word} (h : v <+: w) (hw : IsOnes w) : IsOnes v :=
  fun a ha => hw a (h.subset ha)

theorem not_isOnes_tooth (j x : ℕ) : ¬IsOnes (tooth j x) := by
  intro h
  have := h 0 (by simp [tooth])
  exact absurd this (by decide)

theorem not_isOnes_stub (j : ℕ) : ¬IsOnes (stub j) := not_isOnes_tooth j 0

/-- A word outside `1*` has a first zero. -/
theorem not_isOnes_iff (w : Word) : ¬IsOnes w ↔ ∃ j v, w = ones j ++ 0 :: v := by
  constructor
  · intro h
    induction w with
    | nil => exact absurd isOnes_nil h
    | cons a w ih =>
      fin_cases a
      · exact ⟨0, w, rfl⟩
      · obtain ⟨j, v, rfl⟩ := ih fun hw => h ((isOnes_cons _ _).mpr ⟨rfl, hw⟩)
        exact ⟨j + 1, v, rfl⟩
  · rintro ⟨j, v, rfl⟩ h
    exact absurd (h 0 (by simp)) (by decide)

/-- A word with a zero is not a spine word. -/
theorem not_isOnes_ones_append_zero_cons (q : ℕ) (w : Word) : ¬IsOnes (ones q ++ 0 :: w) :=
  (not_isOnes_iff _).mpr ⟨q, w, rfl⟩

/-- Decomposition at the first zero is unique. -/
theorem ones_append_zero_cons_inj {i j : ℕ} {v w : Word} :
    ones i ++ 0 :: v = ones j ++ 0 :: w ↔ i = j ∧ v = w := by
  induction i generalizing j with
  | zero => cases j <;> simp
  | succ i ih => cases j <;> simp [ih]

/-- Every letter is `0` or `1`. -/
theorem letter_eq_zero_or_eq_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> decide

theorem zero_cons_ne_ones (w : Word) (i : ℕ) : 0 :: w ≠ ones i := by
  intro h
  have := isOnes_ones i
  rw [← h, isOnes_cons] at this
  exact absurd this.1 (by decide)

theorem one_cons_eq_ones_iff {w : Word} {i : ℕ} :
    1 :: w = ones i ↔ ∃ k, i = k + 1 ∧ w = ones k := by
  rcases i with _ | k
  · simp
  · rw [ones_succ, List.cons.injEq]
    constructor
    · rintro ⟨-, rfl⟩
      exact ⟨k, rfl, rfl⟩
    · rintro ⟨k', hk, rfl⟩
      obtain rfl : k = k' := by omega
      exact ⟨rfl, rfl⟩

theorem zero_cons_eq_ones_append_iff {w v : Word} {i : ℕ} :
    0 :: w = ones i ++ 0 :: v ↔ i = 0 ∧ w = v := by
  rw [show (0 : Fin 2) :: w = ones 0 ++ 0 :: w from rfl, ones_append_zero_cons_inj]
  constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem one_cons_eq_ones_append_iff {w v : Word} {i : ℕ} :
    1 :: w = ones i ++ 0 :: v ↔ ∃ k, i = k + 1 ∧ w = ones k ++ 0 :: v := by
  rcases i with _ | k
  · simp
  · rw [ones_succ, List.cons_append, List.cons.injEq]
    constructor
    · rintro ⟨-, rfl⟩
      exact ⟨k, rfl, rfl⟩
    · rintro ⟨k', hk, rfl⟩
      obtain rfl : k = k' := by omega
      exact ⟨rfl, rfl⟩

theorem prefix_ones_iff {w : Word} {j : ℕ} : w <+: ones j ↔ ∃ i ≤ j, w = ones i := by
  constructor
  · intro h
    exact ⟨w.length, by simpa using h.length_le,
      List.eq_replicate_iff.mpr ⟨rfl, (isOnes_ones j).of_prefix h⟩⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ones (j - i), by rw [← ones_add, Nat.add_sub_cancel' hi]⟩

theorem ones_prefix_ones_iff {i j : ℕ} : ones i <+: ones j ↔ i ≤ j := by
  rw [prefix_ones_iff]
  constructor
  · rintro ⟨k, hk, he⟩
    have := congrArg List.length he
    simp only [length_ones] at this
    omega
  · exact fun h => ⟨i, h, rfl⟩

theorem prefix_zeros_iff {w : Word} {x : ℕ} : w <+: zeros x ↔ ∃ y ≤ x, w = zeros y := by
  constructor
  · intro h
    exact ⟨w.length, by simpa using h.length_le,
      List.eq_replicate_iff.mpr ⟨rfl, fun a ha => List.eq_of_mem_replicate (h.subset ha)⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨zeros (x - y), by rw [← zeros_add, Nat.add_sub_cancel' hy]⟩

/-- The prefixes of a tooth are spine words and shorter teeth at the same index. -/
theorem prefix_tooth_iff {w : Word} {j x : ℕ} :
    w <+: tooth j x ↔ (∃ i ≤ j, w = ones i) ∨ ∃ y ≤ x, w = tooth j y := by
  induction j generalizing w with
  | zero =>
    rcases w with _ | ⟨a, w⟩
    · exact iff_of_true (List.nil_prefix) (Or.inl ⟨0, le_rfl, rfl⟩)
    · rw [tooth_zero_left, List.cons_prefix_cons, prefix_zeros_iff]
      constructor
      · rintro ⟨rfl, y, hy, rfl⟩
        exact Or.inr ⟨y, hy, rfl⟩
      · rintro (⟨i, hi, h⟩ | ⟨y, hy, h⟩)
        · obtain rfl : i = 0 := Nat.le_zero.mp hi
          simp at h
        · rw [tooth_zero_left, List.cons.injEq] at h
          exact ⟨h.1, y, hy, h.2⟩
  | succ j ih =>
    rcases w with _ | ⟨a, w⟩
    · exact iff_of_true (List.nil_prefix) (Or.inl ⟨0, Nat.zero_le _, rfl⟩)
    · rw [tooth_succ_left, List.cons_prefix_cons, ih]
      constructor
      · rintro ⟨rfl, ⟨i, hi, rfl⟩ | ⟨y, hy, rfl⟩⟩
        · exact Or.inl ⟨i + 1, by omega, rfl⟩
        · exact Or.inr ⟨y, hy, rfl⟩
      · rintro (⟨i, hi, h⟩ | ⟨y, hy, h⟩)
        · rcases i with _ | i
          · simp at h
          · rw [ones_succ, List.cons.injEq] at h
            exact ⟨h.1, Or.inl ⟨i, by omega, h.2⟩⟩
        · rw [tooth_succ_left, List.cons.injEq] at h
          exact ⟨h.1, Or.inr ⟨y, hy, h.2⟩⟩

/-- The prefixes of `1^q 0 u` are the spine words up to `1^q` and the words `1^q 0 v` with
`v` a prefix of `u`. -/
theorem prefix_ones_append_zero_cons_iff {w u : Word} {q : ℕ} :
    w <+: ones q ++ 0 :: u ↔
      (∃ i ≤ q, w = ones i) ∨ ∃ v, v <+: u ∧ w = ones q ++ 0 :: v := by
  induction q generalizing w with
  | zero =>
    rcases w with _ | ⟨a, w⟩
    · exact iff_of_true List.nil_prefix (Or.inl ⟨0, le_rfl, rfl⟩)
    · rw [ones_zero, List.nil_append, List.cons_prefix_cons]
      constructor
      · rintro ⟨rfl, h⟩
        exact Or.inr ⟨w, h, rfl⟩
      · rintro (⟨i, hi, h⟩ | ⟨v, hv, h⟩)
        · obtain rfl : i = 0 := Nat.le_zero.mp hi
          simp at h
        · rw [List.nil_append, List.cons.injEq] at h
          exact ⟨h.1, h.2 ▸ hv⟩
  | succ q ih =>
    rcases w with _ | ⟨a, w⟩
    · exact iff_of_true List.nil_prefix (Or.inl ⟨0, Nat.zero_le _, rfl⟩)
    · rw [ones_succ, List.cons_append, List.cons_prefix_cons, ih]
      constructor
      · rintro ⟨rfl, ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩⟩
        · exact Or.inl ⟨i + 1, by omega, rfl⟩
        · exact Or.inr ⟨v, hv, rfl⟩
      · rintro (⟨i, hi, h⟩ | ⟨v, hv, h⟩)
        · rcases i with _ | i
          · simp at h
          · rw [ones_succ, List.cons.injEq] at h
            exact ⟨h.1, Or.inl ⟨i, by omega, h.2⟩⟩
        · rw [List.cons_append, List.cons.injEq] at h
          exact ⟨h.1, Or.inr ⟨v, hv, h.2⟩⟩

theorem tooth_inj {j x j' x' : ℕ} : tooth j x = tooth j' x' ↔ j = j' ∧ x = x' := by
  simp only [tooth, ones_append_zero_cons_inj]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa using congrArg List.length h⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem tooth_prefix_tooth_iff {j x j' x' : ℕ} :
    tooth j x <+: tooth j' x' ↔ j = j' ∧ x ≤ x' := by
  rw [prefix_tooth_iff]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨y, hy, h⟩)
    · exact absurd (h ▸ isOnes_ones i) (not_isOnes_tooth j x)
    · obtain ⟨rfl, rfl⟩ := tooth_inj.mp h
      exact ⟨rfl, hy⟩
  · rintro ⟨rfl, h⟩
    exact Or.inr ⟨x, h, rfl⟩

theorem stub_inj {i j : ℕ} : stub i = stub j ↔ i = j := by
  simpa [stub] using (tooth_inj (j := i) (x := 0) (j' := j) (x' := 0))

theorem stub_prefix_tooth (j x : ℕ) : stub j <+: tooth j x :=
  ⟨zeros x, (tooth_eq_stub_append j x).symm⟩

theorem stub_prefix_iff {j : ℕ} {w : Word} : stub j <+: w ↔ ∃ v, w = ones j ++ 0 :: v := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [stub_eq]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [stub_eq]⟩

theorem stub_prefix_stub_iff {i j : ℕ} : stub i <+: stub j ↔ i = j := by
  simpa [stub] using (tooth_prefix_tooth_iff (j := i) (x := 0) (j' := j) (x' := 0))

/-- No spine word extends a stub. -/
theorem not_stub_prefix_ones (i j : ℕ) : ¬stub j <+: ones i := by
  intro h
  exact not_isOnes_stub j ((isOnes_ones i).of_prefix h)

/-! ## Counting zeros -/

/-- A spine word has no zero. -/
theorem count_zero_eq_zero_of_isOnes {w : Word} (h : IsOnes w) : w.count 0 = 0 :=
  List.count_eq_zero.mpr fun h0 => absurd (h 0 h0) (by decide)

/-- A word without zero is a spine word. -/
theorem isOnes_of_count_zero {w : Word} (h : w.count 0 = 0) : IsOnes w := fun a ha => by
  rcases letter_eq_zero_or_eq_one a with rfl | rfl
  · exact absurd ha (List.count_eq_zero.mp h)
  · rfl

/-- The word `1ʲ 0 u` has one zero more than `u`. -/
theorem count_zero_ones_append_zero_cons (j : ℕ) (u : Word) :
    (ones j ++ 0 :: u).count 0 = u.count 0 + 1 := by
  rw [List.count_append, count_zero_eq_zero_of_isOnes (isOnes_ones j), List.count_cons_self]
  omega

/-- A word with its first zero at position `l` does not start with `1ᵐ` for `m > l`. -/
theorem ones_append_zero_cons_ne_ones_append {l m : ℕ} (hl : l < m) (u v : Word) :
    ones l ++ 0 :: u ≠ ones m ++ v := by
  intro h
  have hm : m = l + (m - l - 1 + 1) := by omega
  rw [hm, ones_add, ones_succ, List.append_assoc, List.append_cancel_left_eq] at h
  simp at h

/-- Prepending `1ˡ 0` preserves prefixes. -/
theorem ones_append_zero_cons_prefix (l : ℕ) {v w : Word} (h : v <+: w) :
    ones l ++ 0 :: v <+: ones l ++ 0 :: w := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r, by simp⟩

end Word

end UndeciSigma2
