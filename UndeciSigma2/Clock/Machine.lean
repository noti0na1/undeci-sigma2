import UndeciSigma2.Machine

/-! # The label machine of a two-counter program

The clock sentence describes a run of a two-counter program `P` with `n` instructions by a
sequence of labels `λ₀, …, λ_E` and three counters: the two counters of `P` and a reservoir,
counter `2`. There are `6 + 2n` labels:

| label | name | effect on `(c₀, c₁, R)` | zero test |
|---|---|---|---|
| `0` | start | none | |
| `1` | build-up | `R + 1` | |
| `2` | drain counter `0` | `c₀ - 1`, `R + 1` | |
| `3` | drain counter `1` | `c₁ - 1`, `R + 1` | |
| `4` | unwind | `R - 1` | |
| `5` | end | none | |
| `6 + 2q`, `P[q] = inc c r` | step of `q` | `c + 1`, `R - 1` | |
| `6 + 2q`, `P[q] = jzdec c z p` | zero branch of `q` | none | `c = 0` before the step |
| `7 + 2q`, `P[q] = jzdec c z p` | positive branch of `q` | `c - 1`, `R + 1` | |
| `7 + 2q`, `P[q] = inc c r` | unused | none | |

The entry labels of a working state `q < n` are the labels of instruction `q`; the entry
labels of a halted state are `2, 3, 4, 5`. The start and build-up labels are followed by the
build-up label or an entry label of state `0`; the label of a step of instruction `q` is
followed by the entry labels of its target state, clipped to `n`; the drain and unwind labels
are followed by the same or a later label of the tail `2, 3, 4, 5`; the end label has no
successor.

An exact run starts with the start label and all counters zero, ends with the end label,
follows the successor relation, has natural-number counters satisfying the update equations
`c(s + 1) = c(s) + effect` in `ℤ`, and respects the zero tests. A program halts
exactly when its label machine has an exact run, and then it has a balanced one, with as many
unwind labels as build-up labels.
-/

namespace UndeciSigma2

namespace Clock

/-! ## Labels -/

/-- The number of labels of a program with `n` instructions: `6 + 2n`. -/
def labelCount (P : Program) : ℕ := 6 + 2 * P.length

/-- The start label. -/
abbrev startLabel : ℕ := 0

/-- The build-up label: it fills the reservoir. -/
abbrev buildLabel : ℕ := 1

/-- The label draining counter `0` into the reservoir. -/
abbrev drainZeroLabel : ℕ := 2

/-- The label draining counter `1` into the reservoir. -/
abbrev drainOneLabel : ℕ := 3

/-- The unwinding label: it empties the reservoir. -/
abbrev unwindLabel : ℕ := 4

/-- The end label. -/
abbrev endLabel : ℕ := 5

/-- The label of a step of instruction `q`: an increment, or the zero branch of a test. -/
def stepLabel (q : ℕ) : ℕ := 6 + 2 * q

/-- The label of the positive branch of the test of instruction `q`. -/
def positiveLabel (q : ℕ) : ℕ := 7 + 2 * q

/-- Whether `μ` is an entry label of state `q`: the labels of instruction `q` for a working
state, and the labels `2, 3, 4, 5` for a halted state. -/
def isEntry (P : Program) (q μ : ℕ) : Bool :=
  match P[q]? with
  | none => decide (2 ≤ μ ∧ μ ≤ 5)
  | some (.inc _ _) => decide (μ = 6 + 2 * q)
  | some (.jzdec _ _ _) => decide (μ = 6 + 2 * q ∨ μ = 7 + 2 * q)

/-- Whether label `μ` may follow label `l`. Labels at least `6 + 2n` have no successor. -/
def isSuccessor (P : Program) (l μ : ℕ) : Bool :=
  if l ≤ 1 then decide (μ = 1) || isEntry P 0 μ
  else if l = 2 then decide (2 ≤ μ ∧ μ ≤ 5)
  else if l = 3 then decide (3 ≤ μ ∧ μ ≤ 5)
  else if l = 4 then decide (4 ≤ μ ∧ μ ≤ 5)
  else if l < 6 then false
  else
    match P[(l - 6) / 2]? with
    | none => false
    | some (.inc _ r) => decide ((l - 6) % 2 = 0) && isEntry P (min r P.length) μ
    | some (.jzdec _ z p) =>
      isEntry P (min (if (l - 6) % 2 = 0 then z else p) P.length) μ

/-- Move `a` units from the reservoir into counter `c`: counter `c` changes by `a` and the
reservoir, counter `2`, by `-a`. -/
def transfer (c : Fin 2) (a : ℤ) (i : Fin 3) : ℤ :=
  if i = Fin.castSucc c then a else if i = 2 then -a else 0

/-- The effect of label `l` on counter `i`; counter `2` is the reservoir. -/
def effect (P : Program) (l : ℕ) (i : Fin 3) : ℤ :=
  if l = 1 then (if i = 2 then 1 else 0)
  else if l = 2 then transfer 0 (-1) i
  else if l = 3 then transfer 1 (-1) i
  else if l = 4 then (if i = 2 then -1 else 0)
  else if l < 6 then 0
  else
    match P[(l - 6) / 2]? with
    | none => 0
    | some (.inc c _) => if (l - 6) % 2 = 0 then transfer c 1 i else 0
    | some (.jzdec c _ _) => if (l - 6) % 2 = 0 then 0 else transfer c (-1) i

/-- The counter tested by label `l`: counter `c` for the zero branch of `jzdec c z p`, and
none otherwise. -/
def zeroTest (P : Program) (l : ℕ) : Option (Fin 2) :=
  if l < 6 ∨ (l - 6) % 2 = 1 then none
  else
    match P[(l - 6) / 2]? with
    | some (.jzdec c _ _) => some c
    | _ => none

/-- The number of stamps `1 ≤ t ≤ s` with label `l`. -/
def occurrences (label : ℕ → ℕ) (l s : ℕ) : ℕ :=
  (List.range s).countP fun t => decide (label (t + 1) = l)

@[simp] theorem occurrences_zero (label : ℕ → ℕ) (l : ℕ) : occurrences label l 0 = 0 := rfl

/-- Occurrences change by one exactly when the next stamp has the given label. -/
@[simp] theorem occurrences_succ (label : ℕ → ℕ) (l s : ℕ) :
    occurrences label l (s + 1) = occurrences label l s + if label (s + 1) = l then 1 else 0 := by
  simp [occurrences, List.range_succ]

/-- At most `s` of the stamps `1, …, s` carry a given label. -/
theorem occurrences_le (label : ℕ → ℕ) (l s : ℕ) : occurrences label l s ≤ s := by
  unfold occurrences
  exact List.countP_le_length.trans (by simp)

/-- Occurrences do not decrease with the stamp. -/
theorem occurrences_mono (label : ℕ → ℕ) (l : ℕ) {s s' : ℕ} (h : s ≤ s') :
    occurrences label l s ≤ occurrences label l s' := by
  induction s' with
  | zero =>
    obtain rfl : s = 0 := by omega
    exact le_rfl
  | succ s' ih =>
    rcases h.lt_or_eq with h | h
    · have := ih (by omega)
      rw [occurrences_succ]
      omega
    · rw [h]

/-- If no stamp in `(b, n]` carries label `l`, at most `b` stamps up to `n` carry it. -/
theorem occurrences_le_of_forall_ne {label : ℕ → ℕ} {l b n : ℕ} (hbn : b ≤ n)
    (h : ∀ t, b < t → t ≤ n → label t ≠ l) : occurrences label l n ≤ b := by
  induction n, hbn using Nat.le_induction with
  | base => exact occurrences_le label l b
  | succ n hbn ih =>
    rw [occurrences_succ, ite_eq_right (h (n + 1) (by omega) le_rfl)]
    exact ih fun t h₁ h₂ => h t h₁ (by omega)

/-! ## Exact runs -/

/-- An exact run of the label machine: labels `λ₀, …, λ_E` and counters `(c₀, c₁, R)` in `ℕ`,
starting with the start label and all counters zero, ending with the end label, following the
successor relation and the effects, and with counter `c` zero before every zero branch
testing `c`. -/
structure ExactRun (P : Program) where
  /-- The last stamp `E`. -/
  last : ℕ
  /-- The label at each stamp. -/
  label : ℕ → ℕ
  /-- The counters at each stamp; counter `2` is the reservoir. -/
  count : ℕ → Fin 3 → ℕ
  label_zero : label 0 = startLabel
  label_last : label last = endLabel
  count_zero : ∀ i, count 0 i = 0
  isSuccessor_label : ∀ s < last, isSuccessor P (label s) (label (s + 1)) = true
  count_succ : ∀ s < last, ∀ i,
    (count (s + 1) i : ℤ) = count s i + effect P (label (s + 1)) i
  count_eq_zero : ∀ s < last, ∀ c, zeroTest P (label (s + 1)) = some c →
    count s (Fin.castSucc c) = 0

namespace ExactRun

variable {P : Program}

/-- A run is balanced when it has as many unwind labels as build-up labels. -/
def Balanced (r : ExactRun P) : Prop :=
  occurrences r.label buildLabel r.last = occurrences r.label unwindLabel r.last

end ExactRun

/-! ## Basic facts about the tables -/

section Tables

variable {P : Program}

/-- The end label has no successor. -/
@[simp] theorem isSuccessor_endLabel (μ : ℕ) : isSuccessor P endLabel μ = false := by
  simp [isSuccessor]

/-- Entry labels lie in the machine's label range and are at least two. -/
theorem isEntry_bounds {q μ : ℕ} (h : isEntry P q μ = true) :
    2 ≤ μ ∧ μ < labelCount P := by
  unfold isEntry at h
  split at h
  next hq => simp only [decide_eq_true_eq] at h; unfold labelCount; omega
  next c r hq =>
    obtain ⟨hq', _⟩ := List.getElem?_eq_some_iff.mp hq
    simp only [decide_eq_true_eq] at h
    unfold labelCount
    omega
  next c z p hq =>
    obtain ⟨hq', _⟩ := List.getElem?_eq_some_iff.mp hq
    simp only [decide_eq_true_eq] at h
    unfold labelCount
    omega

/-- Every successor is a label. -/
theorem lt_labelCount_of_isSuccessor {l μ : ℕ} (h : isSuccessor P l μ = true) :
    μ < labelCount P := by
  unfold isSuccessor at h
  split at h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · unfold labelCount; omega
    · exact (isEntry_bounds h).2
  · split at h
    · simp only [decide_eq_true_eq] at h; unfold labelCount; omega
    · split at h
      · simp only [decide_eq_true_eq] at h; unfold labelCount; omega
      · split at h
        · simp only [decide_eq_true_eq] at h; unfold labelCount; omega
        · split at h
          · contradiction
          · split at h
            · contradiction
            · exact (isEntry_bounds (Bool.and_eq_true_iff.mp h).2).2
            · exact (isEntry_bounds h).2

/-- Only the start and build-up labels are followed by the build-up label. -/
theorem eq_start_or_build_of_isSuccessor_build {l : ℕ}
    (h : isSuccessor P l buildLabel = true) : l = startLabel ∨ l = buildLabel := by
  have he (q : ℕ) : isEntry P q buildLabel = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := (isEntry_bounds h).1
    norm_num at this
  unfold isSuccessor at h
  split at h
  · simp only [startLabel, buildLabel]; omega
  · simp only [he, Bool.and_false] at h
    repeat split at h <;> norm_num at h

/-- No label is followed by the start label. -/
theorem isSuccessor_start (l : ℕ) : isSuccessor P l startLabel = false := by
  have he (q : ℕ) : isEntry P q startLabel = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := (isEntry_bounds h).1
    norm_num at this
  unfold isSuccessor
  simp only [he, Bool.and_false]
  repeat split <;> norm_num

/-- Every effect is `-1`, `0` or `1`. -/
theorem effect_mem (l : ℕ) (i : Fin 3) :
    effect P l i = -1 ∨ effect P l i = 0 ∨ effect P l i = 1 := by
  unfold effect
  repeat' first | split | (simp_all [transfer]; done)
  all_goals
    unfold transfer
    repeat' split <;> simp_all

/-- A transfer preserves the sum of the three counters. -/
theorem sum_transfer (c : Fin 2) (a : ℤ) : ∑ i, transfer c a i = 0 := by
  fin_cases c <;> simp [Fin.sum_univ_succ, transfer]

/-- The effects of a label sum to `1` for the build-up label, to `-1` for the unwind label,
and to `0` otherwise: every other label moves units between a counter and the reservoir. -/
theorem sum_effect (l : ℕ) :
    ∑ i, effect P l i = if l = buildLabel then 1 else if l = unwindLabel then -1 else 0 := by
  unfold effect
  split
  · simp_all
  · split
    · simp_all [sum_transfer]
    · split
      · simp_all [sum_transfer]
      · split
        · simp_all
        · split
          · simp_all
          · split
            · simp_all
            · split <;> first | exact sum_transfer _ _ | simp
            · split <;> first | exact sum_transfer _ _ | simp

/-- A zero test is made only by the zero branch of a test instruction. -/
theorem zeroTest_eq_some_iff {l : ℕ} {c : Fin 2} :
    zeroTest P l = some c ↔ ∃ q z p, l = stepLabel q ∧ P[q]? = some (.jzdec c z p) := by
  constructor
  · intro h
    unfold zeroTest at h
    split at h
    · contradiction
    next hn =>
      split at h
      next d z p hq =>
        have hc : d = c := Option.some.inj h
        subst d
        refine ⟨(l - 6) / 2, z, p, ?_, hq⟩
        unfold stepLabel
        omega
      · contradiction
  · rintro ⟨q, z, p, rfl, hq⟩
    simp [zeroTest, stepLabel, hq]

end Tables

/-! ## Label sequences -/

section Sequences

variable {P : Program}

/-- In a label sequence starting with the start label and following the successor relation,
the build-up labels occupy an initial segment of the positive stamps. -/
theorem buildLabel_of_le {E : ℕ} {label : ℕ → ℕ} (h0 : label 0 = startLabel)
    (hsucc : ∀ s < E, isSuccessor P (label s) (label (s + 1)) = true) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ E) (hlt : label t = buildLabel) :
    label s = buildLabel := by
  induction t with
  | zero => simp [h0] at hlt
  | succ t ih =>
    by_cases hst' : s = t + 1
    · simpa [hst'] using hlt
    have hp := hsucc t (by omega)
    rw [hlt] at hp
    rcases eq_start_or_build_of_isSuccessor_build hp with hz | hb
    · have htpos : 0 < t := by omega
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      have hp := hsucc u (by omega)
      rw [hz, isSuccessor_start] at hp
      contradiction
    · exact ih (by omega) (by omega) hb

/-- In a label sequence starting with the start label and following the successor relation,
every label is a label of the machine. -/
theorem label_lt_labelCount {E : ℕ} {label : ℕ → ℕ} (h0 : label 0 = startLabel)
    (hsucc : ∀ s < E, isSuccessor P (label s) (label (s + 1)) = true) {s : ℕ} (hs : s ≤ E) :
    label s < labelCount P := by
  cases s with
  | zero => simp [h0, labelCount]
  | succ s => exact lt_labelCount_of_isSuccessor (hsucc s (by omega))

end Sequences

namespace ExactRun

variable {P : Program} (r : ExactRun P)

/-- The end label occurs only at the last stamp. -/
theorem label_eq_endLabel_iff {s : ℕ} (hs : s ≤ r.last) : r.label s = endLabel ↔ s = r.last := by
  constructor
  · intro h
    by_contra hn
    have hp := r.isSuccessor_label s (by omega)
    rw [h, isSuccessor_endLabel] at hp
    contradiction
  · rintro rfl
    exact r.label_last

/-- Every counter of an exact run is at most its stamp. -/
theorem count_le (s : ℕ) (i : Fin 3) (hs : s ≤ r.last) : r.count s i ≤ s := by
  induction s with
  | zero => simp [r.count_zero]
  | succ s ih =>
    have hi := ih (by omega)
    have he := r.count_succ s (by omega) i
    have hm := effect_mem (P := P) (r.label (s + 1)) i
    rcases hm with hm | hm | hm <;> rw [hm] at he <;> omega

/-- The build-up labels of an exact run are the stamps `1, …, N` with `N` their number. -/
theorem label_eq_buildLabel_iff {s : ℕ} (hs : s ≤ r.last) :
    r.label s = buildLabel ↔ 1 ≤ s ∧ s ≤ occurrences r.label buildLabel r.last := by
  have hprefix := @buildLabel_of_le P r.last r.label r.label_zero r.isSuccessor_label
  have hcount (t : ℕ) (ht : t ≤ r.last) (hb : r.label t = buildLabel) :
      occurrences r.label buildLabel r.last ≥ t := by
    have he : occurrences r.label buildLabel t = t := by
      unfold occurrences
      rw [List.countP_eq_length.mpr]
      · simp
      · intro u hu
        simp only [List.mem_range] at hu
        simpa using hprefix (by omega) (by omega) ht hb
    rw [← he]
    exact (List.range_sublist.mpr ht).countP_le
  constructor
  · intro hb
    refine ⟨?_, hcount s hs hb⟩
    by_contra hn
    have : s = 0 := by omega
    subst s
    simp [r.label_zero] at hb
  · rintro ⟨hpos, hnum⟩
    by_contra hb
    have hbound : occurrences r.label buildLabel r.last ≤ s - 1 := by
      unfold occurrences
      calc
        _ ≤ (List.range r.last).countP (fun t => decide (t < s - 1)) := by
          apply List.countP_mono_left
          intro t ht hlabel
          simp only [List.mem_range] at ht
          simp only [decide_eq_true_eq] at hlabel ⊢
          by_contra hn
          exact hb (hprefix hpos (by omega) (by omega) hlabel)
        _ ≤ s - 1 := by
          have hb (n k : ℕ) : (List.range n).countP (fun t => decide (t < k)) ≤ k := by
            have he : ∀ n, (List.range n).countP (fun t => decide (t < k)) = min n k := by
              intro n
              induction n with
              | zero => simp
              | succ n ih =>
                simp only [List.range_succ, List.countP_append, List.countP_singleton, ih]
                split <;> rename_i hn <;> simp only [decide_eq_true_eq] at hn <;> omega
            rw [he]
            exact Nat.min_le_right _ _
          exact hb _ _
    omega

end ExactRun

/-! ## Halting and exact runs -/

variable {P : Program}

/-- Clipping a state at the program length preserves its entry labels. -/
@[simp] theorem isEntry_min (q μ : ℕ) : isEntry P (min q P.length) μ = isEntry P q μ := by
  by_cases h : q < P.length
  · rw [Nat.min_eq_left (by omega)]
  · simp [isEntry, List.getElem?_eq_none (by omega : P.length ≤ q),
      Nat.min_eq_right (by omega : P.length ≤ q)]

private theorem stepLabel_arithmetic (q : ℕ) :
    ¬ stepLabel q ≤ 1 ∧ stepLabel q ≠ 1 ∧ stepLabel q ≠ 2 ∧
    stepLabel q ≠ 3 ∧ stepLabel q ≠ 4 ∧ ¬ stepLabel q < 6 ∧
    (stepLabel q - 6) / 2 = q ∧ (stepLabel q - 6) % 2 = 0 := by
  unfold stepLabel
  omega

private theorem positiveLabel_arithmetic (q : ℕ) :
    ¬ positiveLabel q ≤ 1 ∧ positiveLabel q ≠ 1 ∧ positiveLabel q ≠ 2 ∧
    positiveLabel q ≠ 3 ∧ positiveLabel q ≠ 4 ∧ ¬ positiveLabel q < 6 ∧
    (positiveLabel q - 6) / 2 = q ∧ (positiveLabel q - 6) % 2 = 1 := by
  unfold positiveLabel
  omega

private theorem inc_tables {q : ℕ} {c : Fin 2} {next : ℕ}
    (hq : P[q]? = some (.inc c next)) :
    (∀ μ, isSuccessor P (stepLabel q) μ = isEntry P next μ) ∧
    (∀ i, effect P (stepLabel q) i = transfer c 1 i) ∧
    zeroTest P (stepLabel q) = none := by
  rcases stepLabel_arithmetic q with ⟨h₀, h₁, h₂, h₃, h₄, h₆, hd, hm⟩
  simp [isSuccessor, effect, zeroTest, h₀, h₁, h₂, h₃, h₄, h₆, hd, hm, hq]

private theorem zero_tables {q : ℕ} {c : Fin 2} {z p : ℕ}
    (hq : P[q]? = some (.jzdec c z p)) :
    (∀ μ, isSuccessor P (stepLabel q) μ = isEntry P z μ) ∧
    (∀ i, effect P (stepLabel q) i = 0) ∧
    zeroTest P (stepLabel q) = some c := by
  rcases stepLabel_arithmetic q with ⟨h₀, h₁, h₂, h₃, h₄, h₆, hd, hm⟩
  simp [isSuccessor, effect, zeroTest, h₀, h₁, h₂, h₃, h₄, h₆, hd, hm, hq]

private theorem positive_tables {q : ℕ} {c : Fin 2} {z p : ℕ}
    (hq : P[q]? = some (.jzdec c z p)) :
    (∀ μ, isSuccessor P (positiveLabel q) μ = isEntry P p μ) ∧
    (∀ i, effect P (positiveLabel q) i = transfer c (-1) i) ∧
    zeroTest P (positiveLabel q) = none := by
  rcases positiveLabel_arithmetic q with ⟨h₀, h₁, h₂, h₃, h₄, h₆, hd, hm⟩
  simp [isSuccessor, effect, zeroTest, h₀, h₁, h₂, h₃, h₄, h₆, hd, hm, hq]

/-- An entry label of a working state executes the program instruction exactly. -/
theorem entry_execution {x : Config} {l : ℕ} {a b : Fin 3 → ℕ}
    (hx : x.state < P.length) (he : isEntry P x.state l = true)
    (ha : ∀ c, a (Fin.castSucc c) = x.counter c)
    (hab : ∀ i, (b i : ℤ) = a i + effect P l i)
    (hz : ∀ c, zeroTest P l = some c → a (Fin.castSucc c) = 0) :
    6 ≤ l ∧ (∀ c, b (Fin.castSucc c) = (P.step x).counter c) ∧
    ∀ μ, isSuccessor P l μ = isEntry P (P.step x).state μ := by
  have hq : P[x.state]? = some P[x.state] := List.getElem?_eq_getElem hx
  generalize hi : P[x.state] = ins at hq
  cases ins with
  | inc c next =>
    have hl : l = stepLabel x.state := by simpa [isEntry, hq, stepLabel] using he
    subst l
    obtain ⟨hs, hf, _⟩ := inc_tables hq
    refine ⟨by unfold stepLabel; omega, ?_, ?_⟩
    · intro d
      have hb := hab (Fin.castSucc d)
      rw [hf, ha] at hb
      simp only [Program.step_of_getElem? hq, Instr.exec_inc_counter]
      by_cases hd : d = c
      · subst d
        simp [transfer] at hb
        simp only [↓reduceIte]
        omega
      · have hcast : Fin.castSucc d ≠ Fin.castSucc c := by simpa using hd
        have htwo : Fin.castSucc d ≠ (2 : Fin 3) := by fin_cases d <;> decide
        simp [transfer, hcast, htwo] at hb
        simp [hd, hb]
    · simpa [Program.step_of_getElem? hq] using hs
  | jzdec c z p =>
    have hl : l = stepLabel x.state ∨ l = positiveLabel x.state := by
      simpa [isEntry, hq, stepLabel, positiveLabel] using he
    rcases hl with rfl | rfl
    · obtain ⟨hs, hf, ht⟩ := zero_tables hq
      have hc : x.counter c = 0 := by rw [← ha]; exact hz c ht
      have hstep := Instr.exec_jzdec_of_eq_zero (z := z) (p := p) hc
      refine ⟨by unfold stepLabel; omega, ?_, ?_⟩
      · intro d
        have hb := hab (Fin.castSucc d)
        rw [hf, ha] at hb
        simp only [Program.step_of_getElem? hq, hstep]
        omega
      · simpa [Program.step_of_getElem? hq, hstep] using hs
    · obtain ⟨hs, hf, _⟩ := positive_tables hq
      have hc : x.counter c ≠ 0 := by
        have hb := hab (Fin.castSucc c)
        rw [hf, ha] at hb
        simp [transfer] at hb
        omega
      have hstep := Instr.exec_jzdec_of_ne_zero (z := z) (p := p) hc
      refine ⟨by unfold positiveLabel; omega, ?_, ?_⟩
      · intro d
        have hb := hab (Fin.castSucc d)
        rw [hf, ha] at hb
        simp only [Program.step_of_getElem? hq, hstep, Function.update_apply]
        by_cases hd : d = c
        · subst d
          simp [transfer] at hb
          simp only [↓reduceIte]
          omega
        · have hcast : Fin.castSucc d ≠ Fin.castSucc c := by simpa using hd
          have htwo : Fin.castSucc d ≠ (2 : Fin 3) := by fin_cases d <;> decide
          simp [transfer, hcast, htwo] at hb
          simp [hd, hb]
      · simpa [Program.step_of_getElem? hq, hstep] using hs

private theorem ExactRun.halts_of_entry (r : ExactRun P) (s t : ℕ)
    (hs : s < r.last) (he : isEntry P (P.run t).state (r.label (s + 1)) = true)
    (hc : ∀ c, r.count s (Fin.castSucc c) = (P.run t).counter c) : P.Halts := by
  by_cases hx : P.length ≤ (P.run t).state
  · exact ⟨t, hx⟩
  have ht := entry_execution (by omega) he hc (r.count_succ s hs) (r.count_eq_zero s hs)
  have hs' : s + 1 < r.last := by
    have := r.label_last
    by_contra hn
    have : s + 1 = r.last := by omega
    rw [this, r.label_last] at ht
    norm_num at ht
  apply r.halts_of_entry (s + 1) (t + 1) hs'
  · rw [Program.run_succ, ← ht.2.2]
    exact r.isSuccessor_label (s + 1) hs'
  · simpa [Program.run_succ] using ht.2.1
termination_by r.last - s

/-- An exact run of the label machine follows the run of the program until it halts. -/
theorem ExactRun.halts (r : ExactRun P) : P.Halts := by
  have hstart : ∀ s, s < r.last → r.label s ≤ 1 →
      (∀ c : Fin 2, r.count s (Fin.castSucc c) = 0) → P.Halts := by
    intro s
    induction hrem : r.last - s using Nat.strong_induction_on generalizing s with
    | h k ih =>
      intro hs hl hc
      have hn := r.isSuccessor_label s hs
      simp only [isSuccessor, hl, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hn
      rcases hn with hb | he
      · have hs' : s + 1 < r.last := by
          have := r.label_last
          by_contra hn
          have : s + 1 = r.last := by omega
          rw [this, r.label_last] at hb
          norm_num at hb
        apply ih (r.last - (s + 1)) (by omega) (s + 1) rfl hs' (by omega)
        intro c
        have hh := r.count_succ s hs (Fin.castSucc c)
        rw [hb, hc] at hh
        have htwo : Fin.castSucc c ≠ (2 : Fin 3) := by fin_cases c <;> decide
        simp [effect, htwo] at hh
        exact hh
      · apply r.halts_of_entry s 0 hs he
        simpa using hc
  apply hstart 0
  · have h₀ := r.label_zero
    have he := r.label_last
    by_contra hn
    have : r.last = 0 := by omega
    rw [this, h₀] at he
    contradiction
  · simp [r.label_zero]
  · intro c; exact r.count_zero _

/-- The total counter value is the number of build-up labels minus the number of unwinds. -/
theorem ExactRun.total_count (r : ExactRun P) (s : ℕ) (hs : s ≤ r.last) :
    (∑ i, (r.count s i : ℤ)) =
      (occurrences r.label buildLabel s : ℤ) - occurrences r.label unwindLabel s := by
  induction s with
  | zero => simp [r.count_zero, occurrences]
  | succ s ih =>
    have he : (∑ i, (r.count (s + 1) i : ℤ)) =
        (∑ i, (r.count s i : ℤ)) + ∑ i, effect P (r.label (s + 1)) i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact r.count_succ s (by omega) i
    rw [he, ih (by omega), sum_effect, occurrences_succ, occurrences_succ]
    split_ifs <;> simp_all [buildLabel, unwindLabel] <;> ring

/-- A run ending with all counters zero is balanced. -/
theorem ExactRun.balanced_of_count_last_zero (r : ExactRun P)
    (h : ∀ i, r.count r.last i = 0) : r.Balanced := by
  have ht := r.total_count r.last le_rfl
  simp only [h, Int.natCast_zero, Finset.sum_const_zero] at ht
  unfold ExactRun.Balanced
  omega

/-- Finite paths with an arbitrary final label, used to assemble complete runs. -/
private structure RunPrefix (P : Program) where
  last : ℕ
  label : ℕ → ℕ
  count : ℕ → Fin 3 → ℕ
  label_zero : label 0 = startLabel
  count_zero : ∀ i, count 0 i = 0
  successor : ∀ s < last, isSuccessor P (label s) (label (s + 1)) = true
  exact : ∀ s < last, ∀ i, (count (s + 1) i : ℤ) = count s i + effect P (label (s + 1)) i
  test : ∀ s < last, ∀ c, zeroTest P (label (s + 1)) = some c → count s (Fin.castSucc c) = 0

private inductive Reachable (P : Program) : ℕ → (Fin 3 → ℕ) → Prop
  | start : Reachable P startLabel (fun _ => 0)
  | step {l μ a b} : Reachable P l a → isSuccessor P l μ = true →
      (∀ i, (b i : ℤ) = a i + effect P μ i) →
      (∀ c, zeroTest P μ = some c → a (Fin.castSucc c) = 0) → Reachable P μ b

private theorem Reachable.prefix {l a} (h : Reachable P l a) :
    ∃ r : RunPrefix P, r.label r.last = l ∧ r.count r.last = a := by
  induction h with
  | start =>
    refine ⟨⟨0, fun _ => 0, fun _ _ => 0, rfl, fun _ => rfl, ?_, ?_, ?_⟩, rfl, rfl⟩
    all_goals intro s hs; omega
  | @step l μ a b h hn he hz ih =>
    obtain ⟨r, hl, ha⟩ := ih
    let label := fun s => if s ≤ r.last then r.label s else μ
    let count := fun s => if s ≤ r.last then r.count s else b
    have hlabel : label (r.last + 1) = μ := by simp [label]
    have hcount : count (r.last + 1) = b := by simp [count]
    refine ⟨⟨r.last + 1, label, count, ?_, ?_, ?_, ?_, ?_⟩, hlabel, hcount⟩
    · simpa [label] using r.label_zero
    · simpa [count] using r.count_zero
    · intro s hs
      by_cases hlt : s < r.last
      · simpa [label, Nat.le_of_lt hlt, show s + 1 ≤ r.last by omega] using r.successor s hlt
      · have : s = r.last := by omega
        subst s
        simpa [label, hl] using hn
    · intro s hs i
      by_cases hlt : s < r.last
      · simpa [count, label, Nat.le_of_lt hlt, show s + 1 ≤ r.last by omega] using r.exact s hlt i
      · have : s = r.last := by omega
        subst s
        simpa [count, label, ha] using he i
    · intro s hs c ht
      by_cases hlt : s < r.last
      · have ht' : zeroTest P (r.label (s + 1)) = some c := by
          simpa [label, show s + 1 ≤ r.last by omega] using ht
        simpa [count, Nat.le_of_lt hlt] using r.test s hlt c ht'
      · have : s = r.last := by omega
        subst s
        have ht' : zeroTest P μ = some c := by simpa [label] using ht
        simpa [count, ha] using hz c ht'

private def storedCount (N : ℕ) (v : Fin 2 → ℕ) : Fin 3 → ℕ :=
  ![v 0, v 1, N - (v 0 + v 1)]

private theorem storedCount_castSucc (N : ℕ) (v : Fin 2 → ℕ) (c : Fin 2) :
    storedCount N v (Fin.castSucc c) = v c := by
  fin_cases c <;> rfl

/-- The chosen instruction label preserves the total amount stored in the reservoir and counters. -/
private theorem exists_stored_step (x : Config) (N : ℕ) (hx : x.state < P.length)
    (hN : x.counter 0 + x.counter 1 ≤ N)
    (hN' : (P.step x).counter 0 + (P.step x).counter 1 ≤ N) :
    ∃ l, isEntry P x.state l = true ∧
      (∀ μ, isSuccessor P l μ = isEntry P (P.step x).state μ) ∧
      (∀ i, (storedCount N (P.step x).counter i : ℤ) =
        storedCount N x.counter i + effect P l i) ∧
      (∀ c, zeroTest P l = some c → storedCount N x.counter (Fin.castSucc c) = 0) := by
  have hq : P[x.state]? = some P[x.state] := List.getElem?_eq_getElem hx
  generalize hi : P[x.state] = ins at hq
  cases ins with
  | inc c next =>
    obtain ⟨hs, hf, ht⟩ := inc_tables hq
    refine ⟨stepLabel x.state, ?_, ?_, ?_, ?_⟩
    · simp [isEntry, hq, stepLabel]
    · simpa [Program.step_of_getElem? hq] using hs
    · intro i
      rw [hf]
      simp only [Program.step_of_getElem? hq, Instr.exec_inc_counter] at hN' ⊢
      fin_cases c <;> fin_cases i <;> simp [storedCount, transfer] at hN' ⊢ <;> omega
    · simp [ht]
  | jzdec c z p =>
    by_cases hc : x.counter c = 0
    · obtain ⟨hs, hf, ht⟩ := zero_tables hq
      have hstep := Instr.exec_jzdec_of_eq_zero (z := z) (p := p) hc
      refine ⟨stepLabel x.state, ?_, ?_, ?_, ?_⟩
      · simp [isEntry, hq, stepLabel]
      · simpa [Program.step_of_getElem? hq, hstep] using hs
      · intro i
        simp [hf, Program.step_of_getElem? hq, hstep]
      · intro d hd
        rw [ht] at hd
        cases Option.some.inj hd
        simpa [storedCount_castSucc] using hc
    · obtain ⟨hs, hf, ht⟩ := positive_tables hq
      have hstep := Instr.exec_jzdec_of_ne_zero (z := z) (p := p) hc
      refine ⟨positiveLabel x.state, ?_, ?_, ?_, ?_⟩
      · simp [isEntry, hq, positiveLabel]
      · simpa [Program.step_of_getElem? hq, hstep] using hs
      · intro i
        rw [hf]
        simp only [Program.step_of_getElem? hq, hstep] at hN' ⊢
        fin_cases c <;> fin_cases i <;>
          simp [storedCount, transfer] at hc hN' ⊢ <;> omega
      · simp [ht]

private theorem reachable_build (N : ℕ) :
    ∃ l, Reachable P l (storedCount N (fun _ => 0)) ∧
      ∀ μ, isEntry P 0 μ = true → isSuccessor P l μ = true := by
  have hb : ∃ l, Reachable P l (storedCount N (fun _ => 0)) ∧ l ≤ 1 := by
    induction N with
    | zero =>
      refine ⟨0, ?_, by omega⟩
      convert Reachable.start (P := P) using 1
      funext i; fin_cases i <;> rfl
    | succ N ih =>
      obtain ⟨l, hr, hl⟩ := ih
      refine ⟨1, Reachable.step hr ?_ ?_ ?_, by omega⟩
      · simp [isSuccessor, hl]
      · intro i; fin_cases i <;> simp [storedCount, effect]
      · simp [zeroTest]
  obtain ⟨l, hr, hl⟩ := hb
  refine ⟨l, hr, ?_⟩
  intro μ h
  simp [isSuccessor, hl, h]

private theorem reachable_program (J N : ℕ)
    (hwork : ∀ t < J, (P.run t).state < P.length)
    (hbound : ∀ t ≤ J, (P.run t).counter 0 + (P.run t).counter 1 ≤ N) :
    ∃ l, Reachable P l (storedCount N (P.run J).counter) ∧
      ∀ μ, isEntry P (P.run J).state μ = true → isSuccessor P l μ = true := by
  induction J with
  | zero => simpa only [Program.run_zero, Config.init] using reachable_build (P := P) N
  | succ J ih =>
    obtain ⟨l, hr, he⟩ := ih (fun t ht => hwork t (by omega)) (fun t ht => hbound t (by omega))
    obtain ⟨μ, hm, hn, hf, hz⟩ := exists_stored_step (P.run J) N (hwork J (by omega))
      (hbound J (by omega)) (by simpa [Program.run_succ] using hbound (J + 1) le_rfl)
    refine ⟨μ, ?_, ?_⟩
    · rw [Program.run_succ]
      exact Reachable.step hr (he μ hm) hf hz
    · intro ν hv
      rw [hn]
      simpa [Program.run_succ] using hv

private theorem reachable_unwind (R : ℕ) {l : ℕ}
    (hr : Reachable P l ![0, 0, R])
    (hs : ∀ μ, 4 ≤ μ → μ ≤ 5 → isSuccessor P l μ = true) :
    Reachable P endLabel (fun _ => 0) := by
  induction R generalizing l with
  | zero =>
    apply Reachable.step hr (hs 5 (by omega) le_rfl)
    · intro i; fin_cases i <;> simp [effect]
    · simp [zeroTest]
  | succ R ih =>
    apply ih (l := unwindLabel)
    · apply Reachable.step hr (hs 4 le_rfl (by omega))
      · intro i; fin_cases i <;> simp [effect]
      · simp [zeroTest]
    · intro μ h₄ h₅; simp [isSuccessor, h₄, h₅]

private theorem reachable_drainOne (N b : ℕ) {l : ℕ} (hb : b ≤ N)
    (hr : Reachable P l (storedCount N ![0, b]))
    (hs : ∀ μ, 3 ≤ μ → μ ≤ 5 → isSuccessor P l μ = true) :
    Reachable P endLabel (fun _ => 0) := by
  induction b generalizing l with
  | zero =>
    apply reachable_unwind N
    · simpa [storedCount] using hr
    · intro μ h₄ h₅; exact hs μ (by omega) h₅
  | succ b ih =>
    apply ih (by omega) (l := drainOneLabel)
    · apply Reachable.step hr (hs 3 le_rfl (by omega))
      · intro i; fin_cases i <;> simp [storedCount, effect, transfer]; omega
      · simp [zeroTest]
    · intro μ h₃ h₅; simp [isSuccessor, h₃, h₅]

private theorem reachable_drainZero (N a b : ℕ) {l : ℕ} (hab : a + b ≤ N)
    (hr : Reachable P l (storedCount N ![a, b]))
    (hs : ∀ μ, 2 ≤ μ → μ ≤ 5 → isSuccessor P l μ = true) :
    Reachable P endLabel (fun _ => 0) := by
  induction a generalizing l with
  | zero =>
    apply reachable_drainOne N b (by omega) hr
    intro μ h₃ h₅; exact hs μ (by omega) h₅
  | succ a ih =>
    apply ih (by omega) (l := drainZeroLabel)
    · apply Reachable.step hr (hs 2 le_rfl (by omega))
      · intro i; fin_cases i <;> simp [storedCount, effect, transfer]; omega
      · simp [zeroTest]
    · intro μ h₂ h₅; simp [isSuccessor, h₂, h₅]

/-- A halting program has a balanced exact run: the start label, `N` build-up labels, the
labels of the steps of the run, the drains of both counters, `N` unwind labels and the end
label, where `N` is the largest sum of the two counters along the run. -/
theorem exists_balanced_exactRun (h : P.Halts) : ∃ r : ExactRun P, r.Balanced := by
  classical
  let J := Nat.find h
  have hhalt : P.length ≤ (P.run J).state := Nat.find_spec h
  have hwork : ∀ t < J, (P.run t).state < P.length := by
    intro t ht
    have := Nat.find_min h ht
    exact Nat.lt_of_not_ge this
  let N := (Finset.range (J + 1)).sup (fun t => (P.run t).counter 0 + (P.run t).counter 1)
  have hbound : ∀ t ≤ J, (P.run t).counter 0 + (P.run t).counter 1 ≤ N := by
    intro t ht
    exact Finset.le_sup (f := fun t => (P.run t).counter 0 + (P.run t).counter 1)
      (Finset.mem_range.mpr (by omega))
  obtain ⟨l, hr, hs⟩ := reachable_program J N hwork hbound
  have hfinal : Reachable P endLabel (fun _ => 0) := by
    apply reachable_drainZero N ((P.run J).counter 0) ((P.run J).counter 1)
      (hbound J le_rfl) hr
    intro μ h₂ h₅
    apply hs
    simp [isEntry, List.getElem?_eq_none hhalt, h₂, h₅]
  obtain ⟨r, hl, hc⟩ := hfinal.prefix
  let run : ExactRun P :=
    { last := r.last
      label := r.label
      count := r.count
      label_zero := r.label_zero
      label_last := hl
      count_zero := r.count_zero
      isSuccessor_label := r.successor
      count_succ := r.exact
      count_eq_zero := r.test }
  refine ⟨run, run.balanced_of_count_last_zero ?_⟩
  intro i
  change r.count r.last i = 0
  rw [hc]

/-- A program halts exactly when its label machine has an exact run. -/
theorem halts_iff_nonempty_exactRun : P.Halts ↔ Nonempty (ExactRun P) :=
  ⟨fun h => (exists_balanced_exactRun h).elim fun r _ => ⟨r⟩, fun ⟨r⟩ => r.halts⟩

/-- The balanced exact run of a halting program. -/
noncomputable def ExactRun.ofHalts (h : P.Halts) : ExactRun P :=
  Classical.choose (exists_balanced_exactRun h)

/-- The run `ExactRun.ofHalts h` is balanced. -/
theorem ExactRun.ofHalts_balanced (h : P.Halts) : (ExactRun.ofHalts h).Balanced :=
  Classical.choose_spec (exists_balanced_exactRun h)

/-! ## Example

The program `[inc 0 → 1, jzdec 0 5 1]` increments counter `0` once, decrements it, and jumps
to the state `5` beyond its length. Its labels are `0, …, 9`; label `7` is unused. Its balanced
run has the labels `start, build, step 0, positive branch 1, zero branch 1, unwind, end`. -/

section Example

private def exampleProgram : Program := [.inc 0 1, .jzdec 0 5 1]

example : labelCount exampleProgram = 10 := rfl
example : (List.range 10).filter (isSuccessor exampleProgram 0) = [1, 6] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 1) = [1, 6] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 6) = [8, 9] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 7) = [] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 8) = [2, 3, 4, 5] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 9) = [8, 9] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 3) = [3, 4, 5] := by decide
example : (List.range 10).filter (isSuccessor exampleProgram 5) = [] := by decide
example : [effect exampleProgram 6 0, effect exampleProgram 6 1, effect exampleProgram 6 2] =
    [1, 0, -1] := by decide
example : [effect exampleProgram 9 0, effect exampleProgram 9 1, effect exampleProgram 9 2] =
    [-1, 0, 1] := by decide
example : [effect exampleProgram 8 0, effect exampleProgram 7 0, effect exampleProgram 2 0,
    effect exampleProgram 2 2] = [0, 0, -1, 1] := by decide
example : (List.range 10).map (zeroTest exampleProgram) =
    [none, none, none, none, none, none, none, none, some 0, none] := by decide

private def exampleLabels : List ℕ := [0, 1, 6, 9, 8, 4, 5]

private def exampleCounts : List (List ℕ) :=
  [[0, 0, 0], [0, 0, 1], [1, 0, 0], [0, 0, 1], [0, 0, 1], [0, 0, 0], [0, 0, 0]]

/-- The balanced run of the example program. -/
private def exampleRun : ExactRun exampleProgram where
  last := 6
  label s := exampleLabels.getD s 0
  count s i := (exampleCounts.getD s []).getD i 0
  label_zero := rfl
  label_last := rfl
  count_zero i := by fin_cases i <;> rfl
  isSuccessor_label := by decide
  count_succ := by decide
  count_eq_zero := by decide

example : exampleRun.Balanced := by unfold ExactRun.Balanced; decide

end Example

end Clock

end UndeciSigma2
