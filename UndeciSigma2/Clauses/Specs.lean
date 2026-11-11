import UndeciSigma2.Sentence.Semantics

/-! # Numeric meaning of the clauses

A counter tree `C` and a state tree `U` describe a run. The state at step `j` is `q`
when `U` contains the stub `1^q 0 1ʲ 0`, and counter `C` at step `j` is at least `x`
when `C` contains the tooth `1ʲ 0 0ˣ`. Each clause of the sentence corresponds to a
numeric statement about these predicates (its specification). The sound direction
derives the specification from the clause; the complete direction derives the clause
from the specification for trees of the intended shape. The last section shows how the
bound specifications determine the value of a counter at the next step.
-/

namespace UndeciSigma2

open Word

namespace Sentence

/-- The state tree has the stub of state `q` at step `j`. -/
def StubAt (U : Tree) (q j : ℕ) : Prop := ones q ++ 0 :: stub j ∈ U.constructorPaths

/-- The counter tree has a tooth of depth at least `x` at step `j`. -/
def ToothAt (C : Tree) (j x : ℕ) : Prop := tooth j x ∈ C.constructorPaths

/-- The comb of state `q` in `U` consists of spine words and stubs. -/
def StubShaped (U : Tree) (q : ℕ) : Prop :=
  ∀ w, ones q ++ 0 :: w ∈ U.constructorPaths → IsOnes w ∨ ∃ j, w = stub j

/-- Every address of `C` is a spine word or a tooth. -/
def IsComb (C : Tree) : Prop :=
  ∀ w ∈ C.constructorPaths, IsOnes w ∨ ∃ j x, w = tooth j x

/-! ## Specifications -/

/-- After a step from state `q`, the counter is at most its previous value plus `1 - δ`
(for positive values only, if `trunc`). -/
def UpperBoundSpec (U C : Tree) (δ : ℕ) (trunc : Bool) (q : ℕ) : Prop :=
  ∀ j x₁ x₂, StubAt U q j → ¬ToothAt C j x₁ → ToothAt C (j + 1) x₂ →
    (trunc = true → 1 ≤ x₂) → x₂ + δ ≤ x₁

/-- After a step from state `q`, the counter is at least its previous value plus `δ - 1`. -/
def LowerBoundSpec (U C : Tree) (δ q : ℕ) : Prop :=
  ∀ j x₁ x₂, StubAt U q j → ToothAt C j x₁ → ¬ToothAt C (j + 1) x₂ → x₁ + δ ≤ x₂

/-- A step from state `q` goes to state `r`. -/
def TransitionSpec (U : Tree) (q r : ℕ) : Prop :=
  ∀ j, StubAt U q j → StubAt U r (j + 1)

/-- After a step from state `q`, the counter has a tooth. -/
def NextToothSpec (U C : Tree) (q : ℕ) : Prop :=
  ∀ j, StubAt U q j → ToothAt C (j + 1) 0

/-- No step is both in state `q` and in state `n`. -/
def HaltUniqueSpec (U : Tree) (n q : ℕ) : Prop :=
  ∀ j, ¬(StubAt U q j ∧ StubAt U n j)

/-- A step from state `q` with the counter zero goes to state `r`. -/
def ZeroTestSpec (U C : Tree) (q r : ℕ) : Prop :=
  ∀ j, StubAt U q j → ¬ToothAt C j 1 → StubAt U r (j + 1)

/-- A step from state `q` with the counter positive goes to state `r`. -/
def PositiveTestSpec (U C : Tree) (q r : ℕ) : Prop :=
  ∀ j, StubAt U q j → ToothAt C j 1 → StubAt U r (j + 1)

/-- The specifications of the clauses of instruction `q`, mirroring `InstructionClauses`. -/
def InstructionSpecs (n : ℕ) (C : Fin 2 → Tree) (U : Tree) (q : ℕ) : Instr → Prop
  | .inc c r =>
    HaltUniqueSpec U n q ∧ TransitionSpec U q (min r n) ∧
      UpperBoundSpec U (C c) 0 false q ∧ LowerBoundSpec U (C c) 2 q ∧
      UpperBoundSpec U (C (otherCounter c)) 1 false q ∧ LowerBoundSpec U (C (otherCounter c)) 1 q
  | .jzdec c z p =>
    HaltUniqueSpec U n q ∧ ZeroTestSpec U (C c) q (min z n) ∧
      PositiveTestSpec U (C c) q (min p n) ∧ UpperBoundSpec U (C c) 2 true q ∧
      LowerBoundSpec U (C c) 0 q ∧ NextToothSpec U (C c) q ∧
      UpperBoundSpec U (C (otherCounter c)) 1 false q ∧ LowerBoundSpec U (C (otherCounter c)) 1 q

/-! ## The next counter value -/

variable {U V : Tree} {q j : ℕ}

/-- Upper and lower bounds with matching offsets determine the counter at the next step: if
the counter is `a` at a step in state `q`, the upper bound with offset `δ` and the lower bound
with offset `ε`, where `a + 1 - δ = b = a + ε - 1`, make it `b` at the next step. -/
theorem toothAt_succ_iff_of_bounds {a b δ ε : ℕ} (hs : StubAt U q j)
    (ha : ∀ x, ToothAt V j x ↔ x ≤ a) (hu : UpperBoundSpec U V δ false q)
    (hl : LowerBoundSpec U V ε q) (hδ : b + δ = a + 1) (hε : a + ε = b + 1) :
    ∀ x, ToothAt V (j + 1) x ↔ x ≤ b := by
  intro x
  have hn : ¬ToothAt V j (a + 1) := fun hx => by
    have := (ha _).mp hx
    omega
  constructor
  · intro hx
    have := hu j (a + 1) x hs hn hx (by simp)
    omega
  · intro hx
    by_contra hn'
    have := hl j a x hs ((ha a).mpr le_rfl) hn'
    omega

/-- The truncated upper bound with offset `2`, the lower bound with offset `0` and the next
tooth determine a decrement: if the counter is `a` at a step in state `q`, it is `a - 1` at
the next step, also when `a = 0`. -/
theorem toothAt_succ_iff_of_decrement {a : ℕ} (hs : StubAt U q j)
    (ha : ∀ x, ToothAt V j x ↔ x ≤ a) (hu : UpperBoundSpec U V 2 true q)
    (hl : LowerBoundSpec U V 0 q) (hn : NextToothSpec U V q) :
    ∀ x, ToothAt V (j + 1) x ↔ x ≤ a - 1 := by
  intro x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · omega
    have hmissing : ¬ToothAt V j (a + 1) := fun ht => by
      have := (ha _).mp ht
      omega
    have := hu j (a + 1) x hs hmissing hx (by omega)
    omega
  · intro hx
    by_cases hx0 : x = 0
    · subst x
      exact hn j hs
    by_contra hmissing
    have := hl j a x hs ((ha a).mpr le_rfl) hmissing
    omega

end Sentence

end UndeciSigma2
