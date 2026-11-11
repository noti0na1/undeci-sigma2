import UndeciSigma2.Clock.Soundness
import UndeciSigma2.Clock.Completeness

/-! # Correctness of the clock sentence

In each of the six structures, finite, regular or arbitrary trees, with or without top, the
clock sentence of a program holds exactly when the program halts. Its prenex negation is a Π₂
sentence that holds exactly when the program does not halt.
-/

namespace UndeciSigma2

open Clock

/-- In each of the six structures, the clock sentence holds if and only if the program
halts. -/
theorem clockSentence_holds_iff (top : Bool) (P : Program) (c : TreeClass) :
    (clockSentence top P).Holds (Structure.ofClass c top) ↔ P.Halts := by
  rw [clockSentence_holds_iff_clockConditions]
  exact ⟨halts_of_clockConditions, clockConditions_of_halts⟩

/-- The prenex negation of the clock sentence is syntactically Π₂. -/
theorem clockSentence_negate_isPi (top : Bool) (P : Program) :
    (clockSentence top P).negate.IsPi 2 :=
  (Formula.isPi_negate_iff 2 _).mpr (clockSentence_isSigma top P)

/-- The prenex negation of the clock sentence uses inequality as its only kind of atom. -/
theorem clockSentence_negate_isLeOnly (top : Bool) (P : Program) :
    (clockSentence top P).negate.IsLeOnly :=
  (clockSentence_isLeOnly top P).negate

/-- In each of the six structures, the prenex negation holds if and only if the program does
not halt. -/
theorem clockSentence_negate_holds_iff (top : Bool) (P : Program) (c : TreeClass) :
    (clockSentence top P).negate.Holds (Structure.ofClass c top) ↔ ¬P.Halts := by
  rw [Formula.Holds, Formula.realize_negate]
  exact not_congr (clockSentence_holds_iff top P c)

end UndeciSigma2
