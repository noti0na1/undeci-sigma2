import UndeciSigma2.Recurrence.Soundness
import UndeciSigma2.Recurrence.Completeness

/-! # Correctness of the recurrence reduction

Over arbitrary trees, with or without top, the recurrence sentence of a nondeterministic
two-counter program holds exactly when the program has an infinite run visiting state `0`
infinitely often. Its prenex negation is a Π₂ sentence that holds exactly when the program
does not recur.
-/

namespace UndeciSigma2

open Recurrence

/-- Over arbitrary trees, with or without top, the recurrence sentence holds if and only if
the program recurs. -/
theorem recurrenceSentence_holds_iff (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).Holds (Structure.ofClass .arbitrary top) ↔ P.Recurs := by
  rw [recurrenceSentence_holds_iff_recurrenceConditions]
  exact ⟨recurs_of_recurrenceConditions, recurrenceConditions_of_recurs⟩

/-- The prenex negation of the recurrence sentence is syntactically Π₂. -/
theorem recurrenceSentence_negate_isPi (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).negate.IsPi 2 :=
  (Formula.isPi_negate_iff 2 _).mpr (recurrenceSentence_isSigma top P)

/-- The prenex negation of the recurrence sentence uses inequality as its only kind of atom. -/
theorem recurrenceSentence_negate_isLeOnly (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).negate.IsLeOnly :=
  (recurrenceSentence_isLeOnly top P).negate

/-- Over arbitrary trees, the prenex negation holds if and only if the program does not
recur. -/
theorem recurrenceSentence_negate_holds_iff (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).negate.Holds (Structure.ofClass .arbitrary top) ↔ ¬P.Recurs := by
  rw [Formula.Holds, Formula.realize_negate]
  exact not_congr (recurrenceSentence_holds_iff top P)

end UndeciSigma2
