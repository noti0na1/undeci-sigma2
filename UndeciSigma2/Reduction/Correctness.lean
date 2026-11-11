import UndeciSigma2.Reduction.Soundness
import UndeciSigma2.Reduction.Completeness

/-! # Correctness of the reduction

Over regular and over arbitrary trees, with or without top, the machine sentence of a
program holds exactly when the program halts. Its prenex negation is a Π₂ sentence that
holds exactly when the program does not halt. The hypothesis `c ≠ .finite` is needed: the
helper trees of the machine sentence are infinite. The clock sentence
(`clockSentence_holds_iff`) is correct in all six structures, finite trees included.
-/

namespace UndeciSigma2

open Sentence

/-- Over regular and over arbitrary trees, with or without top, the machine sentence holds
if and only if the program halts. -/
theorem machineSentence_holds_iff (top : Bool) (P : Program) (c : TreeClass)
    (hc : c ≠ .finite) :
    (machineSentence top P).Holds (Structure.ofClass c top) ↔ P.Halts := by
  rw [machineSentence_holds_iff_machineConditions top P hc]
  exact ⟨halts_of_machineConditions hc, machineConditions_of_halts⟩

/-- The prenex negation of the machine sentence is syntactically Π₂. -/
theorem machineSentence_negate_isPi (top : Bool) (P : Program) :
    (machineSentence top P).negate.IsPi 2 :=
  (Formula.isPi_negate_iff 2 _).mpr (machineSentence_isSigma top P)

/-- The prenex negation of the machine sentence uses inequality as its only kind of atom. -/
theorem machineSentence_negate_isLeOnly (top : Bool) (P : Program) :
    (machineSentence top P).negate.IsLeOnly :=
  (machineSentence_isLeOnly top P).negate

/-- The prenex negation holds if and only if the program does not halt. -/
theorem machineSentence_negate_holds_iff (top : Bool) (P : Program) (c : TreeClass)
    (hc : c ≠ .finite) :
    (machineSentence top P).negate.Holds (Structure.ofClass c top) ↔ ¬P.Halts := by
  rw [Formula.Holds, Formula.realize_negate]
  exact not_congr (machineSentence_holds_iff top P c hc)

end UndeciSigma2
