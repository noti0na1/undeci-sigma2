import UndeciSigma2.Undecidability.Computable
import UndeciSigma2.Reduction.Correctness
import Mathlib.Computability.Reduce

/-! # Undecidability over regular and arbitrary trees

The machine sentence gives a many-one reduction from halting of two-counter
machines to truth of Σ₂ sentences. Its prenex negation reduces non-halting to
truth of Π₂ sentences, so a decision procedure for Π₂ truth would decide halting
by complementation. Assuming that halting is undecidable, Σ₂ truth and Π₂ truth
are not computable over regular trees and over arbitrary trees, with or without
top. Over finite trees the helper equations of the machine sentence have no
solution; all six structures, finite trees included, are treated by the clock
sentence (`sigma2_undecidable` in `Clock/Theorems.lean`).
-/

namespace UndeciSigma2

/-- Halting of two-counter machines is many-one reducible to truth of sentences over regular
and over arbitrary trees. -/
theorem machineSentence_manyOne (top : Bool) (c : TreeClass) (hc : c ≠ .finite) :
    ManyOneReducible Program.Halts
      (fun φ : Formula top 0 => φ.Holds (Structure.ofClass c top)) :=
  ⟨machineSentence top, computable_machineSentence top,
    fun P => (machineSentence_holds_iff top P c hc).symm⟩

/-- If halting of two-counter machines is undecidable, then no computable function decides
the truth of Σ₂ sentences over regular or over arbitrary trees, with or without top.
A decider composed with `machineSentence` would decide halting. -/
theorem sigma2_undecidable_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsSigma 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  apply hHalt
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun P => d (machineSentence top P), hd.comp (computable_machineSentence top), ?_⟩
  funext P
  exact propext ((machineSentence_holds_iff top P c hc).symm.trans
    (hcorrect _ (machineSentence_isSigma top P)).symm)

/-- If halting of two-counter machines is undecidable, then no computable function decides
the truth of Π₂ sentences over regular or over arbitrary trees, with or without top.
A decider composed with the prenex negation of `machineSentence` would decide non-halting. -/
theorem pi2_undecidable_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsPi 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  have hn : ComputablePred (fun P : Program => ¬P.Halts) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun P => d (machineSentence top P).negate,
      hd.comp (computable_machineSentence_negate top), ?_⟩
    funext P
    exact propext ((machineSentence_negate_holds_iff top P c hc).symm.trans
      (hcorrect _ (machineSentence_negate_isPi top P)).symm)
  apply hHalt
  simpa only [not_not] using hn.not

/-- If halting of two-counter machines is undecidable, then truth of first-order sentences
is not computable over regular or over arbitrary trees, with or without top. -/
theorem truth_not_computable_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬ComputablePred (fun φ : Formula top 0 => φ.Holds (Structure.ofClass c top)) :=
  fun h => hHalt (ComputablePred.computable_of_manyOneReducible
    (machineSentence_manyOne top c hc) h)

end UndeciSigma2
