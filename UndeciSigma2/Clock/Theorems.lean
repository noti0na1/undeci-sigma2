import UndeciSigma2.Clock.Correctness
import UndeciSigma2.Clock.Computable
import Mathlib.Computability.Reduce

/-! # Undecidability in all six structures

The clock sentence gives a many-one reduction from halting of two-counter machines to truth of
Σ₂ sentences in each of the six structures: finite, regular and arbitrary trees, with or
without top. Its prenex negation reduces non-halting to truth of Π₂ sentences. Assuming that
halting is undecidable, Σ₂ truth and Π₂ truth are not computable in any of the six structures,
even on the sentences whose only atoms are inequalities.
-/

namespace UndeciSigma2

/-- Halting of two-counter machines is many-one reducible to truth of sentences in each of the
six structures. -/
theorem clockSentence_manyOne (top : Bool) (c : TreeClass) :
    ManyOneReducible Program.Halts
      (fun φ : Formula top 0 => φ.Holds (Structure.ofClass c top)) :=
  ⟨clockSentence top, computable_clockSentence top,
    fun P => (clockSentence_holds_iff top P c).symm⟩

/-- If halting of two-counter machines is undecidable, then no computable function decides the
truth of Σ₂ sentences in any of the six structures. -/
theorem sigma2_undecidable (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsSigma 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  apply hHalt
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun P => d (clockSentence top P), hd.comp (computable_clockSentence top), ?_⟩
  funext P
  exact propext ((clockSentence_holds_iff top P c).symm.trans
    (hcorrect _ (clockSentence_isSigma top P)).symm)

/-- If halting of two-counter machines is undecidable, then no computable function decides the
truth of Π₂ sentences in any of the six structures. -/
theorem pi2_undecidable (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsPi 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  have hn : ComputablePred (fun P : Program => ¬P.Halts) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun P => d (clockSentence top P).negate,
      hd.comp (computable_clockSentence_negate top), ?_⟩
    funext P
    exact propext ((clockSentence_negate_holds_iff top P c).symm.trans
      (hcorrect _ (clockSentence_negate_isPi top P)).symm)
  apply hHalt
  simpa only [not_not] using hn.not

/-- If halting of two-counter machines is undecidable, Σ₂ truth is undecidable in each of the
six structures even on the sentences whose only atoms are inequalities. -/
theorem sigma2_undecidable_le (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsLeOnly → φ.IsSigma 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  apply hHalt
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun P => d (clockSentence top P), hd.comp (computable_clockSentence top), ?_⟩
  funext P
  exact propext ((clockSentence_holds_iff top P c).symm.trans
    (hcorrect _ (clockSentence_isLeOnly top P) (clockSentence_isSigma top P)).symm)

/-- If halting of two-counter machines is undecidable, Π₂ truth is undecidable in each of the
six structures even on the sentences whose only atoms are inequalities. -/
theorem pi2_undecidable_le (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsLeOnly → φ.IsPi 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  have hn : ComputablePred (fun P : Program => ¬P.Halts) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun P => d (clockSentence top P).negate,
      hd.comp (computable_clockSentence_negate top), ?_⟩
    funext P
    exact propext ((clockSentence_negate_holds_iff top P c).symm.trans
      (hcorrect _ (clockSentence_negate_isLeOnly top P) (clockSentence_negate_isPi top P)).symm)
  apply hHalt
  simpa only [not_not] using hn.not

/-- If halting of two-counter machines is undecidable, truth of first-order sentences is not
computable in any of the six structures. -/
theorem truth_not_computable (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬ComputablePred (fun φ : Formula top 0 => φ.Holds (Structure.ofClass c top)) :=
  fun h => hHalt (ComputablePred.computable_of_manyOneReducible (clockSentence_manyOne top c) h)

end UndeciSigma2
