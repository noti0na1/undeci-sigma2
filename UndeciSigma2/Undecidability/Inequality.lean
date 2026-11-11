import UndeciSigma2.Undecidability.Theorems

/-! # The language with inequality as its only predicate

The machine sentence and its prenex negation use inequality as their only kind
of atom. Hence Σ₂ truth and Π₂ truth remain undecidable over regular and over
arbitrary trees when restricted to sentences built from inequality atoms. The same
holds in all six structures by the clock sentence (`sigma2_undecidable_le`).
-/

namespace UndeciSigma2

/-- If halting of two-counter machines is undecidable, Σ₂ truth is undecidable even on the
sentences whose only atoms are inequalities. -/
theorem sigma2_undecidable_le_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsLeOnly → φ.IsSigma 2 →
        (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  apply hHalt
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun P => d (machineSentence top P), hd.comp (computable_machineSentence top), ?_⟩
  funext P
  exact propext ((machineSentence_holds_iff top P c hc).symm.trans
    (hcorrect _ (machineSentence_isLeOnly top P) (machineSentence_isSigma top P)).symm)

/-- If halting of two-counter machines is undecidable, Π₂ truth is undecidable even on the
sentences whose only atoms are inequalities. -/
theorem pi2_undecidable_le_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsLeOnly → φ.IsPi 2 →
        (d φ = true ↔ φ.Holds (Structure.ofClass c top)) := by
  rintro ⟨d, hd, hcorrect⟩
  have hn : ComputablePred (fun P : Program => ¬P.Halts) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun P => d (machineSentence top P).negate,
      hd.comp (computable_machineSentence_negate top), ?_⟩
    funext P
    exact propext ((machineSentence_negate_holds_iff top P c hc).symm.trans
      (hcorrect _ (machineSentence_negate_isLeOnly top P)
        (machineSentence_negate_isPi top P)).symm)
  apply hHalt
  simpa only [not_not] using hn.not

end UndeciSigma2
