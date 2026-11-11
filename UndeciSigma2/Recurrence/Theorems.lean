import UndeciSigma2.Recurrence.Computable
import UndeciSigma2.Recurrence.Correctness
import UndeciSigma2.Undecidability.Fragments
import Mathlib.Computability.Reduce
import Mathlib.Computability.RE

/-! # Recurrence and the Σ₂ theory of arbitrary trees

The recurrence sentence gives a many-one reduction from the recurrence problem of
nondeterministic two-counter machines to truth of Σ₂ sentences over arbitrary trees, with or
without top. Recurrence is Σ¹₁-complete (Alur and Henzinger 1994, after Harel, Pnueli and
Stavi 1983); in particular neither it nor its complement is recursively enumerable. These facts
are not formalized here. Assuming them as hypotheses, truth of Σ₂ sentences over arbitrary trees
is not recursively enumerable, and neither is their falsity.
-/

namespace UndeciSigma2

/-- Recursive enumerability transfers backwards along many-one reductions. -/
theorem rePred_of_manyOneReducible {α β : Type} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} (h : ManyOneReducible p q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hpq⟩ := h
  have : REPred fun a => q (f a) := Partrec.comp hq hf
  exact this.of_eq fun a => (hpq a).symm

/-- The recurrence sentence of a program, as a Σ₂ sentence. -/
def recurrenceSigmaSentence (top : Bool) (P : NProgram) : {φ : Formula top 0 // φ.IsSigma 2} :=
  ⟨recurrenceSentence top P, recurrenceSentence_isSigma top P⟩

theorem computable_recurrenceSigmaSentence (top : Bool) :
    Computable (recurrenceSigmaSentence top) :=
  Computable.subtype_mk (Computability.primrec_isSigma 2) (computable_recurrenceSentence top)

/-- Recurrence of nondeterministic two-counter machines is many-one reducible to truth of
sentences over arbitrary trees, with or without top. -/
theorem recurrence_manyOne (top : Bool) :
    ManyOneReducible NProgram.Recurs
      (fun φ : Formula top 0 => φ.Holds (Structure.ofClass .arbitrary top)) :=
  ⟨recurrenceSentence top, computable_recurrenceSentence top,
    fun P => (recurrenceSentence_holds_iff top P).symm⟩

/-- Recurrence of nondeterministic two-counter machines is many-one reducible to truth of Σ₂
sentences over arbitrary trees, with or without top. -/
theorem recurrence_manyOne_sigma2 (top : Bool) :
    ManyOneReducible NProgram.Recurs
      (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
        φ.1.Holds (Structure.ofClass .arbitrary top)) :=
  ⟨recurrenceSigmaSentence top, computable_recurrenceSigmaSentence top,
    fun P => (recurrenceSentence_holds_iff top P).symm⟩

/-- Non-recurrence of nondeterministic two-counter machines is many-one reducible to falsity of
Σ₂ sentences over arbitrary trees, with or without top. -/
theorem nonrecurrence_manyOne_sigma2 (top : Bool) :
    ManyOneReducible (fun P : NProgram => ¬P.Recurs)
      (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
        ¬φ.1.Holds (Structure.ofClass .arbitrary top)) :=
  ⟨recurrenceSigmaSentence top, computable_recurrenceSigmaSentence top,
    fun P => not_congr (recurrenceSentence_holds_iff top P).symm⟩

/-- If recurrence of nondeterministic two-counter machines is not recursively enumerable, then
truth of Σ₂ sentences over arbitrary trees, with or without top, is not recursively
enumerable. -/
theorem sigma2_truth_not_re (hRecurs : ¬REPred NProgram.Recurs) (top : Bool) :
    ¬REPred (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
      φ.1.Holds (Structure.ofClass .arbitrary top)) :=
  fun h => hRecurs (rePred_of_manyOneReducible (recurrence_manyOne_sigma2 top) h)

/-- If non-recurrence of nondeterministic two-counter machines is not recursively enumerable,
then falsity of Σ₂ sentences over arbitrary trees, with or without top, is not recursively
enumerable. -/
theorem sigma2_falsity_not_re (hNonrecurs : ¬REPred fun P : NProgram => ¬P.Recurs)
    (top : Bool) :
    ¬REPred (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
      ¬φ.1.Holds (Structure.ofClass .arbitrary top)) :=
  fun h => hNonrecurs (rePred_of_manyOneReducible (nonrecurrence_manyOne_sigma2 top) h)

end UndeciSigma2
