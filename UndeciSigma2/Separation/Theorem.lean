import UndeciSigma2.Separation.Arbitrary
import UndeciSigma2.Separation.Regular

/-! # The Σ₂ theories of arbitrary and of regular trees differ

The separating sentence is a Σ₂ sentence whose only atoms are inequalities. It holds over
arbitrary trees and fails over regular trees, in the signature with top and in the signature
without top. At the level of Σ₁ the theories of arbitrary and of regular trees coincide, so
this is the lowest level of the prefix hierarchy at which the two classes can be told apart.
-/

namespace UndeciSigma2

/-- The Σ₂ theories of arbitrary and of regular trees differ, with or without top. -/
theorem sigma2_theories_differ (top : Bool) : ∃ φ : Formula top 0, φ.IsSigma 2 ∧ φ.IsLeOnly ∧
    φ.Holds (Structure.ofClass .arbitrary top) ∧ ¬φ.Holds (Structure.ofClass .regular top) :=
  ⟨separatingSentence top, separatingSentence_isSigma top, separatingSentence_isLeOnly top,
    separatingSentence_holds_arbitrary top, separatingSentence_not_holds_regular top⟩

end UndeciSigma2
