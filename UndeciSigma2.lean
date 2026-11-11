import UndeciSigma2.Tree
import UndeciSigma2.Order
import UndeciSigma2.Syntax
import UndeciSigma2.Computable.Renaming
import UndeciSigma2.Undecidability.Fragments
import UndeciSigma2.Machine
import UndeciSigma2.Words
import UndeciSigma2.Trees.Basic
import UndeciSigma2.Trees.Iterate
import UndeciSigma2.Trees.Helpers
import UndeciSigma2.Trees.Contexts
import UndeciSigma2.Sentence.Blocks
import UndeciSigma2.Sentence.Definition
import UndeciSigma2.Sentence.Semantics
import UndeciSigma2.Clauses.Specs
import UndeciSigma2.Clauses.Sound
import UndeciSigma2.Clauses.Complete
import UndeciSigma2.Reduction.Soundness
import UndeciSigma2.Reduction.Completeness
import UndeciSigma2.Reduction.Correctness
import UndeciSigma2.Undecidability.Computable
import UndeciSigma2.Undecidability.Theorems
import UndeciSigma2.Undecidability.Inequality
import UndeciSigma2.Separation.Theorem
import UndeciSigma2.Recurrence.Theorems
import UndeciSigma2.Clock.Theorems

/-! # Undecidability of the Σ₂ theory of non-structural subtyping

This module imports the whole development. Its main result is a many-one reduction from
halting of two-counter machines to truth of Σ₂ sentences over subtype constraints by the clock
sentence, correct in all six structures (finite, regular and arbitrary trees, with or without
top) and primitive recursive; assuming that halting is undecidable, Σ₂ truth and Π₂ truth are
undecidable in each of the six structures.

The development also contains a first, simpler reduction by the machine sentence, which uses
infinite helper trees and is correct over regular and arbitrary trees; a Σ₂ sentence that
holds over arbitrary trees and fails over regular trees; and a reduction from the recurrence
problem of nondeterministic two-counter machines to truth of Σ₂ sentences over arbitrary trees.
-/
