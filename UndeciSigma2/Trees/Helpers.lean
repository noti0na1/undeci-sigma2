import UndeciSigma2.Trees.Iterate

/-! # The helper trees of the reduction

Six regular top-free trees are fixed in the sentence by guarded equations:

| tree | equation | addresses |
|---|---|---|
| `full` | `X = f(X, X)` | all words |
| `rightRay` | `X = f(⊥, X)` | `1*` |
| `stubComb` | `X = f(e, X)` | `1*` and the stubs `1ʲ 0` |
| `leftRay` | `X = f(X, ⊥)` | `0*` |
| `combUniverse` | `X = f(leftRay, X)` | `1*` and the teeth `1ʲ 0 0ˣ` |
| `shortCombs` | `X = f(f(e, ⊥), X)` | `1*` and the teeth `1ʲ 0` and `1ʲ 0 0` |

Each equation has exactly one solution in every signature. None of the six trees
is finite.
-/

namespace UndeciSigma2

open Word

namespace Tree

/-- The right ray, with addresses `1*`. -/
def rightRay : Tree := rightSpine bot

/-- The comb of stubs, with addresses `1*` and the stubs. -/
def stubComb : Tree := rightSpine e

/-- The left ray, with addresses `0*`. -/
def leftRay : Tree := leftSpine bot

/-- The comb universe, with addresses `1*` and all teeth: every comb lies below it. -/
def combUniverse : Tree := rightSpine leftRay

/-- The universe of combs with teeth of depth at most one, with addresses `1*`, `1ʲ 0` and
`1ʲ 0 0`. -/
def shortCombs : Tree := rightSpine (f e bot)

/-! ## Equations and uniqueness -/

theorem rightRay_eq : rightRay = f bot rightRay := rightSpine_eq bot
theorem stubComb_eq : stubComb = f e stubComb := rightSpine_eq e
theorem leftRay_eq : leftRay = f leftRay bot := leftSpine_eq bot
theorem combUniverse_eq : combUniverse = f leftRay combUniverse := rightSpine_eq leftRay
theorem shortCombs_eq : shortCombs = f (f e bot) shortCombs := rightSpine_eq (f e bot)

theorem eq_rightRay_of_eq {x : Tree} (h : x = f bot x) : x = rightRay := eq_rightSpine_of_eq h
theorem eq_stubComb_of_eq {x : Tree} (h : x = f e x) : x = stubComb := eq_rightSpine_of_eq h
theorem eq_leftRay_of_eq {x : Tree} (h : x = f x bot) : x = leftRay := eq_leftSpine_of_eq h
theorem eq_combUniverse_of_eq {x : Tree} (h : x = f leftRay x) : x = combUniverse :=
  eq_rightSpine_of_eq h
theorem eq_shortCombs_of_eq {x : Tree} (h : x = f (f e bot) x) : x = shortCombs :=
  eq_rightSpine_of_eq h

/-! ## Addresses -/

theorem mem_constructorPaths_rightRay (w : Word) :
    w ∈ rightRay.constructorPaths ↔ IsOnes w := by
  simp [rightRay, mem_constructorPaths_rightSpine]

theorem mem_constructorPaths_stubComb (w : Word) :
    w ∈ stubComb.constructorPaths ↔ IsOnes w ∨ ∃ j, w = stub j := by
  rw [stubComb, mem_constructorPaths_rightSpine]
  simp only [mem_constructorPaths_e, exists_eq_left]
  rfl

theorem mem_constructorPaths_leftRay (w : Word) :
    w ∈ leftRay.constructorPaths ↔ ∃ x, w = zeros x := by
  simp [leftRay, mem_constructorPaths_leftSpine]

theorem mem_constructorPaths_combUniverse (w : Word) :
    w ∈ combUniverse.constructorPaths ↔ IsOnes w ∨ ∃ j x, w = tooth j x := by
  rw [combUniverse, mem_constructorPaths_rightSpine]
  simp only [mem_constructorPaths_leftRay]
  constructor
  · rintro (h | ⟨j, v, ⟨x, rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, x, rfl⟩
  · rintro (h | ⟨j, x, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, zeros x, ⟨x, rfl⟩, rfl⟩

/-- The addresses of `f(e, ⊥)` are the root and its left child. -/
theorem mem_constructorPaths_f_e_bot (w : Word) :
    w ∈ (f e bot).constructorPaths ↔ w = [] ∨ w = [0] := by
  rcases w with _ | ⟨b, w⟩
  · simp
  · obtain rfl | rfl := letter_eq_zero_or_eq_one b
    · simp [mem_constructorPaths_e]
    · simp

theorem mem_constructorPaths_shortCombs (w : Word) :
    w ∈ shortCombs.constructorPaths ↔ IsOnes w ∨ ∃ j, w = tooth j 0 ∨ w = tooth j 1 := by
  rw [shortCombs, mem_constructorPaths_rightSpine]
  simp only [mem_constructorPaths_f_e_bot]
  constructor
  · rintro (h | ⟨j, v, rfl | rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, Or.inl rfl⟩
    · exact Or.inr ⟨j, Or.inr rfl⟩
  · rintro (h | ⟨j, rfl | rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, [], Or.inl rfl, rfl⟩
    · exact Or.inr ⟨j, [0], Or.inr rfl, rfl⟩

/-! ## Top-freeness and regularity -/

@[simp] theorem topFree_rightRay : rightRay.TopFree := topFree_rightSpine topFree_bot
@[simp] theorem topFree_stubComb : stubComb.TopFree := topFree_rightSpine topFree_e
@[simp] theorem topFree_leftRay : leftRay.TopFree := topFree_leftSpine topFree_bot
@[simp] theorem topFree_combUniverse : combUniverse.TopFree := topFree_rightSpine topFree_leftRay
@[simp] theorem topFree_shortCombs : shortCombs.TopFree :=
  topFree_rightSpine ((topFree_f _ _).mpr ⟨topFree_e, topFree_bot⟩)

theorem regular_rightRay : rightRay.IsRegular := regular_rightSpine regular_bot
theorem regular_stubComb : stubComb.IsRegular := regular_rightSpine finite_e.isRegular
theorem regular_leftRay : leftRay.IsRegular := regular_leftSpine regular_bot
theorem regular_combUniverse : combUniverse.IsRegular := regular_rightSpine regular_leftRay
theorem regular_shortCombs : shortCombs.IsRegular :=
  regular_rightSpine (finite_f finite_e finite_bot).isRegular

end Tree

end UndeciSigma2
