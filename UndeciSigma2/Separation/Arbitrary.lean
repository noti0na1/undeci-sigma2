import UndeciSigma2.Separation.Sentence

/-! # The separating sentence over arbitrary trees

Enumerate all words `w₀, w₁, …` and let `cₙ = w₀ w₁ ⋯ wₙ₋₁`. The words `cₙ` increase by
prefix, so their prefixes form a set of pairwise comparable words, the address set of a
top-free tree `x`. Two prefix-closed subsets of such a set are comparable, so any two
top-free trees below `x` are comparable. A top-free tree `d` with `d ≤ f(h, k)`, `h ≤ d`
and `k ≤ d` has an address set closed under removing the first letter. If `x ≤ d`, it
contains every `cₙ₊₁ = cₙ wₙ`, hence every word `wₙ`, so `d` is the full tree. Thus `x`
witnesses the separating sentence over arbitrary trees.
-/

namespace UndeciSigma2

open UndeciSigma2.Tree

namespace Separation

/-! ## Chains of addresses -/

/-- Two prefix-closed subsets of a set of pairwise comparable words are comparable. -/
theorem subset_or_subset_of_chain {X A B : Set Word}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a <+: b ∨ b <+: a) (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hA : ∀ a b, a <+: b → b ∈ A → a ∈ A) (hB : ∀ a b, a <+: b → b ∈ B → a ∈ B) :
    A ⊆ B ∨ B ⊆ A := by
  by_contra h
  simp only [not_or, Set.not_subset] at h
  obtain ⟨⟨a, haA, haB⟩, ⟨b, hbB, hbA⟩⟩ := h
  rcases hX a (hAX haA) b (hBX hbB) with hab | hba
  · exact haB (hB a b hab hbB)
  · exact hbA (hA b a hba haA)

/-- Two top-free trees below a top-free tree whose addresses are pairwise comparable by
prefix are comparable. -/
theorem le_or_le_of_chain {x u v : Tree} (hx : x.TopFree) (hu : u.TopFree) (hv : v.TopFree)
    (hchain : ∀ a ∈ x.constructorPaths, ∀ b ∈ x.constructorPaths, a <+: b ∨ b <+: a)
    (hux : u ≤ x) (hvx : v ≤ x) : u ≤ v ∨ v ≤ u := by
  rw [le_iff_constructorPaths_subset hu hv, le_iff_constructorPaths_subset hv hu]
  exact subset_or_subset_of_chain hchain ((le_iff_constructorPaths_subset hu hx).mp hux)
    ((le_iff_constructorPaths_subset hv hx).mp hvx)
    (fun _ _ h hb => mem_constructorPaths_of_prefix h hb)
    (fun _ _ h hb => mem_constructorPaths_of_prefix h hb)

/-! ## Trees closed under removing the first letter -/

/-- If `d ≤ f(h, k)`, `h ≤ d` and `k ≤ d` for top-free trees, the addresses of `d` are closed
under removing the first letter. -/
theorem mem_of_cons_mem {d h k : Tree} (hd : d.TopFree) (hh : h.TopFree) (hk : k.TopFree)
    (hdf : d ≤ f h k) (hhd : h ≤ d) (hkd : k ≤ d) {i : Fin 2} {r : Word}
    (hr : i :: r ∈ d.constructorPaths) : r ∈ d.constructorPaths := by
  obtain ⟨h₀, h₁⟩ := (le_f_iff hh hk hd).mp hdf
  obtain rfl | rfl := Word.letter_eq_zero_or_eq_one i
  · exact (le_iff_constructorPaths_subset hh hd).mp hhd (h₀ r hr)
  · exact (le_iff_constructorPaths_subset hk hd).mp hkd (h₁ r hr)

/-- A set of words closed under removing the first letter contains every suffix of its
elements. -/
theorem mem_of_append_mem {S : Set Word} (hS : ∀ (i : Fin 2) r, i :: r ∈ S → r ∈ S)
    (p : Word) {r : Word} (h : p ++ r ∈ S) : r ∈ S := by
  induction p with
  | nil => exact h
  | cons i p ih => exact ih (hS i _ h)

/-! ## A chain containing every word as a factor -/

/-- An enumeration of all words. -/
noncomputable def enumWord (n : ℕ) : Word := (Encodable.decode n).getD []

theorem enumWord_surjective : Function.Surjective enumWord := fun w =>
  ⟨Encodable.encode w, by simp [enumWord, Encodable.encodek]⟩

/-- The concatenation `w₀ w₁ ⋯ wₙ₋₁` of the first `n` enumerated words. -/
noncomputable def disjunctivePrefix : ℕ → Word
  | 0 => []
  | n + 1 => disjunctivePrefix n ++ enumWord n

theorem disjunctivePrefix_prefix {m n : ℕ} (h : m ≤ n) :
    disjunctivePrefix m <+: disjunctivePrefix n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ n _ ih => exact ih.trans (List.prefix_append _ _)

/-- The prefixes of the words `disjunctivePrefix n`. -/
def disjunctiveSet : Set Word := {p | ∃ n, p <+: disjunctivePrefix n}

theorem disjunctiveSet_prefixClosed : PrefixClosed disjunctiveSet := by
  rintro p r ⟨n, hn⟩
  exact ⟨n, (List.prefix_append p r).trans hn⟩

/-- The top-free tree whose addresses are the prefixes of an infinite word containing every
word as a factor. -/
noncomputable def disjunctiveChain : Tree :=
  ofConstructorPaths disjunctiveSet disjunctiveSet_prefixClosed

@[simp] theorem disjunctiveChain_constructorPaths :
    disjunctiveChain.constructorPaths = disjunctiveSet :=
  ofConstructorPaths_constructorPaths _ _

theorem topFree_disjunctiveChain : disjunctiveChain.TopFree :=
  ofConstructorPaths_topFree _ _

/-- The addresses of the disjunctive chain are pairwise comparable by prefix. -/
theorem disjunctiveChain_chain :
    ∀ a ∈ disjunctiveChain.constructorPaths, ∀ b ∈ disjunctiveChain.constructorPaths,
      a <+: b ∨ b <+: a := by
  simp only [disjunctiveChain_constructorPaths]
  rintro a ⟨m, ha⟩ b ⟨n, hb⟩
  rcases le_total m n with hmn | hnm
  · exact List.prefix_or_prefix_of_prefix (ha.trans (disjunctivePrefix_prefix hmn)) hb
  · exact List.prefix_or_prefix_of_prefix ha (hb.trans (disjunctivePrefix_prefix hnm))

/-- A top-free tree above the disjunctive chain whose addresses are closed under removing
the first letter is the full tree. -/
theorem full_le_of_disjunctiveChain_le {d : Tree} (hd : d.TopFree)
    (hS : ∀ (i : Fin 2) r, i :: r ∈ d.constructorPaths → r ∈ d.constructorPaths)
    (hxd : disjunctiveChain ≤ d) : full ≤ d := by
  have hsub := (le_iff_constructorPaths_subset topFree_disjunctiveChain hd).mp hxd
  refine le_of_subset topFree_full fun w _ => ?_
  obtain ⟨n, rfl⟩ := enumWord_surjective w
  apply mem_of_append_mem hS (disjunctivePrefix n)
  apply hsub
  rw [disjunctiveChain_constructorPaths]
  exact ⟨n + 1, List.prefix_rfl⟩

end Separation

open Separation

/-- The separating sentence holds over arbitrary trees, with or without top. -/
theorem separatingSentence_holds_arbitrary (top : Bool) :
    (separatingSentence top).Holds (Structure.ofClass .arbitrary top) := by
  rw [separatingSentence_holds_ofClass_iff]
  refine ⟨domain_arbitrary_of_topFree topFree_full, disjunctiveChain,
    domain_arbitrary_of_topFree topFree_disjunctiveChain, topFree_disjunctiveChain, ?_, ?_⟩
  · intro u v _ hu _ hv hux hvx
    exact le_or_le_of_chain topFree_disjunctiveChain hu hv disjunctiveChain_chain hux hvx
  · intro d h k _ hd _ hh _ hk hxd hdf _ hhd hkd
    exact full_le_of_disjunctiveChain_le hd
      (fun _ _ hr => mem_of_cons_mem hd hh hk hdf hhd hkd hr) hxd

end UndeciSigma2
