import UndeciSigma2.Sentence.Blocks
import UndeciSigma2.Trees.Basic

/-! # A Σ₂ sentence separating arbitrary from regular trees

The separating sentence has the prefix `∃ Z x ∀ u v d h k` and a quantifier-free matrix
whose atoms are inequalities:
```
  Z ≤ f(Z, Z) ∧ f(Z, Z) ≤ Z ∧ x ≤ Z
  ∧ (u ≤ Z ∧ v ≤ Z ∧ d ≤ Z ∧ h ≤ Z ∧ k ≤ Z →
      (u ≤ x ∧ v ≤ x → u ≤ v ∨ v ≤ u)
      ∧ (x ≤ d ∧ d ≤ f(h, k) ∧ f(h, k) ≤ d ∧ h ≤ d ∧ k ≤ d → Z ≤ d))
```
The two equations make `Z` the full tree, so the guards `· ≤ Z` say that the values
contain no top. On top-free trees the order is inclusion of constructor addresses. The
first clause then says that any two trees below `x` are comparable, and the second that
every tree `d` above `x` whose addresses contain the empty word and are closed under
removing the first letter is the full tree.

This file defines the sentence, shows that it is a Σ₂ sentence with inequality atoms only,
and reduces its truth in each of the six structures to a statement about trees
(`separatingSentence_holds_ofClass_iff`).
-/

namespace UndeciSigma2

open UndeciSigma2.Tree UndeciSigma2.Sentence

/-! ## Syntax -/

section Syntax
variable {top : Bool} {m : ℕ}

/-- The matrix of the separating sentence, for terms `Z x u v d h k`. -/
def separatingMatrix (Z x u v d h k : Term top m) : Formula top m :=
  .and (.le Z (.f Z Z)) (.and (.le (.f Z Z) Z) (.and (.le x Z)
    (Formula.imp (.and (.le u Z) (.and (.le v Z) (.and (.le d Z) (.and (.le h Z) (.le k Z)))))
      (.and (Formula.imp (.and (.le u x) (.le v x)) (.or (.le u v) (.le v u)))
        (Formula.imp
          (.and (.le x d) (.and (.le d (.f h k)) (.and (.le (.f h k) d)
            (.and (.le h d) (.le k d)))))
          (.le Z d))))))

theorem isMatrix_separatingMatrix (Z x u v d h k : Term top m) :
    (separatingMatrix Z x u v d h k).isMatrix = true := rfl

theorem isLeOnly_separatingMatrix (Z x u v d h k : Term top m) :
    (separatingMatrix Z x u v d h k).IsLeOnly := by
  simp [separatingMatrix, Formula.imp, Formula.IsLeOnly]

end Syntax

/-- The existential variables of the separating sentence: `Z` for `0` and `x` for `1`. -/
def separatingExistentialVar (top : Bool) (i : Fin 2) : Term top (0 + 2 + 5) :=
  .var (i.addNat 5)

/-- The universal variables of the separating sentence: `u v d h k` for `0, …, 4`. -/
def separatingUniversalVar (top : Bool) (i : Fin 5) : Term top (0 + 2 + 5) :=
  .var (i.castAdd 2)

/-- The Σ₂ sentence with prefix `∃ Z x ∀ u v d h k` that holds over arbitrary trees and
fails over regular and over finite trees. -/
def separatingSentence (top : Bool) : Formula top 0 :=
  let X := separatingExistentialVar top
  let Y := separatingUniversalVar top
  exs 2 (alls 5 (separatingMatrix (X 0) (X 1) (Y 0) (Y 1) (Y 2) (Y 3) (Y 4)))

theorem separatingSentence_quantifiers (top : Bool) :
    (separatingSentence top).quantifiers =
      some (List.replicate 2 true ++ List.replicate 5 false) := by
  simp [separatingSentence, quantifiers_exs, quantifiers_alls,
    (Formula.quantifiers_eq_nil_iff _).mpr (isMatrix_separatingMatrix _ _ _ _ _ _ _)]

/-- The separating sentence is syntactically Σ₂. -/
theorem separatingSentence_isSigma (top : Bool) : (separatingSentence top).IsSigma 2 := by
  rw [Formula.IsSigma, separatingSentence_quantifiers]
  simp [List.replicate_succ, Formula.blocks]

/-- The separating sentence uses inequality as its only kind of atom. -/
theorem separatingSentence_isLeOnly (top : Bool) : (separatingSentence top).IsLeOnly := by
  simp only [separatingSentence, isLeOnly_exs, isLeOnly_alls]
  exact isLeOnly_separatingMatrix _ _ _ _ _ _ _

/-! ## Semantics -/

/-- Semantic counterpart of `separatingMatrix`. -/
def SeparatingMatrix (Z x u v d h k : Tree) : Prop :=
  Z ≤ f Z Z ∧ f Z Z ≤ Z ∧ x ≤ Z ∧
    (u ≤ Z ∧ v ≤ Z ∧ d ≤ Z ∧ h ≤ Z ∧ k ≤ Z →
      (u ≤ x ∧ v ≤ x → u ≤ v ∨ v ≤ u) ∧
      (x ≤ d ∧ d ≤ f h k ∧ f h k ≤ d ∧ h ≤ d ∧ k ≤ d → Z ≤ d))

theorem realize_separatingMatrix {top : Bool} {m : ℕ} (M : Structure top)
    (ρ : Fin m → M.Elem) (Z x u v d h k : Term top m) :
    (separatingMatrix Z x u v d h k).Realize M ρ ↔
      SeparatingMatrix (Z.eval M ρ) (x.eval M ρ) (u.eval M ρ) (v.eval M ρ) (d.eval M ρ)
        (h.eval M ρ) (k.eval M ρ) := by
  simp only [separatingMatrix, SeparatingMatrix, Formula.imp, Formula.Realize, imp_iff_not_or]
  exact Iff.rfl

theorem eval_separatingExistentialVar {top : Bool} (M : Structure top) (X : Fin 2 → M.Elem)
    (Y : Fin 5 → M.Elem) (i : Fin 2) :
    (separatingExistentialVar top i).eval M (env Y (env X Fin.elim0)) = X i :=
  (env_back Y (env X Fin.elim0) (i : Fin (0 + 2))).trans (env_front X Fin.elim0 i)

theorem eval_separatingUniversalVar {top : Bool} (M : Structure top) (X : Fin 2 → M.Elem)
    (Y : Fin 5 → M.Elem) (i : Fin 5) :
    (separatingUniversalVar top i).eval M (env Y (env X Fin.elim0)) = Y i :=
  env_front Y _ i

/-- The separating sentence holds when two elements satisfy the semantic matrix for all
five elements. -/
theorem separatingSentence_holds_iff {top : Bool} (M : Structure top) :
    (separatingSentence top).Holds M ↔
      ∃ Z x : M.Elem, ∀ u v d h k : M.Elem, SeparatingMatrix Z x u v d h k := by
  simp only [separatingSentence, Formula.Holds, realize_exs, realize_alls,
    realize_separatingMatrix, eval_separatingExistentialVar, eval_separatingUniversalVar]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X 0, X 1, fun u v d h k => hX ![u, v, d, h, k]⟩
  · rintro ⟨Z, x, hZx⟩
    exact ⟨![Z, x], fun Y => hZx (Y 0) (Y 1) (Y 2) (Y 3) (Y 4)⟩

/-- In each of the six structures, the separating sentence states that the full tree is in
the domain and that some top-free `x` in the domain satisfies two conditions on top-free
elements of the domain: any two trees below `x` are comparable, and every `d = f(h, k)`
above `x` with `h ≤ d` and `k ≤ d` is the full tree. -/
theorem separatingSentence_holds_ofClass_iff (c : TreeClass) (top : Bool) :
    (separatingSentence top).Holds (Structure.ofClass c top) ↔
      Domain c top full ∧ ∃ x, Domain c top x ∧ x.TopFree ∧
        (∀ u v, Domain c top u → u.TopFree → Domain c top v → v.TopFree →
          u ≤ x → v ≤ x → u ≤ v ∨ v ≤ u) ∧
        (∀ d h k, Domain c top d → d.TopFree → Domain c top h → h.TopFree →
          Domain c top k → k.TopFree →
          x ≤ d → d ≤ f h k → f h k ≤ d → h ≤ d → k ≤ d → full ≤ d) := by
  rw [separatingSentence_holds_iff]
  have hbot : (Tree.bot : Tree) ≤ full := (le_full_iff _).mpr topFree_bot
  constructor
  · rintro ⟨Z, x, hZx⟩
    obtain ⟨hZ₁, hZ₂, hx, -⟩ := hZx default default default default default
    have hZ : (Z : Tree) = full := eq_full_of_eq (_root_.le_antisymm hZ₁ hZ₂)
    refine ⟨hZ ▸ Z.2, x, x.2, (le_full_iff _).mp (hZ ▸ hx), ?_, ?_⟩
    · intro u v hu hu' hv hv' hux hvx
      have h := (hZx ⟨u, hu⟩ ⟨v, hv⟩ default default default).2.2.2
      rw [hZ] at h
      exact (h ⟨(le_full_iff _).mpr hu', (le_full_iff _).mpr hv', hbot, hbot, hbot⟩).1
        ⟨hux, hvx⟩
    · intro d h k hd hd' hh hh' hk hk' hxd hdf hfd hhd hkd
      have H := (hZx default default ⟨d, hd⟩ ⟨h, hh⟩ ⟨k, hk⟩).2.2.2
      rw [hZ] at H
      exact (H ⟨hbot, hbot, (le_full_iff _).mpr hd', (le_full_iff _).mpr hh',
        (le_full_iff _).mpr hk'⟩).2 ⟨hxd, hdf, hfd, hhd, hkd⟩
  · rintro ⟨hfull, x, hx, hx', hchain, hclosed⟩
    refine ⟨⟨full, hfull⟩, ⟨x, hx⟩, fun u v d h k => ?_⟩
    have hfZ : full ≤ f full full ∧ f full full ≤ full := by
      rw [← full_eq]; exact ⟨le_rfl, le_rfl⟩
    refine ⟨hfZ.1, hfZ.2, (le_full_iff _).mpr hx', ?_⟩
    rintro ⟨hu, hv, hd, hh, hk⟩
    exact ⟨fun ⟨hux, hvx⟩ => hchain u v u.2 ((le_full_iff _).mp hu) v.2 ((le_full_iff _).mp hv)
        hux hvx,
      fun ⟨hxd, hdf, hfd, hhd, hkd⟩ => hclosed d h k d.2 ((le_full_iff _).mp hd) h.2
        ((le_full_iff _).mp hh) k.2 ((le_full_iff _).mp hk) hxd hdf hfd hhd hkd⟩

/-- The comparability condition of the separating sentence, applied to the paths of two
addresses of `x`, makes the addresses of `x` pairwise comparable by prefix. -/
theorem prefix_or_prefix_of_comparable {c : TreeClass} {top : Bool} {x : Tree}
    (hchain : ∀ u v, Domain c top u → u.TopFree → Domain c top v → v.TopFree →
      u ≤ x → v ≤ x → u ≤ v ∨ v ≤ u)
    {a b : Word} (ha : a ∈ x.constructorPaths) (hb : b ∈ x.constructorPaths) :
    a <+: b ∨ b <+: a := by
  rcases hchain (path a) (path b) (domain_of_isFinite (finite_path a) (topFree_path a))
      (topFree_path a) (domain_of_isFinite (finite_path b) (topFree_path b)) (topFree_path b)
      (path_le_of_mem ha) (path_le_of_mem hb) with h | h
  · exact Or.inl ((mem_constructorPaths_path b a).mp ((path_le_iff (topFree_path b) a).mp h))
  · exact Or.inr ((mem_constructorPaths_path a b).mp ((path_le_iff (topFree_path a) b).mp h))

end UndeciSigma2
