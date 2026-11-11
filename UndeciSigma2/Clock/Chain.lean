import UndeciSigma2.Clock.Readings
import UndeciSigma2.Separation.Arbitrary

/-! # The chain clause and the unwinding bound

For a top-free `B`, the chain clause `y₁ ≤ B ∧ y₂ ≤ B → y₁ ≤ y₂ ∨ y₂ ≤ y₁` holds for all
values of the universal variables exactly when the addresses of `B` are pairwise comparable by
prefix. Refuting values
are the paths to two incomparable addresses; conversely two prefix-closed sets inside a chain
are comparable.

For a top-free `N` and a top-free `U` of the domain, the unwinding bound
`y₁ ≤ N ∧ U ≤ k ∧ k ≤ f(g₁, k) → y₁ ≤ g₁` holds for all values exactly when every address of
`N` lies in the tails of `U`. Refuting values are the path to an address outside the tails,
the spine join of `U` and the tails of `U`, which lie in the domain of `U`; conversely the loop
`k ≤ f(g₁, k)` above `U` puts the tails of `U` into the support of `g₁`.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

variable {c : TreeClass} {top : Bool}

/-- The words of `S` are pairwise comparable by prefix. -/
def IsChain (S : Set Word) : Prop := ∀ a ∈ S, ∀ b ∈ S, a <+: b ∨ b <+: a

/-- The specification of the unwinding bound: the addresses of `N` lie in the tails of `U`. -/
def UnwindBoundSpec (N U : Tree) : Prop :=
  ∀ w ∈ N.constructorPaths, ∃ a, ones a ++ 0 :: w ∈ U.constructorPaths

/-- If the addresses of `B` form a chain, the chain clause holds for all values of the
universal variables, with or without top. -/
theorem chain_holds {B : Tree} (hB : B.TopFree) (hspec : IsChain B.constructorPaths)
    (v : ClockUniversals Tree) : (ClockClause.chain B).Holds v := by
  intro h₁ h₂
  exact Separation.le_or_le_of_chain hB (hB.of_le h₁) (hB.of_le h₂) hspec h₁ h₂

/-- If the chain clause holds for all values of the domain, the addresses of `B` form a
chain. -/
theorem chain_spec {B : Tree} (hB : B.TopFree)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) → (ClockClause.chain B).Holds v) :
    IsChain B.constructorPaths := by
  intro a ha b hb
  let v : ClockUniversals Tree :=
    ⟨path a, path b, bot, bot, bot, bot, bot, bot, bot, bot, bot, bot, bot⟩
  have hv : v.Forall (Domain c top) := by
    apply ClockUniversals.forall_of_each
    all_goals first
      | exact domain_bot c top | exact domain_path a
      | exact domain_path b
  rcases h v hv ((path_le_iff hB a).mpr ha) ((path_le_iff hB b).mpr hb) with hab | hba
  · exact Or.inl ((mem_constructorPaths_path b a).mp ((path_le_iff (topFree_path b) a).mp hab))
  · exact Or.inr ((mem_constructorPaths_path a b).mp ((path_le_iff (topFree_path a) b).mp hba))

/-- If its specification holds, the unwinding bound holds for all values of the universal
variables, with or without top. -/
theorem unwindBound_holds {N U : Tree} (hN : N.TopFree) (hspec : UnwindBoundSpec N U)
    (v : ClockUniversals Tree) : (ClockClause.unwindBound N U).Holds v := by
  intro hy hU hk
  have hyt : v.y₁.TopFree := hN.of_le hy
  rw [le_iff_subset_support hyt]
  intro u hu
  obtain ⟨a, ha⟩ := hspec u ((le_iff_constructorPaths_subset hyt hN).mp hy hu)
  have h₁ : ones a ++ 0 :: u ∈ v.k.support :=
    support_mono hU (constructorPaths_subset_support U ha)
  exact mem_support_of_zero_cons_mem hk (mem_support_of_ones_append_mem hk a h₁)

/-- If the unwinding bound holds for all values of the domain, its specification holds. -/
theorem unwindBound_spec {N U : Tree} (hU : Domain c top U) (hUt : U.TopFree)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) →
      (ClockClause.unwindBound N U).Holds v) :
    UnwindBoundSpec N U := by
  intro w hw
  let v : ClockUniversals Tree :=
    ⟨path w, bot, bot, tails U, bot, bot, spineJoin U, bot, bot, bot, bot, bot, bot⟩
  have hv : v.Forall (Domain c top) := by
    apply ClockUniversals.forall_of_each
    all_goals first
      | exact domain_bot c top | exact domain_path w
      | exact domain_tails hU hUt | exact domain_spineJoin hU hUt
  have hUk : U ≤ spineJoin U :=
    le_of_subset hUt fun u hu => (mem_spineJoin U u).mpr ⟨0, hu⟩
  have hk : spineJoin U ≤ f (tails U) (spineJoin U) := by
    rw [le_f_iff (topFree_tails U) (topFree_spineJoin U) (topFree_spineJoin U)]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [mem_spineJoin] at hu
      exact (mem_tails U u).mpr hu
    · rw [mem_spineJoin] at hu ⊢
      obtain ⟨a, ha⟩ := hu
      exact ⟨a + 1, by rwa [ones_succ', List.append_assoc]⟩
  have hc := h v hv (path_le_of_mem hw) hUk hk
  exact (mem_tails U w).mp ((path_le_iff (topFree_tails U) w).mp hc)

end Clock

end UndeciSigma2
