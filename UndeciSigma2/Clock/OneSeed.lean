import UndeciSigma2.Clock.Readings

/-! # One-seed clauses

A one-seed clause `seeds ∧ bounds ∧ shape → y₁ ≤ g₁` holds for all values of the universal
variables exactly when every word lying in all seed readings and in the shape language lies in
some bound reading (`OneSeedSpec`).

* If the specification holds and the clause has a seed atom, all of whose witnesses are
  top-free, the clause holds for arbitrary values, with or without top: the seed is top-free,
  its addresses lie in the seed readings and in the language, hence in the support of the
  bound.
* If the clause holds for all values of the domain, and its witnesses are top-free trees of the
  domain whose residuals lie below a sink value of the domain, the specification holds: for a
  word `w` violating it, the path to `w`, the union of the trees of the bound atoms, the sink
  value and finite shape auxiliaries refute the clause. These values lie in the domain of the
  witnesses; they are finite when the witnesses are finite.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Clock

variable {c : TreeClass} {top : Bool}

/-- The specification of a one-seed clause: every word in all seed readings and in the shape
language lies in some bound reading. -/
def OneSeedSpec (seeds : List (SeedAtom Tree)) (bounds : List (BoundAtom Tree))
    (sh : SeedShape) : Prop :=
  ∀ w, (∀ a ∈ seeds, w ∈ a.reading) → w ∈ sh.language → ∃ b ∈ bounds, w ∈ b.reading

/-- The values of the universal variables refuting a one-seed clause at the word `w`, with
sink value `z`: the seed is the path to `w`, the bound is the union of the trees of the bound
atoms, the shape auxiliaries are finite, and the other variables are `⊥`. -/
noncomputable def oneSeedValues (bounds : List (BoundAtom Tree)) (sh : SeedShape) (z : Tree)
    (w : Word) : ClockUniversals Tree where
  y₁ := path w
  y₂ := bot
  y₃ := bot
  g₁ := unionTree (bounds.flatMap BoundAtom.trees)
  g₂ := bot
  g₃ := bot
  k := (sh.auxiliaries w).1
  k₀ := (sh.auxiliaries w).2
  d₁ := bot
  d₂ := bot
  e₂ := bot
  e₃ := bot
  z := z

/-- The refuting values of a one-seed clause lie in the domain. -/
theorem oneSeedValues_domain {bounds : List (BoundAtom Tree)} {sh : SeedShape} {z : Tree}
    (hz : Domain c top z) (hb : ∀ b ∈ bounds, Domain c top b.witness ∧ b.witness.TopFree)
    (w : Word) : (oneSeedValues bounds sh z w).Forall (Domain c top) := by
  obtain ⟨hk, hkt, hk₀, hk₀t⟩ := sh.finite_auxiliaries w
  have hg : Domain c top (unionTree (bounds.flatMap BoundAtom.trees)) := by
    apply domain_unionTree
    intro t ht
    obtain ⟨b, hb', ht⟩ := List.mem_flatMap.mp ht
    exact BoundAtom.domain_of_mem_trees (hb b hb').1 (hb b hb').2 ht
  apply ClockUniversals.forall_of_each <;> simp only [oneSeedValues]
  all_goals first
    | exact domain_bot c top | exact hz | exact hg | exact domain_of_isFinite hk hkt
    | exact domain_of_isFinite hk₀ hk₀t | exact domain_path w

/-- If its specification holds, a one-seed clause holds for all values of the universal
variables, with or without top. -/
theorem oneSeed_holds {seeds : List (SeedAtom Tree)} {bounds : List (BoundAtom Tree)}
    {sh : SeedShape} (hne : seeds ≠ []) (hseeds : ∀ a ∈ seeds, a.witness.TopFree)
    (hspec : OneSeedSpec seeds bounds sh) (v : ClockUniversals Tree) :
    (ClockClause.oneSeed seeds bounds sh).Holds v := by
  intro hs hb hsh
  obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil seeds hne
  have hy : v.y₁.TopFree := SeedAtom.topFree_of_holds (hseeds a₀ ha₀) (hs a₀ ha₀)
  rw [le_iff_subset_support hy]
  intro u hu
  obtain ⟨b, hb', hub⟩ :=
    hspec u (fun a ha => SeedAtom.subset_reading (hseeds a ha) (hs a ha) hu)
      (SeedShape.subset_language hsh hu)
  exact BoundAtom.reading_subset_support (hb b hb') hub

/-- If a one-seed clause holds for all values of the domain, its specification holds. -/
theorem oneSeed_spec {seeds : List (SeedAtom Tree)} {bounds : List (BoundAtom Tree)}
    {sh : SeedShape} {z : Tree} (hz : Domain c top z)
    (hseeds : ∀ a ∈ seeds, a.witness.TopFree)
    (hbounds : ∀ b ∈ bounds, IsWitness c top z b.witness)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) →
      (ClockClause.oneSeed seeds bounds sh).Holds v) :
    OneSeedSpec seeds bounds sh := by
  intro w hw hsh
  have hv := oneSeedValues_domain (sh := sh) hz
    (fun b hb => ⟨(hbounds b hb).1, (hbounds b hb).2.1⟩) w
  have hc := h _ hv (fun a ha => (SeedAtom.holds_path_iff (hseeds a ha) w).mpr (hw a ha))
    (fun b hb => BoundAtom.holds_unionTree (hbounds b hb).2.1 (hbounds b hb).2.2
      fun t ht => List.mem_flatMap.mpr ⟨b, hb, ht⟩)
    (SeedShape.holds_auxiliaries hsh)
  obtain ⟨t, ht, hwt⟩ := (path_le_unionTree_iff w _).mp hc
  obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
  exact ⟨b, hb, (BoundAtom.mem_reading_iff w).mpr ⟨t, ht, hwt⟩⟩

end Clock

end UndeciSigma2
