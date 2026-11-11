import UndeciSigma2.Clock.OneSeed
import UndeciSigma2.Clock.Window
import UndeciSigma2.Clock.Chain

/-! # Specifications of the clauses

Every clause description has a specification, a statement about the address sets of its
witnesses (`ClockClause.Spec`). For witnesses of the domain satisfying the guards, a clause of
the sentence holds for all values of the universal variables in the domain exactly when its
specification holds (`ClockClause.holds_of_spec`, `ClockClause.spec_of_holds`): the values may
contain top, and the refuting values lie in the domain of the witnesses. Hence the clock
sentence holds in a structure exactly when twenty-one trees of the domain satisfy the guards,
the root conditions and the specifications of all clauses (`clockConditions_iff`).

The last section unfolds the specification of each clause family into a statement about
words, in the form used by soundness and completeness.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

open Clock

/-- The specification of a clause description. -/
def ClockClause.Spec : ClockClause Tree → Prop
  | .oneSeed seeds bounds sh => OneSeedSpec seeds bounds sh
  | .window X E => WindowSpec 2 (windowSet X E)
  | .window3 X E => WindowSpec 3 (windowSet X E)
  | .chain B => IsChain B.constructorPaths
  | .unwindBound N U => UnwindBoundSpec N U

namespace ClockClause

variable {c : TreeClass} {top : Bool}

/-- A clause with top-free witnesses and a valid specification holds for all values of the
universal variables, with or without top. -/
theorem holds_of_spec {cl : ClockClause Tree} (hwf : cl.WellFormed)
    (htf : ∀ t ∈ cl.witnesses, t.TopFree) (hs : cl.Spec) (v : ClockUniversals Tree) :
    cl.Holds v := by
  cases cl with
  | oneSeed seeds bounds sh =>
    exact oneSeed_holds hwf (fun a ha => htf _ (by simp [witnesses]; exact Or.inl ⟨a, ha, rfl⟩))
      hs v
  | window X E => exact window_holds (htf X (by simp [witnesses])) hs v
  | window3 X E => exact window3_holds (htf X (by simp [witnesses])) hs v
  | chain B => exact chain_holds (htf B (by simp [witnesses])) hs v
  | unwindBound N U => exact unwindBound_holds (htf N (by simp [witnesses])) hs v

/-- A clause holding for all values of the domain satisfies its specification, if its witnesses
are usable in refutations with sink value `z` of the domain. -/
theorem spec_of_holds {cl : ClockClause Tree} {z : Tree} (hz : Domain c top z)
    (hw : ∀ t ∈ cl.witnesses, IsWitness c top z t)
    (h : ∀ v : ClockUniversals Tree, v.Forall (Domain c top) → cl.Holds v) : cl.Spec := by
  cases cl with
  | oneSeed seeds bounds sh =>
    exact oneSeed_spec hz
      (fun a ha => (hw _ (by simp [witnesses]; exact Or.inl ⟨a, ha, rfl⟩)).2.1)
      (fun b hb => hw _ (by simp [witnesses]; exact Or.inr ⟨b, hb, rfl⟩)) h
  | window X E => exact window_spec hz (hw X (by simp [witnesses])) (hw E (by simp [witnesses])) h
  | window3 X E =>
    exact window3_spec hz (hw X (by simp [witnesses])) (hw E (by simp [witnesses])) h
  | chain B => exact chain_spec (hw B (by simp [witnesses])).2.1 h
  | unwindBound N U =>
    exact unwindBound_spec (hw U (by simp [witnesses])).1 (hw U (by simp [witnesses])).2.1 h

end ClockClause

namespace Clock

variable {c : TreeClass} {top : Bool}

/-! ## Membership in the clause list -/

/-- A property holds for all clauses exactly when it holds for every clause family. -/
theorem forall_mem_clauses_iff {α : Type*} (P : Program) (x : ClockExistentials α)
    (Q : ClockClause α → Prop) :
    (∀ cl ∈ clauses P x, Q cl) ↔
      Q (chainClause x) ∧ Q (chainHeadClause x) ∧ Q (clockClause x) ∧ Q (gapClause x) ∧
      Q (endLastClause x) ∧ Q (coverClause P x) ∧
      (∀ l' < labelCount P, ∀ l < l', Q (uniqueClause x l l')) ∧
      (∀ l < labelCount P, l ≠ endLabel → Q (transitionClause P x l)) ∧
      (∀ i, Q (counterStepClause x i) ∧ Q (zeroWindowClause x i) ∧ Q (plusWindowClause x i) ∧
        Q (classLabelClause P x i 1 (x.plusClass i)) ∧
        Q (classLabelClause P x i 0 (x.zeroClass i))) ∧
      (∀ μ < labelCount P, ∀ c, zeroTest P μ = some c → Q (zeroTestClause x μ c)) ∧
      Q (unwindStepClause x) ∧ Q (unwindWindowClause x) ∧ Q (unwindBoundClause x) := by
  simp only [clauses, uniqueClauses, transitionClauses, counterClauses, zeroTestClauses,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_range, List.mem_filter, List.mem_finRange, true_implies, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, bne_iff_ne, ne_eq, and_imp, List.mem_filterMap,
    Option.map_eq_some_iff, forall_exists_index]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩, h₁₁, h₁₂, h₁₃⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, fun μ hμ c hc => h₁₀ _ μ hμ c hc rfl, h₁₁, h₁₂,
      h₁₃⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩
    exact ⟨⟨⟨⟨⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩, h₈⟩, h₉⟩, fun _ μ hμ c hc h => h ▸ h₁₀ μ hμ c hc⟩,
      h₁₁, h₁₂, h₁₃⟩

/-- Every one-seed clause of the sentence has a seed atom. -/
theorem wellFormed_of_mem_clauses {α : Type*} {P : Program} {x : ClockExistentials α}
    {cl : ClockClause α} (h : cl ∈ clauses P x) : cl.WellFormed := by
  refine (forall_mem_clauses_iff P x ClockClause.WellFormed).mpr ?_ cl h
  simp [ClockClause.WellFormed, chainClause, chainHeadClause, clockClause, gapClause,
    endLastClause, coverClause, uniqueClause, transitionClause, counterStepClause,
    zeroWindowClause, plusWindowClause, classLabelClause, zeroTestClause, unwindStepClause,
    unwindWindowClause, unwindBoundClause]

/-- The witnesses of every clause are existential variables of the sentence. -/
theorem witnesses_subset_of_mem_clauses {α : Type*} {P : Program} {x : ClockExistentials α}
    {cl : ClockClause α} (h : cl ∈ clauses P x) : ∀ t ∈ cl.witnesses, t ∈ x.toList := by
  refine (forall_mem_clauses_iff P x fun cl => ∀ t ∈ cl.witnesses, t ∈ x.toList).mpr ?_ cl h
  have h₁ : ∀ i, x.counter i ∈ x.toList := fun i => by
    fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded]
  have h₂ : ∀ i, x.plusClass i ∈ x.toList := fun i => by
    fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded]
  have h₃ : ∀ i, x.zeroClass i ∈ x.toList := fun i => by
    fin_cases i <;> simp [ClockExistentials.toList, ClockExistentials.guarded]
  have h₄ : x.clock ∈ x.toList ∧ x.chain ∈ x.toList ∧ x.chainHead ∈ x.toList ∧
      x.labels ∈ x.toList ∧ x.ray ∈ x.toList ∧ x.unwind ∈ x.toList ∧ x.unwindPart ∈ x.toList ∧
      x.buildRay ∈ x.toList := by
    simp [ClockExistentials.toList, ClockExistentials.guarded]
  obtain ⟨h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h₄
  simp [ClockClause.witnesses, SeedAtom.witness, BoundAtom.witness, chainClause,
    chainHeadClause, clockClause, gapClause, endLastClause, coverClause, uniqueClause,
    transitionClause, counterStepClause, zeroWindowClause, plusWindowClause, classLabelClause,
    zeroTestClause, unwindStepClause, unwindWindowClause, unwindBoundClause, h₁, h₂, h₃, h₅, h₆,
    h₇, h₈, h₉, h₁₀, h₁₁, h₁₂]

/-! ## The semantic content as specifications -/

/-- Witnesses satisfying the guards, the root conditions and the specification of every
clause. -/
structure SpecConditions (P : Program) (x : ClockExistentials Tree) : Prop where
  guarded : Guarded x
  root : RootConditions (labelCount P) x
  spec : ∀ cl ∈ clauses P x, cl.Spec

/-- The clock sentence holds in a structure exactly when twenty-one trees of its domain satisfy
the guards, the root conditions and the specifications of all clauses. -/
theorem clockConditions_iff (c : TreeClass) (top : Bool) (P : Program) :
    ClockConditions c top P ↔ ∃ x : ClockExistentials Tree, x.Forall (Domain c top) ∧
      SpecConditions P x := by
  constructor
  · rintro ⟨x, hd, hg, hr, hcl⟩
    refine ⟨x, hd, hg, hr, fun cl hcl' => ?_⟩
    exact ClockClause.spec_of_holds (domain_universeTree hd)
      (fun t ht => hg.isWitness hd (witnesses_subset_of_mem_clauses hcl' t ht)) (hcl cl hcl')
  · rintro ⟨x, hd, hg, hr, hs⟩
    refine ⟨x, hd, hg, hr, fun cl hcl v _ => ?_⟩
    exact ClockClause.holds_of_spec (wellFormed_of_mem_clauses hcl)
      (fun t ht => hg.topFree t (witnesses_subset_of_mem_clauses hcl t ht)) (hs cl hcl) v

/-! ## The specification of each clause family -/

section Families

variable (P : Program) (x : ClockExistentials Tree)

/-- The specification of the chain clause. -/
theorem chainClause_spec_iff :
    (chainClause x).Spec ↔ IsChain x.chain.constructorPaths := Iff.rfl

/-- The specification of the chain head clause. -/
theorem chainHeadClause_spec_iff :
    (chainHeadClause x).Spec ↔ ∀ w ∈ x.chain.constructorPaths,
      (IsOnes w ∨ ∃ j i, w = toothWord j i) → w ∈ x.chainHead.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    chainHeadClause]

/-- The specification of the clock clause. -/
theorem clockClause_spec_iff :
    (clockClause x).Spec ↔ WindowSpec 2 (windowSet x.clock x.clock) := Iff.rfl

/-- The specification of the gap clause. -/
theorem gapClause_spec_iff :
    (gapClause x).Spec ↔ ∀ w, 1 :: w ∈ x.clock.constructorPaths →
      (IsOnes w ∨ ∃ j, w = stub j) → w ∈ x.clock.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    gapClause]

/-- The specification of the end clause. -/
theorem endLastClause_spec_iff :
    (endLastClause x).Spec ↔ ∀ w, ones endLabel ++ 0 :: w ∈ x.labels.constructorPaths →
      1 :: w ∈ x.clock.constructorPaths → w ∈ x.ray.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    endLastClause]

/-- The specification of the covering clause. -/
theorem coverClause_spec_iff :
    (coverClause P x).Spec ↔ ∀ w ∈ x.clock.constructorPaths,
      ∃ l < labelCount P, ones l ++ 0 :: w ∈ x.labels.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    coverClause]

/-- The specification of the uniqueness clause of labels `l` and `l'`. -/
theorem uniqueClause_spec_iff (l l' : ℕ) :
    (uniqueClause x l l').Spec ↔ ∀ w, ones l ++ 0 :: w ∈ x.labels.constructorPaths →
      ones l' ++ 0 :: w ∈ x.labels.constructorPaths → w ∈ x.ray.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    uniqueClause]

/-- The specification of the transition clause of label `l`. -/
theorem transitionClause_spec_iff (l : ℕ) :
    (transitionClause P x l).Spec ↔ ∀ w, ones l ++ 0 :: w ∈ x.labels.constructorPaths →
      w ∈ x.ray.constructorPaths ∨ ∃ μ < labelCount P, isSuccessor P l μ = true ∧
        ones μ ++ 0 :: 1 :: w ∈ x.labels.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    transitionClause]

/-- The specification of the step clause of counter `i`. -/
theorem counterStepClause_spec_iff (i : Fin 3) :
    (counterStepClause x i).Spec ↔ ∀ w, 1 :: w ∈ (x.counter i).constructorPaths →
      w ∈ (x.counter i).constructorPaths ∨ 1 :: w ∈ (x.plusClass i).constructorPaths ∨
        1 :: w ∈ (x.zeroClass i).constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    counterStepClause]

/-- The specification of the window clause of the keeping class comb of counter `i`. -/
theorem zeroWindowClause_spec_iff (i : Fin 3) :
    (zeroWindowClause x i).Spec ↔ WindowSpec 2 (windowSet (x.zeroClass i) (x.counter i)) :=
  Iff.rfl

/-- The specification of the window clause of the increasing class comb of counter `i`. -/
theorem plusWindowClause_spec_iff (i : Fin 3) :
    (plusWindowClause x i).Spec ↔ WindowSpec 3 (windowSet (x.plusClass i) (x.counter i)) :=
  Iff.rfl

/-- The specification of a class label clause. -/
theorem classLabelClause_spec_iff (i : Fin 3) (κ : ℤ) (X : Tree) :
    (classLabelClause P x i κ X).Spec ↔ ∀ w ∈ X.constructorPaths,
      (IsOnes w ∨ ∃ j, w = stub j) → w ∈ x.ray.constructorPaths ∨
        ∃ ν < labelCount P, (ν ≠ startLabel ∧ effect P ν i = κ) ∧
          ones ν ++ 0 :: w ∈ x.labels.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    classLabelClause]

/-- The specification of the zero-test clause of label `μ` and counter `c`. -/
theorem zeroTestClause_spec_iff (μ : ℕ) (c : Fin 2) :
    (zeroTestClause x μ c).Spec ↔ ∀ w ∈ (x.counter (Fin.castSucc c)).constructorPaths,
      ones μ ++ 0 :: 1 :: w ∈ x.labels.constructorPaths → w ∈ x.clock.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    zeroTestClause]

/-- The specification of the step clause of the unwinding comb. -/
theorem unwindStepClause_spec_iff :
    (unwindStepClause x).Spec ↔ ∀ w, 1 :: w ∈ x.unwind.constructorPaths →
      w ∈ x.unwind.constructorPaths ∨ 1 :: w ∈ x.unwindPart.constructorPaths := by
  simp [ClockClause.Spec, OneSeedSpec, SeedAtom.reading, BoundAtom.reading, SeedShape.language,
    unwindStepClause]

/-- The specification of the window clause of the unwinding part. -/
theorem unwindWindowClause_spec_iff :
    (unwindWindowClause x).Spec ↔ WindowSpec 2 (windowSet x.unwindPart x.unwind) := Iff.rfl

/-- The specification of the unwinding bound. -/
theorem unwindBoundClause_spec_iff :
    (unwindBoundClause x).Spec ↔ UnwindBoundSpec x.buildRay x.unwind := Iff.rfl

end Families

end Clock

end UndeciSigma2
