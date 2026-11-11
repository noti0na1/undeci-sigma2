import UndeciSigma2.Undecidability.Computable
import UndeciSigma2.Clock.Definition

/-! # Primitive recursiveness of the clock sentence

The matrix depends on the program through the number of labels, the successor relation, the
effects and the zero tests of the label machine, all of which are decided by bounded case
distinctions on the instruction at a state, and through lists of clauses indexed by labels
below the number of labels. The quantifier blocks have fixed lengths. The prenex negation of
the sentence is also primitive recursive.
-/

namespace UndeciSigma2

open UndeciSigma2.Computability Sentence Clock

namespace Clock

variable {top : Bool} {n : ℕ}

private theorem primrec_lookup {α β : Type} [Primcodable α] [Primcodable β]
    {P : α → Program} {q : α → ℕ} {noneCase : α → β}
    {incCase : α → Fin 2 → ℕ → β} {testCase : α → Fin 2 → ℕ → ℕ → β}
    (hP : Primrec P) (hq : Primrec q) (hn : Primrec noneCase)
    (hi : Primrec₂ fun a (b : Fin 2 × ℕ) => incCase a b.1 b.2)
    (hz : Primrec₂ fun a (b : Fin 2 × ℕ × ℕ) => testCase a b.1 b.2.1 b.2.2) :
    Primrec (fun a => match (P a)[q a]? with
      | none => noneCase a
      | some (.inc c r) => incCase a c r
      | some (.jzdec c z p) => testCase a c z p) := by
  have hs : Primrec₂ (fun (a : α) (i : Instr) => match i with
      | .inc c r => incCase a c r
      | .jzdec c z p => testCase a c z p) := by
    exact (Primrec.sumCasesOn ((Primrec.of_equiv (e := Instr.equivSum)).comp Primrec.snd)
      (hi.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hz.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun a => by cases a.2 <;> rfl
  exact (Primrec.option_casesOn (Primrec.list_getElem?.comp hP hq) hn hs).of_eq
    fun a => by rcases (P a)[q a]? with _ | (⟨c, r⟩ | ⟨c, z, p⟩) <;> rfl

-- Composition rules used for the arithmetic and Boolean tables below.
local macro "clock_primrec" : tactic => `(tactic|
  repeat' first
  | assumption
  | exact Primrec.id
  | exact Primrec.fst
  | exact Primrec.snd
  | exact Primrec.const _
  | (unfold Primrec₂; dsimp only [Function.uncurry])
  | apply Primrec.ite
  | apply Primrec.cond
  | apply PrimrecPred.decide
  | apply PrimrecPred.and
  | apply PrimrecPred.or
  | apply PrimrecPred.not
  | apply Primrec.eq.comp
  | apply Primrec.nat_le.comp
  | apply Primrec.nat_lt.comp
  | apply Primrec.and.comp
  | apply Primrec.or.comp
  | apply Primrec.succ.comp
  | apply Primrec.nat_add.comp
  | apply Primrec.nat_sub.comp
  | apply Primrec.nat_mul.comp
  | apply Primrec.nat_div.comp
  | apply Primrec.nat_mod.comp
  | apply Primrec.nat_min.comp
  | apply Primrec.list_length.comp
  | apply Primrec.option_some.comp
  | apply Primrec.fst.comp
  | apply Primrec.snd.comp)

/-- Entry into a state is primitive recursive in the program, state, and label. -/
theorem primrec_isEntry : Primrec (fun a : Program × ℕ × ℕ => isEntry a.1 a.2.1 a.2.2) := by
  unfold isEntry
  apply primrec_lookup Primrec.fst (Primrec.fst.comp Primrec.snd)
  all_goals clock_primrec

/-- The successor relation of the label machine is primitive recursive. -/
theorem primrec_isSuccessor :
    Primrec (fun a : Program × ℕ × ℕ => isSuccessor a.1 a.2.1 a.2.2) := by
  unfold isSuccessor
  have he {α : Type} [Primcodable α] {P : α → Program} {q μ : α → ℕ}
      (hP : Primrec P) (hq : Primrec q) (hμ : Primrec μ) :
      Primrec (fun a => isEntry (P a) (q a) (μ a)) :=
    primrec_isEntry.comp (hP.pair (hq.pair hμ))
  apply Primrec.ite
  · clock_primrec
  · apply Primrec.or.comp
    · clock_primrec
    · apply he <;> clock_primrec
  · apply Primrec.ite
    · clock_primrec
    · clock_primrec
    · apply Primrec.ite
      · clock_primrec
      · clock_primrec
      · apply Primrec.ite
        · clock_primrec
        · clock_primrec
        · apply Primrec.ite
          · clock_primrec
          · exact Primrec.const _
          · apply primrec_lookup
            · exact Primrec.fst
            · clock_primrec
            · exact Primrec.const _
            · unfold Primrec₂
              dsimp only [Function.uncurry]
              apply Primrec.and.comp
              · clock_primrec
              · apply he <;> clock_primrec
            · unfold Primrec₂
              dsimp only [Function.uncurry]
              apply he <;> clock_primrec

private theorem decide_ite_eq {α : Type} [DecidableEq α] (p : Prop) [Decidable p]
    (a b c : α) : decide ((if p then a else b) = c) =
      if p then decide (a = c) else decide (b = c) := by
  split <;> rfl

/-- The selection of the labels with a given effect on a counter is primitive recursive. -/
theorem primrec_effect_eq (i : Fin 3) (κ : ℤ) :
    Primrec (fun a : Program × ℕ => decide (a.2 ≠ startLabel ∧ effect a.1 a.2 i = κ)) := by
  have ht : Primrec (fun a : Program × ℕ => decide ((match a.1[(a.2 - 6) / 2]? with
      | none => 0
      | some (.inc c _) => if (a.2 - 6) % 2 = 0 then transfer c 1 i else 0
      | some (.jzdec c _ _) => if (a.2 - 6) % 2 = 0 then 0 else transfer c (-1) i) = κ)) := by
    have h : Primrec (fun a : Program × ℕ => match a.1[(a.2 - 6) / 2]? with
        | none => decide ((0 : ℤ) = κ)
        | some (.inc c _) => if (a.2 - 6) % 2 = 0 then decide (transfer c 1 i = κ)
            else decide ((0 : ℤ) = κ)
        | some (.jzdec c _ _) => if (a.2 - 6) % 2 = 0 then decide ((0 : ℤ) = κ)
            else decide (transfer c (-1) i = κ)) := by
      apply primrec_lookup
      · exact Primrec.fst
      · clock_primrec
      · exact Primrec.const _
      · unfold Primrec₂
        dsimp only [Function.uncurry]
        apply Primrec.ite
        · clock_primrec
        · exact (Primrec.dom_finite fun c : Fin 2 => decide (transfer c 1 i = κ)).comp
            (Primrec.fst.comp Primrec.snd)
        · exact Primrec.const _
      · unfold Primrec₂
        dsimp only [Function.uncurry]
        apply Primrec.ite
        · clock_primrec
        · exact Primrec.const _
        · exact (Primrec.dom_finite fun c : Fin 2 => decide (transfer c (-1) i = κ)).comp
            (Primrec.fst.comp Primrec.snd)
    exact h.of_eq fun a => by
      rcases a.1[(a.2 - 6) / 2]? with _ | (⟨c, r⟩ | ⟨c, z, p⟩) <;>
        simp only [decide_ite_eq]
  have h : Primrec (fun a : Program × ℕ => decide (effect a.1 a.2 i = κ)) := by
    unfold effect
    simp only [decide_ite_eq]
    clock_primrec
  exact (((Primrec.eq.comp Primrec.snd (Primrec.const startLabel)).not).and
    h.primrecPred).decide

/-- The zero tests of the label machine are primitive recursive. -/
theorem primrec_zeroTest : Primrec (fun a : Program × ℕ => zeroTest a.1 a.2) := by
  have h : Primrec (fun a : Program × ℕ => match a.1[(a.2 - 6) / 2]? with
      | none => (none : Option (Fin 2))
      | some (.inc _ _) => none
      | some (.jzdec c _ _) => some c) := by
    apply primrec_lookup
    · exact Primrec.fst
    · clock_primrec
    · exact Primrec.const _
    · exact (Primrec.const _).to₂
    · clock_primrec
  unfold zeroTest
  apply Primrec.ite
  · clock_primrec
  · exact Primrec.const _
  · exact h.of_eq fun a => by
      rcases a.1[(a.2 - 6) / 2]? with _ | (⟨c, r⟩ | ⟨c, z, p⟩) <;> rfl

/-- The number of labels is primitive recursive in the program. -/
theorem primrec_labelCount : Primrec labelCount := by
  unfold labelCount
  clock_primrec

/-- A context assembled from a primitive recursive family of terms is primitive recursive. -/
theorem primrec_select {α : Type} [Primcodable α] {k : α → ℕ}
    {a : α → ℕ → Term top n} {t : α → Term top n}
    (hk : Primrec k) (ha : Primrec₂ a) (ht : Primrec t) :
    Primrec (fun x => Term.select (k x) (a x) (t x)) := by
  exact Primrec.list_foldr (Primrec.list_range.comp hk) ht
    (primrec_f.comp (ha.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- The conjunction with no trailing true atom is primitive recursive in its list. -/
theorem primrec_conj : Primrec (@conj top n) := by
  have h : Primrec (fun ps : List (Formula top n) =>
      List.recOn (motive := fun _ => Formula top n) ps Sentence.trueAtom fun φ rest acc =>
        if rest = [] then φ else Formula.and φ acc) := by
    apply Primrec.list_rec (h := fun (_ : List (Formula top n))
      (b : Formula top n × List (Formula top n) × Formula top n) =>
        if b.2.1 = [] then b.1 else Formula.and b.1 b.2.2) Primrec.id (Primrec.const _)
    unfold Primrec₂
    dsimp only [Function.uncurry]
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const [])
    · exact Primrec.fst.comp Primrec.snd
    · exact primrec_and.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun ps => by
    induction ps with
    | nil => rfl
    | cons φ ps ih =>
      cases ps with
      | nil => rfl
      | cons ψ rest =>
        change Formula.and φ _ = Formula.and φ _
        exact congrArg (Formula.and φ) ih

section FormulaFamilies

variable (x : ClockExistentials (Term top n)) (v : ClockUniversals (Term top n))

private theorem primrec_rootConditions : Primrec (rootConditions x) := by
  have hclock : Primrec (fun m => Term.select m (fun _ => x.clock) Term.bot) :=
    primrec_select Primrec.id (Primrec.const _).to₂ (Primrec.const _)
  have hleft : Primrec (fun m => Term.select m
      (fun l => if l = startLabel then x.sink else Term.f Term.bot x.sink) Term.bot) := by
    apply primrec_select Primrec.id _ (Primrec.const _)
    clock_primrec
  unfold rootConditions
  apply primrec_conj.comp
  repeat' first
  | exact Primrec.const _
  | exact hclock
  | exact hleft
  | apply Primrec.list_append.comp
  | apply Primrec.list_cons.comp
  | apply primrec_le.comp

private theorem primrec_coverFormula :
    Primrec (fun P => (coverClause P x).formula v) := by
  have hctx : Primrec (fun P => Term.componentContext (labelCount P) v.z (fun _ => true) v.g₁) :=
    primrec_select primrec_labelCount (Primrec.const _).to₂ (Primrec.const _)
  unfold coverClause ClockClause.formula SeedAtom.formula BoundAtom.formula SeedShape.formulas
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, conj]
  repeat' first | exact Primrec.const _ | exact hctx |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

private theorem primrec_uniqueFormula :
    Primrec (fun a : ℕ × ℕ => (uniqueClause x a.1 a.2).formula v) := by
  unfold uniqueClause ClockClause.formula SeedAtom.formula BoundAtom.formula SeedShape.formulas
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, conj]
  have hl := (Term.primrec_pack v.y₁).comp (Primrec.fst (α := ℕ) (β := ℕ))
  have hr := (Term.primrec_pack v.y₁).comp (Primrec.snd (α := ℕ) (β := ℕ))
  repeat' first | exact Primrec.const _ | exact hl | exact hr |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

private theorem primrec_transitionFormula :
    Primrec (fun a : Program × ℕ => (transitionClause a.1 x a.2).formula v) := by
  have hctx : Primrec (fun a : Program × ℕ =>
      Term.tailContext (labelCount a.1) v.z (isSuccessor a.1 a.2) v.g₁) := by
    apply primrec_select (primrec_labelCount.comp Primrec.fst) _ (Primrec.const _)
    unfold Primrec₂
    dsimp only [Function.uncurry]
    apply Primrec.ite
    · exact (Primrec.eq.comp (primrec_isSuccessor.comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))) (Primrec.const true))
    · exact Primrec.const _
    · exact Primrec.const _
  unfold transitionClause ClockClause.formula SeedAtom.formula BoundAtom.formula SeedShape.formulas
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, conj]
  have hp := (Term.primrec_pack v.y₁).comp (Primrec.snd (α := Program) (β := ℕ))
  repeat' first | exact Primrec.const _ | exact hctx | exact hp |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

private theorem primrec_classLabelFormula (i : Fin 3) (κ : ℤ) (X : Term top n) :
    Primrec (fun P => (classLabelClause P x i κ X).formula v) := by
  have hctx : Primrec (fun P => Term.componentContext (labelCount P) v.z
      (fun l => decide (l ≠ startLabel ∧ effect P l i = κ)) v.g₁) := by
    apply primrec_select primrec_labelCount _ (Primrec.const _)
    unfold Primrec₂
    dsimp only [Function.uncurry]
    apply Primrec.ite
    · exact Primrec.eq.comp (primrec_effect_eq i κ) (Primrec.const true)
    · exact Primrec.const _
    · exact Primrec.const _
  unfold classLabelClause ClockClause.formula SeedAtom.formula BoundAtom.formula SeedShape.formulas
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, conj]
  repeat' first | exact Primrec.const _ | exact hctx |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

private theorem primrec_zeroTestFormula :
    Primrec (fun a : ℕ × Fin 2 => (zeroTestClause x a.1 a.2).formula v) := by
  unfold zeroTestClause ClockClause.formula SeedAtom.formula BoundAtom.formula SeedShape.formulas
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, conj]
  have hc := (Primrec.dom_finite fun c : Fin 2 => x.counter c.castSucc).comp
    (Primrec.snd (α := ℕ) (β := Fin 2))
  have hp := (Term.primrec_pack (Term.f Term.bot v.y₁)).comp
    (Primrec.fst (α := ℕ) (β := Fin 2))
  repeat' first | exact Primrec.const _ | exact hc | exact hp |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

private theorem primrec_uniqueFormulas :
    Primrec (fun P => (uniqueClauses P x).map (ClockClause.formula v)) := by
  simp only [uniqueClauses, List.map_flatMap, List.map_map, Function.comp_def]
  apply Primrec.list_flatMap (Primrec.list_range.comp primrec_labelCount)
  unfold Primrec₂
  dsimp only [Function.uncurry]
  apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
  exact ((primrec_uniqueFormula x v).comp
    (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂

private theorem primrec_transitionFormulas :
    Primrec (fun P => (transitionClauses P x).map (ClockClause.formula v)) := by
  have hf : Primrec (fun ls : List ℕ => ls.filter (fun l => l != endLabel)) := by
    apply (Primrec.listFilter
      ((Primrec.eq.comp Primrec.id (Primrec.const endLabel)).not)).of_eq
    intro ls
    congr 1
  simp only [transitionClauses, List.map_map, Function.comp_def]
  exact Primrec.list_map (hf.comp (Primrec.list_range.comp primrec_labelCount))
    (primrec_transitionFormula x v).to₂

private theorem primrec_counterFormulas :
    Primrec (fun P => (counterClauses P x).map (ClockClause.formula v)) := by
  simp only [counterClauses, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.map_append]
  repeat' first
  | exact Primrec.const _
  | exact primrec_classLabelFormula x v _ _ _
  | apply Primrec.list_append.comp
  | apply Primrec.list_cons.comp

private theorem primrec_zeroTestFormulas :
    Primrec (fun P => (zeroTestClauses P x).map (ClockClause.formula v)) := by
  simp only [zeroTestClauses, List.map_filterMap, Option.map_map, Function.comp_def]
  apply Primrec.listFilterMap (Primrec.list_range.comp primrec_labelCount)
  unfold Primrec₂
  dsimp only [Function.uncurry]
  apply Primrec.option_map primrec_zeroTest
  exact ((primrec_zeroTestFormula x v).comp
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

/-- The list of clause formulas is primitive recursive in the program. -/
theorem primrec_clauseFormulas :
    Primrec (fun P => (clauses P x).map (ClockClause.formula v)) := by
  simp only [clauses, List.map_append, List.map_cons, List.map_nil]
  repeat' first
  | exact Primrec.const _
  | exact primrec_coverFormula x v
  | exact primrec_uniqueFormulas x v
  | exact primrec_transitionFormulas x v
  | exact primrec_counterFormulas x v
  | exact primrec_zeroTestFormulas x v
  | apply Primrec.list_append.comp
  | apply Primrec.list_cons.comp

end FormulaFamilies

/-- The matrix is primitive recursive in the program, for fixed variable terms. -/
theorem primrec_matrix (x : ClockExistentials (Term top n)) (v : ClockUniversals (Term top n)) :
    Primrec (fun P : Program => matrix x P v) := by
  exact primrec_and.comp
    (primrec_and.comp (Primrec.const _) ((primrec_rootConditions x).comp primrec_labelCount))
    (Sentence.primrec_allOf.comp (primrec_clauseFormulas x v))

/-- Prenex negation exchanges the two quantifier blocks. -/
theorem negate_clockSentence_eq (top : Bool) (P : Program) :
    (clockSentence top P).negate =
      alls 21 (exs 13 (.neg (matrix (existentialVars top) P (universalVars top)))) := rfl

end Clock

/-- The clock sentence is a primitive recursive function of the program. -/
theorem primrec_clockSentence (top : Bool) : Primrec (clockSentence top) :=
  (primrec_exs 21).comp ((primrec_alls 13).comp (Clock.primrec_matrix _ _))

/-- The clock sentence is a computable function of the program. -/
theorem computable_clockSentence (top : Bool) : Computable (clockSentence top) :=
  (primrec_clockSentence top).to_comp

/-- The prenex negation of the clock sentence is primitive recursive. -/
theorem primrec_clockSentence_negate (top : Bool) :
    Primrec (fun P => (clockSentence top P).negate) := by
  have h := (primrec_alls (top := top) (n := 0) 21).comp ((primrec_exs 13).comp
    (primrec_neg.comp (Clock.primrec_matrix (existentialVars top) (universalVars top))))
  exact h.of_eq fun P => (negate_clockSentence_eq top P).symm

/-- The prenex negation of the clock sentence is computable. -/
theorem computable_clockSentence_negate (top : Bool) :
    Computable (fun P => (clockSentence top P).negate) :=
  (primrec_clockSentence_negate top).to_comp

end UndeciSigma2
