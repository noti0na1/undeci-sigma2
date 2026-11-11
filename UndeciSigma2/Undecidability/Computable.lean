import UndeciSigma2.Computable.Renaming
import UndeciSigma2.Sentence.Definition

/-! # Primitive recursiveness of the machine sentence

The matrix depends on the program through its length, the instruction at each
state, and the iterated contexts, all of which are primitive recursive. The
quantifier blocks have fixed lengths. The prenex negation of the sentence is also
primitive recursive.
-/

namespace UndeciSigma2

open UndeciSigma2.Computability Sentence

namespace Term
variable {top : Bool} {n : ℕ}

/-- Packing a fixed term at a numbered state is primitive recursive. -/
theorem primrec_pack (y : Term top n) : Primrec (fun q => pack q y) := by
  have h := Primrec.nat_rec₁ (.f y .bot)
    ((primrec_f.comp (Primrec.const .bot) Primrec.snd).to₂)
  exact h.of_eq fun q => by induction q <;> simp [pack, *]

/-- The context bounding a state's tail is primitive recursive in its state. -/
theorem primrec_stateContext (z g : Term top n) :
    Primrec (fun r => stateContext z r g) := by
  have h := Primrec.nat_rec₁ (.f (.f z g) z)
    ((primrec_f.comp (Primrec.const z) Primrec.snd).to₂)
  exact h.of_eq fun r => by induction r <;> simp [stateContext, *]

/-- The halting context is primitive recursive in the program length. -/
theorem primrec_haltContext (z s : Term top n) : Primrec (haltContext z s) := by
  have h := Primrec.nat_rec₁ (.f s z)
    ((primrec_f.comp (Primrec.const z) Primrec.snd).to₂)
  exact h.of_eq fun k => by induction k <;> simp [haltContext, *]

end Term

namespace Sentence
variable {top : Bool} {n : ℕ}

/-- Prefixing a fixed number of existential quantifiers is primitive recursive. -/
theorem primrec_exs (k : ℕ) : Primrec (@exs top n k) := by
  induction k with
  | zero => exact Primrec.id
  | succ k ih => exact ih.comp primrec_ex

/-- Prefixing a fixed number of universal quantifiers is primitive recursive. -/
theorem primrec_alls (k : ℕ) : Primrec (@alls top n k) := by
  induction k with
  | zero => exact Primrec.id
  | succ k ih => exact ih.comp primrec_all

/-- The conjunction of a list of formulas is primitive recursive in the list. -/
theorem primrec_allOf : Primrec (@allOf top n) :=
  Primrec.list_foldr Primrec.id (Primrec.const _)
    ((primrec_and.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)

section Clauses
variable (x : Existentials (Term top n)) (v : Universals (Term top n))
variable {α : Type} [Primcodable α] {q r k : α → ℕ} {c : α → Fin 2}

/-- The upper-bound clause is primitive recursive in its state and counter. -/
theorem primrec_upperBoundClause (δ : ℕ) (trunc : Bool)
    (hq : Primrec q) (hc : Primrec c) :
    Primrec (fun a => upperBoundClause x v δ trunc (q a) (c a)) := by
  unfold upperBoundClause
  have hcounter := (Primrec.dom_finite x.counter).comp hc
  have hpack := (Term.primrec_pack v.y₃).comp hq
  repeat' first | exact Primrec.const _ | exact hcounter | exact hpack |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The lower-bound clause is primitive recursive in its state and counter. -/
theorem primrec_lowerBoundClause (δ : ℕ) (hq : Primrec q) (hc : Primrec c) :
    Primrec (fun a => lowerBoundClause x v δ (q a) (c a)) := by
  unfold lowerBoundClause
  have hcounter := (Primrec.dom_finite x.counter).comp hc
  have hpack := (Term.primrec_pack v.y₃).comp hq
  repeat' first | exact Primrec.const _ | exact hcounter | exact hpack |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The transition clause is primitive recursive in its two states. -/
theorem primrec_transitionClause (hq : Primrec q) (hr : Primrec r) :
    Primrec (fun a => transitionClause x v (q a) (r a)) := by
  unfold transitionClause
  have hpack := (Term.primrec_pack v.y₁).comp hq
  have hctx := (Term.primrec_stateContext x.full v.g₁).comp hr
  repeat' first | exact Primrec.const _ | exact hpack | exact hctx |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The next-tooth clause is primitive recursive in its state and counter. -/
theorem primrec_nextToothClause (hq : Primrec q) (hc : Primrec c) :
    Primrec (fun a => nextToothClause x v (q a) (c a)) := by
  unfold nextToothClause
  have hcounter := (Primrec.dom_finite x.counter).comp hc
  have hpack := (Term.primrec_pack v.y₁).comp hq
  repeat' first | exact Primrec.const _ | exact hcounter | exact hpack |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The uniqueness clause is primitive recursive in its two states. -/
theorem primrec_haltUniqueClause (hk : Primrec k) (hq : Primrec q) :
    Primrec (fun a => haltUniqueClause x v (k a) (q a)) := by
  unfold haltUniqueClause
  have hpack := (Term.primrec_pack v.y₁).comp hq
  have hhalt := (Term.primrec_pack v.y₁).comp hk
  repeat' first | exact Primrec.const _ | exact hpack | exact hhalt |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The zero-test clause is primitive recursive in its states and counter. -/
theorem primrec_zeroTestClause (hq : Primrec q) (hr : Primrec r) (hc : Primrec c) :
    Primrec (fun a => zeroTestClause x v (q a) (r a) (c a)) := by
  unfold zeroTestClause
  have hcounter := (Primrec.dom_finite x.counter).comp hc
  have hpack := (Term.primrec_pack v.y₃).comp hq
  have hctx := (Term.primrec_stateContext x.full v.g₃).comp hr
  repeat' first | exact Primrec.const _ | exact hcounter | exact hpack | exact hctx |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- The positive-test clause is primitive recursive in its states and counter. -/
theorem primrec_positiveTestClause (hq : Primrec q) (hr : Primrec r) (hc : Primrec c) :
    Primrec (fun a => positiveTestClause x v (q a) (r a) (c a)) := by
  unfold positiveTestClause
  have hcounter := (Primrec.dom_finite x.counter).comp hc
  have hpack := (Term.primrec_pack v.y₃).comp hq
  have hctx := (Term.primrec_stateContext x.full v.g₃).comp hr
  repeat' first | exact Primrec.const _ | exact hcounter | exact hpack | exact hctx |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- Instruction clauses are primitive recursive in the length, state, and instruction. -/
theorem primrec_instructionClauses :
    Primrec (fun a : (ℕ × ℕ) × Instr => instructionClauses x v a.1.1 a.1.2 a.2) := by
  have hsum : Primrec (fun a : (ℕ × ℕ) × Instr => Instr.equivSum a.2) :=
    (Primrec.of_equiv (e := Instr.equivSum)).comp Primrec.snd
  have h := Primrec.sumCasesOn hsum
    (g := fun a (b : Fin 2 × ℕ) => instructionClauses x v a.1.1 a.1.2 (.inc b.1 b.2))
    (h := fun a (b : Fin 2 × ℕ × ℕ) =>
      instructionClauses x v a.1.1 a.1.2 (.jzdec b.1 b.2.1 b.2.2)) ?_ ?_
  · exact h.of_eq fun a => by cases a.2 <;> rfl
  · unfold instructionClauses
    have hk : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hc : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ) => a.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hr : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ) => min a.2.2 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.snd.comp Primrec.snd) hk
    have ho := (Primrec.dom_finite otherCounter).comp hc
    exact (primrec_and.comp (primrec_haltUniqueClause x v hk hq)
      (primrec_and.comp (primrec_transitionClause x v hq hr)
      (primrec_and.comp (primrec_upperBoundClause x v 0 false hq hc)
      (primrec_and.comp (primrec_lowerBoundClause x v 2 hq hc)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq ho)
        (primrec_lowerBoundClause x v 1 hq ho)))))).to₂
  · unfold instructionClauses
    have hk : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ × ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ × ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hc : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ × ℕ) => a.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hz : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ × ℕ) => min a.2.2.1 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hk
    have hp : Primrec (fun a : ((ℕ × ℕ) × Instr) × (Fin 2 × ℕ × ℕ) => min a.2.2.2 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hk
    have ho := (Primrec.dom_finite otherCounter).comp hc
    exact (primrec_and.comp (primrec_haltUniqueClause x v hk hq)
      (primrec_and.comp (primrec_zeroTestClause x v hq hz hc)
      (primrec_and.comp (primrec_positiveTestClause x v hq hp hc)
      (primrec_and.comp (primrec_upperBoundClause x v 2 true hq hc)
      (primrec_and.comp (primrec_lowerBoundClause x v 0 hq hc)
      (primrec_and.comp (primrec_nextToothClause x v hq hc)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq ho)
        (primrec_lowerBoundClause x v 1 hq ho)))))))).to₂

/-- Traversing the program to collect its instruction clauses is primitive recursive. -/
theorem primrec_programClauses : Primrec (programClauses x v) := by
  apply primrec_allOf.comp
  apply Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
  have hi : Primrec₂ (fun a : Program × ℕ => fun i : Instr =>
      instructionClauses x v a.1.length a.2 i) :=
    ((primrec_instructionClauses x v).comp
      (((Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  apply (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const trueAtom) hi).to₂.of_eq
  intro P q
  cases P[q]? <;> rfl

private theorem primrec_rootConditions : Primrec (rootConditions x) := by
  unfold rootConditions
  have hctx := Term.primrec_haltContext x.full x.rightRay
  repeat' first | exact Primrec.const _ | exact hctx |
    apply primrec_and.comp | apply primrec_neg.comp | apply primrec_le.comp

end Clauses

/-- The matrix is primitive recursive in the program, for fixed variable terms. -/
theorem primrec_matrix (x : Existentials (Term top n)) (v : Universals (Term top n)) :
    Primrec (fun P : Program => matrix x v P) := by
  exact primrec_and.comp ((primrec_rootConditions x).comp Primrec.list_length)
    (primrec_imp.comp (Primrec.const (guards x v)) (primrec_programClauses x v))

/-- Prenex negation exchanges the two quantifier blocks. -/
theorem negate_machineSentence_eq (top : Bool) (P : Program) :
    (machineSentence top P).negate =
      alls 9 (exs 14 (.neg (matrix (existentialVars top) (universalVars top) P))) := rfl

end Sentence

/-- The machine sentence is a primitive recursive function of the program. -/
theorem primrec_machineSentence (top : Bool) : Primrec (machineSentence top) :=
  (primrec_exs 9).comp ((primrec_alls 14).comp (primrec_matrix _ _))

/-- The machine sentence is a computable function of the program. -/
theorem computable_machineSentence (top : Bool) : Computable (machineSentence top) :=
  (primrec_machineSentence top).to_comp

/-- The prenex negation of the machine sentence is primitive recursive. -/
theorem primrec_machineSentence_negate (top : Bool) :
    Primrec (fun P => (machineSentence top P).negate) := by
  have h := (primrec_alls (top := top) (n := 0) 9).comp ((primrec_exs 14).comp
    (primrec_neg.comp (primrec_matrix (existentialVars top) (universalVars top))))
  exact h.of_eq fun P => (negate_machineSentence_eq top P).symm

/-- The prenex negation of the machine sentence is computable. -/
theorem computable_machineSentence_negate (top : Bool) :
    Computable (fun P => (machineSentence top P).negate) :=
  (primrec_machineSentence_negate top).to_comp

end UndeciSigma2
