import UndeciSigma2.Undecidability.Computable
import UndeciSigma2.Recurrence.Definition

/-! # Primitive recursiveness of the recurrence sentence

The matrix depends on the program through its length, the instruction at each state, the
iterated contexts and the list of uniqueness clauses, all of which are primitive recursive.
The quantifier blocks have fixed lengths.
-/

namespace UndeciSigma2

open UndeciSigma2.Computability Sentence

namespace Recurrence

variable {top : Bool} {n : ℕ}

section Clauses
variable (x : Existentials (Term top n)) (v : Universals (Term top n))
variable {α : Type} [Primcodable α] {q l r : α → ℕ}

/-- The branch clause is primitive recursive in its three states. -/
theorem primrec_branchClause (hq : Primrec q) (hl : Primrec l) (hr : Primrec r) :
    Primrec (fun a => branchClause x v (q a) (l a) (r a)) := by
  unfold branchClause
  have hpack := (Term.primrec_pack v.y₁).comp hq
  have hctxl := (Term.primrec_stateContext x.full v.g₁).comp hl
  have hctxr := (Term.primrec_stateContext x.full v.g₁).comp hr
  repeat' first | exact Primrec.const _ | exact hpack | exact hctxl | exact hctxr |
    apply primrec_imp.comp | apply primrec_and.comp | apply primrec_le.comp

/-- Instruction clauses are primitive recursive in the length, state, and instruction. -/
theorem primrec_instructionClauses :
    Primrec (fun a : (ℕ × ℕ) × NInstr => instructionClauses x v a.1.1 a.1.2 a.2) := by
  have hsum : Primrec (fun a : (ℕ × ℕ) × NInstr => NInstr.equivSum a.2) :=
    (Primrec.of_equiv (e := NInstr.equivSum)).comp Primrec.snd
  have hinc : Primrec₂ (fun (a : (ℕ × ℕ) × NInstr) (b : Fin 2 × ℕ) =>
      instructionClauses x v a.1.1 a.1.2 (.inc b.1 b.2)) := by
    unfold instructionClauses
    have hk : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hc : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ) => a.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hr : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ) => min a.2.2 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.snd.comp Primrec.snd) hk
    have ho := (Primrec.dom_finite otherCounter).comp hc
    exact (primrec_and.comp (primrec_transitionClause x v hq hr)
      (primrec_and.comp (primrec_upperBoundClause x v 0 false hq hc)
      (primrec_and.comp (primrec_lowerBoundClause x v 2 hq hc)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq ho)
        (primrec_lowerBoundClause x v 1 hq ho))))).to₂
  have hjz : Primrec₂ (fun (a : (ℕ × ℕ) × NInstr) (b : Fin 2 × ℕ × ℕ) =>
      instructionClauses x v a.1.1 a.1.2 (.jzdec b.1 b.2.1 b.2.2)) := by
    unfold instructionClauses
    have hk : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ × ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ × ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hc : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ × ℕ) => a.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hz : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ × ℕ) => min a.2.2.1 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hk
    have hp : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (Fin 2 × ℕ × ℕ) => min a.2.2.2 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hk
    have ho := (Primrec.dom_finite otherCounter).comp hc
    exact (primrec_and.comp (primrec_zeroTestClause x v hq hz hc)
      (primrec_and.comp (primrec_positiveTestClause x v hq hp hc)
      (primrec_and.comp (primrec_upperBoundClause x v 2 true hq hc)
      (primrec_and.comp (primrec_lowerBoundClause x v 0 hq hc)
      (primrec_and.comp (primrec_nextToothClause x v hq hc)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq ho)
        (primrec_lowerBoundClause x v 1 hq ho))))))).to₂
  have hch : Primrec₂ (fun (a : (ℕ × ℕ) × NInstr) (b : ℕ × ℕ) =>
      instructionClauses x v a.1.1 a.1.2 (.choice b.1 b.2)) := by
    unfold instructionClauses
    have hk : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hl : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => min a.2.1 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) hk
    have hr : Primrec (fun a : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => min a.2.2 a.1.1.1) :=
      Primrec.nat_min.comp (Primrec.snd.comp Primrec.snd) hk
    have h₀ : Primrec (fun _ : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => (0 : Fin 2)) := Primrec.const _
    have h₁ : Primrec (fun _ : ((ℕ × ℕ) × NInstr) × (ℕ × ℕ) => (1 : Fin 2)) := Primrec.const _
    exact (primrec_and.comp (primrec_branchClause x v hq hl hr)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq h₀)
      (primrec_and.comp (primrec_lowerBoundClause x v 1 hq h₀)
      (primrec_and.comp (primrec_upperBoundClause x v 1 false hq h₁)
        (primrec_lowerBoundClause x v 1 hq h₁))))).to₂
  have hrest : Primrec₂ (fun (a : (ℕ × ℕ) × NInstr) (b : (Fin 2 × ℕ × ℕ) ⊕ (ℕ × ℕ)) =>
      Sum.casesOn (motive := fun _ => Formula top n) b
        (fun b => instructionClauses x v a.1.1 a.1.2 (.jzdec b.1 b.2.1 b.2.2))
        (fun b => instructionClauses x v a.1.1 a.1.2 (.choice b.1 b.2))) :=
    (Primrec.sumCasesOn Primrec.snd (hjz.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hch.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn hsum hinc hrest).of_eq fun a => by
    rcases a with ⟨⟨k, q⟩, i | i | i⟩ <;> rfl

/-- Traversing the program to collect its instruction clauses is primitive recursive. -/
theorem primrec_programClauses : Primrec (programClauses (top := top) (m := n) x v) := by
  apply primrec_allOf.comp
  apply Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
  have hi : Primrec₂ (fun a : NProgram × ℕ => fun i : NInstr =>
      instructionClauses x v a.1.length a.2 i) :=
    ((primrec_instructionClauses x v).comp
      (((Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  apply (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const trueAtom) hi).to₂.of_eq
  intro P q
  cases P[q]? <;> rfl

/-- The uniqueness clauses are primitive recursive in the number of states. -/
theorem primrec_uniquenessClauses : Primrec (uniquenessClauses (top := top) (m := n) x v) := by
  have hq : Primrec (fun q : ℕ => allOf ((List.range q).map fun r => haltUniqueClause x v r q)) :=
    primrec_allOf.comp (Primrec.list_map Primrec.list_range
      (primrec_haltUniqueClause x v Primrec.snd Primrec.fst).to₂)
  exact primrec_allOf.comp (Primrec.list_map Primrec.list_range (hq.comp Primrec.snd).to₂)

theorem primrec_allClauses : Primrec (allClauses (top := top) (m := n) x v) :=
  primrec_and.comp (primrec_programClauses x v)
    (primrec_and.comp ((primrec_uniquenessClauses x v).comp Primrec.list_length)
      (Primrec.const _))

private theorem primrec_rootConditions : Primrec (rootConditions x) := by
  unfold rootConditions
  have hctx := Term.primrec_haltContext x.full x.rightRay
  repeat' first | exact Primrec.const _ | exact hctx |
    apply primrec_and.comp | apply primrec_le.comp

end Clauses

/-- The matrix is primitive recursive in the program, for fixed variable terms. -/
theorem primrec_matrix (x : Existentials (Term top n)) (v : Universals (Term top n)) :
    Primrec (fun P : NProgram => matrix x v P) :=
  primrec_and.comp ((primrec_rootConditions x).comp Primrec.list_length)
    (primrec_imp.comp (Primrec.const (guards x v)) (primrec_allClauses x v))

end Recurrence

/-- The recurrence sentence is a primitive recursive function of the program. -/
theorem primrec_recurrenceSentence (top : Bool) : Primrec (recurrenceSentence top) :=
  (primrec_exs 9).comp ((primrec_alls 14).comp (Recurrence.primrec_matrix _ _))

/-- The recurrence sentence is a computable function of the program. -/
theorem computable_recurrenceSentence (top : Bool) : Computable (recurrenceSentence top) :=
  (primrec_recurrenceSentence top).to_comp

end UndeciSigma2
