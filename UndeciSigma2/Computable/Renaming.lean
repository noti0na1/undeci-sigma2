import UndeciSigma2.Computable.Constructors
import Mathlib.Data.Fintype.Pi

/-! # Primitive recursive renaming

A variable map is encoded by its finite list of values. Under a binder,
renaming fixes index zero and increments the other indices. The numerical
operations agree with `Term.rename` and `Formula.rename`.
-/

namespace UndeciSigma2.Computability

/-- The finite table of a bounded variable map. -/
def renamingList {n m : Nat} (σ : Fin n → Fin m) : List Nat :=
  List.ofFn (fun i => (σ i).val)

/-- Extend a numerical renaming table under one binder. -/
def liftList (σ : List Nat) : List Nat := 0 :: σ.map Nat.succ

@[simp] theorem liftList_renamingList {n m : Nat} (σ : Fin n → Fin m) :
    liftList (renamingList σ) = renamingList (Formula.lift σ) := by
  simp [liftList, renamingList, List.ofFn_succ, Formula.lift, List.map_ofFn, Function.comp_def]

theorem primrec_liftList : Primrec liftList :=
  Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_map Primrec.id (Primrec.succ.comp Primrec.snd).to₂)

theorem primrec_lift {n m : Nat} : Primrec (@Formula.lift n m) := Primrec.dom_finite _

def renameTermStep (σ : List Nat) (t l _r x y : Nat) : Nat :=
  if t = 0 then node 0 (σ.getD l 0) 0
  else if t = 1 then node 1 0 0
  else if t = 2 then node 2 x y else 0

def renameTermCode : List Nat → Nat → Nat :=
  fold (fun _ => 0) (fun σ _ => σ) renameTermStep

theorem primrec_renameTermStep :
    Primrec (fun p : List Nat × Nat × Nat × Nat × Nat × Nat =>
      renameTermStep p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold renameTermStep
  have ht := Primrec.fst.comp Primrec.snd (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  have hl := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
  · exact primrec_node.comp ((Primrec.const 0).pair
      (((Primrec.list_getD 0).comp Primrec.fst hl).pair (Primrec.const 0)))
  · apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.const _)
    apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) _ (Primrec.const 0)
    exact primrec_node.comp ((Primrec.const 2).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
       (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

theorem primrec_renameTermCode : Primrec₂ renameTermCode :=
  primrec_fold _ _ _ (Primrec.const 0) Primrec.fst primrec_renameTermStep

@[simp] theorem renamingList_getD {n m : Nat} (σ : Fin n → Fin m) (i : Fin n) :
    (renamingList σ).getD i.val 0 = (σ i).val := by
  simp [renamingList, List.getD, i.isLt]

theorem renameTermCode_correct {top : Bool} {n m : Nat} (σ : Fin n → Fin m) (t : Term top n) :
    renameTermCode (renamingList σ) (termCode t) = termCode (t.rename σ) := by
  induction t <;> simp_all [termCode, Term.rename, renameTermCode, renameTermStep, renamingList]

/-- Renaming is primitive recursive jointly in the variable map and term. -/
theorem primrec_termRename {top : Bool} {n m : Nat} : Primrec₂ (@Term.rename top n m) := by
  apply Primrec₂.encode_iff.mp
  exact (primrec_renameTermCode.comp
    ((Primrec.dom_finite renamingList).comp Primrec.fst)
    (primrec_termCode.comp Primrec.snd)).of_eq fun p => renameTermCode_correct p.1 p.2

/-- The arity and renaming table are extended under a quantifier. -/
def nextRenaming (σ : List Nat) (t : Nat) : List Nat :=
  if t = 6 ∨ t = 7 then liftList σ else σ

def renameFormulaStep (σ : List Nat) (t l r x y : Nat) : Nat :=
  if t = 0 ∨ t = 1 then node t (renameTermCode σ l) (renameTermCode σ r)
  else formulaStep false 0 t 0 0 x y

def renameFormulaCode : List Nat → Nat → Nat :=
  fold (fun _ => 0) nextRenaming renameFormulaStep

theorem primrec_nextRenaming : Primrec₂ nextRenaming :=
  Primrec.ite ((Primrec.eq.comp Primrec.snd (Primrec.const 6)).or
    (Primrec.eq.comp Primrec.snd (Primrec.const 7)))
    (primrec_liftList.comp Primrec.fst) Primrec.fst

theorem primrec_renameFormulaStep :
    Primrec (fun p : List Nat × Nat × Nat × Nat × Nat × Nat =>
      renameFormulaStep p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold renameFormulaStep
  have ht := Primrec.fst.comp Primrec.snd (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  have hl := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  have hr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  have hx := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  have hy := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (α := List Nat × Nat × Nat × Nat × Nat × Nat)
  apply Primrec.ite ((Primrec.eq.comp ht (Primrec.const 0)).or
    (Primrec.eq.comp ht (Primrec.const 1)))
  · exact primrec_node.comp (ht.pair
      ((primrec_renameTermCode.comp Primrec.fst hl).pair
        (primrec_renameTermCode.comp Primrec.fst hr)))
  · exact (primrec_formulaStep false).comp ((Primrec.const 0).pair
      (ht.pair ((Primrec.const 0).pair ((Primrec.const 0).pair (hx.pair hy)))))

theorem primrec_renameFormulaCode : Primrec₂ renameFormulaCode :=
  primrec_fold _ _ _ (Primrec.const 0) primrec_nextRenaming primrec_renameFormulaStep

theorem renameFormulaCode_correct {top : Bool} {n m : Nat}
    (σ : Fin n → Fin m) (p : Formula top n) :
    renameFormulaCode (renamingList σ) (formulaCode p) = formulaCode (p.rename σ) := by
  induction p generalizing m <;>
    simp_all [formulaCode, Formula.rename, renameFormulaCode, renameFormulaStep,
      nextRenaming, formulaStep, renameTermCode_correct]

/-- Renaming formulas is primitive recursive, including under binders. -/
theorem primrec_formulaRename {top : Bool} {n m : Nat} : Primrec₂ (@Formula.rename top n m) := by
  apply Primrec₂.encode_iff.mp
  exact (primrec_renameFormulaCode.comp
    ((Primrec.dom_finite renamingList).comp Primrec.fst)
    (primrec_formulaCode.comp Primrec.snd)).of_eq fun p => renameFormulaCode_correct p.1 p.2

/-- Weakening by one variable is computable. -/
theorem computable_weaken {top : Bool} {n : Nat} :
    Computable (fun p : Formula top n => p.rename Fin.succ) :=
  (primrec_formulaRename.comp (Primrec.const Fin.succ) Primrec.id).to_comp

end UndeciSigma2.Computability
