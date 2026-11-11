import UndeciSigma2.Computable.Constructors

/-! # Primitive recursive membership in prenex classes

The quantifier prefix and alternating block count are primitive recursive
on formula codes, so membership in each class Σₖ is a primitive recursive
predicate (`primrec_isSigma`). The subtype of Σ₂ sentences inherits the
standard subtype encoding.
-/

namespace UndeciSigma2.Computability

private abbrev PrefixInfo := Bool × Option (List Bool)

private def matrixInfo (b : Bool) : PrefixInfo :=
  (b, if b then some [] else none)

private def prefixStep (t : Nat) (x y : PrefixInfo) : PrefixInfo :=
  if t = 3 then matrixInfo x.1
  else if t = 4 ∨ t = 5 then matrixInfo (x.1 && y.1)
  else if t = 6 then (false, x.2.map (true :: ·))
  else if t = 7 then (false, x.2.map (false :: ·))
  else matrixInfo true

private def prefixInfo : Nat → PrefixInfo :=
  fold (fun _ : Unit => matrixInfo true) (fun a _ => a)
    (fun _ t _ _ x y => prefixStep t x y) ()

private theorem primrec_matrixInfo : Primrec matrixInfo :=
  Primrec.dom_finite _

private theorem primrec_prefixStep :
    Primrec (fun p : Nat × PrefixInfo × PrefixInfo => prefixStep p.1 p.2.1 p.2.2) := by
  have hx : Primrec (fun p : Nat × PrefixInfo × PrefixInfo => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : Nat × PrefixInfo × PrefixInfo => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hq (q : Bool) := (Primrec.const false).pair
    (Primrec.option_map (Primrec.snd.comp hx)
      (Primrec.list_cons.comp (Primrec.const q) Primrec.snd).to₂)
  unfold prefixStep
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
    (primrec_matrixInfo.comp (Primrec.fst.comp hx))
    (Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const 4)).or
      (Primrec.eq.comp Primrec.fst (Primrec.const 5)))
      (primrec_matrixInfo.comp ((Primrec.dom_bool₂ (· && ·)).comp
        (Primrec.fst.comp hx) (Primrec.fst.comp hy)))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6)) (hq true)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7)) (hq false)
          (Primrec.const _))))

private theorem primrec_prefixInfo : Primrec prefixInfo := by
  apply (primrec_fold (fun _ : Unit => matrixInfo true) (fun a _ => a)
    (fun _ t _ _ x y => prefixStep t x y) (Primrec.const _) Primrec.fst ?_).comp
    (Primrec.const ()) Primrec.id
  exact primrec_prefixStep.comp ((Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

private theorem prefixInfo_code {top : Bool} {n : Nat} (φ : Formula top n) :
    prefixInfo (formulaCode φ) = (φ.isMatrix, φ.quantifiers) := by
  induction φ <;>
    simp_all [prefixInfo, formulaCode, prefixStep, matrixInfo,
      Formula.isMatrix, Formula.quantifiers]
  all_goals rfl

theorem primrec_quantifiers {top : Bool} {n : Nat} :
    Primrec (@Formula.quantifiers top n) := by
  apply (Primrec.snd.comp (primrec_prefixInfo.comp primrec_formulaCode)).of_eq
  intro φ
  exact congrArg Prod.snd (prefixInfo_code φ)

/-- Simultaneously count blocks for both possible initial polarities. -/
private def blockPair (qs : List Bool) : Nat × Nat :=
  qs.foldr (fun q p => if q then (max 1 p.1, 1 + max 1 p.1)
    else (1 + max 1 p.2, max 1 p.2)) (0, 0)

private theorem blockPair_eq (qs : List Bool) :
    blockPair qs = (Formula.blocks true qs, Formula.blocks false qs) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (if q then (max 1 (blockPair qs).1, 1 + max 1 (blockPair qs).1)
      else (1 + max 1 (blockPair qs).2, max 1 (blockPair qs).2)) = _
    rw [ih]
    cases q <;> simp [Formula.blocks]

private theorem primrec_blockPair : Primrec blockPair := by
  have hx : Primrec (fun p : List Bool × Bool × (Nat × Nat) => max 1 p.2.2.1) :=
    Primrec.nat_max.comp (Primrec.const 1)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hy : Primrec (fun p : List Bool × Bool × (Nat × Nat) => max 1 p.2.2.2) :=
    Primrec.nat_max.comp (Primrec.const 1)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr Primrec.id (Primrec.const (0, 0))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
      (hx.pair (Primrec.nat_add.comp (Primrec.const 1) hx))
      ((Primrec.nat_add.comp (Primrec.const 1) hy).pair hy)).to₂

theorem primrec_blocks (start : Bool) : Primrec (Formula.blocks start) := by
  cases start
  · exact (Primrec.snd.comp primrec_blockPair).of_eq
      (fun qs => congrArg Prod.snd (blockPair_eq qs))
  · exact (Primrec.fst.comp primrec_blockPair).of_eq
      (fun qs => congrArg Prod.fst (blockPair_eq qs))

theorem primrec_isSigma {top : Bool} {n : Nat} (k : Nat) :
    PrimrecPred (Formula.IsSigma (top := top) (n := n) k) := by
  have h : Primrec (fun φ : Formula top n =>
      φ.quantifiers.casesOn (motive := fun _ => Bool) false
        (fun qs => decide (Formula.blocks true qs ≤ k))) :=
    Primrec.option_casesOn primrec_quantifiers (Primrec.const false)
      ((Primrec.nat_le.comp ((primrec_blocks true).comp Primrec.snd)
        (Primrec.const k)).decide).to₂
  apply Primrec.primrecPred
  apply h.of_eq
  intro φ
  cases hq : φ.quantifiers <;> simp [Formula.IsSigma, hq]

end UndeciSigma2.Computability

namespace UndeciSigma2

/-- Σ₂ sentences retain the formula codes, with the standard subtype decoder. -/
instance sigma2Primcodable (top : Bool) : Primcodable {φ : Formula top 0 // φ.IsSigma 2} :=
  Primcodable.subtype (Computability.primrec_isSigma 2)

end UndeciSigma2
