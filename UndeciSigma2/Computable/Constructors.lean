import UndeciSigma2.Computable.Instances

/-! # Primitive recursive formula constructors

The syntax constructors are primitive recursive for the encodings in
`Instances`.
-/

namespace UndeciSigma2.Computability

variable {top : Bool} {n : Nat}

theorem primrec_termCode : Primrec (@termCode top n) := Primrec.encode

theorem primrec_formulaCode : Primrec (@formulaCode top n) := Primrec.encode

theorem primrec_var : Primrec (@Term.var top n) := Primrec.dom_finite _

theorem primrec_f : Primrec₂ (@Term.f top n) := by
  apply Primrec₂.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 2).pair
    ((primrec_termCode.comp Primrec.fst).pair (primrec_termCode.comp Primrec.snd)))

theorem primrec_le : Primrec₂ (@Formula.le top n) := by
  apply Primrec₂.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 0).pair
    ((primrec_termCode.comp Primrec.fst).pair (primrec_termCode.comp Primrec.snd)))

theorem primrec_eq : Primrec₂ (@Formula.eq top n) := by
  apply Primrec₂.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 1).pair
    ((primrec_termCode.comp Primrec.fst).pair (primrec_termCode.comp Primrec.snd)))

theorem primrec_neg : Primrec (@Formula.neg top n) := by
  apply Primrec.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 3).pair (primrec_formulaCode.pair (Primrec.const 0)))

theorem primrec_and : Primrec₂ (@Formula.and top n) := by
  apply Primrec₂.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 4).pair
    ((primrec_formulaCode.comp Primrec.fst).pair (primrec_formulaCode.comp Primrec.snd)))

theorem primrec_or : Primrec₂ (@Formula.or top n) := by
  apply Primrec₂.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 5).pair
    ((primrec_formulaCode.comp Primrec.fst).pair (primrec_formulaCode.comp Primrec.snd)))

theorem primrec_ex : Primrec (@Formula.ex top n) := by
  apply Primrec.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 6).pair (primrec_formulaCode.pair (Primrec.const 0)))

theorem primrec_all : Primrec (@Formula.all top n) := by
  apply Primrec.encode_iff.mp
  exact primrec_node.comp ((Primrec.const 7).pair (primrec_formulaCode.pair (Primrec.const 0)))

theorem primrec_imp : Primrec₂ (@Formula.imp top n) :=
  primrec_or.comp (primrec_neg.comp Primrec.fst) Primrec.snd

end UndeciSigma2.Computability
