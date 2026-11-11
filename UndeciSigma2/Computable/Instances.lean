import UndeciSigma2.Computable.Coding
import UndeciSigma2.Syntax

/-! # Encodings of terms and formulas

Terms and formulas use tagged binary trees encoded by natural numbers.
Total decoders and primitive recursive normalization give `Primcodable` instances.
-/

namespace UndeciSigma2.Computability

open Primrec

/-- A primitive coding from a total decoder and a primitive recursive normalizer. -/
@[instance_reducible]
def ofCodec {A : Type} (enc : A → Nat) (dec : Nat → A)
    (h : ∀ a, dec (enc a) = a) (norm : Nat → Nat)
    (hn : Primrec norm) (he : ∀ k, norm k = enc (dec k)) : Primcodable A where
  encode := enc
  decode k := some (dec k)
  encodek a := congrArg some (h a)
  prim := (Nat.Primrec.succ.comp (Primrec.nat_iff.mp hn)).of_eq fun k => by
    change norm k + 1 = enc (dec k) + 1
    rw [he]

/-- The canonical natural-number code of a bounded term. -/
def termCode {top : Bool} {n : Nat} : Term top n → Nat
  | .var i => node 0 i.val 0
  | .bot => 0
  | .top _ => node 1 0 0
  | .f s t => node 2 (termCode s) (termCode t)

/-- Total decoding, with bottom as the malformed-input value. -/
def termDecode (top : Bool) (n k : Nat) : Term top n :=
  if _h : k = 0 then .bot else
  if tag k = 0 then
    if h : left k < n then .var ⟨left k, h⟩ else .bot
  else if tag k = 1 then
    if h : top = true then .top h else .bot
  else if tag k = 2 then .f (termDecode top n (left k)) (termDecode top n (right k))
  else .bot
termination_by k
 decreasing_by
  · exact left_lt _h
  · exact right_lt _h

@[simp] theorem termDecode_code {top : Bool} {n : Nat} (t : Term top n) :
    termDecode top n (termCode t) = t := by
  induction t with
  | var i => simp [termCode, termDecode, i.isLt]
  | bot => simp [termCode, termDecode]
  | top h => simp [termCode, termDecode, h]
  | f s t hs ht => simp [termCode, termDecode, hs, ht]

/-- One step of term-code normalization. -/
def termStep (top : Bool) (n tag l _r x y : Nat) : Nat :=
  if tag = 0 then if l < n then node 0 l 0 else 0
  else if tag = 1 then if top = true then node 1 0 0 else 0
  else if tag = 2 then node 2 x y else 0

def termNorm (top : Bool) : Nat → Nat → Nat :=
  fold (fun _ => 0) (fun n _ => n) (termStep top)

theorem primrec_termStep (top : Bool) :
    Primrec (fun p : Nat × Nat × Nat × Nat × Nat × Nat =>
      termStep top p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold termStep
  have ht := Primrec.fst.comp Primrec.snd (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hl := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := Nat × Nat × Nat × Nat × Nat × Nat)
  apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
  · apply Primrec.ite (Primrec.nat_lt.comp hl Primrec.fst)
    · exact primrec_node.comp ((Primrec.const 0).pair (hl.pair (Primrec.const 0)))
    · exact Primrec.const 0
  · apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.const _)
    apply Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) _ (Primrec.const 0)
    exact primrec_node.comp ((Primrec.const 2).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
       (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

theorem primrec_termNorm (top : Bool) : Primrec₂ (termNorm top) :=
  primrec_fold _ _ _ (Primrec.const 0) Primrec.fst (primrec_termStep top)

theorem termNorm_eq (top : Bool) (n k : Nat) :
    termNorm top n k = termCode (termDecode top n k) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hk : k = 0
    · subst k; simp [termNorm, termDecode, termCode]
    · have hl := ih (left k) (left_lt hk)
      have hr := ih (right k) (right_lt hk)
      unfold termNorm at hl hr
      rw [termNorm, fold, termDecode]
      split_ifs <;> simp_all [termStep, termCode]

instance termPrimcodable (top : Bool) (n : Nat) : Primcodable (Term top n) :=
  ofCodec termCode (termDecode top n) termDecode_code (termNorm top n)
    ((primrec_termNorm top).comp (Primrec.const n) Primrec.id) (termNorm_eq top n)

@[simp] theorem encode_term {top : Bool} {n : Nat} (t : Term top n) :
    Encodable.encode t = termCode t := rfl

/-- Formula codes preserve constructors, including both primitive atom kinds. -/
def formulaCode {top : Bool} : {n : Nat} → Formula top n → Nat
  | _, .le s t => node 0 (termCode s) (termCode t)
  | _, .eq s t => node 1 (termCode s) (termCode t)
  | _, .truth => 0
  | _, .falsity => node 2 0 0
  | _, .neg p => node 3 (formulaCode p) 0
  | _, .and p q => node 4 (formulaCode p) (formulaCode q)
  | _, .or p q => node 5 (formulaCode p) (formulaCode q)
  | _, .ex p => node 6 (formulaCode p) 0
  | _, .all p => node 7 (formulaCode p) 0

/-- A quantifier adds one available de Bruijn variable. -/
def nextArity (n tag : Nat) : Nat := if tag = 6 ∨ tag = 7 then n + 1 else n

/-- Total formula decoder. -/
def formulaDecode (top : Bool) (n k : Nat) : Formula top n :=
  if _h : k = 0 then .truth else
  if tag k = 0 then .le (termDecode top n (left k)) (termDecode top n (right k))
  else if tag k = 1 then .eq (termDecode top n (left k)) (termDecode top n (right k))
  else if tag k = 2 then .falsity
  else if tag k = 3 then .neg (formulaDecode top n (left k))
  else if tag k = 4 then .and (formulaDecode top n (left k)) (formulaDecode top n (right k))
  else if tag k = 5 then .or (formulaDecode top n (left k)) (formulaDecode top n (right k))
  else if tag k = 6 then .ex (formulaDecode top (n + 1) (left k))
  else if tag k = 7 then .all (formulaDecode top (n + 1) (left k))
  else .truth
termination_by k
 decreasing_by all_goals first | exact left_lt _h | exact right_lt _h

@[simp] theorem formulaDecode_code {top : Bool} {n : Nat} (p : Formula top n) :
    formulaDecode top n (formulaCode p) = p := by
  induction p <;> simp only [formulaCode] <;> rw [formulaDecode] <;> simp_all

/-- One normalization step; atom children are decoded as terms. -/
def formulaStep (top : Bool) (n tag l r x y : Nat) : Nat :=
  if tag = 0 then node 0 (termNorm top n l) (termNorm top n r)
  else if tag = 1 then node 1 (termNorm top n l) (termNorm top n r)
  else if tag = 2 then node 2 0 0
  else if tag = 3 then node 3 x 0
  else if tag = 4 then node 4 x y
  else if tag = 5 then node 5 x y
  else if tag = 6 then node 6 x 0
  else if tag = 7 then node 7 x 0
  else 0

def formulaNorm (top : Bool) : Nat → Nat → Nat :=
  fold (fun _ => 0) nextArity (formulaStep top)

theorem primrec_nextArity : Primrec₂ nextArity :=
  Primrec.ite ((Primrec.eq.comp Primrec.snd (Primrec.const 6)).or
    (Primrec.eq.comp Primrec.snd (Primrec.const 7)))
    (Primrec.succ.comp Primrec.fst) Primrec.fst

theorem primrec_formulaStep (top : Bool) :
    Primrec (fun p : Nat × Nat × Nat × Nat × Nat × Nat =>
      formulaStep top p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold formulaStep
  have ht := Primrec.fst.comp Primrec.snd (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hl := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hx := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hy := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (α := Nat × Nat × Nat × Nat × Nat × Nat)
  have hn (t : Nat) := primrec_node.comp ((Primrec.const t).pair
    (((primrec_termNorm top).comp Primrec.fst hl).pair
      ((primrec_termNorm top).comp Primrec.fst hr)))
  have hu (t : Nat) := primrec_node.comp ((Primrec.const t).pair (hx.pair (Primrec.const 0)))
  have hb (t : Nat) := primrec_node.comp ((Primrec.const t).pair (hx.pair hy))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (hn 0)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (hn 1)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) (Primrec.const _)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) (hu 3)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) (hb 4)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 5)) (hb 5)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 6)) (hu 6)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 7)) (hu 7) (Primrec.const 0))))))))

theorem primrec_formulaNorm (top : Bool) : Primrec₂ (formulaNorm top) :=
  primrec_fold _ _ _ (Primrec.const 0) primrec_nextArity (primrec_formulaStep top)

theorem formulaNorm_eq (top : Bool) (n k : Nat) :
    formulaNorm top n k = formulaCode (formulaDecode top n k) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hk : k = 0
    · subst k; simp [formulaNorm, formulaDecode, formulaCode]
    · have hl := ih (left k) (left_lt hk)
      have hr := ih (right k) (right_lt hk)
      unfold formulaNorm at hl hr
      rw [formulaNorm, fold, formulaDecode]
      split_ifs <;> simp_all [formulaStep, formulaCode, nextArity, termNorm_eq]

instance formulaPrimcodable (top : Bool) (n : Nat) : Primcodable (Formula top n) :=
  ofCodec formulaCode (formulaDecode top n) formulaDecode_code (formulaNorm top n)
    ((primrec_formulaNorm top).comp (Primrec.const n) Primrec.id) (formulaNorm_eq top n)

@[simp] theorem encode_formula {top : Bool} {n : Nat} (p : Formula top n) :
    Encodable.encode p = formulaCode p := rfl

end UndeciSigma2.Computability
