import Mathlib.Computability.Partrec

/-! # Gödel codes for tagged binary trees

Each node stores a tag and two smaller child codes. Recursion on these codes
allows a parameter to change when descending to a child and preserves
primitive recursiveness.
-/

namespace UndeciSigma2.Computability

/-- A tagged binary node; zero is reserved for the default leaf. -/
def node (tag left right : Nat) : Nat := Nat.pair tag (Nat.pair left right) + 1

def tag (k : Nat) : Nat := k.pred.unpair.1
def left (k : Nat) : Nat := k.pred.unpair.2.unpair.1
def right (k : Nat) : Nat := k.pred.unpair.2.unpair.2

@[simp] theorem tag_node (t l r : Nat) : tag (node t l r) = t := by simp [tag, node]
@[simp] theorem left_node (t l r : Nat) : left (node t l r) = l := by simp [left, node]
@[simp] theorem right_node (t l r : Nat) : right (node t l r) = r := by simp [right, node]
@[simp] theorem node_ne_zero (t l r : Nat) : node t l r ≠ 0 := by simp [node]

theorem left_lt {k : Nat} (h : k ≠ 0) : left k < k := by
  change k.pred.unpair.2.unpair.1 < k
  exact lt_of_le_of_lt (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (Nat.pred_lt h)

theorem right_lt {k : Nat} (h : k ≠ 0) : right k < k := by
  change k.pred.unpair.2.unpair.2 < k
  exact lt_of_le_of_lt (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (Nat.pred_lt h)

theorem primrec_node : Primrec (fun p : Nat × Nat × Nat => node p.1 p.2.1 p.2.2) :=
  Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem primrec_tag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.pred)
theorem primrec_left : Primrec left :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.pred)))
theorem primrec_right : Primrec right :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.pred)))

/-- Recursion with a parameter that may change when entering either child. -/
def fold {A B : Type} (base : A → B) (next : A → Nat → A)
    (step : A → Nat → Nat → Nat → B → B → B) (a : A) (k : Nat) : B :=
  if _h : k = 0 then base a else
    step a (tag k) (left k) (right k)
      (fold base next step (next a (tag k)) (left k))
      (fold base next step (next a (tag k)) (right k))
termination_by k
 decreasing_by
  · exact left_lt _h
  · exact right_lt _h

@[simp] theorem fold_zero {A B : Type} (b : A → B) (n : A → Nat → A)
    (s : A → Nat → Nat → Nat → B → B → B) (a : A) : fold b n s a 0 = b a := by
  rw [fold]; simp

@[simp] theorem fold_node {A B : Type} (b : A → B) (n : A → Nat → A)
    (s : A → Nat → Nat → Nat → B → B → B) (a : A) (t l r : Nat) :
    fold b n s a (node t l r) =
      s a t l r (fold b n s (n a t) l) (fold b n s (n a t) r) := by
  rw [fold]; simp

/-- Primitive recursion on these codes, including changing the parameter under
binders, preserves primitive recursiveness. -/
theorem primrec_fold {A B : Type} [Primcodable A] [Primcodable B]
    (base : A → B) (next : A → Nat → A)
    (step : A → Nat → Nat → Nat → B → B → B)
    (hb : Primrec base) (hn : Primrec₂ next)
    (hs : Primrec (fun p : A × Nat × Nat × Nat × B × B =>
      step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)) :
    Primrec₂ (fold base next step) := by
  let children (p : A × Nat) : List (A × Nat) :=
    if p.2 = 0 then [] else [(next p.1 (tag p.2), left p.2),
      (next p.1 (tag p.2), right p.2)]
  let finish (p : A × Nat) (rs : List B) : Option B :=
    if p.2 = 0 then some (base p.1) else
      rs[0]?.bind fun l => rs[1]?.map fun r => step p.1 (tag p.2) (left p.2) (right p.2) l r
  have hc : Primrec children := by
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const [])
    have ha := hn.comp Primrec.fst (primrec_tag.comp Primrec.snd)
    exact Primrec.list_cons.comp (ha.pair (primrec_left.comp Primrec.snd))
      (Primrec.list_cons.comp (ha.pair (primrec_right.comp Primrec.snd)) (Primrec.const []))
  have hf : Primrec₂ finish := by
    apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
      (Primrec.option_some.comp (hb.comp (Primrec.fst.comp Primrec.fst)))
    apply Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0))
    apply Primrec.option_map (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const 1))
    exact hs.comp ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((primrec_tag.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
      ((primrec_left.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
      ((primrec_right.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))))
  apply Primrec.nat_omega_rec' (fun p : A × Nat => fold base next step p.1 p.2)
    Primrec.snd hc hf
  · intro p q hq
    simp only [children] at hq
    split_ifs at hq with h
    · simp at hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact left_lt h
      · exact right_lt h
  · intro p
    simp only [finish, children]
    split_ifs with h
    · simp [h]
    · rw [fold, dite_eq_right h]
      simp

end UndeciSigma2.Computability
