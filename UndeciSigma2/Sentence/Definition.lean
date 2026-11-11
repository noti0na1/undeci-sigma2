import UndeciSigma2.Sentence.Blocks
import UndeciSigma2.Machine

/-! # The machine sentence

For a two-counter program `P` with `n` instructions, the sentence has the prefix
`∃⁹ ∀¹⁴` and a quantifier-free matrix whose atoms are inequalities.

The nine existential variables are the two counter combs `A` and `B`, the state
tree `U`, and six helper trees `Z, S, T, L, G, G1` fixed by guarded equations.
The fourteen universal variables are three seeds `y₁ y₂ y₃`, three bounds
`g₁ g₂ g₃`, four auxiliaries `k k₀ kd kp` comparing counters with an offset, and
two pairs `d₁ p₁` and `d₂ p₂` aligning tooth indices.

The matrix is `rootConditions ∧ (guards → programClauses)`, where `programClauses` is
the conjunction of the clauses `instructionClauses n q P[q]` for `q < n`. The root
conditions state the helper equations, that the counters and the state tree
contain no top, that both counters are zero and the state is zero at step zero,
and that the halting state `n` occurs at some step. The guards state that the
universal values contain no top. The clauses relate consecutive steps of the run.
Jump targets are clipped to `n`, so all halting states are represented by `n`.
-/

namespace UndeciSigma2

/-! ## Terms -/

namespace Term
variable {top : Bool} {m : ℕ}

/-- The term `f(⊥, ⊥)`. -/
def e : Term top m := .f .bot .bot

/-- `pack q y = f(⊥, … f(⊥, f(y, ⊥)))`, placing `y` at the address `1^q 0`. -/
def pack : ℕ → Term top m → Term top m
  | 0, y => .f y .bot
  | q + 1, y => .f .bot (pack q y)

/-- `stateContext z r g = f(z, … f(f(z, g), z))`, with `g` at the address `1^r 0 1`. -/
def stateContext (z : Term top m) : ℕ → Term top m → Term top m
  | 0, g => .f (.f z g) z
  | r + 1, g => .f z (stateContext z r g)

/-- `haltContext z s n = f(z, … f(s, z))`, with `s` at the address `1^n 0`. -/
def haltContext (z s : Term top m) : ℕ → Term top m
  | 0 => .f s z
  | n + 1 => .f z (haltContext z s n)

/-- `popContext z δ k = f(… f(k, z) …, z)`, with `k` at the address `0^δ`. -/
def popContext (z : Term top m) : ℕ → Term top m → Term top m
  | 0, k => k
  | δ + 1, k => .f (popContext z δ k) z

example (y : Term top m) : pack 2 y = .f .bot (.f .bot (.f y .bot)) := rfl
example (z g : Term top m) : stateContext z 1 g = .f z (.f (.f z g) z) := rfl
example (z s : Term top m) : haltContext z s 2 = .f z (.f z (.f s z)) := rfl
example (z k : Term top m) : popContext z 2 k = .f (.f k z) z := rfl

end Term

namespace Sentence

/-! ## Variables -/

/-- The nine existential variables of the machine sentence. -/
structure Existentials (α : Type*) where
  /-- The two counter combs, `A` and `B`. -/
  counter : Fin 2 → α
  /-- The state tree `U`. -/
  states : α
  /-- The full tree `Z`. -/
  full : α
  /-- The right ray `S`. -/
  rightRay : α
  /-- The comb of stubs `T`. -/
  stubComb : α
  /-- The left ray `L`. -/
  leftRay : α
  /-- The comb universe `G`. -/
  combUniverse : α
  /-- The universe of short combs `G1`. -/
  shortCombs : α

/-- The fourteen universal variables of the machine sentence: the seeds `y₁ y₂ y₃` and the
bounds `g₁ g₂ g₃`, compared in the conclusions `yᵢ ≤ gᵢ` of the clauses, the auxiliaries
`k k₀ kd kp` of the comparison block, and the auxiliaries `d₁ p₁` and `d₂ p₂` of the two
alignment blocks. -/
structure Universals (α : Type*) where
  y₁ : α
  y₂ : α
  y₃ : α
  g₁ : α
  g₂ : α
  g₃ : α
  k : α
  k₀ : α
  kd : α
  kp : α
  d₁ : α
  p₁ : α
  d₂ : α
  p₂ : α

namespace Existentials
variable {α β : Type*}

/-- Apply a function to every variable. -/
def map (g : α → β) (x : Existentials α) : Existentials β :=
  ⟨g ∘ x.counter, g x.states, g x.full, g x.rightRay, g x.stubComb, g x.leftRay,
    g x.combUniverse, g x.shortCombs⟩

/-- Read the variables from a vector, in the order `A, B, U, Z, S, T, L, G, G1`. -/
def ofFn (x : Fin 9 → α) : Existentials α :=
  ⟨![x 0, x 1], x 2, x 3, x 4, x 5, x 6, x 7, x 8⟩

end Existentials

namespace Universals
variable {α β : Type*}

/-- Apply a function to every variable. -/
def map (g : α → β) (v : Universals α) : Universals β :=
  ⟨g v.y₁, g v.y₂, g v.y₃, g v.g₁, g v.g₂, g v.g₃, g v.k, g v.k₀, g v.kd, g v.kp,
    g v.d₁, g v.p₁, g v.d₂, g v.p₂⟩

/-- Read the variables from a vector, in the order
`y₁ y₂ y₃ g₁ g₂ g₃ k k₀ kd kp d₁ p₁ d₂ p₂`. -/
def ofFn (y : Fin 14 → α) : Universals α :=
  ⟨y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8, y 9, y 10, y 11, y 12, y 13⟩

/-- The variables as a vector, inverse to `ofFn`. -/
def toFn (v : Universals α) : Fin 14 → α :=
  ![v.y₁, v.y₂, v.y₃, v.g₁, v.g₂, v.g₃, v.k, v.k₀, v.kd, v.kp, v.d₁, v.p₁, v.d₂, v.p₂]

/-- Every variable satisfies `p`. -/
def Forall (p : α → Prop) (v : Universals α) : Prop :=
  p v.y₁ ∧ p v.y₂ ∧ p v.y₃ ∧ p v.g₁ ∧ p v.g₂ ∧ p v.g₃ ∧ p v.k ∧ p v.k₀ ∧ p v.kd ∧ p v.kp ∧
    p v.d₁ ∧ p v.p₁ ∧ p v.d₂ ∧ p v.p₂

@[simp] theorem ofFn_toFn (v : Universals α) : ofFn v.toFn = v := rfl

@[simp] theorem toFn_ofFn (y : Fin 14 → α) : (ofFn y).toFn = y := by
  funext i
  fin_cases i <;> rfl

theorem forall_iff_toFn (p : α → Prop) (v : Universals α) :
    v.Forall p ↔ ∀ i, p (v.toFn i) := by
  simp [Forall, toFn, Fin.forall_fin_succ]

theorem Forall.imp {p p' : α → Prop} (h : ∀ a, p a → p' a) {v : Universals α}
    (hv : v.Forall p) : v.Forall p' := by
  rw [forall_iff_toFn] at hv ⊢
  exact fun i => h _ (hv i)

end Universals

/-! ## Blocks -/

variable {top : Bool} {m : ℕ}

/-- An inequality atom that always holds; it ends every finite conjunction. -/
def trueAtom : Formula top m := .le .bot .bot

/-- The conjunction of a list of formulas, ending in `trueAtom`. -/
def allOf (ps : List (Formula top m)) : Formula top m := ps.foldr .and trueAtom

/-- An equation, written as two inequalities. -/
def equation (s t : Term top m) : Formula top m := .and (.le s t) (.le t s)

/-- The alignment block
`y ≤ f(z, d) ∧ d ≤ f(z, d) ∧ d ≤ g ∧ f(⊥, y) ≤ p ∧ f(⊥, p) ≤ p ∧ p ≤ g`.
For `z` the full tree and top-free values, `g` contains every address of `y` with leading
ones removed or added (`AlignBlock.mem`). Hence a tooth of `y` and a stub outside `g` have
the same spine index (`AlignBlock.index_eq`). -/
def alignBlock (z y g d p : Term top m) : Formula top m :=
  .and (.le y (.f z d)) (.and (.le d (.f z d)) (.and (.le d g)
    (.and (.le (.f .bot y) p) (.and (.le (.f .bot p) p) (.le p g)))))

/-- The comparison block with offset `δ`. For `δ = 0` it is `y ≤ g`; otherwise
`y ≤ k ∧ k ≤ f(k₀, k) ∧ k₀ ≤ popContext z δ kd ∧ f(kd, ⊥) ≤ kp ∧ f(⊥, kp) ≤ kp ∧ kp ≤ g`.
For `z` the full tree and top-free values, whenever `y` contains the tooth address
`1ʲ 0 0^(δ + x)`, `g` contains `1ʲ 0 0ˣ` (`PopBlock.mem`): teeth are shortened by `δ`. -/
def popBlock (z : Term top m) : ℕ → (y g k k₀ kd kp : Term top m) → Formula top m
  | 0, y, g, _, _, _, _ => .le y g
  | δ + 1, y, g, k, k₀, kd, kp =>
    .and (.le y k) (.and (.le k (.f k₀ k)) (.and (.le k₀ (Term.popContext z (δ + 1) kd))
      (.and (.le (.f kd .bot) kp) (.and (.le (.f .bot kp) kp) (.le kp g)))))

/-! ## Clauses -/

section Clauses
variable (x : Existentials (Term top m)) (v : Universals (Term top m))

/-- After a step from state `q`, counter `c` is at most its previous value plus `1 - δ`: if
the tooth at step `j + 1` reaches depth `x₂`, the tooth at step `j` reaches every depth below
`x₂ + δ`. With `trunc` this is required only for `x₂ ≥ 1`. -/
def upperBoundClause (δ : ℕ) (trunc : Bool) (q : ℕ) (c : Fin 2) : Formula top m :=
  Formula.imp
    (.and (.le v.y₁ x.combUniverse) (.and (.le (x.counter c) v.g₁) (.and (.le x.rightRay v.g₁)
      (.and (.le (.f .bot v.y₂) (x.counter c))
      (.and (popBlock x.full δ v.y₁ v.g₂ v.k v.k₀ v.kd v.kp)
      (.and (.le (if trunc then x.stubComb else x.rightRay) v.g₂)
      (.and (.le (Term.pack q v.y₃) x.states)
      (.and (alignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁) (alignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂)))))))))
    (.or (.le v.y₁ v.g₁) (.or (.le v.y₂ v.g₂) (.le v.y₃ v.g₃)))

/-- After a step from state `q`, counter `c` is at least its previous value plus `δ - 1`: if
the tooth at step `j` reaches depth `x₁`, the tooth at step `j + 1` reaches every depth below
`x₁ + δ`. -/
def lowerBoundClause (δ q : ℕ) (c : Fin 2) : Formula top m :=
  Formula.imp
    (.and (.le v.y₁ (x.counter c)) (.and (popBlock x.full δ v.y₂ v.g₁ v.k v.k₀ v.kd v.kp)
      (.and (.le x.rightRay v.g₁) (.and (.le v.y₂ x.combUniverse)
      (.and (.le (x.counter c) (.f x.full v.g₂)) (.and (.le x.rightRay v.g₂)
      (.and (.le (Term.pack q v.y₃) x.states)
      (.and (alignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁) (alignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂)))))))))
    (.or (.le v.y₁ v.g₁) (.or (.le v.y₂ v.g₂) (.le v.y₃ v.g₃)))

/-- A step from state `q` reaches state `r`. -/
def transitionClause (q r : ℕ) : Formula top m :=
  Formula.imp
    (.and (.le (Term.pack q v.y₁) x.states)
      (.and (.le x.states (Term.stateContext x.full r v.g₁)) (.le x.rightRay v.g₁)))
    (.le v.y₁ v.g₁)

/-- After a step from state `q`, counter `c` has a tooth at the next step. -/
def nextToothClause (q : ℕ) (c : Fin 2) : Formula top m :=
  Formula.imp
    (.and (.le (Term.pack q v.y₁) x.states)
      (.and (.le (x.counter c) (.f x.full v.g₁)) (.le x.rightRay v.g₁)))
    (.le v.y₁ v.g₁)

/-- No step is both in state `q` and in the halting state `n`. -/
def haltUniqueClause (n q : ℕ) : Formula top m :=
  Formula.imp (.and (.le (Term.pack q v.y₁) x.states) (.le (Term.pack n v.y₁) x.states))
    (.le v.y₁ x.rightRay)

/-- A step from state `q` with counter `c` zero reaches state `r`. -/
def zeroTestClause (q r : ℕ) (c : Fin 2) : Formula top m :=
  Formula.imp
    (.and (.le v.y₁ x.shortCombs) (.and (.le (x.counter c) v.g₁) (.and (.le x.stubComb v.g₁)
      (.and (.le (Term.pack q v.y₃) x.states)
      (.and (.le x.states (Term.stateContext x.full r v.g₃))
        (alignBlock x.full v.y₁ v.g₃ v.d₁ v.p₁))))))
    (.or (.le v.y₁ v.g₁) (.le v.y₃ v.g₃))

/-- A step from state `q` with counter `c` positive reaches state `r`. -/
def positiveTestClause (q r : ℕ) (c : Fin 2) : Formula top m :=
  Formula.imp
    (.and (.le v.y₂ (x.counter c)) (.and (.le v.y₂ x.combUniverse)
      (.and (.le (Term.pack q v.y₃) x.states)
      (.and (.le x.states (Term.stateContext x.full r v.g₃))
        (alignBlock x.full v.y₂ v.g₃ v.d₂ v.p₂)))))
    (.or (.le v.y₂ x.stubComb) (.le v.y₃ v.g₃))

/-- The clauses for instruction `q` of a program with `n` instructions. -/
def instructionClauses (n q : ℕ) : Instr → Formula top m
  | .inc c r =>
    .and (haltUniqueClause x v n q) (.and (transitionClause x v q (min r n))
    (.and (upperBoundClause x v 0 false q c) (.and (lowerBoundClause x v 2 q c)
    (.and (upperBoundClause x v 1 false q (otherCounter c))
      (lowerBoundClause x v 1 q (otherCounter c))))))
  | .jzdec c z p =>
    .and (haltUniqueClause x v n q) (.and (zeroTestClause x v q (min z n) c)
    (.and (positiveTestClause x v q (min p n) c) (.and (upperBoundClause x v 2 true q c)
    (.and (lowerBoundClause x v 0 q c) (.and (nextToothClause x v q c)
    (.and (upperBoundClause x v 1 false q (otherCounter c))
      (lowerBoundClause x v 1 q (otherCounter c))))))))

/-- The clauses of all instructions of a program. -/
def programClauses (P : Program) : Formula top m :=
  allOf ((List.range P.length).map fun q =>
    (P[q]?).elim trueAtom (instructionClauses x v P.length q))

/-- The guards: no universal value contains top. -/
def guards : Formula top m :=
  .and (.le v.y₁ x.full) (.and (.le v.y₂ x.full) (.and (.le v.y₃ x.full)
    (.and (.le v.g₁ x.full) (.and (.le v.g₂ x.full) (.and (.le v.g₃ x.full)
    (.and (.le v.k x.full) (.and (.le v.k₀ x.full) (.and (.le v.kd x.full)
    (.and (.le v.kp x.full) (.and (.le v.d₁ x.full) (.and (.le v.p₁ x.full)
    (.and (.le v.d₂ x.full) (.le v.p₂ x.full)))))))))))))

end Clauses

/-- The root conditions for a program with `n` instructions: the six helper equations,
the guards of the counters and the state tree, both counters zero and state zero at
step zero, and an occurrence of the halting state `n`. -/
def rootConditions (x : Existentials (Term top m)) (n : ℕ) : Formula top m :=
  .and (equation x.full (.f x.full x.full))
  (.and (equation x.rightRay (.f .bot x.rightRay))
  (.and (equation x.stubComb (.f Term.e x.stubComb))
  (.and (equation x.leftRay (.f x.leftRay .bot))
  (.and (equation x.combUniverse (.f x.leftRay x.combUniverse))
  (.and (equation x.shortCombs (.f (.f Term.e .bot) x.shortCombs))
  (.and (.le (x.counter 0) x.full) (.and (.le (x.counter 1) x.full) (.and (.le x.states x.full)
  (.and (.le (.f Term.e .bot) (x.counter 0)) (.and (.le (x.counter 0) (.f Term.e x.full))
  (.and (.le (.f Term.e .bot) (x.counter 1)) (.and (.le (x.counter 1) (.f Term.e x.full))
  (.and (.le (Term.pack 0 (.f Term.e .bot)) x.states)
    (.neg (.le x.states (Term.haltContext x.full x.rightRay n))))))))))))))))

/-- The quantifier-free matrix: the root conditions, and the clauses of every instruction
under the guards. -/
def matrix (x : Existentials (Term top m)) (v : Universals (Term top m)) (P : Program) :
    Formula top m :=
  .and (rootConditions x P.length) (.imp (guards x v) (programClauses x v P))

/-! ## Syntactic class of the matrix -/

theorem isMatrix_allOf {ps : List (Formula top m)} (h : ∀ φ ∈ ps, φ.isMatrix = true) :
    (allOf ps).isMatrix = true := by
  induction ps with
  | nil => rfl
  | cons φ ps ih =>
    simp only [allOf, List.foldr_cons, Formula.isMatrix, Bool.and_eq_true]
    exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

theorem isLeOnly_allOf {ps : List (Formula top m)} (h : ∀ φ ∈ ps, φ.IsLeOnly) :
    (allOf ps).IsLeOnly := by
  induction ps with
  | nil => trivial
  | cons φ ps ih =>
    exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

section Syntax
variable (x : Existentials (Term top m)) (v : Universals (Term top m))

theorem isMatrix_popBlock (z : Term top m) (δ : ℕ) (y g k k₀ kd kp : Term top m) :
    (popBlock z δ y g k k₀ kd kp).isMatrix = true := by
  cases δ <;> rfl

theorem isLeOnly_popBlock (z : Term top m) (δ : ℕ) (y g k k₀ kd kp : Term top m) :
    (popBlock z δ y g k k₀ kd kp).IsLeOnly := by
  cases δ <;> simp [popBlock, Formula.IsLeOnly]

theorem isMatrix_instructionClauses (n q : ℕ) (i : Instr) :
    (instructionClauses x v n q i).isMatrix = true := by
  cases i <;>
    simp [instructionClauses, upperBoundClause, lowerBoundClause, transitionClause,
      nextToothClause, haltUniqueClause, zeroTestClause, positiveTestClause, alignBlock,
      isMatrix_popBlock, Formula.imp, Formula.isMatrix]

theorem isLeOnly_instructionClauses (n q : ℕ) (i : Instr) :
    (instructionClauses x v n q i).IsLeOnly := by
  cases i <;>
    simp [instructionClauses, upperBoundClause, lowerBoundClause, transitionClause,
      nextToothClause, haltUniqueClause, zeroTestClause, positiveTestClause, alignBlock,
      isLeOnly_popBlock, Formula.imp, Formula.IsLeOnly]

theorem isMatrix_matrix (P : Program) : (matrix x v P).isMatrix = true := by
  have hp : (programClauses x v P).isMatrix = true := by
    apply isMatrix_allOf
    intro φ hφ
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
    cases P[q]? with
    | none => rfl
    | some i => exact isMatrix_instructionClauses x v _ q i
  simp [matrix, rootConditions, guards, equation, Formula.imp, Formula.isMatrix, hp]

theorem isLeOnly_matrix (P : Program) : (matrix x v P).IsLeOnly := by
  have hp : (programClauses x v P).IsLeOnly := by
    apply isLeOnly_allOf
    intro φ hφ
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
    cases P[q]? with
    | none => trivial
    | some i => exact isLeOnly_instructionClauses x v _ q i
  simp [matrix, rootConditions, guards, equation, Formula.imp, Formula.IsLeOnly, hp]

end Syntax

end Sentence

open Sentence

/-- The existential variables of the sentence, as de Bruijn variables. -/
def Sentence.existentialVars (top : Bool) : Existentials (Term top (0 + 9 + 14)) :=
  Existentials.ofFn fun i => .var (i.addNat 14)

/-- The universal variables of the sentence, as de Bruijn variables. -/
def Sentence.universalVars (top : Bool) : Universals (Term top (0 + 9 + 14)) :=
  Universals.ofFn fun i => .var (i.castAdd 9)

/-- The Σ₂ sentence with prefix `∃⁹ ∀¹⁴` expressing that a two-counter program halts. -/
def machineSentence (top : Bool) (P : Program) : Formula top 0 :=
  exs 9 (alls 14 (matrix (existentialVars top) (universalVars top) P))

theorem machineSentence_quantifiers (top : Bool) (P : Program) :
    (machineSentence top P).quantifiers =
      some (List.replicate 9 true ++ List.replicate 14 false) := by
  simp [machineSentence, quantifiers_exs, quantifiers_alls,
    (Formula.quantifiers_eq_nil_iff _).mpr (isMatrix_matrix _ _ P)]

/-- The machine sentence is syntactically Σ₂. -/
theorem machineSentence_isSigma (top : Bool) (P : Program) : (machineSentence top P).IsSigma 2 := by
  rw [Formula.IsSigma, machineSentence_quantifiers]
  simp [List.replicate_succ, Formula.blocks]

/-- The machine sentence uses inequality as its only kind of atom. -/
theorem machineSentence_isLeOnly (top : Bool) (P : Program) : (machineSentence top P).IsLeOnly := by
  simp only [machineSentence, isLeOnly_exs, isLeOnly_alls]
  exact isLeOnly_matrix _ _ P

end UndeciSigma2
