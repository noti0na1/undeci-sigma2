import UndeciSigma2.Sentence.Definition
import UndeciSigma2.Clock.Machine

/-! # The clock sentence

For a two-counter program `P` with `n` instructions and `m = 6 + 2n` labels, the clock
sentence has the prefix `∃²¹ ∀¹³` and a quantifier-free Boolean matrix of inequality atoms.
The part about the existential variables alone has fifty positive atoms and one negated atom;
the remaining conjuncts are implications, one per clause. The sentence contains neither top
nor an equation, so the same sentence serves both signatures.

The intended values of the existential variables describe a balanced exact run
`λ₀, …, λ_E` of the label machine of `P` by combs read to the right: the comb with tooth
lengths `t(s)` has the addresses `1ⁱ` for `i ≤ E` and `1^s 0 1^x` for `x ≤ t(s)`.

* The clock `D` has the tooth `s` at every stamp `s ≤ E`.
* The label tree `L` has at `1ˡ 0` the component of label `l`: the part of the clock at the
  stamps with label `l`.
* The counter combs `C i` have the tooth `s + cᵢ(s)`; the class combs `C⁺ i` and `C⁰ i` keep
  the teeth at the stamps whose label changes counter `i` by `+1` and by `0`.
* The unwinding comb has the tooth `u(s)`, the number of unwinding labels up to `s`; its part
  at the unwinding stamps is a second variable.
* The chain `B = 1^E 0 1^E 0`, its head `1^E 0 1^E` and its loop fix the last stamp; the ray
  `N = 1^N` and its loop compare the number of build-up labels with the number of unwinding
  labels.
* The ray, the comb bound and the sink are the guards: their inequalities
  `R ≤ f(⊥, R)`, `K ≤ f(R, K)`, `K₂ ≤ f(K, K₂)`, with the eighteen other variables below the
  sink, force every witness to be top-free with addresses of at most two zeros.

The thirteen universal variables are three seeds `y₁ y₂ y₃`, three bounds `g₁ g₂ g₃`, the
shape auxiliaries `k k₀`, the window auxiliaries `d₁ d₂ e₂ e₃`, and the sink `z`.

The clauses are described by data, `ClockClause`, with one formula per description:

* a one-seed clause states `seeds ∧ bounds ∧ shape → y₁ ≤ g₁`, where the seed atoms bound
  `y₁` by a witness, the bound atoms bound a witness by `g₁` (with the sink `z` in the
  remaining positions of a context), and the shape atoms restrict `y₁` to spine words and
  stubs, or to words with at most one zero;
* a window clause with source `X` and base `E` bounds the number of new tooth words of the
  right child of `X` over `E` at each stamp by one, and a triple window clause by two;
* the chain clause states that any two seeds below the chain are comparable;
* the unwinding bound states that the ray `N` lies in the tails of the unwinding comb.
-/

namespace UndeciSigma2

/-! ## Contexts on terms -/

namespace Term
variable {top : Bool} {n : ℕ}

/-- `select k a t = f(a 0, f(a 1, … f(a (k - 1), t)))`: the term `a l` sits at `1ˡ 0` for
`l < k` and `t` sits at `1ᵏ`. -/
def select (k : ℕ) (a : ℕ → Term top n) (t : Term top n) : Term top n :=
  (List.range k).foldr (fun l acc => .f (a l) acc) t

/-- `g` at `1ˡ 0` for the selected `l < k`, and `z` at the other `1ˡ 0` and at `1ᵏ`. Below a
label tree, it bounds the selected components by `g`. -/
def componentContext (k : ℕ) (z : Term top n) (sel : ℕ → Bool) (g : Term top n) :
    Term top n :=
  select k (fun l => if sel l then g else z) z

/-- `f(z, g)` at `1ˡ 0` for the selected `l < k`, and `z` at the other `1ˡ 0` and at `1ᵏ`.
Below a label tree, it bounds the right children of the selected components by `g`. -/
def tailContext (k : ℕ) (z : Term top n) (sel : ℕ → Bool) (g : Term top n) : Term top n :=
  select k (fun l => if sel l then .f z g else z) z

example (a : ℕ → Term top n) (t : Term top n) : select 2 a t = .f (a 0) (.f (a 1) t) := rfl

example (z g : Term top n) :
    componentContext 3 z (fun l => l == 1) g = .f z (.f g (.f z z)) := rfl

example (z g : Term top n) :
    tailContext 2 z (fun l => l == 0) g = .f (.f z g) (.f z z) := rfl

end Term

/-! ## Variables -/

/-- The twenty-one existential variables of the clock sentence. -/
structure ClockExistentials (α : Type*) where
  /-- The clock `D`: its tooth at stamp `s` has length `s`. -/
  clock : α
  /-- The chain `B`: the word `1^E 0 1^E 0` and its prefixes. -/
  chain : α
  /-- The head of the chain: the word `1^E 0 1^E` and its prefixes. -/
  chainHead : α
  /-- The loop of the chain, closed under removing leading ones. -/
  chainLoop : α
  /-- The label tree `L`: its subtree at `1ˡ 0` is the component of label `l`. -/
  labels : α
  /-- The counter combs; counter `2` is the reservoir. -/
  counter : Fin 3 → α
  /-- The class combs of the steps that increase a counter. -/
  plusClass : Fin 3 → α
  /-- The class combs of the steps that keep a counter. -/
  zeroClass : Fin 3 → α
  /-- The unwinding comb: its tooth at `s` is the number of unwinding labels up to `s`. -/
  unwind : α
  /-- The part of the unwinding comb at the unwinding stamps. -/
  unwindPart : α
  /-- The ray `N` measuring the number of build-up labels. -/
  buildRay : α
  /-- The loop below which the component of the build-up label lies. -/
  buildLoop : α
  /-- The guard whose addresses are words of ones. -/
  ray : α
  /-- The guard whose addresses have at most one zero. -/
  combBound : α
  /-- The guard whose addresses have at most two zeros; it bounds the eighteen other
  variables. -/
  sink : α

/-- The thirteen universal variables of the clock sentence: the seeds `y₁ y₂ y₃` and the
bounds `g₁ g₂ g₃` compared in the conclusions `yᵢ ≤ gᵢ`, the shape auxiliaries `k k₀`, the
window auxiliaries `d₁ d₂ e₂ e₃`, and the sink `z`. -/
structure ClockUniversals (α : Type*) where
  y₁ : α
  y₂ : α
  y₃ : α
  g₁ : α
  g₂ : α
  g₃ : α
  k : α
  k₀ : α
  d₁ : α
  d₂ : α
  e₂ : α
  e₃ : α
  z : α

namespace ClockExistentials
variable {α β : Type*}

/-- Apply a function to every variable. -/
def map (g : α → β) (x : ClockExistentials α) : ClockExistentials β :=
  ⟨g x.clock, g x.chain, g x.chainHead, g x.chainLoop, g x.labels, g ∘ x.counter,
    g ∘ x.plusClass, g ∘ x.zeroClass, g x.unwind, g x.unwindPart, g x.buildRay, g x.buildLoop,
    g x.ray, g x.combBound, g x.sink⟩

/-- Read the variables from a vector, in the order `D, B, B₀, k_B, L, C 0, C 1, C 2, C⁺ 0,
C⁺ 1, C⁺ 2, C⁰ 0, C⁰ 1, C⁰ 2`, unwinding comb, its part, `N`, `k_N`, ray, comb bound, sink. -/
def ofFn (x : Fin 21 → α) : ClockExistentials α :=
  ⟨x 0, x 1, x 2, x 3, x 4, ![x 5, x 6, x 7], ![x 8, x 9, x 10], ![x 11, x 12, x 13], x 14, x 15,
    x 16, x 17, x 18, x 19, x 20⟩

/-- The variables as a vector, inverse to `ofFn`. -/
def toFn (x : ClockExistentials α) : Fin 21 → α :=
  ![x.clock, x.chain, x.chainHead, x.chainLoop, x.labels, x.counter 0, x.counter 1, x.counter 2,
    x.plusClass 0, x.plusClass 1, x.plusClass 2, x.zeroClass 0, x.zeroClass 1, x.zeroClass 2,
    x.unwind, x.unwindPart, x.buildRay, x.buildLoop, x.ray, x.combBound, x.sink]

/-- The eighteen variables bounded by the sink: all but the three guards. -/
def guarded (x : ClockExistentials α) : List α :=
  [x.clock, x.chain, x.chainHead, x.chainLoop, x.labels, x.counter 0, x.counter 1, x.counter 2,
    x.plusClass 0, x.plusClass 1, x.plusClass 2, x.zeroClass 0, x.zeroClass 1, x.zeroClass 2,
    x.unwind, x.unwindPart, x.buildRay, x.buildLoop]

/-- All twenty-one variables. -/
def toList (x : ClockExistentials α) : List α := x.guarded ++ [x.ray, x.combBound, x.sink]

/-- Every variable satisfies `p`. -/
def Forall (p : α → Prop) (x : ClockExistentials α) : Prop := ∀ t ∈ x.toList, p t

@[simp] theorem toFn_ofFn (x : Fin 21 → α) : (ofFn x).toFn = x := by
  funext i
  fin_cases i <;> rfl

theorem toList_length (x : ClockExistentials α) : x.toList.length = 21 := rfl

theorem guarded_map (g : α → β) (x : ClockExistentials α) :
    (x.map g).guarded = x.guarded.map g := rfl

theorem toList_map (g : α → β) (x : ClockExistentials α) :
    (x.map g).toList = x.toList.map g := rfl

end ClockExistentials

namespace ClockUniversals
variable {α β : Type*}

/-- Apply a function to every variable. -/
def map (g : α → β) (v : ClockUniversals α) : ClockUniversals β :=
  ⟨g v.y₁, g v.y₂, g v.y₃, g v.g₁, g v.g₂, g v.g₃, g v.k, g v.k₀, g v.d₁, g v.d₂, g v.e₂,
    g v.e₃, g v.z⟩

/-- Read the variables from a vector, in the order `y₁ y₂ y₃ g₁ g₂ g₃ k k₀ d₁ d₂ e₂ e₃ z`. -/
def ofFn (y : Fin 13 → α) : ClockUniversals α :=
  ⟨y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8, y 9, y 10, y 11, y 12⟩

/-- The variables as a vector, inverse to `ofFn`. -/
def toFn (v : ClockUniversals α) : Fin 13 → α :=
  ![v.y₁, v.y₂, v.y₃, v.g₁, v.g₂, v.g₃, v.k, v.k₀, v.d₁, v.d₂, v.e₂, v.e₃, v.z]

/-- Every variable satisfies `p`. -/
def Forall (p : α → Prop) (v : ClockUniversals α) : Prop := ∀ i, p (v.toFn i)

@[simp] theorem ofFn_toFn (v : ClockUniversals α) : ofFn v.toFn = v := rfl

@[simp] theorem toFn_ofFn (y : Fin 13 → α) : (ofFn y).toFn = y := by
  funext i
  fin_cases i <;> rfl

end ClockUniversals

/-! ## Descriptions of the clauses -/

namespace Clock

/-- An atom of a one-seed clause bounding the seed `y` by a witness. -/
inductive SeedAtom (α : Type*) where
  /-- `y ≤ X`. -/
  | le (X : α)
  /-- `f(⊥, y) ≤ X`: the seed lies below the right child of `X`. -/
  | rightLe (X : α)
  /-- `pack l y ≤ L`: the seed lies below the component of label `l` of `L`. -/
  | component (L : α) (l : ℕ)
  /-- `pack l (f(⊥, y)) ≤ L`: the seed lies below the right child of the component of `l`. -/
  | componentRight (L : α) (l : ℕ)

/-- An atom of a one-seed clause bounding a witness by the bound `g`; the sink `z` fills the
remaining positions of the contexts. -/
inductive BoundAtom (α : Type*) where
  /-- `X ≤ g`. -/
  | le (X : α)
  /-- `X ≤ f(z, g)`: the right child of `X` lies below `g`. -/
  | rightLe (X : α)
  /-- `L ≤ componentContext m z sel g`: the selected components of `L` lie below `g`. -/
  | components (L : α) (m : ℕ) (sel : ℕ → Bool)
  /-- `L ≤ tailContext m z sel g`: the right children of the selected components lie below
  `g`. -/
  | tails (L : α) (m : ℕ) (sel : ℕ → Bool)

/-- The restriction of the seed of a one-seed clause. -/
inductive SeedShape where
  /-- No restriction. -/
  | any
  /-- `y ≤ k ∧ k ≤ f(e, k)`: the seed consists of spine words and stubs. -/
  | spineOrStub
  /-- `y ≤ k ∧ k ≤ f(k₀, k) ∧ k₀ ≤ f(⊥, k₀)`: the seed consists of words with at most one
  zero. -/
  | atMostOneZero

namespace SeedAtom
variable {α β : Type*}

/-- Apply a function to the witnesses. -/
def map (g : α → β) : SeedAtom α → SeedAtom β
  | .le X => .le (g X)
  | .rightLe X => .rightLe (g X)
  | .component L l => .component (g L) l
  | .componentRight L l => .componentRight (g L) l

/-- The witness of the atom. -/
def witness : SeedAtom α → α
  | .le X | .rightLe X | .component X _ | .componentRight X _ => X

end SeedAtom

namespace BoundAtom
variable {α β : Type*}

/-- Apply a function to the witnesses. -/
def map (g : α → β) : BoundAtom α → BoundAtom β
  | .le X => .le (g X)
  | .rightLe X => .rightLe (g X)
  | .components L m sel => .components (g L) m sel
  | .tails L m sel => .tails (g L) m sel

/-- The witness of the atom. -/
def witness : BoundAtom α → α
  | .le X | .rightLe X | .components X _ _ | .tails X _ _ => X

end BoundAtom

end Clock

open Clock

/-- The description of a clause of the clock sentence, with the witnesses it mentions. -/
inductive ClockClause (α : Type*) where
  /-- `seeds ∧ bounds ∧ shape → y₁ ≤ g₁`. -/
  | oneSeed (seeds : List (SeedAtom α)) (bounds : List (BoundAtom α)) (shape : SeedShape)
  /-- The window clause with source `X` and base `E`: at most one new tooth word per stamp. -/
  | window (source base : α)
  /-- The triple window clause with source `X` and base `E`: at most two new tooth words per
  stamp. -/
  | window3 (source base : α)
  /-- Any two seeds below the chain `B` are comparable. -/
  | chain (B : α)
  /-- The ray `N` lies in the tails of the comb `U`. -/
  | unwindBound (N U : α)

namespace ClockClause
variable {α β : Type*}

/-- Apply a function to the witnesses. -/
def map (g : α → β) : ClockClause α → ClockClause β
  | .oneSeed seeds bounds sh =>
    .oneSeed (seeds.map (SeedAtom.map g)) (bounds.map (BoundAtom.map g)) sh
  | .window X E => .window (g X) (g E)
  | .window3 X E => .window3 (g X) (g E)
  | .chain B => .chain (g B)
  | .unwindBound N U => .unwindBound (g N) (g U)

/-- The witnesses mentioned by the clause. -/
def witnesses : ClockClause α → List α
  | .oneSeed seeds bounds _ => seeds.map SeedAtom.witness ++ bounds.map BoundAtom.witness
  | .window X E | .window3 X E => [X, E]
  | .chain B => [B]
  | .unwindBound N U => [N, U]

/-- One-seed clauses have at least one seed atom. -/
def WellFormed : ClockClause α → Prop
  | .oneSeed seeds _ _ => seeds ≠ []
  | _ => True

end ClockClause

/-! ## Formulas -/

namespace Clock

variable {top : Bool} {n : ℕ}

/-- The conjunction of a nonempty list of formulas, `φ₁ ∧ (φ₂ ∧ … φₖ)`. The empty list gives
`trueAtom`. -/
def conj : List (Formula top n) → Formula top n
  | [] => Sentence.trueAtom
  | [φ] => φ
  | φ :: ψ :: ψs => .and φ (conj (ψ :: ψs))

/-- The formula of a seed atom with seed `y`. -/
def SeedAtom.formula (y : Term top n) : SeedAtom (Term top n) → Formula top n
  | .le X => .le y X
  | .rightLe X => .le (.f .bot y) X
  | .component L l => .le (Term.pack l y) L
  | .componentRight L l => .le (Term.pack l (.f .bot y)) L

/-- The formula of a bound atom with sink `z` and bound `g`. -/
def BoundAtom.formula (z g : Term top n) : BoundAtom (Term top n) → Formula top n
  | .le X => .le X g
  | .rightLe X => .le X (.f z g)
  | .components L m sel => .le L (Term.componentContext m z sel g)
  | .tails L m sel => .le L (Term.tailContext m z sel g)

/-- The shape atoms for the seed `y` with auxiliaries `k` and `k₀`. -/
def SeedShape.formulas (y k k₀ : Term top n) : SeedShape → List (Formula top n)
  | .any => []
  | .spineOrStub => [.le y k, .le k (.f Term.e k)]
  | .atMostOneZero => [.le y k, .le k (.f k₀ k), .le k₀ (.f .bot k₀)]

/-- The block `y ≤ d ∧ d ≤ f(z, d) ∧ ⋀_{g ∈ gs} d ≤ g`: every `g ∈ gs` contains the words
obtained from the addresses of `y` by removing leading ones. -/
def dropBlock (z y d : Term top n) (gs : List (Term top n)) : List (Formula top n) :=
  [.le y d, .le d (.f z d)] ++ gs.map fun g => .le d g

/-- The block `y ≤ f(z, e) ∧ e ≤ f(z, e) ∧ ⋀_{g ∈ gs} e ≤ g`: every `g ∈ gs` contains the
words obtained from the addresses of `y` by removing at least one leading one. -/
def strictDropBlock (z y e : Term top n) (gs : List (Term top n)) : List (Formula top n) :=
  [.le y (.f z e), .le e (.f z e)] ++ gs.map fun g => .le e g

end Clock

namespace ClockClause

variable {top : Bool} {n : ℕ}

/-- The formula of a clause description, for the universal variables `v`. -/
def formula (v : ClockUniversals (Term top n)) : ClockClause (Term top n) → Formula top n
  | .oneSeed seeds bounds sh =>
    Formula.imp
      (conj (seeds.map (·.formula v.y₁) ++ bounds.map (·.formula v.z v.g₁) ++
        sh.formulas v.y₁ v.k v.k₀))
      (.le v.y₁ v.g₁)
  | .window X E =>
    Formula.imp
      (conj ([.le (.f .bot v.y₁) X, .le (.f .bot v.y₂) X, .le E v.g₁, .le E v.g₂] ++
        dropBlock v.z v.y₁ v.d₁ [v.g₂] ++ strictDropBlock v.z v.y₂ v.e₂ [v.g₁]))
      (.or (.le v.y₁ v.g₁) (.le v.y₂ v.g₂))
  | .window3 X E =>
    Formula.imp
      (conj ([.le (.f .bot v.y₁) X, .le (.f .bot v.y₂) X, .le (.f .bot v.y₃) X,
          .le E v.g₁, .le E v.g₂, .le E v.g₃] ++
        dropBlock v.z v.y₁ v.d₁ [v.g₂, v.g₃] ++ dropBlock v.z v.y₂ v.d₂ [v.g₃] ++
        strictDropBlock v.z v.y₂ v.e₂ [v.g₁] ++ strictDropBlock v.z v.y₃ v.e₃ [v.g₁, v.g₂]))
      (.or (.le v.y₁ v.g₁) (.or (.le v.y₂ v.g₂) (.le v.y₃ v.g₃)))
  | .chain B =>
    Formula.imp (.and (.le v.y₁ B) (.le v.y₂ B)) (.or (.le v.y₁ v.y₂) (.le v.y₂ v.y₁))
  | .unwindBound N U =>
    Formula.imp (.and (.le v.y₁ N) (.and (.le U v.k) (.le v.k (.f v.g₁ v.k)))) (.le v.y₁ v.g₁)

end ClockClause

/-! ## The clauses -/

namespace Clock

section Clauses

variable {α : Type*} (P : Program) (x : ClockExistentials α)

/-- Any two seeds below the chain are comparable. -/
def chainClause : ClockClause α := .chain x.chain

/-- The words of the chain with at most one zero lie in its head. -/
def chainHeadClause : ClockClause α := .oneSeed [.le x.chain] [.le x.chainHead] .atMostOneZero

/-- The tooth of the clock grows by at most one from each stamp to the next. -/
def clockClause : ClockClause α := .window x.clock x.clock

/-- The spine words and stubs of the right child of the clock are addresses of the clock. -/
def gapClause : ClockClause α := .oneSeed [.rightLe x.clock] [.le x.clock] .spineOrStub

/-- The component of the end label and the right child of the clock share only spine words. -/
def endLastClause : ClockClause α :=
  .oneSeed [.component x.labels endLabel, .rightLe x.clock] [.le x.ray] .any

/-- Every address of the clock lies in some component. -/
def coverClause : ClockClause α :=
  .oneSeed [.le x.clock] [.components x.labels (labelCount P) fun _ => true] .any

/-- The components of labels `l` and `l'` share only spine words. -/
def uniqueClause (l l' : ℕ) : ClockClause α :=
  .oneSeed [.component x.labels l, .component x.labels l'] [.le x.ray] .any

/-- A tooth word at stamp `s` of the component of label `l` reappears at stamp `s + 1` in the
component of a successor of `l`, that is, at stamp `s` in the right child of that component;
spine words are exempt. -/
def transitionClause (l : ℕ) : ClockClause α :=
  .oneSeed [.component x.labels l]
    [.le x.ray, .tails x.labels (labelCount P) (isSuccessor P l)] .any

/-- A tooth word of the right child of counter comb `i` lies in the counter comb or in the
right child of one of its two class combs. -/
def counterStepClause (i : Fin 3) : ClockClause α :=
  .oneSeed [.rightLe (x.counter i)]
    [.le (x.counter i), .rightLe (x.plusClass i), .rightLe (x.zeroClass i)] .any

/-- At most one tooth word of the right child of the keeping class comb of counter `i` is new
over the counter comb at each stamp. -/
def zeroWindowClause (i : Fin 3) : ClockClause α := .window (x.zeroClass i) (x.counter i)

/-- At most two tooth words of the right child of the increasing class comb of counter `i` are
new over the counter comb at each stamp. -/
def plusWindowClause (i : Fin 3) : ClockClause α := .window3 (x.plusClass i) (x.counter i)

/-- The stubs of the class comb `X` of counter `i` are at stamps whose label is not the start
label and changes counter `i` by `κ`. -/
def classLabelClause (i : Fin 3) (κ : ℤ) (X : α) : ClockClause α :=
  .oneSeed [.le X]
    [.le x.ray, .components x.labels (labelCount P)
      fun ν => decide (ν ≠ startLabel ∧ effect P ν i = κ)]
    .spineOrStub

/-- Before a step with label `μ` testing counter `c` for zero, the tooth of counter comb `c`
has the length of the tooth of the clock. -/
def zeroTestClause (μ : ℕ) (c : Fin 2) : ClockClause α :=
  .oneSeed [.le (x.counter (Fin.castSucc c)), .componentRight x.labels μ] [.le x.clock] .any

/-- A tooth word of the right child of the unwinding comb lies in the unwinding comb or in the
right child of its unwinding part. -/
def unwindStepClause : ClockClause α :=
  .oneSeed [.rightLe x.unwind] [.le x.unwind, .rightLe x.unwindPart] .any

/-- At most one tooth word of the right child of the unwinding part is new over the unwinding
comb at each stamp. -/
def unwindWindowClause : ClockClause α := .window x.unwindPart x.unwind

/-- The ray of build-up labels lies in the tails of the unwinding comb. -/
def unwindBoundClause : ClockClause α := .unwindBound x.buildRay x.unwind

/-- The uniqueness clauses for all pairs of labels `l < l' < m`. -/
def uniqueClauses : List (ClockClause α) :=
  (List.range (labelCount P)).flatMap fun l' => (List.range l').map fun l => uniqueClause x l l'

/-- The transition clauses for all labels `l < m` except the end label. -/
def transitionClauses : List (ClockClause α) :=
  ((List.range (labelCount P)).filter fun l => l != endLabel).map (transitionClause P x)

/-- The five clauses of each counter. -/
def counterClauses : List (ClockClause α) :=
  (List.finRange 3).flatMap fun i =>
    [counterStepClause x i, zeroWindowClause x i, plusWindowClause x i,
      classLabelClause P x i 1 (x.plusClass i), classLabelClause P x i 0 (x.zeroClass i)]

/-- The zero-test clauses for all labels `μ < m` that test a counter. -/
def zeroTestClauses : List (ClockClause α) :=
  (List.range (labelCount P)).filterMap fun μ => (zeroTest P μ).map (zeroTestClause x μ)

/-- All clauses of the clock sentence. -/
def clauses : List (ClockClause α) :=
  [chainClause x, chainHeadClause x, clockClause x, gapClause x, endLastClause x,
    coverClause P x] ++
  uniqueClauses P x ++ transitionClauses P x ++ counterClauses P x ++ zeroTestClauses P x ++
  [unwindStepClause x, unwindWindowClause x, unwindBoundClause x]

end Clauses

/-! ## The quantifier-free part -/

section QuantifierFree

variable {top : Bool} {n : ℕ} (x : ClockExistentials (Term top n))

/-- The guards: `R ≤ f(⊥, R)`, `K ≤ f(R, K)`, `K₂ ≤ f(K, K₂)` for the ray `R`, the comb bound
`K` and the sink `K₂`, and every other variable below the sink. -/
def guards : Formula top n :=
  conj ([.le x.ray (.f .bot x.ray), .le x.combBound (.f x.ray x.combBound),
    .le x.sink (.f x.combBound x.sink)] ++ x.guarded.map fun t => .le t x.sink)

/-- The root conditions for `m` labels: the shapes of the roots of the clock, the counter
combs and the unwinding comb, the start label at stamp `0`, the components inside the clock,
the end label at the stamp of the chain, the loops of the chain and of the build-up
component, and the chain outside its head. -/
def rootConditions (m : ℕ) : Formula top n :=
  conj ([.le (.f Term.e .bot) x.clock, .le x.clock (.f Term.e x.sink),
      .le (Term.pack startLabel (.f Term.e .bot)) x.labels,
      .le x.labels (Term.select m (fun _ => x.clock) .bot),
      .le x.labels
        (Term.select m (fun l => if l = startLabel then x.sink else .f .bot x.sink) .bot),
      .le x.chain x.chainLoop, .le x.chainLoop (.f x.chain x.chainLoop),
      .le (Term.pack endLabel x.chainHead) x.labels] ++
    (List.finRange 3).flatMap (fun i =>
      [.le (.f Term.e .bot) (x.counter i), .le (x.counter i) (.f Term.e x.sink),
        .le x.clock (x.counter i), .le (x.plusClass i) (.f .bot x.sink),
        .le (x.zeroClass i) (.f .bot x.sink)]) ++
    [.le (.f Term.e .bot) x.unwind, .le x.unwind (.f Term.e x.sink),
      .le x.unwindPart (.f .bot x.sink), .le (Term.pack unwindLabel x.unwindPart) x.labels,
      .le x.labels (.f x.sink (.f x.buildLoop x.sink)),
      .le x.buildLoop (.f x.buildRay x.buildLoop),
      .neg (.le x.chain x.chainHead)])

/-- The quantifier-free matrix for a program `P`: the guards, the root conditions, and every
clause for the universal variables `v`. -/
def matrix (P : Program) (v : ClockUniversals (Term top n)) : Formula top n :=
  .and (.and (guards x) (rootConditions x (labelCount P)))
    (Sentence.allOf ((clauses P x).map (·.formula v)))

end QuantifierFree

/-! ## Syntactic class -/

section Syntax

variable {top : Bool} {n : ℕ}

theorem isMatrix_conj {ps : List (Formula top n)} (h : ∀ φ ∈ ps, φ.isMatrix = true) :
    (conj ps).isMatrix = true := by
  induction ps with
  | nil => rfl
  | cons φ ps ih =>
    cases ps with
    | nil => exact h φ (by simp)
    | cons ψ ψs =>
      simp only [conj, Formula.isMatrix, Bool.and_eq_true]
      exact ⟨h φ (by simp), ih fun χ hχ => h χ (by simp [hχ])⟩

theorem isLeOnly_conj {ps : List (Formula top n)} (h : ∀ φ ∈ ps, φ.IsLeOnly) :
    (conj ps).IsLeOnly := by
  induction ps with
  | nil => trivial
  | cons φ ps ih =>
    cases ps with
    | nil => exact h φ (by simp)
    | cons ψ ψs => exact ⟨h φ (by simp), ih fun χ hχ => h χ (by simp [hχ])⟩

@[simp] theorem SeedAtom.isMatrix_formula (y : Term top n) (a : SeedAtom (Term top n)) :
    (a.formula y).isMatrix = true := by
  cases a <;> rfl

@[simp] theorem SeedAtom.isLeOnly_formula (y : Term top n) (a : SeedAtom (Term top n)) :
    (a.formula y).IsLeOnly := by
  cases a <;> trivial

@[simp] theorem BoundAtom.isMatrix_formula (z g : Term top n) (b : BoundAtom (Term top n)) :
    (b.formula z g).isMatrix = true := by
  cases b <;> rfl

@[simp] theorem BoundAtom.isLeOnly_formula (z g : Term top n) (b : BoundAtom (Term top n)) :
    (b.formula z g).IsLeOnly := by
  cases b <;> trivial

theorem SeedShape.isMatrix_formulas (y k k₀ : Term top n) (sh : SeedShape) :
    ∀ φ ∈ sh.formulas y k k₀, φ.isMatrix = true := by
  cases sh <;> simp [SeedShape.formulas, Formula.isMatrix]

theorem SeedShape.isLeOnly_formulas (y k k₀ : Term top n) (sh : SeedShape) :
    ∀ φ ∈ sh.formulas y k k₀, φ.IsLeOnly := by
  cases sh <;> simp [SeedShape.formulas, Formula.IsLeOnly]

theorem isMatrix_formula (v : ClockUniversals (Term top n)) (c : ClockClause (Term top n)) :
    (c.formula v).isMatrix = true := by
  cases c with
  | oneSeed seeds bounds sh =>
    simp only [ClockClause.formula, Formula.imp, Formula.isMatrix, Bool.and_true]
    apply isMatrix_conj
    simp only [List.mem_append, List.mem_map]
    rintro φ ((⟨a, -, rfl⟩ | ⟨b, -, rfl⟩) | hφ)
    · exact SeedAtom.isMatrix_formula _ a
    · exact BoundAtom.isMatrix_formula _ _ b
    · exact SeedShape.isMatrix_formulas _ _ _ sh φ hφ
  | window X E =>
    simp only [ClockClause.formula, Formula.imp, Formula.isMatrix, Bool.and_true]
    apply isMatrix_conj
    simp [dropBlock, strictDropBlock, Formula.isMatrix]
  | window3 X E =>
    simp only [ClockClause.formula, Formula.imp, Formula.isMatrix, Bool.and_true]
    apply isMatrix_conj
    simp [dropBlock, strictDropBlock, Formula.isMatrix]
  | chain B => rfl
  | unwindBound N U => rfl

theorem isLeOnly_formula (v : ClockUniversals (Term top n)) (c : ClockClause (Term top n)) :
    (c.formula v).IsLeOnly := by
  cases c with
  | oneSeed seeds bounds sh =>
    refine ⟨isLeOnly_conj ?_, trivial⟩
    simp only [List.mem_append, List.mem_map]
    rintro φ ((⟨a, -, rfl⟩ | ⟨b, -, rfl⟩) | hφ)
    · exact SeedAtom.isLeOnly_formula _ a
    · exact BoundAtom.isLeOnly_formula _ _ b
    · exact SeedShape.isLeOnly_formulas _ _ _ sh φ hφ
  | window X E =>
    refine ⟨isLeOnly_conj ?_, trivial, trivial⟩
    simp [dropBlock, strictDropBlock, Formula.IsLeOnly]
  | window3 X E =>
    refine ⟨isLeOnly_conj ?_, trivial, trivial, trivial⟩
    simp [dropBlock, strictDropBlock, Formula.IsLeOnly]
  | chain B => exact ⟨⟨trivial, trivial⟩, trivial, trivial⟩
  | unwindBound N U => exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩

/-- The matrix is quantifier-free. -/
theorem isMatrix_matrix (P : Program) (x : ClockExistentials (Term top n))
    (v : ClockUniversals (Term top n)) : (matrix x P v).isMatrix = true := by
  simp only [matrix, Formula.isMatrix, Bool.and_eq_true]
  refine ⟨⟨isMatrix_conj ?_, isMatrix_conj ?_⟩, Sentence.isMatrix_allOf ?_⟩
  · simp [ClockExistentials.guarded, Formula.isMatrix]
  · simp only [List.mem_append, List.mem_cons, List.mem_flatMap,
      List.mem_finRange, true_and, List.not_mem_nil, or_false]
    rintro φ (((h | h | h | h | h | h | h | h) | ⟨i, h | h | h | h | h⟩) |
      h | h | h | h | h | h | h) <;> subst h <;> rfl
  · simp only [List.mem_map]
    rintro φ ⟨c, -, rfl⟩
    exact isMatrix_formula v c

/-- The matrix uses inequality as its only kind of atom. -/
theorem isLeOnly_matrix (P : Program) (x : ClockExistentials (Term top n))
    (v : ClockUniversals (Term top n)) : (matrix x P v).IsLeOnly := by
  refine ⟨⟨isLeOnly_conj ?_, isLeOnly_conj ?_⟩, Sentence.isLeOnly_allOf ?_⟩
  · simp [ClockExistentials.guarded, Formula.IsLeOnly]
  · simp only [List.mem_append, List.mem_cons, List.mem_flatMap,
      List.mem_finRange, true_and, List.not_mem_nil, or_false]
    rintro φ (((h | h | h | h | h | h | h | h) | ⟨i, h | h | h | h | h⟩) |
      h | h | h | h | h | h | h) <;> subst h <;> trivial
  · simp only [List.mem_map]
    rintro φ ⟨c, -, rfl⟩
    exact isLeOnly_formula v c

end Syntax

/-- The existential variables of the sentence, as de Bruijn variables. -/
def existentialVars (top : Bool) : ClockExistentials (Term top (0 + 21 + 13)) :=
  ClockExistentials.ofFn fun i => .var (i.addNat 13)

/-- The universal variables of the sentence, as de Bruijn variables. -/
def universalVars (top : Bool) : ClockUniversals (Term top (0 + 21 + 13)) :=
  ClockUniversals.ofFn fun i => .var (i.castAdd 21)

end Clock

open Clock

/-- The Σ₂ sentence with prefix `∃²¹ ∀¹³` expressing that a two-counter program halts, in
every one of the six structures. -/
def clockSentence (top : Bool) (P : Program) : Formula top 0 :=
  Sentence.exs 21 (Sentence.alls 13 (matrix (existentialVars top) P (universalVars top)))

/-- The clock sentence has the prefix `∃²¹ ∀¹³`. -/
theorem clockSentence_quantifiers (top : Bool) (P : Program) :
    (clockSentence top P).quantifiers =
      some (List.replicate 21 true ++ List.replicate 13 false) := by
  simp [clockSentence, Sentence.quantifiers_exs, Sentence.quantifiers_alls,
    (Formula.quantifiers_eq_nil_iff _).mpr (isMatrix_matrix P _ _)]

/-- The clock sentence is syntactically Σ₂. -/
theorem clockSentence_isSigma (top : Bool) (P : Program) : (clockSentence top P).IsSigma 2 := by
  rw [Formula.IsSigma, clockSentence_quantifiers]
  simp [List.replicate_succ, Formula.blocks]

/-- The clock sentence uses inequality as its only kind of atom. -/
theorem clockSentence_isLeOnly (top : Bool) (P : Program) : (clockSentence top P).IsLeOnly := by
  simp only [clockSentence, Sentence.isLeOnly_exs, Sentence.isLeOnly_alls]
  exact isLeOnly_matrix P _ _

end UndeciSigma2
