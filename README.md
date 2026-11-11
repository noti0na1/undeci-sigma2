# Undecidability of the Σ₂ theory of non-structural subtyping

**The truth of first-order sentences with prefix ∃∀ over non-structural
subtype constraints is undecidable.** This holds for the signature with the
least type `⊥` and one binary covariant constructor `f`, with or without the
greatest type `⊤`, over finite trees, over regular trees and over arbitrary
trees: in all six structures. By duality, the ∀∃ (Π₂) fragment is undecidable
as well, and both remain undecidable when `≤` is the only predicate. The proof
is a many-one reduction from the halting problem of two-counter machines,
given in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

One sentence per program serves all six structures. A primitive recursive map
sends each program `P` to the *clock sentence* `clockSentence top P`: exactly
21 existential quantifiers followed by 13 universal quantifiers, a
quantifier-free Boolean matrix of inequality atoms, and no `⊤`. It holds in
each of the six structures exactly when `P` halts (`clockSentence_holds_iff`),
and its prenex negation, with prefix ∀²¹∃¹³, holds exactly when `P` does not
halt.

The undecidability of halting for two-counter machines started with both
counters zero is the classical theorem of Minsky [1, 2], carried over to the
machine model of this library by standard translations (see
[Two-counter machines](#two-counter-machines)). It is cited, not formalized: it
appears as the explicit hypothesis `hHalt` of the undecidability theorems, as
the undecidability of the Post correspondence problem does in
[undeci-sigma3](https://github.com/noti0na1/undeci-sigma3).

The library also contains a first, simpler reduction, the *machine sentence*
`machineSentence top P`. It fixes infinite helper trees by equations such as
`Z = f(Z, Z)`, so it is correct over regular and arbitrary trees only
(`machineSentence_holds_iff`, with the hypothesis `c ≠ .finite`). Over finite
trees these equations have no solution. The clock sentence avoids infinite
trees altogether, and this is what extends the result to finite trees.

The library contains two further results.

**The Σ₂ theories of arbitrary and of regular trees differ.** A Σ₂ sentence
whose only atoms are inequalities holds over arbitrary trees and fails over
regular trees, with or without `⊤` (`sigma2_theories_differ`). Boolean
combinations of Σ₁ sentences cannot tell the two classes apart
([deci-sigma1](https://github.com/noti0na1/deci-sigma1)), so Σ₂ is the lowest
level of the prefix hierarchy at which their theories differ.

**Recurrence reduces to Σ₂ truth over arbitrary trees.** A variant of the
machine sentence reduces the recurrence problem of nondeterministic two-counter
machines to the truth of Σ₂ sentences over arbitrary trees, with or without
`⊤` (`recurrenceSentence_holds_iff`). This reduction is stated for arbitrary
trees only. Recurrence is Σ¹₁-complete [8, 9]; this fact is cited, **not
formalized**. With it, Σ₂ truth over arbitrary trees is Σ¹₁-hard: neither
recursively enumerable nor co-recursively enumerable, and not arithmetical.

## The first-order theory of subtype constraints

### Types and the subtype order

A type is a possibly infinite binary tree. Every node is labeled `⊥`, `f`, or
`⊤`. A node labeled `f` has two children, and `⊥` and `⊤` are leaves. The
structures without `⊤` use only `⊥` and `f`. A tree is *finite* if it has
finitely many nodes. It is *regular* if it is the unfolding of a finite graph,
equivalently if it has finitely many distinct subtrees; Lean uses the first
definition. *Arbitrary* trees have no restriction. The Lean library defines all
six structures (three tree classes, with or without `⊤`), and the main theorems
hold in each of them.

The **non-structural** subtype order `s ≤ t` holds when the labels of `s` and
`t` satisfy `⊥ ≤ f ≤ ⊤` at every path where both trees have a node. Thus `⊥` is
below every type, `⊤` is above every type, and `f` is covariant in both
arguments: `f(s₁, s₂) ≤ f(t₁, t₂)` exactly when `s₁ ≤ t₁` and `s₂ ≤ t₂`. Trees
of different shapes can be compared, for example `⊥ ≤ f(⊥, ⊥)`.

A tree without `⊤` is determined by its *addresses*: the set of words over
`{0, 1}` (`0` for the left child, `1` for the right child) that lead to an
`f`-labeled node. This set is closed under prefixes, every prefix-closed set
arises, and on trees without `⊤` the order is inclusion of address sets
(`Tree.le_iff_constructorPaths_subset`). The whole proof works with this view.

### Formulas

Terms are built from variables, `⊥`, `f`, and `⊤` where available. The Lean
syntax has two primitive atoms, `s ≤ t` and `s = t`, and the constants true
and false. Formulas combine these with `¬`, `∧`, `∨`, `∃`, and `∀`. Quantifiers
range over the trees of the chosen structure.

A sentence is **Σₙ** if it is syntactically in prenex normal form with a
quantifier-free matrix and at most `n` alternating quantifier blocks, the
first existential and possibly empty. **Πₙ** uses the same convention with a
universal first block. This cumulative convention is implemented by
`Formula.IsSigma` and `Formula.IsPi`; it includes the lower levels. These
predicates test the syntax, not equivalence to a prenex sentence. The clock
sentence has the exact prefix ∃²¹∀¹³ (the machine sentence ∃⁹∀¹⁴), and both
use `≤` as their only atom (`Formula.IsLeOnly`), so the results also hold for
the language with `≤` as its only predicate and without Boolean constants
(`sigma2_undecidable_le` and `pi2_undecidable_le`).

### What is known

Several natural questions about type inference with subtyping are fragments of
this theory. Below, `φ` and `ψ` are finite conjunctions of atoms.

| Fragment | Question | Status |
|---|---|---|
| Satisfiability | does `φ` have a solution? | decidable in polynomial time [6, 7] |
| Entailment `φ ⊨ x ≤ y` | does every solution of `φ` satisfy `x ≤ y`? | decidable: [deci-nsse](https://github.com/noti0na1/deci-nsse) |
| Existential entailment `φ ⊨ ∃z̄. ψ` | does every solution of `φ` extend to a solution of `ψ`? | decidable: [deci-ensse](https://github.com/noti0na1/deci-ensse) |
| The Σ₁ theory: Boolean combinations of Σ₁ sentences | e.g. `φ ⊨ x₁ ≤ y₁ ∨ x₂ ≤ y₂` | decidable: [deci-sigma1](https://github.com/noti0na1/deci-sigma1) |
| **Σ₂ / Π₂** | | **undecidable in all six structures: this repository** |
| Σ₃ / Π₃ | | undecidable in all six structures: [undeci-sigma3](https://github.com/noti0na1/undeci-sigma3) |
| Full first-order theory | | undecidable [3] |

The decidability results hold in all six structures, and the three Lean
developments cited for them also treat constructors of other arities and
variances. Entailment has been studied by Niehren and Priesnitz [4, 5] and is
[Problem 16 of the TLCA open problem
list](https://tlca.di.unito.it/opltlca/opltlcasu23.html). Existential
entailment is a decidable fragment of Π₂: its sentences have the special form
`∀x̄. (φ → ∃z̄. ψ)` with conjunctions `φ` and `ψ`.

So in each of the six structures the boundary between decidable and
undecidable prefix classes lies exactly between Σ₁ and Σ₂: every Boolean
combination of Σ₁ sentences can be decided, while Σ₂ sentences and Π₂
sentences cannot.

Over arbitrary trees, Σ₂ truth is not merely undecidable. The recurrence
reduction described below makes it Σ¹₁-hard, so neither Σ₂ truth nor Σ₂
falsity is recursively enumerable; the Σ¹₁-completeness of recurrence that
this uses is cited, not formalized. Over finite and over regular trees, by
contrast, Σ₂ truth is recursively enumerable (also not part of this library).
Regular and arbitrary trees agree at Σ₁ and differ at Σ₂: in their theories,
as the separating sentence below shows, and, by these cited results, in
complexity.

## Two-counter machines

A program is a list of instructions acting on two counters `0` and `1`, which
hold natural numbers:

* `inc c r` increments counter `c` and goes to state `r`;
* `jzdec c z p` goes to state `z` if counter `c` is zero, and otherwise
  decrements counter `c` and goes to state `p`.

Every instruction names its successor states explicitly; there is no implicit
passage to the next instruction and no halt instruction. A program with `n`
instructions has the working states `0, …, n - 1`, and instruction `q` is
executed in state `q`. A state with no instruction, that is, any state at
least `n`, is halted, and a step from a halted configuration changes nothing.
The run starts in state `0` with both counters zero, and the program *halts*
if the run reaches a halted state.

```lean
inductive Instr where
  | inc (c : Fin 2) (next : ℕ)
  | jzdec (c : Fin 2) (ifZero ifPos : ℕ)

abbrev Program := List Instr

-- in namespace `Program`
def step (P : Program) (s : Config) : Config :=
  match P[s.state]? with
  | none => s
  | some i => i.exec s

def Halts (P : Program) : Prop :=
  ∃ t, P.length ≤ ((P.step)^[t] ⟨0, fun _ => 0⟩).state
```

Programs are encoded through an equivalence of `Instr` with a sum of products
(`Instr.equivSum`), which gives the `Primcodable` instance used by the
computability statements.

The hypothesis `hHalt : ¬ComputablePred Program.Halts` of the undecidability
theorems is the undecidability of halting for exactly this model. It follows
from Minsky's theorem [1, 2] by standard translations. Minsky's program
machines with two registers [2] run a numbered list of increment,
test-and-decrement and halt instructions and pass to the next instruction
unless a jump is taken; renumbering the instructions other than halt as
states, writing every successor explicitly and sending every transfer to a
halt instruction to a state without instruction gives a program of this model
that halts exactly when the machine does.
His simulation of a Turing machine on the empty tape starts from counter
values computable from the Turing machine, which a prefix of `inc`
instructions produces from zero, so halting from both counters zero is
undecidable.

## The reduction: the clock sentence

All witnesses of the clock sentence are free of `⊤`, so they are prefix-closed
sets of words, and the order between them is inclusion. Write `1ʲ` for the
word of `j` ones (`Word.ones`). Most Lean names of this development are in the
namespace `UndeciSigma2.Clock`; `clockSentence` and its theorems,
`ClockExistentials`, `ClockUniversals` and `ClockClause` are in `UndeciSigma2`.

### Stamps, combs and tooth words

Time is recorded along the right spine: the word `1ˢ` is the *stamp* `s`. The
*tooth words* at stamp `s` are `1ˢ 0 1ˣ` (`Clock.toothWord s x`), and the stub
`1ˢ 0` is the tooth word of depth `0`. A *comb* with last stamp `E` and tooth
lengths `t(0), …, t(E)` has the addresses `1ⁱ` for `i ≤ E` and `1ˢ 0 1ˣ` for
`s ≤ E` and `x ≤ t(s)`; a negative `t(s)` means no tooth at `s`. The right
child of a comb is the same comb one stamp earlier: it contains `1ˢ 0 1ˣ`
exactly when the comb contains `1ˢ⁺¹ 0 1ˣ`. So a clause compares the tooth at
stamp `s + 1` with the tooth at stamp `s` by comparing a tree with its right
child.

### The label machine

The sentence describes a run by a sequence of *labels* `λ₀, …, λ_E`, one per
stamp, and three counters: the two counters of the program and a *reservoir*,
counter `2` (`Clock/Machine.lean`). A program with `n` instructions has
`m = 6 + 2n` labels (`labelCount`):

| Label | Name | Effect on `(c₀, c₁, R)` | Zero test |
|---|---|---|---|
| `0` | start | none | |
| `1` | build-up | `R + 1` | |
| `2` | drain counter `0` | `c₀ - 1`, `R + 1` | |
| `3` | drain counter `1` | `c₁ - 1`, `R + 1` | |
| `4` | unwind | `R - 1` | |
| `5` | end | none | |
| `6 + 2q`, `P[q] = inc c r` | step of `q` | `c + 1`, `R - 1` | |
| `6 + 2q`, `P[q] = jzdec c z p` | zero branch of `q` | none | `c = 0` before the step |
| `7 + 2q`, `P[q] = jzdec c z p` | positive branch of `q` | `c - 1`, `R + 1` | |
| `7 + 2q`, `P[q] = inc c r` | unused | none | |

The successor relation `isSuccessor P l μ` follows the control flow of the
program: the start and build-up labels are followed by the build-up label or
by the labels of instruction `0`; the label of a step of instruction `q` is
followed by the labels of its target state (clipped to `n`), and a halted state
is entered through the drains, the unwind label or the end label; the drains
and the unwind label are followed only by the same or a later label among
`2, 3, 4, 5`; the end label has no successor. An *exact run* (`ExactRun`)
starts with the start label and all counters zero, ends with the end label,
follows the successor relation and the effects `effect P l i` in `ℕ`, and has
counter `c` zero before every zero branch testing `c` (`zeroTest`).

A program halts exactly when its label machine has an exact run
(`halts_iff_nonempty_exactRun`), and then it has a *balanced* one, with as
many unwind labels as build-up labels (`exists_balanced_exactRun`): `N`
build-up labels fill the reservoir with `N` units, the steps of the program
move units between the reservoir and the counters, the drains return the
counters to the reservoir, and `N` unwind labels empty it. Every label other
than build-up and unwind moves one unit between a counter and the reservoir or
none, so at every stamp the sum of the three counters is the number of
build-up labels minus the number of unwind labels so far
(`ExactRun.total_count`).

### The intended witnesses

For a balanced exact run with last stamp `E`, the twenty-one existential
variables (`ClockExistentials`) have the following intended values. All of
them are finite.

| Variable | Lean field | Intended value |
|---|---|---|
| `D` | `clock` | the comb with tooth `s` at every stamp `s ≤ E` |
| `L` | `labels` | the *label tree*: at `1ˡ 0` the *component* of label `l`, the part of the clock at the stamps with label `l` |
| `C i`, `i < 3` | `counter i` | the comb with tooth `s + cᵢ(s)` at stamp `s` |
| `C⁺ i`, `C⁰ i` | `plusClass i`, `zeroClass i` | the part of `C i` at the stamps `s ≥ 1` whose label adds `1` to counter `i`, resp. keeps it |
| `W`, `Wᵤ` | `unwind`, `unwindPart` | the comb whose tooth at `s` is the number of unwind labels up to `s`, and its part at the unwind stamps |
| `B`, `B₀`, `k_B` | `chain`, `chainHead`, `chainLoop` | the prefixes of `1ᴱ 0 1ᴱ 0`, the prefixes of `1ᴱ 0 1ᴱ`, and the words obtained from them by removing leading ones |
| `N`, `k_N` | `buildRay`, `buildLoop` | the prefixes of `1ᴺ` for `N` the number of build-up labels, and the words obtained from the build-up component by removing leading ones |
| `R`, `K`, `K₂` | `ray`, `combBound`, `sink` | the words of length at most `m + 3E + 3` with no zero, at most one zero, at most two zeros |

Three ideas carry the construction. The run is timed by a *clock*, a comb whose
tooth at stamp `s` has length exactly `s`. The label of each step is recorded
by splitting the clock into components, one per label, all packed into the
label tree: the component of label `l` sits at the address `1ˡ 0` of `L`, so
`pack l y ≤ L` (with `pack l y = f(⊥, … f(⊥, f(y, ⊥)))`) says that `y` lies
below the component of `l`. And a counter value `c` at stamp `s` is stored as
a tooth of length `c + s`. A counter changes by at most one per step, so these
teeth never shrink from one stamp to the next; this is what lets two words of
different stamps be compared through leading ones.

### How a clause reads addresses

On trees without `⊤`, a negated inequality `¬(y ≤ g)` says that some address
lies in `y` and not in `g`. A universal clause `hypothesis → y₁ ≤ g₁ ∨ …` fails
exactly when some assignment of the universal variables satisfies its
hypothesis and none of its conclusions, so the universal block ranges, in
effect, over tuples of addresses, and every clause becomes an inclusion
between sets of words built from the witnesses.

Most clauses are *one-seed clauses* `seeds ∧ bounds ∧ shape → y₁ ≤ g₁`
(`ClockClause.oneSeed`). The *seed atoms* bound the seed `y₁` by a witness:
`y₁ ≤ X`, `f(⊥, y₁) ≤ X` (below the right child of `X`), `pack l y₁ ≤ L` (below
the component of `l`), or `pack l (f(⊥, y₁)) ≤ L`. The *bound atoms* bound a
witness by `g₁`: `X ≤ g₁`, `X ≤ f(z, g₁)` (the right child of `X` lies below
`g₁`), or `L ≤ componentContext m z sel g₁` and `L ≤ tailContext m z sel g₁`,
which put the selected components, or their right children, below `g₁` and
everything else below the *sink* `z`. The optional *shape* restricts the seed
to spine words and stubs (`y₁ ≤ k ∧ k ≤ f(e, k)`, with `e = f(⊥, ⊥)`) or to
words with at most one zero. Each atom has a *reading*, a set of words, and the
clause holds for all values exactly when every word lying in all seed readings
and in the shape lies in some bound reading (`OneSeedSpec`). The other clause
kinds are the window clauses, the chain clause and the unwinding bound
described below. Every clause has a specification of this kind
(`ClockClause.Spec`), proved equivalent to the clause in both directions
(`ClockClause.holds_of_spec`, `ClockClause.spec_of_holds`).

### Certifying the clock

The tooth of the clock can grow by at most one per stamp. This is the *window
clause* `ClockClause.window D D`; in general, for a source `X` and a base `Y`,
the window clause `ClockClause.window X Y` is

```text
f(⊥, y₁) ≤ X ∧ f(⊥, y₂) ≤ X ∧ Y ≤ g₁ ∧ Y ≤ g₂
  ∧ y₁ ≤ d₁ ∧ d₁ ≤ f(z, d₁) ∧ d₁ ≤ g₂
  ∧ y₂ ≤ f(z, e₂) ∧ e₂ ≤ f(z, e₂) ∧ e₂ ≤ g₁
  →  y₁ ≤ g₁ ∨ y₂ ≤ g₂
```

Suppose it fails, with addresses `w₁` of `y₁` outside `g₁` and `w₂` of `y₂`
outside `g₂`. The first line makes `w₁` and `w₂` *new* words: addresses of the
right child of `X` that are not addresses of `Y`. The loop `d₁ ≤ f(z, d₁)`
closes `d₁` under removing a leading one, so `g₂` contains every word obtained
from `w₁` by removing leading ones, and `w₂` is not such a word; likewise `w₁`
is not obtained from `w₂` by removing at least one leading one. So the clause
holds exactly when no two new words are unrelated in this sense
(`WindowSpec 2`). Two new tooth words of the same stamp are unrelated, so the
window clause allows at most one new tooth word per stamp
(`WindowSpec.not_strictMono`). Two new tooth words of different stamps are
related as soon as the new words of later stamps are not shorter, and then the
window clause says exactly this (`windowSpec_of_onion`). The *triple window
clause* `ClockClause.window3`, with three seeds, allows two new tooth words
per stamp.

For the clock this gives: the tooth at stamp `s + 1` is at most one longer than
the tooth at `s`, and going back one stamp shortens a tooth by at most one. The
root conditions `f(e, ⊥) ≤ D ≤ f(e, K₂)` give the tooth `0` at stamp `0`, so
the tooth at stamp `s` is at most `s` long.

One lower bound remains: the tooth at the last stamp must be reached. It comes
from a *balanced word* `1ᴱ 0 1ᴱ` produced by a chain that overlaps itself. The
chain clause `y₁ ≤ B ∧ y₂ ≤ B → y₁ ≤ y₂ ∨ y₂ ≤ y₁` makes the addresses of `B`
pairwise comparable: `B` is the set of prefixes of a single word. The loop
`B ≤ k_B ∧ k_B ≤ f(B, k_B)` makes `B` contain every word obtained from an
address of `B` by removing leading ones and then a zero. The root condition
`¬(B ≤ B₀)` and the head clause (the words of `B` with at most one zero lie in
`B₀`) give an address `1ᵃ 0 γ` of `B` with a zero in `γ`; by the loop `γ` is
an address of `B` too, comparable with `1ᵃ 0 γ`, which forces `γ` to start
with `1ᵃ 0`. So `1ᵃ 0 1ᵃ` lies in the head `B₀`, and the root condition
`pack 5 B₀ ≤ L` puts it into the component of the end label, inside the clock.
With `E = a`, the clock has the tooth word `1ᴱ 0 1ᴱ`; going back one stamp at
a time, it has the tooth `s` at every stamp `s ≤ E`. The *gap clause* (spine
words and stubs of the right child of `D` lie in `D`) makes the stamps an
initial segment.

### Labels

Each stamp `s ≤ E` carries exactly one label: the *covering clause* puts every
address of the clock into some component, and the *uniqueness clauses* say
that two components share only spine words (they lie in the ray `R`, whose
addresses are words of ones). The label at stamp `0` is the start label (root
conditions), the *transition clause* of label `l`

```text
pack l y₁ ≤ L ∧ R ≤ g₁ ∧ L ≤ tailContext m z (isSuccessor P l) g₁  →  y₁ ≤ g₁
```

says that every word of the component of `l` other than a spine word lies,
one stamp later, in the component of a successor of `l`, and the *end clause*
says that the component of the end label and the right child of the clock
share only spine words, so no stamp follows the end label. The tooth of the
clock at stamp `s` lies in the component of the label at `s`, and the labels
`λ₀, …, λ_E` follow the successor relation from the start label to the end
label at `E`.

### Counters: bounded from above, made exact by a budget

The root conditions give each counter comb `C i` the tooth `0` at stamp `0`,
and `D ≤ C i` makes its tooth at stamp `s` at least `s` long; so
`cᵢ(s) = (tooth of C i at s) - s` is a natural number with `cᵢ(0) = 0`. A
counter step is checked by four clauses:

* the *step clause*: a new tooth word of the right child of `C i` (one not in
  `C i`) lies in the right child of `C⁺ i` or of `C⁰ i`;
* the *class clauses*: the stubs of `C⁺ i` lie at stamps whose label adds `1`
  to counter `i`, and those of `C⁰ i` at stamps whose label keeps it;
* the *window clauses*: `C⁰ i` contributes at most one new tooth word per
  stamp, `C⁺ i` at most two (the triple window clause).

So the tooth grows by at most `1 + effect` from stamp `s` to stamp `s + 1`, and
not at all if the label decreases counter `i`:
`cᵢ(s + 1) ≤ cᵢ(s) + effect(λₛ₊₁, i)`. In the same way a step clause, a window
clause and the root condition `pack 4 Wᵤ ≤ L` bound the teeth of the unwinding
comb `W` by the number of unwind labels so far.

These are bounds from above only. A clause compares stamp `s + 1` with stamp
`s` through right children, which remove a leading `1`; it can say that the
words of one tooth reappear one stamp later, or that few new words appear, but
none of the clauses forces a tooth to grow, which would require producing the
longer word `1ˢ⁺¹ 0 1ˣ⁺¹` from `1ˢ 0 1ˣ`. So far, the clauses describe the run
of a *lossy* counter machine, whose counters may drop below their true values
at any step.

The reservoir makes every step exact. Every effect sums to `0` over the three
counters, except `+1` for build-up and `-1` for unwind (`sum_effect`), so the
quantity

```text
c₀(s) + c₁(s) + c₂(s) - (build-up labels up to s) + (unwind labels up to s)
```

starts at `0` and decreases by the total loss of each step. At the last stamp
it is nonnegative as soon as there are at most as many build-up labels as
unwind labels, and then no step loses anything. This inequality is enforced by
the ray `N` and the *unwinding bound*
`y₁ ≤ N ∧ W ≤ k ∧ k ≤ f(g₁, k) → y₁ ≤ g₁`, which states that every address of
`N` lies in the *tails* of `W` (the words `v` with `1ᵃ 0 v` an address of `W`).
Let `b` be the last stamp with the build-up label, so that there are at most
`b` build-up labels. The tooth `1ᵇ 0 1ᵇ` of the clock at stamp `b` lies in the
build-up component, which the root conditions put below `k_N` with
`k_N ≤ f(N, k_N)`, so `1ᵇ` is an address of `N`; the unwinding bound puts `1ᵇ`
into some tooth of `W`, whose teeth are at most the number of unwind labels.
So every step is exact: `cᵢ(s + 1) = cᵢ(s) + effect(λₛ₊₁, i)`.

### Zero tests

The *zero-test clause* of a zero branch `μ` testing counter `c`,

```text
y₁ ≤ C c ∧ pack μ (f(⊥, y₁)) ≤ L ∧ D ≤ g₁  →  y₁ ≤ g₁
```

says that a tooth word of `C c` that lies, one stamp later, in the component
of `μ` is an address of the clock. If `λₛ₊₁ = μ` and `c_c(s) ≥ 1`, the word
`1ˢ 0 1ˢ⁺¹` lies in `C c` and in the right child of the component of `μ`, but
not in the clock, whose tooth at `s` has length `s`. So the counter is zero
before the step. The labels and counters therefore form an exact run, and the
program halts (`ExactRun.halts`).

### Why finite trees suffice

In every clause of the clock sentence, a constructor occurs on the left of an
inequality only when the right side is a witness, as in `f(⊥, y₁) ≤ X` or
`pack l y₁ ≤ L`. No clause *pushes*: none forces a universal variable to
contain words longer than words of the witnesses, as the atom `f(⊥, p) ≤ p` of
the first reduction does (if `p` contains a word `w`, it contains `1ʲ w` for
every `j`). The universal values only need words copied from the witnesses or
shortened by removing leading letters. So whenever a clause fails, it fails
for values built from the witnesses and small finite trees by paths, finite
unions, residuals (subtrees at an address) and *spine joins* (unions of the
residuals along the right spine), all of which are finite when the witnesses
are finite and regular when they are regular (`domain_residual`,
`domain_unionTree`, `domain_spineJoin`). The specifications are therefore the
same in all three tree classes, and the intended witnesses, being finite, lie
in all of them.

### Keeping witnesses free of ⊤

The sentence contains neither `⊤` nor an equation. Three *guard trees* keep
the witnesses free of `⊤`: the ray `R ≤ f(⊥, R)`, the comb bound
`K ≤ f(R, K)` and the sink `K₂ ≤ f(K, K₂)`, with every other existential
variable below `K₂`. A tree `t ≤ f(a, t)` with `a` free of `⊤` is free of `⊤`:
a shortest address at or below a `⊤` of `t` would be `1 w` with `w` a shorter
one (`Tree.topFree_of_le_f`). So `R`, `K`, `K₂` and every witness are free of
`⊤`, and their addresses have no zero, at most one zero and at most two zeros.
The universal values may contain `⊤` in the signature with `⊤`; the clauses
are read through *supports*, the addresses at or below an `f` or a `⊤`, which
are monotone for the order (`Tree.support_mono`, `Tree.le_iff_subset_support`).
The union `R ⊔ K ⊔ K₂` contains every residual of every witness and serves as
the value of the sink `z` in the refutations that need one. One sentence therefore serves
both signatures.

### The sentence

For a program `P` with `n` instructions and `m = 6 + 2n` labels,
`clockSentence top P` is

```text
∃ D B B₀ k_B L C₀ C₁ C₂ C⁺₀ C⁺₁ C⁺₂ C⁰₀ C⁰₁ C⁰₂ W Wᵤ N k_N R K K₂
∀ y₁ y₂ y₃ g₁ g₂ g₃ k k₀ d₁ d₂ e₂ e₃ z.
    (guards ∧ rootConditions) ∧ clauses
```

where `Cᵢ`, `C⁺ᵢ` and `C⁰ᵢ` stand for `C i`, `C⁺ i` and `C⁰ i`. Within each
block the variables are listed in the order of their de Bruijn indices in the
Lean definition (`Clock.existentialVars` and `Clock.universalVars`): the first
variable listed has index 0 in its block and is the innermost binder of the
block, so `D` is the innermost existential and `y₁` the innermost universal
quantifier. The universal variables are three seeds `y₁ y₂ y₃`, three bounds
`g₁ g₂ g₃`, the shape auxiliaries `k k₀`, the window auxiliaries
`d₁ d₂ e₂ e₃`, and the sink `z`.

* **Guards** (`Clock.guards`): `R ≤ f(⊥, R)`, `K ≤ f(R, K)`, `K₂ ≤ f(K, K₂)`,
  and `X ≤ K₂` for the eighteen other existential variables.
* **Root conditions** (`Clock.rootConditions`), twenty-nine inequalities and
  one negated inequality: `f(e, ⊥) ≤ D ≤ f(e, K₂)`, and the same for each
  counter comb and for `W` (tooth `0` at stamp `0`); `D ≤ C i`; `C⁺ i`, `C⁰ i`
  and `Wᵤ` below `f(⊥, K₂)` (no tooth at stamp `0`); the start label has the
  stub at stamp `0` and is the only label with a tooth there; every component
  lies below the clock; `pack 5 B₀ ≤ L` and `pack 4 Wᵤ ≤ L`; the loops
  `B ≤ k_B ≤ f(B, k_B)` and `k_N ≤ f(N, k_N)` with the build-up component below
  `k_N`; and `¬(B ≤ B₀)`.
* **Clauses** (`Clock.clauses`), each universally quantified over the thirteen
  universal variables: the chain clause, the head clause, the clock window
  clause, the gap clause, the end clause, the covering clause; a uniqueness
  clause for each pair of labels `l < l' < m`; a transition clause for each
  label other than the end label; for each counter `i < 3` the step clause,
  the two class clauses, the window clause of `C⁰ i` and the triple window
  clause of `C⁺ i`; a zero-test clause for each `jzdec` instruction; and the
  step clause, the window clause and the bound of the unwinding comb. That is
  `m(m - 1)/2 + m + 23 + (number of jzdec instructions)` clauses.

The clauses are described by data (`ClockClause`), with one formula per
description (`ClockClause.formula`); the transition, window, zero-test and
unwinding-bound clauses are written out above.

### Correctness

*Soundness* (`Clock/Soundness.lean`). If the sentence holds in one of the six
structures, the guards make the witnesses free of `⊤`, every clause satisfies
its specification because the refuting values of each clause lie in the
structure, and the argument above reads off an exact run: the stamp `E` from
the chain, the clock, the labels, the counters, the budget and the zero tests.
The trees may be infinite; every tooth length used is shown to be finite from
the clauses, never assumed.

*Completeness* (`Clock/Completeness.lean`). If the program halts, take a
balanced exact run (`exists_balanced_exactRun`) and the finite trees of the
table above. They satisfy the guards, the root conditions and every
specification; the balance of the run is used only for the unwinding bound.
Being finite and free of `⊤`, they lie in every structure, and the clauses hold
for all universal values, with or without `⊤`.

## The first reduction: the machine sentence

The machine sentence is the simpler construction, and the recurrence
reduction is built on its clauses. It does not apply to finite trees: it fixes
six helper trees by equations whose solutions are infinite, and the correctness
proof also refutes clauses with infinite values. Over finite trees these
equations have no solution, so there the sentence is false for every program
(an observation not formalized here). Its correctness theorem
`machineSentence_holds_iff` assumes `c ≠ .finite`.

### A run recorded in trees

The machine sentence reads combs to the left. Write `tooth j x = 1ʲ 0 0ˣ` and
`stub j = 1ʲ 0` (`Word.tooth`, `Word.stub`); spine node `j` stands for step `j`
of the run.

* **A counter is a comb.** The tooth below spine node `j` has depth equal to
  the value of the counter at step `j`: it consists of the addresses `1ʲ 0 0ˣ`
  for `x` at most that value. The sentence has one such comb for each counter,
  `A` and `B`.
* **One tree records the states.** The state tree `U` has the spine `1^q` for
  `q ≤ n`, and below the address `1^q 0` it holds the comb of state `q`. This
  comb contains the stub `1ʲ 0` (so `U` contains `1^q 0 1ʲ 0`) exactly when the
  state at step `j` is `q`. All halted states are represented by `n`: jump
  targets are clipped to `min r n` in the sentence.

The Lean predicates are `ToothAt C j x` (the comb `C` contains `1ʲ 0 0ˣ`, that
is, the counter at step `j` is at least `x`) and `StubAt U q j` (the state at
step `j` is `q`).

### Helper trees

Six existential variables are fixed by equations in which the variable occurs
below a constructor. Each such equation has exactly one solution among all
trees, with or without `⊤`, and the solution is regular, free of `⊤`, and
infinite.

| Variable | Lean | Equation | Addresses |
|---|---|---|---|
| `Z` | `Tree.full` | `Z = f(Z, Z)` | all words |
| `S` | `Tree.rightRay` | `S = f(⊥, S)` | `1*` |
| `T` | `Tree.stubComb` | `T = f(e, T)` | `1*` and the stubs `1ʲ 0` |
| `L` | `Tree.leftRay` | `L = f(L, ⊥)` | `0*` |
| `G` | `Tree.combUniverse` | `G = f(L, G)` | `1*` and all teeth `1ʲ 0 0ˣ` |
| `G₁` | `Tree.shortCombs` | `G₁ = f(f(e, ⊥), G₁)` | `1*` and the teeth `1ʲ 0` and `1ʲ 0 0` |

A tree is below `Z` exactly when it contains no `⊤` (`Tree.le_full_iff`). Every
other variable `v` carries the guard `v ≤ Z`, so with `⊤` in the signature all
values are free of `⊤`, and without `⊤` the guards are true. One sentence
`machineSentence top P` therefore serves both signatures.

The sentence also uses four families of term contexts
(`Trees/Contexts.lean`): `pack q y` places `y` at the address `1^q 0`;
`stateContext Z r g` has `g` at `1^r 0 1` and `Z` at every other leaf;
`haltContext Z S n` has `S` at `1ⁿ 0` and `Z` at every other leaf;
`popContext Z δ k` has `k` at `0^δ` and `Z` at every other leaf. For trees
without `⊤`, `U ≤ stateContext Z r g` says that every address `w` with
`1^r 0 1 w` in `U` lies in `g`: the comb of state `r` without its first spine
step lies in `g`, so `g` contains `1ʲ 0` whenever the state at step `j + 1` is
`r`.

### The sentence

For a program `P` with `n` instructions, `machineSentence top P` is

```text
∃ A B U Z S T L G G₁  ∀ y₁ y₂ y₃ g₁ g₂ g₃ k k₀ kd kp d₁ p₁ d₂ p₂.
    rootConditions ∧ (guards → programClauses)
```

with the variables of each block again listed in de Bruijn order
(`Sentence.existentialVars`, `Sentence.universalVars`).

* **Root conditions** (`rootConditions`): the six helper equations; the
  guards `A ≤ Z`, `B ≤ Z`, `U ≤ Z`; `f(e, ⊥) ≤ A ≤ f(e, Z)` and the same for `B`
  (both counters are zero at step zero); `pack 0 (f(e, ⊥)) ≤ U` (the state is
  zero at step zero); and `¬(U ≤ haltContext Z S n)`, which says that the comb
  of the halting state `n` contains a word outside `1*`, hence a stub `1ᴶ 0`:
  the run is in a halted state at some step `J`.
* **Guards** (`guards`): `v ≤ Z` for each of the fourteen universal variables.
* **Clauses** (`programClauses`): for each instruction `q`, the conjunction
  `instructionClauses n q P[q]` below. Each clause is an implication
  `hypothesis → y₁ ≤ g₁ ∨ y₂ ≤ g₂ ∨ y₃ ≤ g₃` whose hypothesis is a conjunction
  of inequalities; some clauses have fewer disjuncts, or a helper tree in
  place of a bound.

The clauses of instruction `q`, with `c` the counter of the instruction, `c'`
the other counter, and `a` and `a'` the values of a counter at steps `j` and
`j + 1` for a step `j` in state `q`:

| Clause | Meaning |
|---|---|
| `haltUniqueClause n q` | step `j` is not also in the halted state `n` |
| `transitionClause q r` | the state at step `j + 1` is `r` |
| `zeroTestClause q z c` | if `a = 0` for counter `c`, the state at step `j + 1` is `z` |
| `positiveTestClause q p c` | if `a ≥ 1` for counter `c`, the state at step `j + 1` is `p` |
| `upperBoundClause δ trunc q c` | `a' ≤ a + 1 - δ`; with `trunc`, only when `a' ≥ 1` |
| `lowerBoundClause δ q c` | `a' ≥ a + δ - 1` |
| `nextToothClause q c` | counter `c` has a tooth at step `j + 1` |

* `inc c r`: `haltUniqueClause`, `transitionClause q r`, the bounds with
  `δ = 0` and `δ = 2` for `c` (so `a' = a + 1`), and the bounds with `δ = 1` for
  `c'` (so `a' = a`).
* `jzdec c z p`: `haltUniqueClause`, `zeroTestClause q z c`,
  `positiveTestClause q p c`, the truncated upper bound with `δ = 2`, the lower
  bound with `δ = 0` and `nextToothClause` for `c` (so `a' = a - 1` if `a ≥ 1`
  and `a' = 0` if `a = 0`), and the bounds with `δ = 1` for `c'`.

The targets `r`, `z` and `p` enter the clauses as `min r n`, `min z n` and
`min p n`.

### One clause written out

Unlike the clock sentence, the machine sentence bounds each step from below
as well as from above. The lower-bound clause `lowerBoundClause δ q c` for the
counter comb `C` is

```text
y₁ ≤ C ∧ Pop_δ(y₂, g₁) ∧ S ≤ g₁ ∧ y₂ ≤ G ∧ C ≤ f(Z, g₂) ∧ S ≤ g₂ ∧ pack q y₃ ≤ U
  ∧ Align(y₁, g₃; d₁, p₁) ∧ Align(y₂, g₃; d₂, p₂)
  →  y₁ ≤ g₁ ∨ y₂ ≤ g₂ ∨ y₃ ≤ g₃
```

with the *alignment block* (`alignBlock`)

```text
Align(y, g; d, p) := y ≤ f(Z, d) ∧ d ≤ f(Z, d) ∧ d ≤ g ∧ f(⊥, y) ≤ p ∧ f(⊥, p) ≤ p ∧ p ≤ g
```

and the *comparison block* (`popBlock`), `Pop_0(y, g) := y ≤ g` and, for `δ ≥ 1`,

```text
Pop_δ(y, g) := y ≤ k ∧ k ≤ f(k₀, k) ∧ k₀ ≤ popContext Z δ kd ∧ f(kd, ⊥) ≤ kp
               ∧ f(⊥, kp) ≤ kp ∧ kp ≤ g
```

Each failed conclusion `yᵢ ≤ gᵢ` provides an address `wᵢ` of `yᵢ` outside
`gᵢ`. When the counter trees are combs and the combs of the state tree consist
of spine words and stubs, the hypothesis constrains the three addresses as
follows:

* `pack q y₃ ≤ U` puts `1^q 0 w₃` into `U`; since `g₃` contains the spine
  (from the alignment blocks), `w₃` is a stub `1ʲ 0` with state `q` at step `j`;
* `y₁ ≤ C` and `S ≤ g₁` make `w₁` a tooth address `1^j₁ 0 0^x₁` of `C`;
* `y₂ ≤ G` and `S ≤ g₂` make `w₂` a tooth address `1^j₂ 0 0^x₂`, and
  `C ≤ f(Z, g₂)` says that `C` does not contain `1 w₂`, the address of depth
  `x₂` one step later;
* the alignment blocks force `g₃` to contain every address of `y₁` and `y₂`
  with leading ones added or removed, while `g₃` misses the stub `1ʲ 0`; so all
  three words lie in the tooth of the same step, `j₁ = j₂ = j`;
* the comparison block puts into `g₁` every tooth address of `y₂` shortened by
  `δ`, while `g₁` misses `w₁`; this forces `x₂ < x₁ + δ`.

So the clause fails exactly when, at some step `j` in state `q`, the counter
reaches depth `x₁` at step `j` but not depth `x₂` at step `j + 1`, with
`x₂ < x₁ + δ`: a violation of `a' ≥ a + δ - 1`. The atoms `f(⊥, p) ≤ p` and
`f(⊥, kp) ≤ kp` push: if `p` contains a word `w`, it contains `1ʲ w` for every
`j`. Together with the infinite helper trees below the bounds, such as
`S ≤ g₁`, this makes the values refuting a clause infinite: right spines, and
the largest trees avoiding a word (`Tree.cocone`) as bounds. This is why the
machine sentence needs regular or arbitrary trees.

In the Lean development, the *sound* direction of each clause
(`Clauses/Sound.lean`) refutes a clause whose numeric meaning fails by these
explicit values, and the *complete* direction (`Clauses/Complete.lean`)
derives the clause from its numeric meaning when the counter trees are combs
and the state tree consists of stubs.

### Correctness

*Soundness* (`Reduction/Soundness.lean`). Suppose the sentence holds. The root
conditions fix the helper trees, and the clauses imply their numeric meanings,
because the refuting values of the sound direction belong to the structure.
By induction on `j`, while the run has not halted before step `j`, the state
tree has the stub of the current state at step `j`, and the tooth of each
counter at step `j` has depth exactly its value. The root condition gives a
step `J` in the halted state `n`; if the run had not halted by step `J`, the
uniqueness clause of the current state would be violated at `J`.

*Completeness* (`Reduction/Completeness.lean`). If the program halts by step
`J`, take for `A` and `B` the finite combs of the run up to `J`, for `U` the
finite state tree of the run up to `J` (states clipped to `n`), and the helper
trees. All values are regular and free of `⊤`, and every clause holds because
the run satisfies its numeric meaning at every step.

### Why one quantifier alternation suffices

This holds for both sentences. On trees without `⊤`, the universal block
ranges in effect over tuples of addresses, and the quantifier-free hypothesis
of a clause compares them: contexts such as `f(⊥, ·)` and `f(z, ·)` move an
address one stamp along the spine, loops such as `d ≤ f(z, d)` move it any
number of stamps, and the windows and comparison blocks bound the length of a
tooth. Positions of the run are compared through the universal variables
alone, so no inner existential block is needed. The run itself is chosen by
the existential block, and its length is fixed by a single address at finite
depth: the balanced word `1ᴱ 0 1ᴱ` of the chain in the clock sentence, the
stub `1ⁿ 0 1ᴶ 0` of the state tree in the machine sentence. No condition on
the length of the run is needed, and the soundness proofs are inductions on
the stamps up to it.

## What the Lean development proves

For every two-counter program `P` and each of the six structures:

* `clockSentence top P` is a Σ₂ sentence with prefix ∃²¹∀¹³ and only
  inequality atoms, true if and only if `P` halts;
* the map `P ↦ clockSentence top P` is primitive recursive;
* this map is a many-one reduction from halting to truth;
* the prenex negation of `clockSentence top P` is a Π₂ sentence with only
  inequality atoms, computed by a primitive recursive function and true if and
  only if `P` does not halt: it reduces non-halting to Π₂ truth;
* assuming that halting of two-counter machines is undecidable, no computable
  Boolean function is correct on all Σ₂ sentences, nor on all Π₂ sentences, and
  this remains so for sentences whose only atoms are inequalities; truth of all
  sentences is not computable.

The same statements hold for `machineSentence top P` (prefix ∃⁹∀¹⁴) in the
four structures over regular and arbitrary trees. The hypothesis
`hHalt : ¬ComputablePred Program.Halts` represents Minsky's theorem [1, 2]; the
development does not postulate it. The theorems about the clock sentence have
no further hypotheses; those about the machine sentence assume `c ≠ .finite`.
The two further results, `sigma2_theories_differ` and the reduction from
recurrence over arbitrary trees, are described in their own sections below.

### Main theorems

All names below are in `UndeciSigma2`. Import `UndeciSigma2` for the complete
development. The flag `top : Bool` selects the signature (with `⊤` when it is
`true`), `c : TreeClass` selects finite, regular or arbitrary trees, and
`Structure.ofClass c top` is the corresponding structure.

```lean
theorem clockSentence_holds_iff (top : Bool) (P : Program) (c : TreeClass) :
    (clockSentence top P).Holds (Structure.ofClass c top) ↔ P.Halts

theorem clockSentence_isSigma (top : Bool) (P : Program) : (clockSentence top P).IsSigma 2

theorem clockSentence_isLeOnly (top : Bool) (P : Program) : (clockSentence top P).IsLeOnly

theorem primrec_clockSentence (top : Bool) : Primrec (clockSentence top)

theorem sigma2_undecidable (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsSigma 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top))

theorem pi2_undecidable (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsPi 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top))
```

`sigma2_undecidable_le` and `pi2_undecidable_le` restrict the deciders
to sentences satisfying `Formula.IsLeOnly`. The reduction statement is
`clockSentence_manyOne`, and the full-truth corollary is
`truth_not_computable`. For the Π₂ results, the prenex negation of the
sentence reduces non-halting to Π₂ truth: it is a Π₂ sentence
(`clockSentence_negate_isPi`), and `clockSentence_negate_holds_iff` shows that
it holds exactly when the program does not halt. A decider for Π₂ truth would
therefore decide halting by complementation.

The first reduction has the same results over regular and arbitrary trees:

```lean
theorem machineSentence_holds_iff (top : Bool) (P : Program) (c : TreeClass)
    (hc : c ≠ .finite) :
    (machineSentence top P).Holds (Structure.ofClass c top) ↔ P.Halts

theorem sigma2_undecidable_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsSigma 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top))

theorem pi2_undecidable_of_ne_finite (hHalt : ¬ComputablePred Program.Halts) (top : Bool)
    (c : TreeClass) (hc : c ≠ .finite) :
    ¬∃ d : Formula top 0 → Bool, Computable d ∧
      ∀ φ, φ.IsPi 2 → (d φ = true ↔ φ.Holds (Structure.ofClass c top))
```

together with `machineSentence_isSigma`, `machineSentence_isLeOnly`,
`primrec_machineSentence`, `machineSentence_manyOne`,
`sigma2_undecidable_le_of_ne_finite`, `pi2_undecidable_le_of_ne_finite` and
`truth_not_computable_of_ne_finite`.

## The Σ₂ theories of arbitrary and regular trees differ

The separating sentence `separatingSentence top` is

```text
∃ Z x  ∀ u v d h k.
    Z ≤ f(Z, Z) ∧ f(Z, Z) ≤ Z ∧ x ≤ Z
    ∧ (u ≤ Z ∧ v ≤ Z ∧ d ≤ Z ∧ h ≤ Z ∧ k ≤ Z →
         (u ≤ x ∧ v ≤ x → u ≤ v ∨ v ≤ u)
         ∧ (x ≤ d ∧ d ≤ f(h, k) ∧ f(h, k) ≤ d ∧ h ≤ d ∧ k ≤ d → Z ≤ d))
```

with the variables of each block again listed in de Bruijn order. Its only
atoms are inequalities. The two equations make `Z` the full tree, and the
guards `· ≤ Z` make all values free of `⊤`, so the order is inclusion of
address sets (`separatingSentence_holds_ofClass_iff`).

* The first clause says that any two trees below `x` are comparable. Applied
  to the paths to two addresses of `x`, it makes the addresses pairwise
  comparable by prefix: `x` is a *chain*, the set of prefixes of a finite or
  infinite word `ω`. Conversely, any two prefix-closed subsets of a chain are
  comparable. (The clock sentence uses the same clause for its chain `B`.)
* The trees `d` with `d ≤ f(h, k)`, `f(h, k) ≤ d`, `h ≤ d` and `k ≤ d` are the
  trees whose addresses contain the empty word and are closed under removing
  the first letter. Above `x`, the least of them has as addresses the factors
  of `ω`. The second clause says that every such `d` above `x` is the full
  tree.

So the sentence states that **some path contains every finite word as a
factor**.

*Over arbitrary trees it holds* (`separatingSentence_holds_arbitrary`).
Enumerate all words `w₀, w₁, …` and take for `x` the chain of prefixes of the
infinite word `w₀ w₁ w₂ ⋯` (`Separation.disjunctiveChain`). Every word is a
factor of it.

*Over regular trees it fails* (`separatingSentence_not_holds_regular`). Let
`x` be a regular chain, the unfolding of a finite graph with `N` states. Its
subtrees are the unfoldings at the reachable states. Each of them is again a
chain, and **a chain has at most one address of each length**. The join `d` of
`f(⊥, ⊥)` and these finitely many subtrees is regular and lies above `x`, and
its addresses contain the empty word and are closed under removing the first
letter. But `d` has at most `N` addresses of each length `ℓ ≥ 1`, so for
`2^ℓ > N` some word of length `ℓ` is not an address of `d`, and `d` is not the
full tree.

Over finite trees the sentence fails as well
(`separatingSentence_not_holds_finite`), but only because `Z = f(Z, Z)` has no
finite solution. Finite and arbitrary trees are already told apart at Σ₁, for
example by `∃Z. Z ≤ f(Z, Z) ∧ f(Z, Z) ≤ Z`. Regular and arbitrary trees are
not: a Boolean combination of Σ₁ sentences is true over regular trees exactly
when it is true over arbitrary trees
([deci-sigma1](https://github.com/noti0na1/deci-sigma1)). So Σ₂ is the lowest
level at which their theories differ.

```lean
theorem sigma2_theories_differ (top : Bool) : ∃ φ : Formula top 0, φ.IsSigma 2 ∧ φ.IsLeOnly ∧
    φ.Holds (Structure.ofClass .arbitrary top) ∧ ¬φ.Holds (Structure.ofClass .regular top)
```

## Recurrence and the complexity over arbitrary trees

### Nondeterministic two-counter machines

A nondeterministic program is a list of instructions `inc c r` and
`jzdec c z p`, acting as before, and `choice l r`, which keeps both counters
and goes to state `l` or to state `r`. A step exists only from a state that
has an instruction, so an infinite run never reaches a state at least `n`. The
program *recurs* if some infinite run from state `0` with both counters zero
visits state `0` infinitely often.

```lean
inductive NInstr where
  | inc (c : Fin 2) (next : ℕ)
  | jzdec (c : Fin 2) (ifZero ifPos : ℕ)
  | choice (left right : ℕ)

abbrev NProgram := List NInstr

-- in namespace `NInstr`
def Step : NInstr → Config → Config → Prop
  | inc c r, s, t => t = (Instr.inc c r).exec s
  | jzdec c z p, s, t => t = (Instr.jzdec c z p).exec s
  | choice l r, s, t => t = ⟨l, s.counter⟩ ∨ t = ⟨r, s.counter⟩

-- in namespace `NProgram`
def Step (P : NProgram) (s t : Config) : Prop := ∃ i, P[s.state]? = some i ∧ i.Step s t

def Recurs (P : NProgram) : Prop :=
  ∃ run : ℕ → Config, run 0 = Config.init ∧ (∀ t, P.Step (run t) (run (t + 1))) ∧
    ∀ t, ∃ t', t ≤ t' ∧ (run t').state = 0
```

### The recurrence sentence

`recurrenceSentence top P` has the prefix ∃⁹∀¹⁴, the variables, helper trees,
contexts and blocks of the machine sentence, and inequality atoms only. Jump
targets are again clipped to `n`. Its matrix
`rootConditions ∧ (guards → allClauses)` differs from that of the machine
sentence in four ways.

1. **No step outside the program.** The halting literal
   `¬(U ≤ haltContext Z S n)` is replaced by the positive root atom
   `U ≤ haltContext Z S n`: the comb of state `n` has no stub, so no step is in
   a state at least `n`.
2. **The branch clause.** The clauses of `inc` and `jzdec` are those of the
   machine sentence without `haltUniqueClause`. The clauses of `choice l r` in
   state `q` are the branch clause (`branchClause`)

   ```text
   pack q y₁ ≤ U ∧ U ≤ stateContext Z l g₁ ∧ U ≤ stateContext Z r g₁ ∧ S ≤ g₁  →  y₁ ≤ g₁
   ```

   which fails exactly when some stub `1ʲ 0` of state `q` is matched neither
   in the comb of state `l` nor in the comb of state `r` at step `j + 1`,
   together with the bounds with `δ = 1` for **both** counters, which copy the
   two counters to the next step. Without the copies the counters could change at a
   `choice` step, and the reduction would not be sound.
3. **Uniqueness of the state at every step.** The uniqueness clause
   `haltUniqueClause r q` is required for all pairs of states `r < q < n`, so
   no step has stubs of two states. The machine sentence needs it only for the
   halting state; here the recurrence clause reads the stubs of state `0`,
   which must be states of the run.
4. **The recurrence clause** (`recurrenceClause`)

   ```text
   U ≤ f(g₁, Z) ∧ g₁ ≤ f(Z, g₁) ∧ y₁ ≤ T  →  y₁ ≤ g₁
   ```

   The hypothesis says that `g₁` contains the comb of state `0`, the subtree of
   `U` at the address `0`, and is closed under removing leading ones; for all
   seeds `y₁` below the comb of stubs `T`, the conclusion says that `g₁`
   contains every stub `1ʲ 0`. The clause holds for all values exactly when
   state `0` occurs at arbitrarily late steps.

Soundness builds an infinite run step by step, following at each `choice` a
branch whose stub is present, and identifies the arbitrarily late stubs of
state `0` with states of the run. Completeness takes the infinite combs of a
recurring run. Both directions use trees that are in general not regular: the
value of `g₁` refuting the recurrence clause, the least tree containing the
comb of state `0` and closed under removing leading ones, and the combs of an
infinite run. The reduction is therefore stated for arbitrary trees only.

```lean
theorem recurrenceSentence_holds_iff (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).Holds (Structure.ofClass .arbitrary top) ↔ P.Recurs

theorem recurrenceSentence_isSigma (top : Bool) (P : NProgram) :
    (recurrenceSentence top P).IsSigma 2

theorem primrec_recurrenceSentence (top : Bool) : Primrec (recurrenceSentence top)

theorem recurrence_manyOne_sigma2 (top : Bool) :
    ManyOneReducible NProgram.Recurs
      (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
        φ.1.Holds (Structure.ofClass .arbitrary top))

theorem sigma2_truth_not_re (hRecurs : ¬REPred NProgram.Recurs) (top : Bool) :
    ¬REPred (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
      φ.1.Holds (Structure.ofClass .arbitrary top))

theorem sigma2_falsity_not_re (hNonrecurs : ¬REPred fun P : NProgram => ¬P.Recurs)
    (top : Bool) :
    ¬REPred (fun φ : {φ : Formula top 0 // φ.IsSigma 2} =>
      ¬φ.1.Holds (Structure.ofClass .arbitrary top))
```

Σ₂ sentences are coded by the subtype `{φ : Formula top 0 // φ.IsSigma 2}`
with the formula codes (`sigma2Primcodable`). The development also contains
`recurrenceSentence_isLeOnly`, the reduction `recurrence_manyOne` to the truth
of all sentences, `nonrecurrence_manyOne_sigma2` from non-recurrence to Σ₂
falsity, and the prenex negation (`recurrenceSentence_negate_holds_iff`).

### The cited complexity result (not formalized)

> **Not formalized.** Recurrence for nondeterministic two-counter machines is
> Σ¹₁-complete: R. Alur and T. A. Henzinger [8, Section 4.1, Lemma 8], after
> D. Harel, A. Pnueli and J. Stavi [9]. Neither this theorem nor the
> translation between the machines of [8] and `NProgram` is part of this
> library.

Since `recurrenceSentence` is a computable many-one reduction, Σ₂ truth over
arbitrary trees, with or without `⊤`, is then Σ¹₁-hard: it is neither
recursively enumerable nor co-recursively enumerable, and it is not
arithmetical. The first two consequences are proved in Lean as
`sigma2_truth_not_re` and `sigma2_falsity_not_re`, conditionally on the
hypotheses `¬REPred NProgram.Recurs` and `¬REPred fun P => ¬P.Recurs`, which
follow from the cited theorem.

Over finite and over regular trees, by contrast, Σ₂ truth is recursively
enumerable, given the decision procedure for the Σ₁ theory
([deci-sigma1](https://github.com/noti0na1/deci-sigma1)). A finite tree is a
finite term, and a regular tree is the unique solution of a finite system of
guarded equations, so a Σ₂ sentence holds over finite (regular) trees exactly
when, for some choice of finite terms (finite graphs) for its existential
variables, a Π₁ sentence holds, and Π₁ truth is decidable. Since halting of
two-counter machines is complete for the recursively enumerable sets, the
clock sentence then makes Σ₂ truth over finite and over regular trees
complete for them as well. This upper bound is not part of this library.

## Structure of the development

In dependency order:

| Module | Contents |
|---|---|
| `UndeciSigma2/Tree.lean` | trees over `⊥`, `f`, `⊤`; finite terms and finite graphs; finite and regular trees; the six structures |
| `UndeciSigma2/Order.lean` | the non-structural order; inclusion of addresses on trees without `⊤`; meets and joins |
| `UndeciSigma2/Syntax.lean` | terms, formulas, satisfaction, Σₙ/Πₙ classes, prenex negation, inequality-only formulas |
| `UndeciSigma2/Computable/` | Gödel codes of terms and formulas; primitive recursive formula constructors and renaming |
| `UndeciSigma2/Undecidability/Fragments.lean` | primitive recursive quantifier prefixes and Σₖ membership; the coding of Σ₂ sentences |
| `UndeciSigma2/Machine.lean` | two-counter machines, runs and halting |
| `UndeciSigma2/Words.lean` | spine words, teeth and stubs: prefixes, injectivity, counting zeros |
| `UndeciSigma2/Trees/Basic.lean` | addresses of `⊥`, `f`, the full tree, paths, cocones and right nests; finite joins; membership in the domains |
| `UndeciSigma2/Trees/Iterate.lean` | the unique solutions of `X = f(a, X)` and `X = f(X, b)`, and their regularity |
| `UndeciSigma2/Trees/Helpers.lean` | the six helper trees: equations, uniqueness, addresses |
| `UndeciSigma2/Trees/Contexts.lean` | the contexts `pack`, `stateContext`, `haltContext`, `popContext` and their order characterizations |
| `UndeciSigma2/Sentence/Blocks.lean` | finite quantifier blocks and their satisfaction |
| `UndeciSigma2/Sentence/Definition.lean` | the blocks, clauses and matrix; `machineSentence`, its prefix and its atoms |
| `UndeciSigma2/Sentence/Semantics.lean` | semantic counterparts of the clauses; truth of the sentence as a statement about trees |
| `UndeciSigma2/Clauses/Specs.lean` | `StubAt`, `ToothAt`, the numeric meaning of each clause, and the counter value at the next step |
| `UndeciSigma2/Clauses/Sound.lean` | each clause implies its numeric meaning |
| `UndeciSigma2/Clauses/Complete.lean` | the numeric meaning implies the clause for combs |
| `UndeciSigma2/Reduction/Soundness.lean` | a true machine sentence records the run, which halts |
| `UndeciSigma2/Reduction/Completeness.lean` | the trees of a halting run satisfy the machine sentence |
| `UndeciSigma2/Reduction/Correctness.lean` | `machineSentence_holds_iff` and its prenex negation |
| `UndeciSigma2/Undecidability/Computable.lean` | primitive recursiveness of the machine sentence and of its negation |
| `UndeciSigma2/Undecidability/Theorems.lean` | the many-one reduction; Σ₂ and Π₂ undecidability over regular and arbitrary trees; noncomputability of truth |
| `UndeciSigma2/Undecidability/Inequality.lean` | the same Σ₂ and Π₂ results for sentences with only inequality atoms |
| `UndeciSigma2/Separation/Sentence.lean` | the separating sentence, its prefix and atoms, and its meaning in each structure |
| `UndeciSigma2/Separation/Arbitrary.lean` | a chain containing every word as a factor; the sentence holds over arbitrary trees |
| `UndeciSigma2/Separation/Regular.lean` | the suffix closure of a regular chain; the sentence fails over regular and over finite trees |
| `UndeciSigma2/Separation/Theorem.lean` | `sigma2_theories_differ` |
| `UndeciSigma2/Recurrence/Machine.lean` | nondeterministic two-counter machines, steps and recurrence |
| `UndeciSigma2/Recurrence/Definition.lean` | the branch, uniqueness and recurrence clauses; `recurrenceSentence`, its prefix and its atoms |
| `UndeciSigma2/Recurrence/Semantics.lean` | semantic counterparts; truth over arbitrary trees as a statement about trees |
| `UndeciSigma2/Recurrence/Clauses.lean` | numeric meaning of the branch and recurrence clauses, in both directions |
| `UndeciSigma2/Recurrence/Soundness.lean` | a true sentence records an infinite run, which recurs |
| `UndeciSigma2/Recurrence/Completeness.lean` | the infinite trees of a recurring run satisfy the sentence |
| `UndeciSigma2/Recurrence/Correctness.lean` | `recurrenceSentence_holds_iff` and its prenex negation |
| `UndeciSigma2/Recurrence/Computable.lean` | primitive recursiveness of the recurrence sentence |
| `UndeciSigma2/Recurrence/Theorems.lean` | many-one reductions from recurrence and non-recurrence; truth and falsity of Σ₂ sentences are not recursively enumerable under the cited hypotheses |
| `UndeciSigma2/Clock/Machine.lean` | the label machine of a program: labels, successors, effects, zero tests; exact runs; a program halts exactly when it has a balanced exact run |
| `UndeciSigma2/Clock/Definition.lean` | the selection contexts, the variables, the clause descriptions and their formulas; `clockSentence`, its prefix and its atoms |
| `UndeciSigma2/Clock/Support.lean` | supports and top paths; trees below a loop `t ≤ f(a, t)` are free of `⊤` |
| `UndeciSigma2/Clock/Trees.lean` | tooth words; residuals, spine joins, tails, finite unions, prefix closures and drop trees; selections; closure of the three tree classes under these constructions |
| `UndeciSigma2/Clock/Semantics.lean` | semantic counterparts of the clauses; truth of the sentence as `ClockConditions` |
| `UndeciSigma2/Clock/Readings.lean` | the guards make the witnesses free of `⊤`; readings of the atoms, shapes and blocks |
| `UndeciSigma2/Clock/OneSeed.lean` | one-seed clauses and `OneSeedSpec`, in both directions |
| `UndeciSigma2/Clock/Window.lean` | window clauses and `WindowSpec`, in both directions; new tooth words per stamp |
| `UndeciSigma2/Clock/Chain.lean` | the chain clause and the unwinding bound, in both directions |
| `UndeciSigma2/Clock/Specs.lean` | the specification of every clause; truth of the sentence as `SpecConditions`; the specification of each clause family as a statement about words |
| `UndeciSigma2/Clock/Soundness.lean` | trees satisfying the specifications record an exact run, so the program halts |
| `UndeciSigma2/Clock/Completeness.lean` | the finite trees of a balanced exact run satisfy the specifications |
| `UndeciSigma2/Clock/Correctness.lean` | `clockSentence_holds_iff` and its prenex negation |
| `UndeciSigma2/Clock/Computable.lean` | primitive recursiveness of the clock sentence and of its negation |
| `UndeciSigma2/Clock/Theorems.lean` | the many-one reduction; Σ₂ and Π₂ undecidability in all six structures; noncomputability of truth |
| `UndeciSigma2.lean` | the root module, importing the whole development |

## Building and checking

Install [elan](https://github.com/leanprover/elan). The package uses Lean
4.35.0 and Mathlib v4.35.0.

```sh
lake exe cache get
lake build
```

The first command downloads compiled Mathlib dependencies; the second checks
the whole development. It uses no `sorry`, no additional axioms and no
`native_decide`. To inspect the logical dependencies of the main results, save
the following as `Check.lean` in the package root and run
`lake env lean Check.lean`:

```lean
import UndeciSigma2

#print axioms UndeciSigma2.clockSentence_holds_iff
#print axioms UndeciSigma2.primrec_clockSentence
#print axioms UndeciSigma2.sigma2_undecidable
#print axioms UndeciSigma2.pi2_undecidable
#print axioms UndeciSigma2.sigma2_undecidable_le
#print axioms UndeciSigma2.pi2_undecidable_le
#print axioms UndeciSigma2.truth_not_computable
#print axioms UndeciSigma2.machineSentence_holds_iff
#print axioms UndeciSigma2.primrec_machineSentence
#print axioms UndeciSigma2.sigma2_undecidable_of_ne_finite
#print axioms UndeciSigma2.pi2_undecidable_of_ne_finite
#print axioms UndeciSigma2.sigma2_undecidable_le_of_ne_finite
#print axioms UndeciSigma2.pi2_undecidable_le_of_ne_finite
#print axioms UndeciSigma2.truth_not_computable_of_ne_finite
#print axioms UndeciSigma2.sigma2_theories_differ
#print axioms UndeciSigma2.recurrenceSentence_holds_iff
#print axioms UndeciSigma2.primrec_recurrenceSentence
#print axioms UndeciSigma2.recurrence_manyOne_sigma2
#print axioms UndeciSigma2.sigma2_truth_not_re
#print axioms UndeciSigma2.sigma2_falsity_not_re
```

Each result depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## References

1. M. L. Minsky. *Recursive unsolvability of Post's problem of "Tag" and other
   topics in theory of Turing machines.* Annals of Mathematics 74(3), 437–455,
   1961.
2. M. L. Minsky. *Computation: Finite and Infinite Machines.* Prentice-Hall,
   1967.
3. Z. Su, A. Aiken, J. Niehren, T. Priesnitz and R. Treinen. *The first-order
   theory of subtyping constraints.* POPL 2002, 203–216.
   [doi:10.1145/503272.503292](https://doi.org/10.1145/503272.503292)
4. J. Niehren and T. Priesnitz. *Entailment of non-structural subtype
   constraints.* ASIAN 1999, LNCS 1742, 251–265.
   [doi:10.1007/3-540-46674-6_22](https://doi.org/10.1007/3-540-46674-6_22)
5. J. Niehren and T. Priesnitz. *Non-structural subtype entailment in automata
   theory.* Information and Computation 186(2), 319–354, 2003.
   [doi:10.1016/S0890-5401(03)00140-8](https://doi.org/10.1016/S0890-5401(03)00140-8)
6. D. Kozen, J. Palsberg and M. I. Schwartzbach. *Efficient inference of
   partial types.* Journal of Computer and System Sciences 49(2), 306–324,
   1994.
7. J. Palsberg, M. Wand and P. O'Keefe. *Type inference with non-structural
   subtyping.* Formal Aspects of Computing 9, 49–67, 1997.
   [doi:10.1007/BF01212524](https://doi.org/10.1007/BF01212524)
8. R. Alur and T. A. Henzinger. *A really temporal logic.* Journal of the ACM
   41(1), 1994.
9. D. Harel, A. Pnueli and J. Stavi. *Propositional dynamic logic of nonregular
   programs.* Journal of Computer and System Sciences 26(2), 222–243, 1983.

Related Lean developments: [deci-nsse](https://github.com/noti0na1/deci-nsse)
(entailment), [deci-ensse](https://github.com/noti0na1/deci-ensse) (existential
entailment), [deci-sigma1](https://github.com/noti0na1/deci-sigma1) (the Σ₁
theory) and [undeci-sigma3](https://github.com/noti0na1/undeci-sigma3) (the Σ₃
theory, by a reduction from the Post correspondence problem).

## License

Apache License 2.0. See [LICENSE](LICENSE).
