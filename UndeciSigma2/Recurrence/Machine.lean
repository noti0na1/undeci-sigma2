import UndeciSigma2.Machine

/-! # Nondeterministic two-counter machines

A nondeterministic program is a list of instructions acting on two counters. Besides the
instructions `inc c r` and `jzdec c z p` of the deterministic machine, the instruction
`choice l r` keeps both counters and goes to state `l` or to state `r`. A program with
`n` instructions has the states `0, …, n - 1`; a step exists only from a state that has an
instruction, so an infinite run never leaves the program.

The recurrence problem asks whether some infinite run from the initial configuration visits
state `0` infinitely often. For nondeterministic two-counter machines it is
Σ¹₁-complete (Alur and Henzinger 1994, after Harel, Pnueli and Stavi 1983); the reduction in
this library uses only the definition.
-/

namespace UndeciSigma2

/-- Instructions of a nondeterministic two-counter machine. -/
inductive NInstr where
  /-- Increment counter `c`, then go to state `next`. -/
  | inc (c : Fin 2) (next : ℕ)
  /-- If counter `c` is zero go to `ifZero`; otherwise decrement it and go to `ifPos`. -/
  | jzdec (c : Fin 2) (ifZero ifPos : ℕ)
  /-- Keep both counters and go to state `left` or to state `right`. -/
  | choice (left right : ℕ)
  deriving DecidableEq, Repr

/-- A nondeterministic program: instruction `q` is executed in state `q`. -/
abbrev NProgram := List NInstr

namespace NInstr

/-- `i.Step s t`: executing `i` in configuration `s` can give `t`. The instructions `inc`
and `jzdec` act as in the deterministic machine; `choice l r` keeps both counters and goes to
`l` or to `r`. -/
def Step : NInstr → Config → Config → Prop
  | inc c r, s, t => t = (Instr.inc c r).exec s
  | jzdec c z p, s, t => t = (Instr.jzdec c z p).exec s
  | choice l r, s, t => t = ⟨l, s.counter⟩ ∨ t = ⟨r, s.counter⟩

@[simp] theorem step_inc_iff (c : Fin 2) (r : ℕ) (s t : Config) :
    (inc c r).Step s t ↔ t = (Instr.inc c r).exec s := Iff.rfl

@[simp] theorem step_jzdec_iff (c : Fin 2) (z p : ℕ) (s t : Config) :
    (jzdec c z p).Step s t ↔ t = (Instr.jzdec c z p).exec s := Iff.rfl

@[simp] theorem step_choice_iff (l r : ℕ) (s t : Config) :
    (choice l r).Step s t ↔ t = ⟨l, s.counter⟩ ∨ t = ⟨r, s.counter⟩ := Iff.rfl

/-- The equivalence with a sum of products, used for the computability instance. -/
def equivSum : NInstr ≃ (Fin 2 × ℕ) ⊕ (Fin 2 × ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun
    | inc c r => .inl (c, r)
    | jzdec c z p => .inr (.inl (c, z, p))
    | choice l r => .inr (.inr (l, r))
  invFun
    | .inl (c, r) => inc c r
    | .inr (.inl (c, z, p)) => jzdec c z p
    | .inr (.inr (l, r)) => choice l r
  left_inv i := by cases i <;> rfl
  right_inv s := by rcases s with ⟨c, r⟩ | ⟨c, z, p⟩ | ⟨l, r⟩ <;> rfl

instance : Primcodable NInstr := Primcodable.ofEquiv _ equivSum

end NInstr

namespace NProgram

/-- `P.Step s t`: one step of `P` can lead from `s` to `t`. A step exists only from a state
that has an instruction. -/
def Step (P : NProgram) (s t : Config) : Prop := ∃ i, P[s.state]? = some i ∧ i.Step s t

/-- Some infinite run from the initial configuration visits state `0` infinitely often. -/
def Recurs (P : NProgram) : Prop :=
  ∃ run : ℕ → Config, run 0 = Config.init ∧ (∀ t, P.Step (run t) (run (t + 1))) ∧
    ∀ t, ∃ t', t ≤ t' ∧ (run t').state = 0

/-- A step starts from a state that has an instruction. -/
theorem Step.state_lt_length {P : NProgram} {s t : Config} (h : P.Step s t) :
    s.state < P.length := by
  obtain ⟨i, hi, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp hi).1

/-- A program that recurs has at least one instruction. -/
theorem Recurs.length_pos {P : NProgram} (h : P.Recurs) : 0 < P.length := by
  obtain ⟨run, h0, hstep, -⟩ := h
  have := (hstep 0).state_lt_length
  rwa [h0] at this

end NProgram

/-! ## Examples

The program `[choice 0 0]` stays in state `0` forever. The program `[inc 0 1]` moves to
state `1`, which has no instruction, so it has no infinite run. -/

section Examples

example : NProgram.Recurs [.choice 0 0] :=
  ⟨fun _ => Config.init, rfl, fun _ => ⟨.choice 0 0, rfl, Or.inl rfl⟩,
    fun t => ⟨t, le_rfl, rfl⟩⟩

example : ¬NProgram.Recurs [.inc 0 1] := by
  rintro ⟨run, h0, hstep, -⟩
  obtain ⟨i, hi, hs⟩ := hstep 0
  rw [h0] at hi
  obtain rfl : i = .inc 0 1 := (Option.some.inj hi).symm
  have h1 : (run 1).state = 1 := by
    rw [NInstr.step_inc_iff] at hs
    rw [hs, Instr.exec_inc_state]
  have := (hstep 1).state_lt_length
  rw [h1] at this
  exact absurd this (by decide)

end Examples

end UndeciSigma2
