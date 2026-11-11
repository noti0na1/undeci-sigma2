import Mathlib

/-! # Two-counter machines

A program is a list of instructions acting on two counters. The instruction
`inc c r` increments counter `c` and goes to state `r`. The instruction
`jzdec c z p` goes to state `z` if counter `c` is zero, and otherwise
decrements counter `c` and goes to state `p`. A program with `n` instructions
has the working states `0, …, n - 1`; every state at least `n` is halted, and a
step from a halted configuration changes nothing.

Halting of two-counter machines started with both counters zero is
undecidable (Minsky 1961, 1967). The reduction in this library uses that fact
as a hypothesis.
-/

namespace UndeciSigma2

/-- Instructions of a machine with two counters. -/
inductive Instr where
  /-- Increment counter `c`, then go to state `next`. -/
  | inc (c : Fin 2) (next : ℕ)
  /-- If counter `c` is zero go to `ifZero`; otherwise decrement it and go to `ifPos`. -/
  | jzdec (c : Fin 2) (ifZero ifPos : ℕ)
  deriving DecidableEq, Repr

/-- A program: instruction `q` is executed in state `q`. -/
abbrev Program := List Instr

/-- A configuration: the current state and the values of both counters. -/
structure Config where
  /-- The current state. -/
  state : ℕ
  /-- The values of the two counters. -/
  counter : Fin 2 → ℕ

namespace Config

/-- The initial configuration: state zero and both counters zero. -/
def init : Config := ⟨0, fun _ => 0⟩

@[simp] theorem init_state : init.state = 0 := rfl
@[simp] theorem init_counter (c : Fin 2) : init.counter c = 0 := rfl

end Config

/-- The counter other than `c`. -/
def otherCounter (c : Fin 2) : Fin 2 := 1 - c

@[simp] theorem otherCounter_zero : otherCounter 0 = 1 := rfl
@[simp] theorem otherCounter_one : otherCounter 1 = 0 := rfl

theorem otherCounter_ne (c : Fin 2) : otherCounter c ≠ c := by
  fin_cases c <;> decide

theorem ne_otherCounter (c : Fin 2) : c ≠ otherCounter c := (otherCounter_ne c).symm

/-- Every counter is `c` or the other one. -/
theorem eq_or_eq_otherCounter (c d : Fin 2) : d = c ∨ d = otherCounter c := by
  fin_cases c <;> fin_cases d <;> decide

namespace Instr

/-- Execute one instruction. -/
def exec : Instr → Config → Config
  | inc c r, s => ⟨r, Function.update s.counter c (s.counter c + 1)⟩
  | jzdec c z p, s =>
    if s.counter c = 0 then ⟨z, s.counter⟩
    else ⟨p, Function.update s.counter c (s.counter c - 1)⟩

@[simp] theorem exec_inc_state (c : Fin 2) (r : ℕ) (s : Config) :
    ((inc c r).exec s).state = r := rfl

@[simp] theorem exec_inc_counter (c : Fin 2) (r : ℕ) (s : Config) (d : Fin 2) :
    ((inc c r).exec s).counter d = if d = c then s.counter c + 1 else s.counter d := by
  simp only [exec, Function.update_apply]

theorem exec_jzdec_of_eq_zero {c : Fin 2} {z p : ℕ} {s : Config} (h : s.counter c = 0) :
    (jzdec c z p).exec s = ⟨z, s.counter⟩ := by
  simp [exec, h]

theorem exec_jzdec_of_ne_zero {c : Fin 2} {z p : ℕ} {s : Config} (h : s.counter c ≠ 0) :
    (jzdec c z p).exec s = ⟨p, Function.update s.counter c (s.counter c - 1)⟩ := by
  simp [exec, h]

/-- The equivalence with a sum of products, used for the computability instance. -/
def equivSum : Instr ≃ (Fin 2 × ℕ) ⊕ (Fin 2 × ℕ × ℕ) where
  toFun
    | inc c r => .inl (c, r)
    | jzdec c z p => .inr (c, z, p)
  invFun
    | .inl (c, r) => inc c r
    | .inr (c, z, p) => jzdec c z p
  left_inv i := by cases i <;> rfl
  right_inv s := by rcases s with ⟨c, r⟩ | ⟨c, z, p⟩ <;> rfl

instance : Primcodable Instr := Primcodable.ofEquiv _ equivSum

end Instr

namespace Program

/-- One step of a program. Configurations whose state has no instruction are halted. -/
def step (P : Program) (s : Config) : Config :=
  match P[s.state]? with
  | none => s
  | some i => i.exec s

/-- The program halts when started in state zero with both counters zero. -/
def Halts (P : Program) : Prop :=
  ∃ t, P.length ≤ ((P.step)^[t] ⟨0, fun _ => 0⟩).state

/-- The configuration after `t` steps from the initial configuration. -/
def run (P : Program) (t : ℕ) : Config := (P.step)^[t] Config.init

theorem step_of_getElem? {P : Program} {s : Config} {i : Instr} (h : P[s.state]? = some i) :
    P.step s = i.exec s := by
  simp [step, h]

/-- A halted configuration is a fixed point of the step function. -/
theorem step_of_length_le {P : Program} {s : Config} (h : P.length ≤ s.state) :
    P.step s = s := by
  have : P[s.state]? = none := List.getElem?_eq_none h
  simp [step, this]

@[simp] theorem run_zero (P : Program) : P.run 0 = Config.init := rfl

theorem run_succ (P : Program) (t : ℕ) : P.run (t + 1) = P.step (P.run t) :=
  Function.iterate_succ_apply' _ _ _

/-- Once halted, the run stays at the same configuration. -/
theorem run_eq_of_halted {P : Program} {t t' : ℕ} (h : P.length ≤ (P.run t).state)
    (ht : t ≤ t') : P.run t' = P.run t := by
  induction t', ht using Nat.le_induction with
  | base => rfl
  | succ t' _ ih => rw [run_succ, ih, step_of_length_le h]

theorem halts_iff_run (P : Program) : P.Halts ↔ ∃ t, P.length ≤ (P.run t).state := Iff.rfl

/-- The first state of a run is zero. -/
@[simp] theorem run_zero_state (P : Program) : (P.run 0).state = 0 := rfl

end Program

/-! ## Example

The program below adds two to counter `0`, moves counter `0` into counter `1` one unit at
a time, and halts in state `4`. -/

section Examples

private def transferProgram : Program :=
  [.inc 0 1, .inc 0 2, .jzdec 0 4 3, .inc 1 2]

example : (transferProgram.run 2).counter 0 = 2 := by decide
example : (transferProgram.run 4).counter 0 = 1 ∧ (transferProgram.run 4).counter 1 = 1 := by
  decide
example : (transferProgram.run 7).state = 4 ∧ (transferProgram.run 7).counter 1 = 2 := by decide
example : (transferProgram.run 9).state = 4 := by decide
example : transferProgram.Halts := ⟨7, by decide⟩

end Examples

end UndeciSigma2
