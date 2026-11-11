import UndeciSigma2.Clauses.Sound

/-! # Soundness of the reduction

If the machine sentence holds, the program halts. The counter trees and the state
tree record the run of the program step by step, as long as it has not halted: at
step `j` the state tree has the stub of state `qⱼ` (clipped to `n`), and counter `d`
has exactly the teeth of depth at most its value. The halting literal provides a step
`J` with the stub of the halting state `n`; the uniqueness clause then shows that the
run has halted by step `J`.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Sentence

variable {P : Program} {C : Fin 2 → Tree} {U : Tree}

/-- At step zero the state is zero and both counters are zero. -/
theorem initial_recorded (h : InitialConditions P.length C U) :
    StubAt U 0 0 ∧ ∀ d x, ToothAt (C d) 0 x ↔ x = 0 := by
  obtain ⟨hC, hU, hcounter, hstate, -⟩ := h
  constructor
  · exact ((pack_le_iff (by simp) hU 0).mp hstate).2 (stub 0) (by simp)
  · intro d x
    obtain ⟨hlo, hhi⟩ := hcounter d
    constructor
    · intro hx
      have hz := ((le_f_iff topFree_e topFree_full (hC d)).mp hhi).1 (zeros x) hx
      have he := (mem_constructorPaths_e _).mp hz
      have := congrArg List.length he
      simpa using this
    · rintro rfl
      exact ((f_le_iff topFree_e topFree_bot (hC d)).mp hlo).2.1 []
        nil_mem_constructorPaths_e

/-- The halting state occurs at some step. -/
theorem exists_halt_stub (h : InitialConditions P.length C U) : ∃ J, StubAt U P.length J := by
  classical
  have hn := h.2.2.2.2
  rw [le_haltContext_iff h.2.1] at hn
  push Not at hn
  obtain ⟨w, hw, hn⟩ := hn
  obtain ⟨J, v, rfl⟩ := (not_isOnes_iff w).mp hn
  refine ⟨J, mem_constructorPaths_of_prefix ?_ hw⟩
  exact ⟨v, by simp [stub_eq, List.append_assoc]⟩

/-- While the program runs, the trees record its configurations. -/
theorem run_recorded (h : InitialConditions P.length C U)
    (hspec : ∀ q ins, P[q]? = some ins → InstructionSpecs P.length C U q ins) :
    ∀ j, (∀ i < j, (P.run i).state < P.length) →
      StubAt U (min (P.run j).state P.length) j ∧
        ∀ d x, ToothAt (C d) j x ↔ x ≤ (P.run j).counter d := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa using initial_recorded h
  | succ j ih =>
    intro hlt
    obtain ⟨hs, hc⟩ := ih fun i hi => hlt i (by omega)
    have hj := hlt j (Nat.lt_succ_self j)
    rw [min_eq_left hj.le] at hs
    obtain ⟨ins, hins⟩ : ∃ ins, P[(P.run j).state]? = some ins :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    have hstep : P.run (j + 1) = ins.exec (P.run j) :=
      (P.run_succ j).trans (Program.step_of_getElem? hins)
    have hspec' := hspec _ _ hins
    rw [hstep]
    cases ins with
    | inc c r =>
      obtain ⟨-, ht, hu, hl, hu', hl'⟩ := hspec'
      refine ⟨ht j hs, ?_⟩
      intro d x
      rcases eq_or_eq_otherCounter c d with hd | hd <;> subst d
      · simpa using toothAt_succ_iff_of_bounds hs (hc c) hu hl
          (b := (P.run j).counter c + 1) (by omega) (by omega) x
      · simpa [otherCounter_ne] using
          toothAt_succ_iff_of_bounds hs (hc (otherCounter c)) hu' hl'
            (b := (P.run j).counter (otherCounter c)) (by omega) (by omega) x
    | jzdec c z p =>
      obtain ⟨-, hz, hp, hu, hl, hn, hu', hl'⟩ := hspec'
      have hdec := toothAt_succ_iff_of_decrement hs (hc c) hu hl hn
      have hcopy := toothAt_succ_iff_of_bounds hs (hc (otherCounter c)) hu' hl'
        (b := (P.run j).counter (otherCounter c)) (by omega) (by omega)
      by_cases hc0 : (P.run j).counter c = 0
      · rw [Instr.exec_jzdec_of_eq_zero hc0]
        refine ⟨hz j hs (fun ht => ?_), ?_⟩
        · have := (hc c 1).mp ht
          omega
        · intro d x
          rcases eq_or_eq_otherCounter c d with rfl | rfl
          · simpa [hc0] using hdec x
          · exact hcopy x
      · rw [Instr.exec_jzdec_of_ne_zero hc0]
        refine ⟨hp j hs ((hc c 1).mpr (by omega)), ?_⟩
        intro d x
        rcases eq_or_eq_otherCounter c d with rfl | rfl
        · simpa using hdec x
        · simpa [otherCounter_ne] using hcopy x

/-- Trees satisfying the initial conditions and all specifications witness halting. -/
theorem halts_of_specs (h : InitialConditions P.length C U)
    (hspec : ∀ q ins, P[q]? = some ins → InstructionSpecs P.length C U q ins) : P.Halts := by
  obtain ⟨J, hJ⟩ := exists_halt_stub h
  by_contra hn
  have hlt : ∀ i, (P.run i).state < P.length := fun i => lt_of_not_ge fun hi => hn ⟨i, hi⟩
  obtain ⟨hstub, -⟩ := run_recorded h hspec J fun i _ => hlt i
  rw [min_eq_left (hlt J).le] at hstub
  obtain ⟨ins, hins⟩ : ∃ ins, P[(P.run J).state]? = some ins :=
    ⟨_, List.getElem?_eq_getElem (hlt J)⟩
  have hu : HaltUniqueSpec U P.length (P.run J).state := by
    have hs := hspec _ _ hins
    cases ins <;> exact hs.1
  exact hu J ⟨hstub, hJ⟩

/-- Soundness: the semantic content of the sentence implies halting. -/
theorem halts_of_machineConditions {c : TreeClass} {top : Bool} (hc : c ≠ .finite)
    (h : MachineConditions c top P) : P.Halts := by
  obtain ⟨C, U, -, -, hinit, hcl⟩ := h
  exact halts_of_specs hinit fun q ins hq =>
    instructionSpecs_of_clauses hc hinit.2.1 hinit.1 fun v hv => hcl v hv q ins hq

end Sentence

end UndeciSigma2
