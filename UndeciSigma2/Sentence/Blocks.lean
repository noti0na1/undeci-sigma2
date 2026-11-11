import UndeciSigma2.Syntax

/-! # Finite quantifier blocks

Finite vectors extend environments at the lowest de Bruijn indices.
The satisfaction and prefix lemmas describe iterated existential and
universal quantifiers.
-/
namespace UndeciSigma2.Sentence

/-- Prepend a finite vector of bound values to an environment. -/
def env {α : Type*} {n k : Nat} (v : Fin k → α) (ρ : Fin n → α) : Fin (n + k) → α :=
  fun i => if h : i.val < k then v ⟨i.val, h⟩ else ρ ⟨i.val - k, by omega⟩

@[simp] theorem env_zero {α : Type*} {n : Nat} (v : Fin 0 → α) (ρ : Fin n → α) :
    env v ρ = ρ := by funext i; simp [env]

@[simp] theorem env_front {α : Type*} {n k : Nat} (v : Fin k → α) (ρ : Fin n → α)
    (i : Fin k) : env v ρ ⟨i.val, by omega⟩ = v i := by
  simp [env, i.isLt]

@[simp] theorem env_back {α : Type*} {n k : Nat} (v : Fin k → α) (ρ : Fin n → α)
    (i : Fin n) : env v ρ (i.addNat k) = ρ i := by
  simp [env, show ¬i.val + k < k by omega]

theorem env_cons {α : Type*} {n k : Nat} (a : α) (v : Fin k → α) (ρ : Fin n → α) :
    env (Fin.cases a v) ρ = Fin.cases a (env v ρ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [env]
  · have hj : j.val < n + k := j.isLt
    change (if h : j.val + 1 < k + 1 then
        Fin.cases a v ⟨j.val + 1, h⟩ else ρ ⟨j.val + 1 - (k + 1), by omega⟩) = env v ρ j
    by_cases h : j.val < k
    · rw [dite_eq_left (show j.val + 1 < k + 1 by omega)]
      change v ⟨j.val, h⟩ = env v ρ j
      simp [env, h]
    · simp [env, h, show ¬j.val + 1 < k + 1 by omega]

def exs {top : Bool} {n : Nat} : (k : Nat) → Formula top (n + k) → Formula top n
  | 0, φ => φ
  | k + 1, φ => exs k (.ex φ)

def alls {top : Bool} {n : Nat} : (k : Nat) → Formula top (n + k) → Formula top n
  | 0, φ => φ
  | k + 1, φ => alls k (.all φ)

@[simp] theorem realize_exs {top : Bool} {n k : Nat} (M : Structure top)
    (ρ : Fin n → M.Elem) (φ : Formula top (n + k)) :
    (exs k φ).Realize M ρ ↔ ∃ v : Fin k → M.Elem, φ.Realize M (env v ρ) := by
  induction k with
  | zero => simp [exs]
  | succ k ih =>
    rw [exs, ih]
    simp only [Formula.Realize]
    constructor
    · rintro ⟨v, a, ha⟩
      exact ⟨Fin.cases a v, by rw [env_cons]; exact ha⟩
    · rintro ⟨v, hv⟩
      refine ⟨fun i => v i.succ, v 0, ?_⟩
      have he : v = Fin.cases (v 0) (fun i => v i.succ) := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      rw [he, env_cons] at hv
      exact hv

@[simp] theorem realize_alls {top : Bool} {n k : Nat} (M : Structure top)
    (ρ : Fin n → M.Elem) (φ : Formula top (n + k)) :
    (alls k φ).Realize M ρ ↔ ∀ v : Fin k → M.Elem, φ.Realize M (env v ρ) := by
  induction k with
  | zero => simp [alls]
  | succ k ih =>
    rw [alls, ih]
    simp only [Formula.Realize]
    constructor
    · intro h v
      have he : v = Fin.cases (v 0) (fun i => v i.succ) := by
        funext i; exact Fin.cases rfl (fun _ => rfl) i
      rw [he, env_cons]
      exact h (fun i => v i.succ) (v 0)
    · intro h v a
      have hh := h (Fin.cases a v)
      rw [env_cons] at hh
      exact hh

theorem quantifiers_exs {top : Bool} {n k : Nat} (φ : Formula top (n + k)) :
    (exs k φ).quantifiers = φ.quantifiers.map (List.replicate k true ++ ·) := by
  induction k with
  | zero => simp [exs]
  | succ k ih =>
    simp only [exs, ih, Formula.quantifiers, Option.map_map]
    congr 1
    funext qs
    simp [List.replicate_succ', List.append_assoc]

theorem quantifiers_alls {top : Bool} {n k : Nat} (φ : Formula top (n + k)) :
    (alls k φ).quantifiers = φ.quantifiers.map (List.replicate k false ++ ·) := by
  induction k with
  | zero => simp [alls]
  | succ k ih =>
    simp only [alls, ih, Formula.quantifiers, Option.map_map]
    congr 1
    funext qs
    simp [List.replicate_succ', List.append_assoc]

end UndeciSigma2.Sentence

namespace UndeciSigma2.Sentence

@[simp] theorem isLeOnly_exs {top : Bool} {n k : Nat} (φ : Formula top (n + k)) :
    (exs k φ).IsLeOnly ↔ φ.IsLeOnly := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem isLeOnly_alls {top : Bool} {n k : Nat} (φ : Formula top (n + k)) :
    (alls k φ).IsLeOnly ↔ φ.IsLeOnly := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _

end UndeciSigma2.Sentence
