import UndeciSigma2.Order

/-! # First-order syntax and prenex classes

Terms and formulas use bounded de Bruijn indices. The signature parameter
controls the availability of top. `IsSigma` and `IsPi` recognize syntactic
prenex form with at most the specified number of blocks, allowing empty
blocks and arbitrary quantifier-free matrices. Renaming and prenex negation
preserve satisfaction.
-/

namespace UndeciSigma2

/-- A structure specified by its tree domain and closure under the signature. -/
structure Structure (withTop : Bool) where
  domain : Tree → Prop
  bot_mem : domain Tree.bot
  top_mem : withTop = true → domain Tree.top
  f_mem : ∀ {a b}, domain a → domain b → domain (Tree.f a b)

namespace Structure
abbrev Elem {top : Bool} (M : Structure top) := {t : Tree // M.domain t}
instance {top : Bool} (M : Structure top) : Inhabited M.Elem := ⟨⟨_, M.bot_mem⟩⟩

/-- Each of the six intended structures is a nonempty model of the signature. -/
def ofClass (c : TreeClass) (top : Bool) : Structure top where
  domain := Domain c top
  bot_mem := domain_bot c top
  top_mem := by
    intro ht
    constructor
    · cases c <;> simp [Tree.finite_top, Tree.regular_top]
    · exact Or.inl ht
  f_mem := by
    intro a b ha hb
    apply domain_node
    intro i
    fin_cases i <;> assumption
end Structure

/-- Finite terms with `n` available variables. -/
inductive Term (withTop : Bool) (n : Nat) where
  | var : Fin n → Term withTop n
  | bot : Term withTop n
  | top : withTop = true → Term withTop n
  | f : Term withTop n → Term withTop n → Term withTop n
  deriving DecidableEq

namespace Term
variable {top : Bool} {n m : Nat}

def rename (σ : Fin n → Fin m) : Term top n → Term top m
  | .var i => .var (σ i)
  | .bot => .bot
  | .top h => .top h
  | .f s t => .f (s.rename σ) (t.rename σ)

/-- Evaluation stays inside the specified domain. -/
def eval (M : Structure top) (ρ : Fin n → M.Elem) : Term top n → M.Elem
  | .var i => ρ i
  | .bot => ⟨_, M.bot_mem⟩
  | .top h => ⟨_, M.top_mem h⟩
  | .f s t => ⟨Tree.f (s.eval M ρ) (t.eval M ρ), M.f_mem (s.eval M ρ).2 (t.eval M ρ).2⟩

@[simp] theorem eval_rename (M : Structure top) (ρ : Fin m → M.Elem)
    (σ : Fin n → Fin m) (t : Term top n) :
    (t.rename σ).eval M ρ = t.eval M (ρ ∘ σ) := by
  induction t <;> simp_all [rename, eval]
end Term

/-- First-order formulas. Equality is primitive for convenience; in these
structures it is equivalent to the conjunction of the two inequalities. -/
inductive Formula (withTop : Bool) : Nat → Type where
  | le {n} : Term withTop n → Term withTop n → Formula withTop n
  | eq {n} : Term withTop n → Term withTop n → Formula withTop n
  | truth {n} : Formula withTop n
  | falsity {n} : Formula withTop n
  | neg {n} : Formula withTop n → Formula withTop n
  | and {n} : Formula withTop n → Formula withTop n → Formula withTop n
  | or {n} : Formula withTop n → Formula withTop n → Formula withTop n
  | ex {n} : Formula withTop (n + 1) → Formula withTop n
  | all {n} : Formula withTop (n + 1) → Formula withTop n
  deriving DecidableEq

namespace Formula
variable {top : Bool} {n m : Nat}

/-- Implication introduces no additional quantifiers. -/
def imp (φ ψ : Formula top n) : Formula top n := .or (.neg φ) ψ

/-- Extend a renaming under a binder, preserving the bound variable zero. -/
def lift (σ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (σ i).succ)

def rename : {n m : Nat} → (Fin n → Fin m) → Formula top n → Formula top m
  | _, _, σ, .le s t => .le (s.rename σ) (t.rename σ)
  | _, _, σ, .eq s t => .eq (s.rename σ) (t.rename σ)
  | _, _, _, .truth => .truth
  | _, _, _, .falsity => .falsity
  | _, _, σ, .neg φ => .neg (φ.rename σ)
  | _, _, σ, .and φ ψ => .and (φ.rename σ) (ψ.rename σ)
  | _, _, σ, .or φ ψ => .or (φ.rename σ) (ψ.rename σ)
  | _, _, σ, .ex φ => .ex (φ.rename (lift σ))
  | _, _, σ, .all φ => .all (φ.rename (lift σ))

/-- Satisfaction with all free variables assigned elements of the domain. -/
def Realize (M : Structure top) : {n : Nat} → (Fin n → M.Elem) → Formula top n → Prop
  | _, ρ, .le s t => (s.eval M ρ : Tree) ≤ (t.eval M ρ : Tree)
  | _, ρ, .eq s t => s.eval M ρ = t.eval M ρ
  | _, _, .truth => True
  | _, _, .falsity => False
  | _, ρ, .neg φ => ¬φ.Realize M ρ
  | _, ρ, .and φ ψ => φ.Realize M ρ ∧ ψ.Realize M ρ
  | _, ρ, .or φ ψ => φ.Realize M ρ ∨ ψ.Realize M ρ
  | _, ρ, .ex φ => ∃ x : M.Elem, φ.Realize M (Fin.cases x ρ)
  | _, ρ, .all φ => ∀ x : M.Elem, φ.Realize M (Fin.cases x ρ)

/-- Truth of a closed sentence. -/
def Holds (M : Structure top) (φ : Formula top 0) : Prop :=
  φ.Realize M Fin.elim0

@[simp] theorem realize_rename (M : Structure top) (ρ : Fin m → M.Elem)
    (σ : Fin n → Fin m) (φ : Formula top n) :
    (φ.rename σ).Realize M ρ ↔ φ.Realize M (ρ ∘ σ) := by
  induction φ generalizing m with
  | le s t => simp [rename, Realize]
  | eq s t => simp [rename, Realize]
  | truth => rfl
  | falsity => rfl
  | neg φ ih => simp [rename, Realize, ih]
  | and φ ψ ihφ ihψ => simp [rename, Realize, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [rename, Realize, ihφ, ihψ]
  | ex φ ih =>
    simp only [rename, Realize, ih]
    apply exists_congr
    intro x
    have he : (Fin.cases x ρ) ∘ lift σ = Fin.cases x (ρ ∘ σ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he]
  | all φ ih =>
    simp only [rename, Realize, ih]
    apply forall_congr'
    intro x
    have he : (Fin.cases x ρ) ∘ lift σ = Fin.cases x (ρ ∘ σ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he]

theorem realize_eq_iff (M : Structure top) (ρ : Fin n → M.Elem) (s t : Term top n) :
    (.eq s t : Formula top n).Realize M ρ ↔
      (Formula.and (.le s t) (.le t s)).Realize M ρ := by
  simp only [Realize, Subtype.ext_iff]
  exact le_antisymm_iff

/-- Boolean matrices may contain negation, conjunction and disjunction freely. -/
def isMatrix : Formula top n → Bool
  | .le _ _ | .eq _ _ | .truth | .falsity => true
  | .neg φ => φ.isMatrix
  | .and φ ψ | .or φ ψ => φ.isMatrix && ψ.isMatrix
  | .ex _ | .all _ => false

/-- Extract the quantifiers of a prenex formula; `true` denotes existential. -/
def quantifiers : {n : Nat} → Formula top n → Option (List Bool)
  | _, .ex φ => (φ.quantifiers).map (true :: ·)
  | _, .all φ => (φ.quantifiers).map (false :: ·)
  | _, φ => if φ.isMatrix then some [] else none

/-- Minimum number of alternating blocks, allowing an empty initial block. -/
def blocks (start : Bool) : List Bool → Nat
  | [] => 0
  | q :: qs => (if q = start then 0 else 1) + max 1 (blocks q qs)

/-- Decidable membership in the Boolean prenex Σ hierarchy (at most `k` blocks). -/
def IsSigma (k : Nat) (φ : Formula top n) : Prop :=
  match φ.quantifiers with
  | none => False
  | some qs => blocks true qs ≤ k

/-- Decidable membership in the dual Π hierarchy. -/
def IsPi (k : Nat) (φ : Formula top n) : Prop :=
  match φ.quantifiers with
  | none => False
  | some qs => blocks false qs ≤ k

instance (k : Nat) (φ : Formula top n) : Decidable (IsSigma k φ) := by
  unfold IsSigma; split <;> infer_instance
instance (k : Nat) (φ : Formula top n) : Decidable (IsPi k φ) := by
  unfold IsPi; split <;> infer_instance

/-- A formula has an empty quantifier prefix exactly when it is quantifier-free. -/
theorem quantifiers_eq_nil_iff (φ : Formula top n) : φ.quantifiers = some [] ↔ φ.isMatrix = true := by
  cases φ <;> simp [quantifiers, isMatrix]
  split_ifs <;> simp_all

/-- Every Boolean matrix belongs to every level of both hierarchies. -/
theorem matrix_isSigma (φ : Formula top n) (h : φ.isMatrix = true) (k : Nat) :
    IsSigma k φ := by
  simp [IsSigma, (quantifiers_eq_nil_iff φ).mpr h, blocks]

theorem matrix_isPi (φ : Formula top n) (h : φ.isMatrix = true) (k : Nat) :
    IsPi k φ := by
  simp [IsPi, (quantifiers_eq_nil_iff φ).mpr h, blocks]

end Formula

end UndeciSigma2

namespace UndeciSigma2.Formula
variable {top : Bool} {n : Nat}

/-- Negate a prenex presentation by dualizing its quantifiers and negating its
Boolean matrix. This is an executable syntax transformation. -/
def negate : {n : Nat} → Formula top n → Formula top n
  | _, .ex φ => .all φ.negate
  | _, .all φ => .ex φ.negate
  | _, φ => .neg φ

theorem realize_negate (M : Structure top) (ρ : Fin n → M.Elem) (φ : Formula top n) :
    φ.negate.Realize M ρ ↔ ¬φ.Realize M ρ := by
  classical
  induction φ with
  | ex φ ih => simp [negate, Realize, ih]
  | all φ ih => simp [negate, Realize, ih]
  | _ => rfl

theorem quantifiers_negate (φ : Formula top n) :
    φ.negate.quantifiers = φ.quantifiers.map (List.map Bool.not) := by
  induction φ with
  | ex φ ih => simp [negate, quantifiers, ih, Option.map_map, Function.comp_def]
  | all φ ih => simp [negate, quantifiers, ih, Option.map_map, Function.comp_def]
  | neg φ _ =>
    simp only [negate, quantifiers, isMatrix]
    split_ifs <;> simp_all
  | _ => simp [negate, quantifiers, isMatrix]

theorem blocks_flip (start : Bool) (qs : List Bool) :
    blocks (!start) (qs.map Bool.not) = blocks start qs := by
  induction qs generalizing start with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, blocks]
    rw [ih q]
    cases q <;> cases start <;> rfl

/-- Prenex negation exchanges the Σ and Π levels without adding a block. -/
theorem isPi_negate_iff (k : Nat) (φ : Formula top n) :
    IsPi k φ.negate ↔ IsSigma k φ := by
  unfold IsPi IsSigma
  rw [quantifiers_negate]
  cases h : φ.quantifiers with
  | none => rfl
  | some qs =>
    simp only [Option.map_some]
    rw [show false = !true from rfl, blocks_flip]

theorem isSigma_negate_iff (k : Nat) (φ : Formula top n) :
    IsSigma k φ.negate ↔ IsPi k φ := by
  unfold IsPi IsSigma
  rw [quantifiers_negate]
  cases h : φ.quantifiers with
  | none => rfl
  | some qs =>
    simp only [Option.map_some]
    rw [show true = !false from rfl, blocks_flip]

theorem isSigma_mono {k l : Nat} {φ : Formula top n} (h : IsSigma k φ) (hkl : k ≤ l) :
    IsSigma l φ := by
  unfold IsSigma at *
  cases hq : φ.quantifiers with
  | none => simp [hq] at h
  | some qs =>
    simp only [hq] at h ⊢
    exact Nat.le_trans h hkl

theorem isPi_mono {k l : Nat} {φ : Formula top n} (h : IsPi k φ) (hkl : k ≤ l) :
    IsPi l φ := by
  unfold IsPi at *
  cases hq : φ.quantifiers with
  | none => simp [hq] at h
  | some qs =>
    simp only [hq] at h ⊢
    exact Nat.le_trans h hkl

/-- The standard two-block presentations with a Boolean matrix. -/
theorem isSigma_two (φ : Formula top (n + 1 + 1)) (h : φ.isMatrix = true) :
    IsSigma 2 (.ex (.all φ)) := by
  simp [IsSigma, quantifiers, (quantifiers_eq_nil_iff φ).mpr h, blocks]

theorem isPi_two (φ : Formula top (n + 1 + 1)) (h : φ.isMatrix = true) :
    IsPi 2 (.all (.ex φ)) := by
  simp [IsPi, quantifiers, (quantifiers_eq_nil_iff φ).mpr h, blocks]
end UndeciSigma2.Formula

namespace UndeciSigma2.Formula
variable {top : Bool} {n : Nat}

/-- Formulas built from inequality atoms, Boolean connectives, and quantifiers. -/
def IsLeOnly : {n : Nat} → Formula top n → Prop
  | _, .le _ _ => True
  | _, .eq _ _ | _, .truth | _, .falsity => False
  | _, .neg φ => φ.IsLeOnly
  | _, .and φ ψ | _, .or φ ψ => φ.IsLeOnly ∧ ψ.IsLeOnly
  | _, .ex φ | _, .all φ => φ.IsLeOnly

@[simp] theorem isLeOnly_imp {φ ψ : Formula top n} :
    (φ.imp ψ).IsLeOnly ↔ φ.IsLeOnly ∧ ψ.IsLeOnly := Iff.rfl

/-- Prenex negation keeps inequality as the only kind of atom. -/
theorem IsLeOnly.negate {φ : Formula top n} (h : φ.IsLeOnly) : φ.negate.IsLeOnly := by
  induction φ with
  | ex φ ih => exact ih h
  | all φ ih => exact ih h
  | _ => exact h
end UndeciSigma2.Formula
