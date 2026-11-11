import UndeciSigma2.Clauses.Specs

/-! # Complete direction of the clauses

For a state tree whose comb at `q` consists of stubs and a counter tree that is a
comb, each specification implies its clause for all top-free values of the universal
variables. If every disjunct of a clause fails, words `wᵢ` in the seeds `yᵢ` outside
the bounds `gᵢ` exist; the antecedent turns them into a tooth or a stub at a common
index `j`, and the specification at `j` gives a contradiction.
-/

namespace UndeciSigma2

open Word UndeciSigma2.Tree

namespace Sentence

variable {C : Fin 2 → Tree} {U : Tree}

/-! ## Reading the blocks -/

/-- The alignment block moves words of `y` along the right spine into `g`: removing
leading ones, or adding leading ones. -/
theorem AlignBlock.mem {y g d p : Tree} (hy : y.TopFree) (hg : g.TopFree) (hd : d.TopFree)
    (hp : p.TopFree) (h : AlignBlock full y g d p) :
    (∀ a v, 1 ≤ a → ones a ++ v ∈ y.constructorPaths → v ∈ g.constructorPaths) ∧
      (∀ b v, 1 ≤ b → v ∈ y.constructorPaths → ones b ++ v ∈ g.constructorPaths) ∧
      ∀ b, ones b ∈ g.constructorPaths := by
  obtain ⟨hyd, hdd, hdg, hyp, hpp, hpg⟩ := h
  have drop := (le_f_full_iff hd hd).mp hdd
  have push := ((f_bot_le_iff hp hp).mp hpp).2
  have dg := (le_iff_constructorPaths_subset hd hg).mp hdg
  have pg := (le_iff_constructorPaths_subset hp hg).mp hpg
  have drop_many : ∀ a v, ones a ++ v ∈ d.constructorPaths → v ∈ d.constructorPaths :=
    fun a _ hv => mem_of_ones_append_mem drop a hv
  have push_many : ∀ b v, v ∈ p.constructorPaths → ones b ++ v ∈ p.constructorPaths := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => exact fun v hv => push _ (ih v hv)
  refine ⟨?_, ?_, ?_⟩
  · intro a v ha hv
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    exact dg (drop_many a v ((le_f_full_iff hy hd).mp hyd _ hv))
  · intro b v hb hv
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    rw [ones_succ', List.append_assoc]
    exact pg (push_many b (1 :: v) (((f_bot_le_iff hy hp).mp hyp).2 v hv))
  · intro b
    simpa using pg (push_many b [] ((f_bot_le_iff hy hp).mp hyp).1)

/-- The comparison block with offset `δ` moves teeth of `y` up by `δ` into `g`. -/
theorem PopBlock.mem {δ : ℕ} {y g k k₀ kd kp : Tree} (hy : y.TopFree) (hg : g.TopFree)
    (hk : k.TopFree) (hk₀ : k₀.TopFree) (hkd : kd.TopFree) (hkp : kp.TopFree)
    (h : PopBlock full δ y g k k₀ kd kp) (j x : ℕ)
    (hx : tooth j (δ + x) ∈ y.constructorPaths) : tooth j x ∈ g.constructorPaths := by
  cases δ with
  | zero => exact (le_iff_constructorPaths_subset hy hg).mp h (by simpa using hx)
  | succ δ =>
    obtain ⟨hyk, hkk, hpop, hdp, hpp, hpg⟩ := h
    have hkf := (le_f_iff hk₀ hk hk).mp hkk
    have hxk := (le_iff_constructorPaths_subset hy hk).mp hyk hx
    have hz := hkf.1 _ (mem_of_ones_append_mem hkf.2 j hxk)
    have hd : zeros x ∈ kd.constructorPaths :=
      (le_popContext_iff hk₀ hkd (δ + 1)).mp hpop _ (by
        simpa [zeros_add] using hz)
    have hp0 : tooth 0 x ∈ kp.constructorPaths :=
      ((f_le_iff hkd topFree_bot hkp).mp hdp).2.1 _ hd
    have push := ((f_bot_le_iff hkp hkp).mp hpp).2
    have hpj : ∀ j, tooth j x ∈ kp.constructorPaths := by
      intro j
      induction j with
      | zero => exact hp0
      | succ j ih => exact push _ ih
    exact (le_iff_constructorPaths_subset hkp hg).mp hpg (hpj j)

private theorem paths_mono {a b : Tree} (ha : a.TopFree) (hb : b.TopFree)
    (h : a ≤ b) {w : Word} (hw : w ∈ a.constructorPaths) : w ∈ b.constructorPaths :=
  (le_iff_constructorPaths_subset ha hb).mp h hw

private theorem spine_mem {g : Tree} (hg : g.TopFree) (h : rightRay ≤ g)
    {w : Word} (hw : IsOnes w) : w ∈ g.constructorPaths :=
  paths_mono topFree_rightRay hg h ((mem_constructorPaths_rightRay w).mpr hw)

private theorem packed_stub {y g U : Tree} {q : ℕ} (hy : y.TopFree) (hU : U.TopFree)
    (hshape : StubShaped U q) (hpack : pack q y ≤ U)
    (hspine : ∀ b, ones b ∈ g.constructorPaths) {w : Word}
    (hw : w ∈ y.constructorPaths) (hout : w ∉ g.constructorPaths) :
    ∃ j, w = stub j ∧ StubAt U q j := by
  have hu := ((pack_le_iff hy hU q).mp hpack).2 w hw
  rcases hshape w hu with hs | ⟨j, rfl⟩
  · obtain ⟨b, rfl⟩ := (isOnes_iff w).mp hs
    exact False.elim (hout (hspine b))
  · exact ⟨j, rfl, hu⟩

/-- A seed tooth and an excluded stub have the same index under alignment. -/
theorem AlignBlock.index_eq {y g d p : Tree} (hy : y.TopFree) (hg : g.TopFree)
    (hd : d.TopFree) (hp : p.TopFree) (h : AlignBlock full y g d p)
    {j x b : ℕ} (hw : tooth j x ∈ y.constructorPaths) (hout : stub b ∉ g.constructorPaths) :
    j = b := by
  have hs := mem_constructorPaths_of_prefix (stub_prefix_tooth j x) hw
  obtain ⟨hdrop, hpush, -⟩ := h.mem hy hg hd hp
  rcases lt_trichotomy j b with hlt | heq | hlt
  · apply False.elim
    apply hout
    have := hpush (b - j) (stub j) (by omega) hs
    simpa [ones_append_stub, Nat.sub_add_cancel (by omega : j ≤ b)] using this
  · exact heq
  · apply False.elim
    apply hout
    apply hdrop (j - b) (stub b) (by omega)
    simpa [ones_append_stub, Nat.sub_add_cancel (by omega : b ≤ j)] using hs

private theorem tail_comb {C : Tree} (hc : IsComb C) {w : Word}
    (hw : 1 :: w ∈ C.constructorPaths) (hn : ¬IsOnes w) :
    ∃ j x, w = tooth j x := by
  rcases hc _ hw with hs | ⟨j, x, he⟩
  · exact False.elim (hn ((isOnes_cons _ _).mp hs).2)
  · cases j with
    | zero => simp at he
    | succ j => exact ⟨j, x, List.cons.inj he |>.2⟩

/-! ## The clauses -/

variable {i : Fin 2} {v : Universals Tree}

/-- The upper-bound specification implies the clause for a stub-shaped state and a counter comb. -/
theorem upperBoundClause_complete (hU : U.TopFree) (hC : (C i).TopFree) {δ : ℕ} {trunc : Bool}
    {q : ℕ} (hshape : StubShaped U q) (hcomb : IsComb (C i))
    (hspec : UpperBoundSpec U (C i) δ trunc q) (hv : v.Forall Tree.TopFree) :
    UpperBoundClause (Existentials.standard C U) v δ trunc q i := by
  classical
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hyG, hCg, hS, hyC, hpop, hT, hpack, ha₁, ha₂⟩
  by_contra hn
  obtain ⟨hn₁, hn₂, hn₃⟩ := not_or.mp hn |>.imp_right not_or.mp
  obtain ⟨w₁, hw₁, ho₁⟩ := (not_le_iff_exists hy₁ hg₁).mp hn₁
  obtain ⟨w₂, hw₂, ho₂⟩ := (not_le_iff_exists hy₂ hg₂).mp hn₂
  obtain ⟨w₃, hw₃, ho₃⟩ := (not_le_iff_exists hy₃ hg₃).mp hn₃
  have a₁ := ha₁.mem hy₁ hg₃ hd₁ hp₁
  obtain ⟨j, rfl, hstate⟩ := packed_stub hy₃ hU hshape hpack a₁.2.2 hw₃ ho₃
  have hnw₁ : ¬IsOnes w₁ := fun hs => ho₁ (spine_mem hg₁ hS hs)
  obtain ⟨j₁, x₁, rfl⟩ := ((mem_constructorPaths_combUniverse _).mp
    (paths_mono hy₁ topFree_combUniverse hyG hw₁)).resolve_left hnw₁
  have hsp₂ : ∀ w, IsOnes w → w ∈ v.g₂.constructorPaths := by
    intro w hs
    cases trunc
    · exact spine_mem hg₂ hT hs
    · exact paths_mono topFree_stubComb hg₂ hT ((mem_constructorPaths_stubComb _).mpr (.inl hs))
  have hc₂ := ((f_bot_le_iff hy₂ hC).mp hyC).2 w₂ hw₂
  obtain ⟨j₂, x₂, rfl⟩ := tail_comb hcomb hc₂ (fun hs => ho₂ (hsp₂ _ hs))
  have hj₁ := ha₁.index_eq hy₁ hg₃ hd₁ hp₁ hw₁ ho₃
  have hj₂ := ha₂.index_eq hy₂ hg₃ hd₂ hp₂ hw₂ ho₃
  subst j₁
  subst j₂
  have htrunc : trunc = true → 1 ≤ x₂ := by
    intro ht
    subst trunc
    by_contra hx
    have hx0 : x₂ = 0 := by omega
    subst x₂
    exact ho₂ (paths_mono topFree_stubComb hg₂ hT
      ((mem_constructorPaths_stubComb _).mpr (.inr ⟨j, rfl⟩)))
  have hnum := hspec j x₁ x₂ hstate
    (fun hc => ho₁ (paths_mono hC hg₁ hCg hc)) hc₂ htrunc
  have hprefix : tooth j (δ + x₂) ∈ v.y₁.constructorPaths :=
    mem_constructorPaths_of_prefix (tooth_prefix_tooth_iff.mpr ⟨rfl, by omega⟩) hw₁
  exact ho₂ (hpop.mem hy₁ hg₂ hk hk₀ hkd hkp j x₂ hprefix)

/-- The lower-bound specification implies the clause for a stub-shaped state and a counter comb. -/
theorem lowerBoundClause_complete (hU : U.TopFree) (hC : (C i).TopFree) {δ q : ℕ}
    (hshape : StubShaped U q) (hcomb : IsComb (C i)) (hspec : LowerBoundSpec U (C i) δ q)
    (hv : v.Forall Tree.TopFree) :
    LowerBoundClause (Existentials.standard C U) v δ q i := by
  classical
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hyC, hpop, hS₁, hyG, hCg, hS₂, hpack, ha₁, ha₂⟩
  by_contra hn
  obtain ⟨hn₁, hn₂, hn₃⟩ := not_or.mp hn |>.imp_right not_or.mp
  obtain ⟨w₁, hw₁, ho₁⟩ := (not_le_iff_exists hy₁ hg₁).mp hn₁
  obtain ⟨w₂, hw₂, ho₂⟩ := (not_le_iff_exists hy₂ hg₂).mp hn₂
  obtain ⟨w₃, hw₃, ho₃⟩ := (not_le_iff_exists hy₃ hg₃).mp hn₃
  obtain ⟨j, rfl, hstate⟩ := packed_stub hy₃ hU hshape hpack
    (ha₁.mem hy₁ hg₃ hd₁ hp₁).2.2 hw₃ ho₃
  have hc₁ := paths_mono hy₁ hC hyC hw₁
  obtain ⟨j₁, x₁, rfl⟩ := (hcomb w₁ hc₁).resolve_left
    (fun hs => ho₁ (spine_mem hg₁ hS₁ hs))
  obtain ⟨j₂, x₂, rfl⟩ := ((mem_constructorPaths_combUniverse _).mp
    (paths_mono hy₂ topFree_combUniverse hyG hw₂)).resolve_left
    (fun hs => ho₂ (spine_mem hg₂ hS₂ hs))
  have hj₁ := ha₁.index_eq hy₁ hg₃ hd₁ hp₁ hw₁ ho₃
  have hj₂ := ha₂.index_eq hy₂ hg₃ hd₂ hp₂ hw₂ ho₃
  subst j₁
  subst j₂
  have hnum := hspec j x₁ x₂ hstate hc₁
    (fun hc => ho₂ ((le_f_full_iff hC hg₂).mp hCg _ hc))
  have hprefix : tooth j (δ + x₁) ∈ v.y₂.constructorPaths :=
    mem_constructorPaths_of_prefix (tooth_prefix_tooth_iff.mpr ⟨rfl, by omega⟩) hw₂
  exact ho₁ (hpop.mem hy₂ hg₁ hk hk₀ hkd hkp j x₁ hprefix)

/-- The transition specification sends every seed stub into the target bound. -/
theorem transitionClause_complete (hU : U.TopFree) {q r : ℕ} (hshape : StubShaped U q)
    (hspec : TransitionSpec U q r) (hv : v.Forall Tree.TopFree) :
    TransitionClause (Existentials.standard C U) v q r := by
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hpack, hctx, hsp⟩
  apply (le_iff_constructorPaths_subset hy₁ hg₁).mpr
  intro w hw
  have hu := ((pack_le_iff hy₁ hU q).mp hpack).2 w hw
  rcases hshape w hu with hs | ⟨j, rfl⟩
  · exact spine_mem hg₁ hsp hs
  · exact (le_stateContext_iff hU hg₁ r).mp hctx _ (hspec j hu)

/-- The next-tooth specification sends every seed stub into the counter tail. -/
theorem nextToothClause_complete (hU : U.TopFree) (hC : (C i).TopFree) {q : ℕ}
    (hshape : StubShaped U q) (hspec : NextToothSpec U (C i) q) (hv : v.Forall Tree.TopFree) :
    NextToothClause (Existentials.standard C U) v q i := by
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hpack, hctx, hsp⟩
  apply (le_iff_constructorPaths_subset hy₁ hg₁).mpr
  intro w hw
  have hu := ((pack_le_iff hy₁ hU q).mp hpack).2 w hw
  rcases hshape w hu with hs | ⟨j, rfl⟩
  · exact spine_mem hg₁ hsp hs
  · exact (le_f_full_iff hC hg₁).mp hctx _ (hspec j hu)

/-- Disjoint state stubs force a seed packed at both states to lie on the right ray. -/
theorem haltUniqueClause_complete (hU : U.TopFree) {n q : ℕ} (hshape : StubShaped U q)
    (hspec : HaltUniqueSpec U n q) (hv : v.Forall Tree.TopFree) :
    HaltUniqueClause (Existentials.standard C U) v n q := by
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hpack, hhalt⟩
  apply (le_iff_constructorPaths_subset hy₁ topFree_rightRay).mpr
  intro w hw
  have hu := ((pack_le_iff hy₁ hU q).mp hpack).2 w hw
  rcases hshape w hu with hs | ⟨j, rfl⟩
  · exact (mem_constructorPaths_rightRay _).mpr hs
  · exact False.elim (hspec j ⟨hu, ((pack_le_iff hy₁ hU n).mp hhalt).2 _ hw⟩)

/-- The zero-test specification implies the clause for a stub-shaped state tree. -/
theorem zeroTestClause_complete (hU : U.TopFree) (hC : (C i).TopFree) {q r : ℕ}
    (hshape : StubShaped U q) (hspec : ZeroTestSpec U (C i) q r) (hv : v.Forall Tree.TopFree) :
    ZeroTestClause (Existentials.standard C U) v q r i := by
  classical
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hyG, hCg, hT, hpack, hctx, ha⟩
  by_contra hn
  obtain ⟨hn₁, hn₃⟩ := not_or.mp hn
  obtain ⟨w₁, hw₁, ho₁⟩ := (not_le_iff_exists hy₁ hg₁).mp hn₁
  obtain ⟨w₃, hw₃, ho₃⟩ := (not_le_iff_exists hy₃ hg₃).mp hn₃
  obtain ⟨j, rfl, hstate⟩ := packed_stub hy₃ hU hshape hpack
    (ha.mem hy₁ hg₃ hd₁ hp₁).2.2 hw₃ ho₃
  have hout : w₁ ∉ stubComb.constructorPaths :=
    fun hm => ho₁ (paths_mono topFree_stubComb hg₁ hT hm)
  have hword : ∃ b, w₁ = tooth b 1 := by
    rcases (mem_constructorPaths_shortCombs _).mp
        (paths_mono hy₁ topFree_shortCombs hyG hw₁) with hs | ⟨b, hb | hb⟩
    · exact False.elim (hout ((mem_constructorPaths_stubComb _).mpr (.inl hs)))
    · exact False.elim (hout ((mem_constructorPaths_stubComb _).mpr (.inr ⟨b, hb⟩)))
    · exact ⟨b, hb⟩
  obtain ⟨b, rfl⟩ := hword
  have hb := ha.index_eq hy₁ hg₃ hd₁ hp₁ hw₁ ho₃
  subst b
  have hnC : ¬ToothAt (C i) j 1 := fun hc => ho₁ (paths_mono hC hg₁ hCg hc)
  exact ho₃ ((le_stateContext_iff hU hg₃ r).mp hctx _ (hspec j hstate hnC))

/-- The positive-test specification implies the clause for a stub-shaped state tree. -/
theorem positiveTestClause_complete (hU : U.TopFree) (hC : (C i).TopFree) {q r : ℕ}
    (hshape : StubShaped U q) (hspec : PositiveTestSpec U (C i) q r)
    (hv : v.Forall Tree.TopFree) :
    PositiveTestClause (Existentials.standard C U) v q r i := by
  classical
  obtain ⟨hy₁, hy₂, hy₃, hg₁, hg₂, hg₃, hk, hk₀, hkd, hkp, hd₁, hp₁, hd₂, hp₂⟩ := hv
  rintro ⟨hyC, hyG, hpack, hctx, ha⟩
  by_contra hn
  obtain ⟨hn₂, hn₃⟩ := not_or.mp hn
  obtain ⟨w₂, hw₂, ho₂⟩ := (not_le_iff_exists hy₂ topFree_stubComb).mp hn₂
  obtain ⟨w₃, hw₃, ho₃⟩ := (not_le_iff_exists hy₃ hg₃).mp hn₃
  obtain ⟨j, rfl, hstate⟩ := packed_stub hy₃ hU hshape hpack
    (ha.mem hy₂ hg₃ hd₂ hp₂).2.2 hw₃ ho₃
  obtain ⟨b, x, rfl⟩ := ((mem_constructorPaths_combUniverse _).mp
    (paths_mono hy₂ topFree_combUniverse hyG hw₂)).resolve_left
    (fun hs => ho₂ ((mem_constructorPaths_stubComb _).mpr (.inl hs)))
  have hb := ha.index_eq hy₂ hg₃ hd₂ hp₂ hw₂ ho₃
  subst b
  have hx : 1 ≤ x := by
    by_contra hx
    have hx0 : x = 0 := by omega
    subst x
    exact ho₂ ((mem_constructorPaths_stubComb _).mpr (.inr ⟨j, rfl⟩))
  have hc : ToothAt (C i) j 1 := paths_mono hy₂ hC hyC
    (mem_constructorPaths_of_prefix (tooth_prefix_tooth_iff.mpr ⟨rfl, hx⟩) hw₂)
  exact ho₃ ((le_stateContext_iff hU hg₃ r).mp hctx _ (hspec j hstate hc))

/-- The specifications of an instruction imply its clauses. -/
theorem instructionClauses_of_specs (hU : U.TopFree) (hC : ∀ i, (C i).TopFree)
    (hcomb : ∀ i, IsComb (C i)) {n q : ℕ} (hshape : StubShaped U q) {ins : Instr}
    (h : InstructionSpecs n C U q ins) (hv : v.Forall Tree.TopFree) :
    InstructionClauses (Existentials.standard C U) v n q ins := by
  cases ins with
  | inc d r =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨haltUniqueClause_complete hU hshape h1 hv,
      transitionClause_complete hU hshape h2 hv,
      upperBoundClause_complete hU (hC d) hshape (hcomb d) h3 hv,
      lowerBoundClause_complete hU (hC d) hshape (hcomb d) h4 hv,
      upperBoundClause_complete hU (hC _) hshape (hcomb _) h5 hv,
      lowerBoundClause_complete hU (hC _) hshape (hcomb _) h6 hv⟩
  | jzdec d z p =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨haltUniqueClause_complete hU hshape h1 hv,
      zeroTestClause_complete hU (hC d) hshape h2 hv,
      positiveTestClause_complete hU (hC d) hshape h3 hv,
      upperBoundClause_complete hU (hC d) hshape (hcomb d) h4 hv,
      lowerBoundClause_complete hU (hC d) hshape (hcomb d) h5 hv,
      nextToothClause_complete hU (hC d) hshape h6 hv,
      upperBoundClause_complete hU (hC _) hshape (hcomb _) h7 hv,
      lowerBoundClause_complete hU (hC _) hshape (hcomb _) h8 hv⟩

end Sentence

end UndeciSigma2
