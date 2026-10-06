import R0FS.Protocol

/-! # (D1), (D2), (D3) and the verifier property for R0

(D2) per round: the state flips only when the fresh challenge lands in the
round's ledger bad set; its density is the bad set's cardinality times the
sampler's point mass.  (D3): a doomed complete transcript has every challenge
outside its bad set, so `binding` would produce a witness — contradiction
with doomedness, hence the verifier cannot accept. -/
set_option autoImplicit false
namespace R0FS

open FS AspisR0.ListsResponses AspisR0.Fold AspisR0.Chord
open AspisR0.ChordGeometry AspisR0.RootCounts AspisR0.RoundNormalization
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisPool.AlgorithmicCircleDecoderV7 AspisV6Width29CorrelatedAgreement
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisR0.Opening hiding indicator
open Polynomial
open scoped BigOperators
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}

/-! ## Generic mean lemmas -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem mean_finset_sum {A X : Type} [Fintype A] (S : Finset X) (g : X → A → ℚ) :
    mean (fun a => ∑ c ∈ S, g c a) = ∑ c ∈ S, mean (g c) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem indicator_exists_field {A : Type} (f : A → Chal E) (S : Finset E) (a : A) :
    indicator (∃ c, f a = .field c ∧ c ∈ S) = ∑ c ∈ S, indicator (f a = .field c) := by
  classical
  cases hf : f a with
  | field d =>
      have h1 : (∃ c, Chal.field d = Chal.field c ∧ c ∈ S) ↔ d ∈ S := by
        constructor
        · rintro ⟨c, hc, hcS⟩; cases hc; exact hcS
        · intro hd; exact ⟨d, rfl, hd⟩
      have h2 : ∀ c, indicator (Chal.field d = Chal.field c) = indicator (d = c) := fun c =>
        indicator_iff ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩
      rw [indicator_iff h1]
      simp only [h2]
      unfold indicator
      simp
  | set S' =>
      have h1 : ¬ ∃ c, Chal.set S' = Chal.field c ∧ c ∈ S := by
        rintro ⟨c, hc, _⟩; cases hc
      rw [indicator_iff (iff_false_intro h1), indicator_false]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [indicator_iff (iff_false_intro (by intro h; cases h)), indicator_false]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem mean_exists_field_le {A : Type} [Fintype A] (f : A → Chal E) (S : Finset E) (c0 : ℚ)
    (h : ∀ c, mean (fun a => indicator (f a = .field c)) ≤ c0) :
    mean (fun a => indicator (∃ c, f a = .field c ∧ c ∈ S)) ≤ (S.card : ℚ) * c0 := by
  rw [mean_congr (fun a => indicator_exists_field f S a), mean_finset_sum]
  calc (∑ c ∈ S, mean (fun a => indicator (f a = .field c))) ≤ ∑ _c ∈ S, c0 :=
        Finset.sum_le_sum fun c _ => h c
    _ = (S.card : ℚ) * c0 := by simp

omit [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem mean_indicator_false {A : Type} [Fintype A] [Nonempty A] :
    mean (fun _ : A => indicator False) = 0 := by
  rw [indicator_false]; exact mean_const 0

omit [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem card_E_pos : (0 : ℚ) < (Fintype.card E : ℚ) - 1 := by
  have : 1 < Fintype.card E := Fintype.one_lt_card
  have h : (1 : ℚ) < (Fintype.card E : ℚ) := by exact_mod_cast this
  linarith

omit [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem ε_nonneg (i : Nat) : 0 ≤ ε E i := by
  have hpos := card_E_pos (E := E)
  have hc : (0 : ℚ) ≤ (Fintype.card E : ℚ) := Nat.cast_nonneg _
  match i with
  | 0 => exact div_nonneg (by norm_num) hpos.le
  | 1 => exact div_nonneg (by norm_num) hc
  | 2 => exact div_nonneg (by norm_num) hc
  | 3 => exact div_nonneg (by norm_num) hc
  | 4 => exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  | n + 5 => exact le_refl 0

/-! ## List lemmas for the state function -/

theorem goodFrom_append (x : Stmt E Sfield) (m : Msg E) (c : Chal E) :
    ∀ (l prev : List (Msg E × Chal E)),
      goodFrom x prev (l ++ [(m, c)]) ↔ goodFrom x prev l ∨ roundBad x (prev ++ l) m c := by
  intro l
  induction l with
  | nil => intro prev; simp [goodFrom]
  | cons q rest ih =>
      intro prev
      obtain ⟨m', c'⟩ := q
      simp only [List.cons_append, goodFrom, ih (prev ++ [(m', c')]), List.append_assoc]
      tauto

theorem good_append (x : Stmt E Sfield) (l : List (Msg E × Chal E)) (m : Msg E) (c : Chal E) :
    good x (l ++ [(m, c)]) ↔ good x l ∨ roundBad x l m c := by
  unfold good
  rw [goodFrom_append]
  simp

/-- Shape lemmas: `roundBad` on each protocol shape. -/
theorem rb0 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (c : Chal E) :
    roundBad x [] (.values y) c ↔ ∃ γ, c = .field γ ∧ γ ∈ bad0 x y := by
  simp [roundBad]

theorem rb1 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v : E) (c : Chal E) :
    roundBad x [(.values y, .field γ)] (.scalar v) c ↔ ∃ κ, c = .field κ ∧ κ ∈ bad1 x y γ v := by
  simp [roundBad]

theorem rb2 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v κ : E) (c : Chal E) :
    roundBad x [(.values y, .field γ), (.scalar v, .field κ)] .unit c ↔
      ∃ τ, c = .field τ ∧ τ ∈ bad2 x y γ v κ := by
  simp [roundBad]

theorem rb3 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v κ τ : E) (P : E[X]) (c : Chal E) :
    roundBad x [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] (.poly P) c ↔
      ∃ α, c = .field α ∧ α ∈ bad3 x y γ κ τ P := by
  simp [roundBad]

theorem rb4 (x : Stmt E Sfield) (y : Fin 29 → Fin 2 → E) (γ v κ τ α : E) (P : E[X])
    (F : FinalMessage E) (c : Chal E) :
    roundBad x [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ), (.poly P, .field α)]
      (.final F) c ↔ ∃ S, c = .set S ∧ bad4 x y γ α F S := by
  simp [roundBad]

/-- The length of a bad round's prefix fixes its shape. -/
theorem roundBad_shape (x : Stmt E Sfield) (l : List (Msg E × Chal E)) (m : Msg E) (c : Chal E)
    (h : roundBad x l m c) :
    (l.length = 0 ∧ ∃ y, l = [] ∧ m = .values y) ∨
    (l.length = 1 ∧ ∃ y γ v, l = [(.values y, .field γ)] ∧ m = .scalar v) ∨
    (l.length = 2 ∧ ∃ y γ v κ, l = [(.values y, .field γ), (.scalar v, .field κ)] ∧ m = .unit) ∨
    (l.length = 3 ∧ ∃ y γ v κ τ P,
      l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] ∧ m = .poly P) ∨
    (l.length = 4 ∧ ∃ y γ v κ τ P α F, l = [(.values y, .field γ), (.scalar v, .field κ),
      (.unit, .field τ), (.poly P, .field α)] ∧ m = .final F) := by
  rcases h with ⟨y, γ, hl, hm, _, _⟩ | ⟨y, γ, v, κ, hl, hm, _, _⟩ | ⟨y, γ, v, κ, τ, hl, hm, _, _⟩ |
    ⟨y, γ, v, κ, τ, P, α, hl, hm, _, _⟩ | ⟨y, γ, v, κ, τ, P, α, F, S, hl, hm, _, _⟩
  · exact Or.inl ⟨by subst hl; rfl, y, hl, hm⟩
  · exact Or.inr (Or.inl ⟨by subst hl; rfl, y, γ, v, hl, hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by subst hl; rfl, y, γ, v, κ, hl, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by subst hl; rfl, y, γ, v, κ, τ, P, hl, hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by subst hl; rfl, y, γ, v, κ, τ, P, α, F, hl, hm⟩)))

/-! ## (D1) -/

variable {Pf I B : Type} {Kw : Nat}

theorem d1 (p : Params E Sfield Pf I B Kw) : D1 (protocol p) (roundByRound p) := by
  intro x T hx
  have e : (protocol p).extract x T = extract x T := by simp only [protocol]
  rw [e] at hx
  have h2 : ¬ ∃ t, Witness x t := (extract_eq_none_iff x T).mp hx
  simp only [roundByRound]
  exact ⟨h2, fun h => h⟩

/-! ## (D2) -/

section D2
variable [Fintype B] [Nonempty B]

omit [Nonempty B] in
/-- The flip density of one round is the density of its `roundBad`. -/
theorem flip_density (p : Params E Sfield Pf I B Kw) (i : Nat)
    (P : Prefix (Stmt E Sfield) (Msg E) (Chal E)) (m : Msg E) (T' T : Table I (Block B Kw))
    (hd : doomed P T') :
    mean (fun a : Fin (p.k i) → B =>
        indicator (¬ doomed (P.ext m (p.sampler i a)) T)) =
      mean (fun a : Fin (p.k i) → B => indicator (roundBad P.statement P.rounds m (p.sampler i a))) := by
  apply mean_congr
  intro a
  apply indicator_iff
  obtain ⟨hw, hg⟩ := hd
  simp only [doomed, Prefix.ext, good_append, not_and, not_not]
  constructor
  · intro h
    rcases h hw with h | h
    · exact absurd h hg
    · exact h
  · intro h _
    exact Or.inr h

/-- Off the round's shape nothing flips. -/
theorem mean_roundBad_zero (p : Params E Sfield Pf I B Kw) (i : Nat) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (m : Msg E) (hnone : ∀ c, ¬ roundBad x l m c) :
    mean (fun a : Fin (p.k i) → B => indicator (roundBad x l m (p.sampler i a))) = 0 := by
  rw [mean_congr fun a => indicator_iff (iff_false_intro (hnone _)), mean_indicator_false]

theorem d2_round0 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 0) (m : Msg E) :
    mean (fun a : Fin (p.k 0) → B => indicator (roundBad x l m (p.sampler 0 a))) ≤ ε E 0 := by
  by_cases hshape : ∃ y, l = [] ∧ m = .values y
  · obtain ⟨y, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 0) → B => indicator (roundBad x [] (.values y) (p.sampler 0 a)))
        = mean (fun a : Fin (p.k 0) → B =>
            indicator (∃ γ, p.sampler 0 a = .field γ ∧ γ ∈ bad0 x y)) :=
          mean_congr fun a => indicator_iff (rb0 x y _)
      _ ≤ ((bad0 x y).card : ℚ) * (1 / ((Fintype.card E : ℚ) - 1)) :=
          mean_exists_field_le _ _ _ hs.gamma
      _ ≤ ε E 0 := by
          have hc : (bad0 x y).card ≤ 336869026605739 + 14000 := by
            have := (grouped_cardinalities (data x y) 0 0 0 0 0 (by simp)).1
            simpa [bad0] using this
          have hpos := card_E_pos (E := E)
          show _ ≤ (336869026605739 + 14000 : ℚ) / ((Fintype.card E : ℚ) - 1)
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ hpos.le
          exact_mod_cast hc
  · rw [mean_roundBad_zero]
    · exact ε_nonneg 0
    · intro c h
      rcases roundBad_shape x l m c h with ⟨_, y, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hshape ⟨y, hl', hm⟩
      all_goals omega

theorem d2_round1 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 1) (m : Msg E) :
    mean (fun a : Fin (p.k 1) → B => indicator (roundBad x l m (p.sampler 1 a))) ≤ ε E 1 := by
  by_cases hshape : ∃ y γ v, l = [(.values y, .field γ)] ∧ m = .scalar v
  · obtain ⟨y, γ, v, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 1) → B =>
            indicator (roundBad x [(.values y, .field γ)] (.scalar v) (p.sampler 1 a)))
        = mean (fun a : Fin (p.k 1) → B =>
            indicator (∃ κ, p.sampler 1 a = .field κ ∧ κ ∈ bad1 x y γ v)) :=
          mean_congr fun a => indicator_iff (rb1 x y γ v _)
      _ ≤ ((bad1 x y γ v).card : ℚ) * (1 / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.kappa
      _ ≤ ε E 1 := by
          have hc : (bad1 x y γ v).card ≤ 300 := B4_card (data x y) γ v
          show _ ≤ (300 : ℚ) / (Fintype.card E : ℚ)
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hc
  · rw [mean_roundBad_zero]
    · exact ε_nonneg 1
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨_, y, γ, v, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · exact hshape ⟨y, γ, v, hl', hm⟩
      all_goals omega

theorem d2_round2 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 2) (m : Msg E) :
    mean (fun a : Fin (p.k 2) → B => indicator (roundBad x l m (p.sampler 2 a))) ≤ ε E 2 := by
  by_cases hshape : ∃ y γ v κ, l = [(.values y, .field γ), (.scalar v, .field κ)] ∧ m = .unit
  · obtain ⟨y, γ, v, κ, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 2) → B => indicator
            (roundBad x [(.values y, .field γ), (.scalar v, .field κ)] .unit (p.sampler 2 a)))
        = mean (fun a : Fin (p.k 2) → B =>
            indicator (∃ τ, p.sampler 2 a = .field τ ∧ τ ∈ bad2 x y γ v κ)) :=
          mean_congr fun a => indicator_iff (rb2 x y γ v κ _)
      _ ≤ ((bad2 x y γ v κ).card : ℚ) * (1 / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.tau
      _ ≤ ε E 2 := by
          have hc : (bad2 x y γ v κ).card ≤ 200 := B5_card (data x y) γ v κ
          show _ ≤ (200 : ℚ) / (Fintype.card E : ℚ)
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hc
  · rw [mean_roundBad_zero]
    · exact ε_nonneg 2
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, y, γ, v, κ, hl', hm⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, hl', hm⟩
      all_goals omega

theorem d2_round3 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 3) (m : Msg E) :
    mean (fun a : Fin (p.k 3) → B => indicator (roundBad x l m (p.sampler 3 a))) ≤ ε E 3 := by
  by_cases hshape : ∃ y γ v κ τ P,
      l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] ∧ m = .poly P
  · obtain ⟨y, γ, v, κ, τ, P, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 3) → B => indicator (roundBad x
            [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] (.poly P) (p.sampler 3 a)))
        = mean (fun a : Fin (p.k 3) → B =>
            indicator (∃ α, p.sampler 3 a = .field α ∧ α ∈ bad3 x y γ κ τ P)) :=
          mean_congr fun a => indicator_iff (rb3 x y γ v κ τ P _)
      _ ≤ ((bad3 x y γ κ τ P).card : ℚ) * (1 / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.alpha
      _ ≤ ε E 3 := by
          have hc : (bad3 x y γ κ τ P).card ≤ 9396508281246 + 600 := by
            unfold bad3
            split
            · exact (grouped_cardinalities (data x y) γ v κ τ P (by assumption)).2.2.2
            · rw [Finset.union_empty]
              have := B6_card (channels (batch (data x y) γ))
              omega
          show _ ≤ (9396508281246 + 600 : ℚ) / (Fintype.card E : ℚ)
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hc
  · rw [mean_roundBad_zero]
    · exact ε_nonneg 3
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨_, y, γ, v, κ, τ, P, hl', hm⟩ | ⟨h1, _⟩
      · omega
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, τ, P, hl', hm⟩
      · omega

theorem d2_round4 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 4) (m : Msg E) :
    mean (fun a : Fin (p.k 4) → B => indicator (roundBad x l m (p.sampler 4 a))) ≤ ε E 4 := by
  by_cases hshape : ∃ y γ v κ τ P α F,
      l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ), (.poly P, .field α)] ∧
        m = .final F
  · obtain ⟨y, γ, v, κ, τ, P, α, F, rfl, rfl⟩ := hshape
    by_cases hbig : (matchingFibres (data x y) γ α F).card ≤ 9557
    · calc mean (fun a : Fin (p.k 4) → B => indicator (roundBad x
            [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ), (.poly P, .field α)]
            (.final F) (p.sampler 4 a)))
          = mean (fun a : Fin (p.k 4) → B =>
              indicator (∃ S, p.sampler 4 a = .set S ∧ S.card = 22 ∧
                S ⊆ matchingFibres (data x y) γ α F)) := by
            apply mean_congr; intro a; apply indicator_iff
            rw [rb4]
            simp only [bad4, hbig, true_and]
        _ ≤ ((matchingFibres (data x y) γ α F).card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) :=
            hs.queries _
        _ ≤ ε E 4 := by
            show _ ≤ (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast Nat.choose_le_choose 22 hbig
    · rw [mean_roundBad_zero]
      · exact ε_nonneg 4
      · intro c h
        rw [rb4] at h
        obtain ⟨S, _, hb, _, _⟩ := h
        exact hbig hb
  · rw [mean_roundBad_zero]
    · exact ε_nonneg 4
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨_, y, γ, v, κ, τ, P, α, F, hl', hm⟩
      · omega
      · omega
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, τ, P, α, F, hl', hm⟩

theorem d2 (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) :
    D2 (protocol p) (roundByRound p) := by
  intro i P m T' T hround hi hd
  change mean (fun a : Fin (p.k i) → B =>
    indicator (¬ doomed (P.ext m (p.sampler i a)) T)) ≤ ε E i
  rw [flip_density p i P m T' T hd]
  have hl : P.rounds.length = i := hround
  match i, hi with
  | 0, _ => exact d2_round0 p hs P.statement P.rounds hl m
  | 1, _ => exact d2_round1 p hs P.statement P.rounds hl m
  | 2, _ => exact d2_round2 p hs P.statement P.rounds hl m
  | 3, _ => exact d2_round3 p hs P.statement P.rounds hl m
  | 4, _ => exact d2_round4 p hs P.statement P.rounds hl m

end D2

/-! ## (D3) and the verifier property -/

/-- An accepting decision exposes the transcript's shape and R0's `Accept`. -/
theorem decision_true (P : Prefix (Stmt E Sfield) (Msg E) (Chal E)) (m : Msg E)
    (h : decision P m = true) :
    ∃ y γ v κ τ Q α F S,
      P.rounds = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ),
        (.poly Q, .field α), (.final F, .set S)] ∧ m = .opening ∧
      Accept (data P.statement y) γ v κ τ α Q F S P.statement.semantic True := by
  classical
  unfold decision at h
  exact decide_eq_true_iff.mp h

/-- The transcript's five rounds, written out. -/
theorem transcript5 (p : Params E Sfield Pf I B Kw) (H : I → Block B Kw) (x : Stmt E Sfield)
    (π : Pf) :
    (Protocol.transcript (protocol p) H x π 5).rounds =
      [(p.msg π 0, p.sampler 0 (restrict (p.hk 0) (H ((protocol p).chalAddr H x π 0)))),
       (p.msg π 1, p.sampler 1 (restrict (p.hk 1) (H ((protocol p).chalAddr H x π 1)))),
       (p.msg π 2, p.sampler 2 (restrict (p.hk 2) (H ((protocol p).chalAddr H x π 2)))),
       (p.msg π 3, p.sampler 3 (restrict (p.hk 3) (H ((protocol p).chalAddr H x π 3)))),
       (p.msg π 4, p.sampler 4 (restrict (p.hk 4) (H ((protocol p).chalAddr H x π 4))))] := rfl

theorem transcript_statement (p : Params E Sfield Pf I B Kw) (H : I → Block B Kw)
    (x : Stmt E Sfield) (π : Pf) : ∀ n, (Protocol.transcript (protocol p) H x π n).statement = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [Protocol.transcript, Prefix.ext] using ih

theorem d3 [Fintype B] (p : Params E Sfield Pf I B Kw) (hs : SamplerLaws p) :
    D3 (protocol p) (roundByRound p) (verifierR0 p) := by
  intro H x π T hd
  unfold verifierR0
  rw [verifier_decision]
  have hr5 : (protocol p).r = 5 := rfl
  rw [hr5] at hd ⊢
  by_contra hacc
  have hacc' : decision (Protocol.transcript (protocol p) H x π 5) ((protocol p).msg π 5) = true := by
    rcases h : decision (Protocol.transcript (protocol p) H x π 5) ((protocol p).msg π 5)
    · exact absurd h hacc
    · rfl
  obtain ⟨y, γ, v, κ, τ, Q, α, F, S, hr, _, hacc⟩ := decision_true _ _ hacc'
  obtain ⟨hw, hg⟩ := hd
  rw [transcript_statement] at hw hg hacc
  rw [transcript5] at hr hg
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hr
  obtain ⟨⟨hm0, hc0⟩, ⟨hm1, hc1⟩, ⟨hm2, hc2⟩, ⟨hm3, hc3⟩, ⟨hm4, hc4⟩⟩ := hr
  rw [hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3, hm4, hc4] at hg
  simp only [good, goodFrom, List.nil_append, List.cons_append,
    rb0, rb1, rb2, rb3, rb4, Chal.field.injEq, Chal.set.injEq, exists_eq_left', or_false,
    not_or] at hg
  obtain ⟨h0, h1, h2, h3, h4⟩ := hg
  -- the transcript's challenges come from the samplers
  have hγ : γ ≠ 0 := by
    obtain ⟨c, hc, hne⟩ := hs.nonzero (restrict (p.hk 0) (H ((protocol p).chalAddr H x π 0)))
    rw [hc] at hc0
    cases hc0
    exact hne
  have hScard : S.card = 22 := by
    obtain ⟨S', hS', hcard⟩ := hs.queryCard (restrict (p.hk 4) (H ((protocol p).chalAddr H x π 4)))
    rw [hS'] at hc4
    cases hc4
    exact hcard
  have hdeg : Q.natDegree ≤ 6 := hacc.2.2.1
  simp only [bad0, bad3, bad4, Finset.mem_union, hdeg, if_true, not_or] at h0 h3 h4
  have hsub : S ⊆ matchingFibres (data x y) γ α F := by
    intro u hu
    simp only [matchingFibres, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hacc.2.2.2.2.1 u hu
  have large : 9558 ≤ (matchingFibres (data x y) γ α F).card := by
    by_contra hlt
    exact h4 ⟨by omega, hScard, hsub⟩
  obtain ⟨t, ht, _, hpt, _, hsf⟩ := binding (data x y) x.hne x.h0 x.h1 Sfield
    (fun l i => x.base l i) γ v κ τ α hγ Q F S x.semantic True hacc h0.1.1 h0.1.2 h0.2 h1 h2
    h3.1 h3.2 large
  exact hw ⟨t, ht, hpt, hsf⟩

theorem readsChallenges (p : Params E Sfield Pf I B Kw) :
    ReadsChallenges (protocol p) (verifierR0 p) :=
  verifier_readsChallenges (protocol p) decision

end
end R0FS
