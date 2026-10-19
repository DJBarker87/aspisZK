import R0C.SlackStatement

/-! A2: scaled versions of the five original R0 opening density proofs.
All combinatorial bounds and state predicates are reused without alteration. -/
set_option autoImplicit false
namespace R0C.SlackDensity
open FS R0FS R0C.SlackStatement
open AspisR0.ListsResponses AspisR0.Fold AspisR0.Chord
open AspisR0.ChordGeometry AspisR0.RootCounts AspisR0.RoundNormalization
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisPool.AlgorithmicCircleDecoderV7 AspisV6Width29CorrelatedAgreement
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisR0.Opening hiding indicator
open Polynomial
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}
  {Pf I B : Type} {Kw : Nat} {δ : ℚ}

private theorem scaled_card_le {a b : Nat} {d δ : ℚ}
    (h : a ≤ b) (hd : 0 ≤ d) (hδ : 0 ≤ δ) :
    (a : ℚ) * ((1+δ)/d) ≤ (1+δ) * ((b : ℚ)/d) := by
  calc
    _ = (1+δ) * ((a : ℚ)/d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (by exact_mod_cast h) hd) (by linarith)

omit [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E] in
theorem epsilonSlack_nonneg (hδ : 0 ≤ δ) (i : Nat) : 0 ≤ epsilonSlack E δ i :=
  mul_nonneg (by linarith) (R0FS.ε_nonneg i)

variable [Fintype B] [Nonempty B]

theorem d2_round0 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 0) (m : Msg E) :
    mean (fun a : Fin (p.k 0) → B => indicator (roundBad x l m (p.sampler 0 a))) ≤ epsilonSlack E δ 0 := by
  by_cases hshape : ∃ y, l = [] ∧ m = .values y
  · obtain ⟨y, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 0) → B => indicator (roundBad x [] (.values y) (p.sampler 0 a)))
        = mean (fun a : Fin (p.k 0) → B =>
            indicator (∃ γ, p.sampler 0 a = .field γ ∧ γ ∈ bad0 x y)) :=
          mean_congr fun a => indicator_iff (rb0 x y _)
      _ ≤ ((bad0 x y).card : ℚ) * ((1+δ) / ((Fintype.card E : ℚ) - 1)) :=
          mean_exists_field_le _ _ _ hs.gamma
      _ ≤ epsilonSlack E δ 0 := by
          have hc : (bad0 x y).card ≤ 336869026605739 + 16800 := by
            have := (grouped_cardinalities (data x y) 0 0 0 0 0 (by simp)).1
            simpa [bad0] using this
          have hpos := card_E_pos (E := E)
          change _ ≤ (1+δ) * ((336869026605739 + 16800 : ℚ) / ((Fintype.card E : ℚ)-1))
          simpa only [Nat.cast_add, Nat.cast_ofNat] using scaled_card_le hc hpos.le hδ
  · rw [mean_roundBad_zero]
    · exact epsilonSlack_nonneg hδ 0
    · intro c h
      rcases roundBad_shape x l m c h with ⟨_, y, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hshape ⟨y, hl', hm⟩
      all_goals omega

theorem d2_round1 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 1) (m : Msg E) :
    mean (fun a : Fin (p.k 1) → B => indicator (roundBad x l m (p.sampler 1 a))) ≤ epsilonSlack E δ 1 := by
  by_cases hshape : ∃ y γ v, l = [(.values y, .field γ)] ∧ m = .scalar v
  · obtain ⟨y, γ, v, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 1) → B =>
            indicator (roundBad x [(.values y, .field γ)] (.scalar v) (p.sampler 1 a)))
        = mean (fun a : Fin (p.k 1) → B =>
            indicator (∃ κ, p.sampler 1 a = .field κ ∧ κ ∈ bad1 x y γ v)) :=
          mean_congr fun a => indicator_iff (rb1 x y γ v _)
      _ ≤ ((bad1 x y γ v).card : ℚ) * ((1+δ) / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.kappa
      _ ≤ epsilonSlack E δ 1 := by
          have hc : (bad1 x y γ v).card ≤ 400 := B4_card (data x y) γ v
          change _ ≤ (1+δ) * ((400 : ℚ) / (Fintype.card E : ℚ))
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            scaled_card_le hc (Nat.cast_nonneg (α := ℚ) (Fintype.card E)) hδ
  · rw [mean_roundBad_zero]
    · exact epsilonSlack_nonneg hδ 1
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨_, y, γ, v, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · exact hshape ⟨y, γ, v, hl', hm⟩
      all_goals omega

theorem d2_round2 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 2) (m : Msg E) :
    mean (fun a : Fin (p.k 2) → B => indicator (roundBad x l m (p.sampler 2 a))) ≤ epsilonSlack E δ 2 := by
  by_cases hshape : ∃ y γ v κ, l = [(.values y, .field γ), (.scalar v, .field κ)] ∧ m = .unit
  · obtain ⟨y, γ, v, κ, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 2) → B => indicator
            (roundBad x [(.values y, .field γ), (.scalar v, .field κ)] .unit (p.sampler 2 a)))
        = mean (fun a : Fin (p.k 2) → B =>
            indicator (∃ τ, p.sampler 2 a = .field τ ∧ τ ∈ bad2 x y γ v κ)) :=
          mean_congr fun a => indicator_iff (rb2 x y γ v κ _)
      _ ≤ ((bad2 x y γ v κ).card : ℚ) * ((1+δ) / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.tau
      _ ≤ epsilonSlack E δ 2 := by
          have hc : (bad2 x y γ v κ).card ≤ 200 := B5_card (data x y) γ v κ
          change _ ≤ (1+δ) * ((200 : ℚ) / (Fintype.card E : ℚ))
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            scaled_card_le hc (Nat.cast_nonneg (α := ℚ) (Fintype.card E)) hδ
  · rw [mean_roundBad_zero]
    · exact epsilonSlack_nonneg hδ 2
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, y, γ, v, κ, hl', hm⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, hl', hm⟩
      all_goals omega

theorem d2_round3 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 3) (m : Msg E) :
    mean (fun a : Fin (p.k 3) → B => indicator (roundBad x l m (p.sampler 3 a))) ≤ epsilonSlack E δ 3 := by
  by_cases hshape : ∃ y γ v κ τ P,
      l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] ∧ m = .poly P
  · obtain ⟨y, γ, v, κ, τ, P, rfl, rfl⟩ := hshape
    calc mean (fun a : Fin (p.k 3) → B => indicator (roundBad x
            [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] (.poly P) (p.sampler 3 a)))
        = mean (fun a : Fin (p.k 3) → B =>
            indicator (∃ α, p.sampler 3 a = .field α ∧ α ∈ bad3 x y γ κ τ P)) :=
          mean_congr fun a => indicator_iff (rb3 x y γ v κ τ P _)
      _ ≤ ((bad3 x y γ κ τ P).card : ℚ) * ((1+δ) / (Fintype.card E : ℚ)) :=
          mean_exists_field_le _ _ _ hs.alpha
      _ ≤ epsilonSlack E δ 3 := by
          have hc : (bad3 x y γ κ τ P).card ≤ 9396508281246 + 600 := by
            unfold bad3
            split
            · exact (grouped_cardinalities (data x y) γ v κ τ P (by assumption)).2.2.2
            · rw [Finset.union_empty]
              have := B6_card (channels (batch (data x y) γ))
              omega
          change _ ≤ (1+δ) * ((9396508281246 + 600 : ℚ) / (Fintype.card E : ℚ))
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            scaled_card_le hc (Nat.cast_nonneg (α := ℚ) (Fintype.card E)) hδ
  · rw [mean_roundBad_zero]
    · exact epsilonSlack_nonneg hδ 3
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨_, y, γ, v, κ, τ, P, hl', hm⟩ | ⟨h1, _⟩
      · omega
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, τ, P, hl', hm⟩
      · omega

theorem d2_round4 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) (x : Stmt E Sfield)
    (l : List (Msg E × Chal E)) (hl : l.length = 4) (m : Msg E) :
    mean (fun a : Fin (p.k 4) → B => indicator (roundBad x l m (p.sampler 4 a))) ≤ epsilonSlack E δ 4 := by
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
        _ ≤ (1+δ) * (((matchingFibres (data x y) γ α F).card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ)) :=
            hs.queries _
        _ ≤ epsilonSlack E δ 4 := by
            change _ ≤ (1+δ) * ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast Nat.choose_le_choose 22 hbig
    · rw [mean_roundBad_zero]
      · exact epsilonSlack_nonneg hδ 4
      · intro c h
        rw [rb4] at h
        obtain ⟨S, _, hb, _, _⟩ := h
        exact hbig hb
  · rw [mean_roundBad_zero]
    · exact epsilonSlack_nonneg hδ 4
    · intro c h
      rcases roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨_, y, γ, v, κ, τ, P, α, F, hl', hm⟩
      · omega
      · omega
      · omega
      · omega
      · exact hshape ⟨y, γ, v, κ, τ, P, α, F, hl', hm⟩

theorem d2 (p : Params E Sfield Pf I B Kw) (hδ : 0 ≤ δ) (hs : SamplerLawsSlack δ p) :
    D2 (protocol p) (rbSlack p δ) := by
  intro i P m T' T hround hi hd
  change mean (fun a : Fin (p.k i) → B =>
    indicator (¬ doomed (P.ext m (p.sampler i a)) T)) ≤ epsilonSlack E δ i
  rw [flip_density p i P m T' T hd]
  have hl : P.rounds.length = i := hround
  match i, hi with
  | 0, _ => exact d2_round0 p hδ hs P.statement P.rounds hl m
  | 1, _ => exact d2_round1 p hδ hs P.statement P.rounds hl m
  | 2, _ => exact d2_round2 p hδ hs P.statement P.rounds hl m
  | 3, _ => exact d2_round3 p hδ hs P.statement P.rounds hl m
  | 4, _ => exact d2_round4 p hδ hs P.statement P.rounds hl m


#print axioms d2_round0
#print axioms d2_round1
#print axioms d2_round2
#print axioms d2_round3
#print axioms d2_round4
#print axioms d2
end
end R0C.SlackDensity
