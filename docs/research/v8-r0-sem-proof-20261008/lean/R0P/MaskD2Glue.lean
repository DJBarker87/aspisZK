import R0P.MaskDensity
import R0P.MaskSource

/-! Duplex transfer of masked semantic/circle/opening root bounds. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 FS2.Duplex R0C.SemStatement R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8PairedCommitment
open AspisR0.ChordGeometry R0C.SlackStatement AspisWideTower
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact} {L : Nat}
variable (maskClaims : (Fin 29 → WideExact) → (Fin 10 → WideExact) → WideExact) (B : PackBasis F) (budget : Nat → ℚ)

abbrev DP := FS.Prefix (TypedContext WideExact Sfield) (MsgZ WideExact) (Duplex.Chal (ChalZ WideExact))

theorem flipZ (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (c : Duplex.Chal (ChalZ WideExact))
    (T' T : Table (Addr L) State)
    (hd : (duplexRowsZ maskClaims B budget).doomed P T')
    (hn : ¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m c) T) :
    roundBad (sourceDataZ maskClaims B) (valuePrefix P) m c.1 := by
  apply doomed_ext_roundBad (sourceDataZ maskClaims B) (valuePrefix P) m c.1 T' T hd
  have hn' : ¬ doomed (sourceDataZ maskClaims B) (valuePrefix (P.ext m c)) T := hn
  simpa only [valuePrefix_ext] using hn'

/-- The fresh absorb and advance answers disappear after pointwise containment. -/
theorem one_row_bound (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (i : Nat) (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T : Table (Addr L) State)
    (bad : State → Prop) (e : ℚ)
    (hpoint : ∀ a b : State, ¬ (duplexRowsZ maskClaims B budget).doomed
      (P.ext m (p.σ i a, b)) T → bad a)
    (hmass : mean (fun a => indicator (bad a)) ≤ e) :
    independentMean (Duplex.samp p i P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤ e := by
  rw [Duplex.samp_mean p i P m
    (fun c => ¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m c) T)]
  apply le_trans _ hmass
  apply mean_mono
  intro a
  apply le_trans (mean_mono (fun b => indicator_mono (hpoint a b)))
  exact (mean_const _).le

theorem early_roundBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : ChalZ WideExact) (hi : Q.round < 25)
    (h : roundBad (sourceDataZ maskClaims B) Q m c) :
    ∃ sm k, m = .semantic sm ∧ c = .semantic k ∧ semanticBadZ maskClaims B Q sm k := by
  simp only [roundBad, sourceDataZ, sourceDataWithFallbackZ] at h
  rcases h with hs | hz0 | hz1 | ho
  · obtain ⟨sm,k,_,hm,hc,hb⟩ := hs
    exact ⟨sm,k,hm,hc,hb⟩
  · obtain ⟨_,_,hr,_,_,_⟩ := hz0; omega
  · obtain ⟨_,_,_,_,hr,_,_,_,_⟩ := hz1; omega
  · obtain ⟨_,_,_,_,_,_,hr,_⟩ := ho; omega

def semanticMessageBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : WideExact) : Prop :=
  match m with
  | .semantic sm => semanticBadZ maskClaims B Q sm c
  | _ => False

theorem combinedD2BudgetZ_nonneg (i : Nat) : 0 ≤ combinedD2BudgetZ i := by
  have hδ := deltaQ_nonneg
  have heps (j : Nat) : 0 ≤ epsilonSlack WideExact delta0 j :=
    R0C.SlackDensity.epsilonSlack_nonneg R0C.ConcreteSlack.delta0_nonneg j
  unfold combinedD2BudgetZ
  split_ifs
  · unfold combinedD2Budget
    split_ifs <;> first | positivity | exact heps _
  all_goals first | positivity | exact heps _

theorem semantic_rowZ_D2 (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (i : Nat) (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T' T : Table (Addr L) State)
    (hr : P.round = i) (hi : i < 25)
    (hd : (duplexRowsZ maskClaims B budget).doomed P T')
    (hσ : ∀ a, p.σ i a = .semantic (semChal a)) :
    independentMean (Duplex.samp p i P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤
      combinedD2BudgetZ i := by
  let Q := valuePrefix P
  have hQr : Q.round = i := (valuePrefix_round P).trans hr
  apply one_row_bound maskClaims B budget p i P m T
    (fun a => semanticMessageBadZ maskClaims B Q m (semChal a)) _
  · intro a b hf
    obtain ⟨sm,k,hm,hc,hb⟩ := early_roundBadZ maskClaims B Q m (p.σ i a)
      (by rw [hQr]; exact hi) (flipZ maskClaims B budget P m (p.σ i a,b) T' T hd hf)
    rw [hσ a] at hc
    have hk := Chal.semantic.inj hc
    rw [hm, hk]
    exact hb
  · cases m <;> simp only [semanticMessageBadZ, indicator_false, mean_const]
    · rename_i sm
      have h := semantic_round_densityZ maskClaims B Q sm (by change Q.round < 25; omega)
      simpa only [show Q.rounds.length = i from hQr] using h
    all_goals exact combinedD2BudgetZ_nonneg i

theorem circle0_roundBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : ChalZ WideExact) (hr : Q.round = 25)
    (h : roundBad (sourceDataZ maskClaims B) Q m c) :
    ∃ (y : Fin 3 → Fin 29 → WideExact) (z : Point WideExact), m = .beforeZ0 y ∧ c = .circle z ∧ z0Bad' z := by
  simp only [roundBad, sourceDataZ, sourceDataWithFallbackZ] at h
  rcases h with hs | hz0 | hz1 | ho
  · obtain ⟨_,_,hlt,_,_,_⟩ := hs; omega
  · obtain ⟨y,z,_,hm,hc,hb⟩ := hz0; exact ⟨y,z,hm,hc,hb⟩
  · obtain ⟨_,_,_,_,he,_,_,_,_⟩ := hz1; omega
  · obtain ⟨_,_,_,_,_,_,he,_⟩ := ho; omega

theorem circle1_roundBadZ (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (m : MsgZ WideExact) (c : ChalZ WideExact) (hr : Q.round = 26)
    (h : roundBad (sourceDataZ maskClaims B) Q m c) :
    ∃ (y : Fin 3 → Fin 29 → WideExact) (y0 : Fin 29 → WideExact) (z0 z1 : Point WideExact), Q.rounds.getLast? = some (.beforeZ0 y, .circle z0) ∧
      m = .beforeZ1 y0 ∧ c = .circle z1 ∧ z1Bad z0 z1 := by
  simp only [roundBad, sourceDataZ, sourceDataWithFallbackZ] at h
  rcases h with hs | hz0 | hz1 | ho
  · obtain ⟨_,_,hlt,_,_,_⟩ := hs; omega
  · obtain ⟨_,_,he,_,_,_⟩ := hz0; omega
  · obtain ⟨y,y0,z0,z1,_,hp,hm,hc,hb⟩ := hz1; exact ⟨y,y0,z0,z1,hp,hm,hc,hb⟩
  · obtain ⟨_,_,_,_,_,_,he,_⟩ := ho; omega

theorem circle_slack_le_two : (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 ≤
    2 / (AspisCircleGroupOrder.P : ℚ)^4 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
  have h : deltaQ ≤ 1 := deltaQ_small.trans (by norm_num)
  linarith

theorem circle_row25_D2 (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T' T : Table (Addr L) State)
    (hr : P.round = 25) (hd : (duplexRowsZ maskClaims B budget).doomed P T')
    (hσ : ∀ a, p.σ 25 a = .circle (R0P.SemSource.circleSample0 a)) :
    independentMean (Duplex.samp p 25 P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤
      2 / (AspisCircleGroupOrder.P : ℚ)^4 := by
  apply one_row_bound maskClaims B budget p 25 P m T (fun a => z0Bad' (R0P.SemSource.circleSample0 a)) _
  · intro a b hf
    obtain ⟨y,z,_,hc,hb⟩ := circle0_roundBadZ maskClaims B (valuePrefix P) m (p.σ 25 a)
      ((valuePrefix_round P).trans hr) (flipZ maskClaims B budget P m (p.σ 25 a,b) T' T hd hf)
    rw [hσ a] at hc
    exact (Chal.circle.inj hc).symm ▸ hb
  · apply le_trans _ circle_slack_le_two
    simpa only [R0P.SemSource.P_eq] using R0P.SemSource.circleSample0_mass

theorem no_hit_last_circle_ne_fallbackZ
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsgZ WideExact))
    (y : Fin 3 → Fin 29 → WideExact) (z0 : Point WideExact) (hr : Q.round = 26)
    (hprev : Q.rounds.getLast? = some (.beforeZ0 y, .circle z0))
    (hno : ¬ hitFrom (sourceDataZ maskClaims B) Q.statement [] Q.rounds) : z0 ≠ R0P.SemSource.circleFallback1 := by
  obtain ⟨rs,hrs⟩ := List.getLast?_eq_some_iff.mp hprev
  have hlen : rs.length = 25 := by
    change Q.rounds.length = 26 at hr
    rw [hrs, List.length_append, List.length_singleton] at hr
    omega
  intro heq
  apply hno
  rw [hrs, hitFrom_append]
  apply Or.inr
  simp only [List.nil_append, hitFrom]
  apply Or.inl
  apply Or.inr
  apply Or.inl
  exact ⟨y,z0,hlen,rfl,rfl,Or.inr heq⟩

theorem circle_row26_D2 (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
    (P : DP (Sfield := Sfield)) (m : MsgZ WideExact) (T' T : Table (Addr L) State)
    (hr : P.round = 26) (hd : (duplexRowsZ maskClaims B budget).doomed P T')
    (hσ : ∀ a, p.σ 26 a = .circle (R0P.SemSource.circleSample1 a)) :
    independentMean (Duplex.samp p 26 P m).toProgram
      (fun w => indicator (¬ (duplexRowsZ maskClaims B budget).doomed (P.ext m w.2) T)) ≤
      2 / (AspisCircleGroupOrder.P : ℚ)^4 := by
  let Q := valuePrefix P
  have hQr : Q.round = 26 := (valuePrefix_round P).trans hr
  by_cases hp : ∃ (y : Fin 3 → Fin 29 → WideExact) (z0 : Point WideExact), Q.rounds.getLast? = some (.beforeZ0 y, .circle z0)
  · obtain ⟨y,z0,hprev⟩ := hp
    have hz0 := no_hit_last_circle_ne_fallbackZ maskClaims B Q y z0 hQr hprev hd.2
    apply one_row_bound maskClaims B budget p 26 P m T (fun a => z1Bad z0 (R0P.SemSource.circleSample1 a)) _
    · intro a b hf
      obtain ⟨y',y0,z0',z1,hprev',_,hc,hb⟩ := circle1_roundBadZ maskClaims B Q m (p.σ 26 a) hQr
        (flipZ maskClaims B budget P m (p.σ 26 a,b) T' T hd hf)
      have hz := Chal.circle.inj (congrArg Prod.snd (Option.some.inj (hprev.symm.trans hprev')))
      rw [hσ a] at hc
      rw [hz, Chal.circle.inj hc]
      exact hb
    · apply le_trans _ circle_slack_le_two
      simpa only [R0P.SemSource.P_eq] using R0P.SemSource.circleSample1_mass z0 hz0
  · apply one_row_bound maskClaims B budget p 26 P m T (fun _ => False) _
    · intro a b hf
      obtain ⟨y,y0,z0,z1,hprev,_,_,_⟩ := circle1_roundBadZ maskClaims B Q m (p.σ 26 a) hQr
        (flipZ maskClaims B budget P m (p.σ 26 a,b) T' T hd hf)
      exact hp ⟨y,z0,hprev⟩
    · simp only [indicator_false, mean_const]
      positivity

#print axioms flipZ
#print axioms one_row_bound
#print axioms semantic_rowZ_D2
#print axioms circle_row25_D2
#print axioms circle_row26_D2
end
end R0P.Mask
