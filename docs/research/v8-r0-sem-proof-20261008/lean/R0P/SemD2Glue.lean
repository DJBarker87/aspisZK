import R0P.SemD2
import R0P.SemD3Glue
import FS2.DuplexDensity
import R0C.CircleRows
import R0C.V3.DuplexQ

/-!
G16 semantic-row D2 bridge.  The degree check is already internal to the
lead's `semanticBad`: invalid current sumcheck polynomials are not bad events.
The old `X^28` witness only showed that the former external degree premise was
not automatic; it no longer blocks this density bound.  This file proves the
semantic one-block row case against the source's `semChal` law.  The circle
uniform-point laws and the q22 opening-chain law remain separate components of
the full 31-round D2 assembly.
-/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 FS2.Duplex R0C.SemStatement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisWideTower

/-- Splitting a concatenated transcript preserves the current prefix. -/
theorem hitFrom_append {K E : Type} [Field K] [Field E]
    [Fintype K] [Fintype E] [DecidableEq E]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    [Algebra (ZMod AspisCircleGroupOrder.P) E]
    {X SM W : Type} {Sfield : Fin 29 → Subfield E}
    (s : SourceData (K := K) (E := E) X SM W Sfield)
    (x : X) (prev xs ys : List (Msg K E SM × Chal K E)) :
    hitFrom s x prev (xs ++ ys) ↔
      hitFrom s x prev xs ∨ hitFrom s x (prev ++ xs) ys := by
  induction xs generalizing prev with
  | nil => simp [hitFrom]
  | cons a xs ih =>
    rcases a with ⟨m, c⟩
    simp only [List.cons_append, hitFrom]
    rw [ih]
    simp only [List.append_assoc]
    tauto

#print axioms hitFrom_append

/-- A doomed prefix that becomes not doomed after one extension must register
that extension as the current round's bad event. -/
theorem doomed_ext_roundBad {K E : Type} [Field K] [Field E]
    [Fintype K] [Fintype E] [DecidableEq E]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    [Algebra (ZMod AspisCircleGroupOrder.P) E]
    {X SM W I A : Type} {Sfield : Fin 29 → Subfield E}
    [DecidableEq I] [Inhabited A]
    (s : SourceData (K := K) (E := E) X SM W Sfield)
    (P : Prefix K E X SM) (m : Msg K E SM) (c : Chal K E)
    (T' T : Table I A) (hdoomed : doomed s P T')
    (hnot : ¬ doomed s (P.ext m c) T) :
    roundBad s ⟨P.statement, P.rounds⟩ m c := by
  rcases hdoomed with ⟨hpay, hprior⟩
  have hhit : hitFrom s P.statement [] (P.rounds ++ [(m, c)]) := by
    by_contra hno
    exact hnot ⟨hpay, by simpa only [FS.Prefix.ext] using hno⟩
  rw [hitFrom_append] at hhit
  rcases hhit with hprior' | hcur
  · exact (hprior hprior').elim
  · rcases hcur with hcur | hfalse
    · exact hcur
    · exact False.elim hfalse

#print axioms doomed_ext_roundBad

/-- At an early semantic row, every classifier hit has semantic message and
challenge tags. -/
theorem early_roundBad_semantic
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F)
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (m : Msg WideExact WideExact (SemMsg WideExact)) (c : Chal WideExact WideExact)
    (i : Nat) (hi : i < 24) (hr : Q.round = i)
    (hbad : roundBad (R0P.SemD3Glue.sourceData B) Q m c) :
    ∃ sm k, m = .semantic sm ∧ c = .semantic k ∧ semanticBad B Q sm k := by
  simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
  rcases hbad with hsem | hrest
  · rcases hsem with ⟨sm, k, _hlt, hm, hc, hb⟩
    exact ⟨sm, k, hm, hc, hb⟩
  · rcases hrest with hz0 | hrest
    · obtain ⟨_, _, hround, _, _, _⟩ := hz0
      rw [hr] at hround
      omega
    · rcases hrest with hz1 | hopen
      · obtain ⟨_, _, _, _, hround, _, _, _, _⟩ := hz1
        rw [hr] at hround
        omega
      · obtain ⟨Q', _, _, _, _, _, hround, _⟩ := hopen
        rw [hr] at hround
        omega

#print axioms early_roundBad_semantic


/-- At a row below the two circle rounds, any message excluded from the
semantic constructor leaves the lifted state predicate doomed. -/
theorem early_nonsemantic_stay
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F) {L : Nat} (budget : Nat → ℚ) (i : Nat)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = i) (hi : i < 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hshape : ∀ sm : SemMsg WideExact, m ≠ .semantic sm) :
    ∀ (a : Chal WideExact WideExact) (b : State),
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m (a, b)) T := by
  classical
  intro a b
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQround : Q.round = i := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQdoomed : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m (a, b))) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m a T' T hQdoomed hnot
  obtain ⟨sm, _, hm, _, _⟩ := early_roundBad_semantic B Q m a i hi hQround hbad
  exact (hshape sm hm).elim

#print axioms early_nonsemantic_stay

/-- One semantic outgoing message: a doomed-state flip is contained in the
lead's `semanticBad` event for that row. -/
theorem semantic_row_D2_semantic
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F) {L : Nat} (p : Duplex.Params
      (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ) (i : Nat)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (sm : SemMsg WideExact)
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = i) (hi : i < 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ a : State, p.σ i a = Chal.semantic (semChal a)) :
    independentMean (Duplex.samp p i P (.semantic sm)).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.semantic sm) w.2) T)) ≤
      (1 + deltaQ) * ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /
        (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQround : Q.round = i := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQdoomed : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  have hpoint (a b : State) :
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.semantic sm) (p.σ i a, b)) T →
      semanticBad B Q sm (semChal a) := by
    intro hflip
    have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
        (R0P.SemD3Glue.valuePrefix (P.ext (.semantic sm) (p.σ i a, b))) T := hflip
    rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
    have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
      Q (.semantic sm) (p.σ i a) T' T hQdoomed hnot
    obtain ⟨sm', k, hm, hc, hb⟩ :=
      early_roundBad_semantic B Q (.semantic sm) (p.σ i a) i hi hQround hbad
    have hsm : sm' = sm := (Msg.semantic.inj hm).symm
    subst sm'
    rw [hσ a] at hc
    have hk : semChal a = k := Chal.semantic.inj hc
    rw [hk]
    exact hb
  have hmean :
      mean (fun a : State => mean (fun b : State =>
        indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.semantic sm) (p.σ i a, b)) T))) ≤
      mean (fun a : State => indicator (semanticBad B Q sm (semChal a))) := by
    calc
      mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.semantic sm) (p.σ i a, b)) T)))
          ≤ mean (fun a : State => mean (fun b : State =>
            indicator (semanticBad B Q sm (semChal a)))) := by
              apply mean_mono
              intro a
              apply mean_mono
              intro b
              apply indicator_mono
              exact hpoint a b
      _ = mean (fun a : State => indicator (semanticBad B Q sm (semChal a))) := by
            simp only [mean_const]
  calc
    independentMean (Duplex.samp p i P (.semantic sm)).toProgram
        (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.semantic sm) w.2) T))
        = mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.semantic sm) (p.σ i a, b)) T))) := by
              rw [Duplex.samp_mean p i P (.semantic sm)
                (fun c : Duplex.Chal (Chal WideExact WideExact) =>
                  ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
                    (P.ext (.semantic sm) c) T)]
    _ ≤ mean (fun a : State => indicator (semanticBad B Q sm (semChal a))) := hmean
    _ ≤ (1 + deltaQ) *
        ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /
          (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
          have hqi : Q.rounds.length = i := hQround
          have hlen : Q.rounds.length < 24 := by omega
          have hden := semantic_round_density B Q sm hlen
          simpa only [hqi] using hden

#print axioms semantic_row_D2_semantic

/-- The row bound for every outgoing message.  At an early semantic row a
nonsemantic message cannot register a `roundBad`, so its flip event is empty. -/
theorem semantic_row_D2
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F) {L : Nat} (p : Duplex.Params
      (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ) (i : Nat)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = i) (hi : i < 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ a : State, p.σ i a = Chal.semantic (semChal a)) :
    independentMean (Duplex.samp p i P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext m w.2) T)) ≤
      (1 + deltaQ) * ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /
        (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
  cases m with
  | semantic sm =>
      exact semantic_row_D2_semantic B p budget i P sm T' T hr hi hd hσ
  | beforeZ0 y =>
      have hstay := early_nonsemantic_stay B budget i P (.beforeZ0 y)
        T' T hr hi hd (by intro sm h; cases h)
      rw [Duplex.samp_mean p i P (.beforeZ0 y)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext (.beforeZ0 y) c) T)]
      have hnonneg : 0 ≤ (1 + deltaQ) *
          ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /
            (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
        have hδ := deltaQ_nonneg
        positivity
      have hleft : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ0 y) (p.σ i a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ i a) b)))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hleft]
      exact hnonneg
  | beforeZ1 y =>
      have hstay := early_nonsemantic_stay B budget i P (.beforeZ1 y)
        T' T hr hi hd (by intro sm h; cases h)
      rw [Duplex.samp_mean p i P (.beforeZ1 y)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext (.beforeZ1 y) c) T)]
      have hnonneg : 0 ≤ (1 + deltaQ) *
          ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /
            (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
        have hδ := deltaQ_nonneg
        positivity
      have hleft : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ1 y) (p.σ i a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ i a) b)))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hleft]
      exact hnonneg
  | opening om =>
      have hstay := early_nonsemantic_stay B budget i P (.opening om)
        T' T hr hi hd (by intro sm h; cases h)
      rw [Duplex.samp_mean p i P (.opening om)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext (.opening om) c) T)]
      have hnonneg : 0 ≤ (1 + deltaQ) *
          ((100 * semRoundBudget (⟨i, hi⟩ : Fin 24) : Nat) /            (AspisCircleGroupOrder.P ^ 4 : ℚ)) := by
        have hδ := deltaQ_nonneg
        positivity
      have hleft : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.opening om) (p.σ i a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ i a) b)))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hleft]
      exact hnonneg

#print axioms semantic_row_D2

end R0P.SemSource
