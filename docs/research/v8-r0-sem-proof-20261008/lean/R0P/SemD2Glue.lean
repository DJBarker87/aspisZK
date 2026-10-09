import R0P.SemD2
import R0P.CircleSampler
import R0P.SemD3Glue
import FS2.DuplexDensity
import R0C.CircleRows
import R0C.V3.DuplexQ

/-!
G16 complete 31-row D2 bridge. The degree check is internal to the lead's
`semanticBad`: invalid current sumcheck polynomials are not bad events.
The semantic rows use the `semChal` density, both circle rows use the proved
one-block `circleSample0`/`circleSample1` masses, and opening rows use the existing field and
q22 chain bounds. Malformed message tags or parser failure give empty flip
events. The final theorem uses only the source-fixed decoder identities and
the authorized per-round budget; all row bounds are proved here.
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


noncomputable section
attribute [local instance] Classical.propDecidable

variable {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
/-- The sampler `chainS` reads one squeeze and one advance state per step,
with the same law as the symbolic `Q22.chainE`. -/
theorem chainS_independentMean
    {L : Nat} {C : Type}
    (p : Duplex.Params (R0FS.Msg WideExact) (R0FS.Chal WideExact) L)
    (out : List State → List State → C) (obs : C → ℚ) :
    ∀ (n : Nat) (s : State) (bs xs : List State),
      independentMean
          (R0C.V3.DQ.chainS p out n s bs xs).toProgram
          (fun w => obs w.2) =
        R0C.V3.Q22.chainE
          (fun bs' xs' => obs (out (bs ++ bs') (xs ++ xs'))) n := by
  intro n
  induction n with
  | zero =>
      intro s bs xs
      simp [R0C.V3.DQ.chainS, FS2.Sampler.toProgram,
        AspisV8R19.AdaptiveFirstReadLaw.independentMean,
        R0C.V3.Q22.chainE]
  | succ n ih =>
      intro s bs xs
      simp only [R0C.V3.DQ.chainS, FS2.Sampler.toProgram,
        AspisV8R19.AdaptiveFirstReadLaw.independentMean,
        R0C.V3.Q22.chainE]
      apply mean_congr
      intro b
      apply mean_congr
      intro x
      have h := ih x (bs ++ [b]) (xs ++ [x])
      simpa only [List.append_assoc, List.singleton_append] using h

#print axioms chainS_independentMean

/-- An opening-row field flip is the matching standalone R0 field event.
The caller supplies the parser view and the source-fixed decoder identity. -/
theorem opening_field_row_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (O : FS.Prefix (R0FS.Stmt WideExact Sfield)
      (R0FS.Msg WideExact) (R0FS.Chal WideExact))
    (j : Fin 4) (om : R0FS.Msg WideExact)
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 26 + j.val)
    (hview : R0P.SemSource.openingView (R0P.SemD3Glue.valuePrefix P) = some O)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State,
      p.σ (26 + j.val) s = Chal.opening (R0C.V3.DQ.σQ j.val s)) :
    independentMean (Duplex.samp p (26 + j.val) P (.opening om)).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.opening om) w.2) T)) ≤
      R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 j.val := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 26 + j.val := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  obtain ⟨sem, cs, hw, gw, y, y0, z0, z1, hcs, hb, hne, h0, h1, os,
      hsem, hparse, hc2, hrounds, hO⟩ :=
    R0P.SemD3Glue.openingView_some_structure Q O hview
  have hOrounds : O.rounds = os := congrArg FS.Prefix.rounds hO
  have hlen : O.rounds.length = j.val := by
    rw [hOrounds]
    have htotal : Q.round = 26 + os.length := by
      rw [FS.Prefix.round, hrounds]
      simp only [List.length_append, List.length_cons,
        R0P.SemD3Glue.openingPairs, List.length_map, hsem]
      omega
    omega
  have hpoint (a b : State) :
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.opening om) (p.σ (26 + j.val) a, b)) T →
        R0FS.roundBad O.statement O.rounds om (R0C.V3.DQ.σQ j.val a) := by
    intro hflip
    have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
        (R0P.SemD3Glue.valuePrefix (P.ext (.opening om)
          (p.σ (26 + j.val) a, b))) T := hflip
    rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
    have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
      Q (.opening om) (p.σ (26 + j.val) a) T' T hQd hnot
    simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
    rcases hbad with hsem | hz0 | hz1 | hopen
    · rcases hsem with ⟨_, _, hlt, _, _, _⟩
      rw [hQr] at hlt
      omega
    · rcases hz0 with ⟨_, _, hround, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hz1 with ⟨_, _, _, _, hround, _, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hopen with ⟨O', om', oc, hview', hm, hc, hround, hlocal⟩
      have hO : O' = O := Option.some.inj (hview'.symm.trans hview)
      subst O'
      have hm' : om' = om := (Msg.opening.inj hm).symm
      subst om'
      rw [hQr] at hround
      have hc' : R0C.V3.DQ.σQ j.val a = oc := by
        rw [hσ a] at hc
        exact Chal.opening.inj hc
      rw [hc']
      exact hlocal
  rw [Duplex.samp_mean p (26 + j.val) P (.opening om)
    (fun c : Duplex.Chal (Chal WideExact WideExact) =>
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.opening om) c) T)]
  calc
    mean (fun a : State => mean (fun b : State =>
        indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.opening om) (p.σ (26 + j.val) a, b)) T)))
        ≤ mean (fun a : State =>
          indicator (R0FS.roundBad O.statement O.rounds om (R0C.V3.DQ.σQ j.val a))) := by
          apply mean_mono
          intro a
          calc
            mean (fun b : State => indicator (¬
                (R0P.SemD3Glue.duplexRows B budget).doomed
                  (P.ext (.opening om) (p.σ (26 + j.val) a, b)) T))
                ≤ mean (fun _ : State =>
                    indicator (R0FS.roundBad O.statement O.rounds om
                      (R0C.V3.DQ.σQ j.val a))) := by
                  apply mean_mono
                  intro b
                  apply indicator_mono
                  exact hpoint a b
            _ = indicator (R0FS.roundBad O.statement O.rounds om
                (R0C.V3.DQ.σQ j.val a)) := mean_const _
    _ ≤ R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 j.val := by
          exact R0C.V3.DQ.round_field_bound O.statement O.rounds om
            j.val j.isLt hlen

#print axioms opening_field_row_D2

/-- The final q22 row averages the standalone fixed-seed q22 bound over the
absorption state, after identifying the same local opening suffix. -/
theorem opening_q22_row_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (O : FS.Prefix (R0FS.Stmt WideExact Sfield)
      (R0FS.Msg WideExact) (R0FS.Chal WideExact))
    (om : R0FS.Msg WideExact) (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 30)
    (hview : R0P.SemSource.openingView (R0P.SemD3Glue.valuePrefix P) = some O)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T') :
    independentMean (R0P.SemD3Glue.combinedSampler p 30 P (.opening om)).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.opening om) w.2) T)) ≤
      R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 4 := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 30 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  obtain ⟨sem, cs, hw, gw, y, y0, z0, z1, hcs, hb, hne, h0, h1, os,
      hsem, hparse, hc2, hrounds, hO⟩ :=
    R0P.SemD3Glue.openingView_some_structure Q O hview
  have hOrounds : O.rounds = os := congrArg FS.Prefix.rounds hO
  have hlen : O.rounds.length = 4 := by
    rw [hOrounds]
    have htotal : Q.round = 26 + os.length := by
      rw [FS.Prefix.round, hrounds]
      simp only [List.length_append, List.length_cons,
        R0P.SemD3Glue.openingPairs, List.length_map, hsem]
      omega
    omega
  have hpoint (s' : State) (bs xs : List State) :
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.opening om) (R0P.SemD3Glue.openingChallenge
            (R0C.V3.DQ.out4 s' bs xs))) T →
        R0FS.roundBad O.statement O.rounds om
          (R0C.V3.DQ.out4 s' bs xs).1 := by
    intro hflip
    have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
        (R0P.SemD3Glue.valuePrefix (P.ext (.opening om)
          (R0P.SemD3Glue.openingChallenge (R0C.V3.DQ.out4 s' bs xs)))) T := hflip
    rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
    have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
      Q (.opening om)
      (R0P.SemD3Glue.openingChallenge (R0C.V3.DQ.out4 s' bs xs)).1
      T' T hQd hnot
    simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
    rcases hbad with hsem | hz0 | hz1 | hopen
    · rcases hsem with ⟨_, _, hlt, _, _, _⟩
      rw [hQr] at hlt
      omega
    · rcases hz0 with ⟨_, _, hround, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hz1 with ⟨_, _, _, _, hround, _, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hopen with ⟨O', om', oc, hview', hm, hc, hround, hlocal⟩
      have hO' : O' = O := Option.some.inj (hview'.symm.trans hview)
      subst O'
      have hm' : om' = om := (Msg.opening.inj hm).symm
      subst om'
      rw [hQr] at hround
      have hc' : oc = (R0C.V3.DQ.out4 s' bs xs).1 := by
        exact (Chal.opening.inj hc).symm
      rw [hc'] at hlocal
      exact hlocal
  rw [R0P.SemD3Glue.combinedSampler, if_neg (show ¬ (30 : Nat) < 30 by omega)]
  simp only [FS2.Sampler.toProgram,
    AspisV8R19.AdaptiveFirstReadLaw.independentMean]
  calc
    mean (fun s' : State =>
        independentMean
          (R0C.V3.DQ.chainS (R0P.SemD3Glue.openingParams p s')
            (fun bs xs => R0P.SemD3Glue.openingChallenge
              (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []).toProgram
          (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.opening om) w.2) T)))
        ≤ mean (fun _ : State => R0C.SlackStatement.epsilonSlack WideExact
          R0C.SlackStatement.delta0 4) := by
          apply mean_mono
          intro s'
          rw [chainS_independentMean (R0P.SemD3Glue.openingParams p s')
            (fun bs xs => R0P.SemD3Glue.openingChallenge (R0C.V3.DQ.out4 s' bs xs))
            (fun c => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.opening om) c) T)) 8 s' [] []]
          simp only [List.nil_append]
          calc
            R0C.V3.Q22.chainE
                (fun bs xs => indicator (¬
                  (R0P.SemD3Glue.duplexRows B budget).doomed
                    (P.ext (.opening om)
                      (R0P.SemD3Glue.openingChallenge
                        (R0C.V3.DQ.out4 s' bs xs))) T)) 8
                ≤ R0C.V3.Q22.chainE
                    (fun bs xs => indicator
                      (R0FS.roundBad O.statement O.rounds om
                        (R0C.V3.DQ.out4 s' bs xs).1)) 8 := by
                    apply R0C.V3.Q22.chainE_mono
                    intro bs xs
                    apply indicator_mono
                    exact hpoint s' bs xs
            _ ≤ R0C.SlackStatement.epsilonSlack WideExact
                R0C.SlackStatement.delta0 4 :=
                  R0C.V3.DQ.round_q22_bound O.statement O.rounds om hlen s'
    _ = R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 4 := mean_const _

#print axioms opening_q22_row_D2

end
end R0P.SemSource

set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 FS2.Duplex R0C.SemStatement
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisWideTower
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisR0.Chord AspisR0.ChordGeometry

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}

/-- The canonical tower and circle interfaces name the same M31 prime. -/
theorem P_eq : (AspisV5ComponentCQM31TowerExact.P : ℚ) =
    AspisCircleGroupOrder.P := by
  norm_num [AspisV5ComponentCQM31TowerExact.P, AspisCircleGroupOrder.P]

#print axioms P_eq

/-- A doomed prefix at row 25 has avoided the reserved fallback at row 24. -/
theorem no_hit_last_circle_ne_fallback
    (B : PackBasis F)
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (y : Fin 3 → Fin 29 → WideExact) (z0 : Point WideExact)
    (hr : Q.round = 25)
    (hprev : Q.rounds.getLast? = some (.beforeZ0 y, .circle z0))
    (hno : ¬ hitFrom (R0P.SemD3Glue.sourceData B) Q.statement [] Q.rounds) :
    z0 ≠ circleFallback1 := by
  obtain ⟨rs, hrs⟩ := List.getLast?_eq_some_iff.mp hprev
  have hlen : rs.length = 24 := by
    change Q.rounds.length = 25 at hr
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
  refine ⟨y, z0, ?_, rfl, rfl, Or.inr heq⟩
  exact hlen

#print axioms no_hit_last_circle_ne_fallback

private theorem roundBad24_shape
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F)
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (m : Msg WideExact WideExact (SemMsg WideExact)) (c : Chal WideExact WideExact)
    (hround : Q.round = 24)
    (hbad : roundBad (R0P.SemD3Glue.sourceData B) Q m c) :
    ∃ y z, m = .beforeZ0 y ∧ c = .circle z ∧ z0Bad circleFallback1 z := by
  simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
  rcases hbad with hsem | hrest
  · rcases hsem with ⟨_, _, hlt, _, _, _⟩
    rw [hround] at hlt
    omega
  · rcases hrest with hz0 | hrest
    · rcases hz0 with ⟨y, z, _, hm, hc, hb⟩
      exact ⟨y, z, hm, hc, hb⟩
    · rcases hrest with hz1 | hopen
      · rcases hz1 with ⟨_, _, _, _, hrow, _, _, _, _⟩
        rw [hround] at hrow
        omega
      · rcases hopen with ⟨_, _, _, _, _, _, hrow, _⟩
        rw [hround] at hrow
        omega

#print axioms roundBad24_shape

private theorem roundBad25_shape
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F)
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (m : Msg WideExact WideExact (SemMsg WideExact)) (c : Chal WideExact WideExact)
    (hround : Q.round = 25)
    (hbad : roundBad (R0P.SemD3Glue.sourceData B) Q m c) :
    ∃ y y0 z0 z1, Q.rounds.getLast? = some (.beforeZ0 y, .circle z0) ∧
      m = .beforeZ1 y0 ∧ c = .circle z1 ∧ z1Bad z0 z1 := by
  simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
  rcases hbad with hsem | hrest
  · rcases hsem with ⟨_, _, hlt, _, _, _⟩
    rw [hround] at hlt
    omega
  · rcases hrest with hz0 | hrest
    · rcases hz0 with ⟨_, _, hrow, _, _, _⟩
      rw [hround] at hrow
      omega
    · rcases hrest with hz1 | hopen
      · rcases hz1 with ⟨y, y0, z0, z1, _, hlast, hm, hc, hb⟩
        exact ⟨y, y0, z0, z1, hlast, hm, hc, hb⟩
      · rcases hopen with ⟨_, _, _, _, _, _, hrow, _⟩
        rw [hround] at hrow
        omega

#print axioms roundBad25_shape

private theorem roundBadOpen_shape
    {Sfield : Fin 29 → Subfield WideExact} {F : Subfield WideExact}
    (B : PackBasis F)
    (Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact))
    (m : Msg WideExact WideExact (SemMsg WideExact)) (c : Chal WideExact WideExact)
    (hround : 26 ≤ Q.round)
    (hbad : roundBad (R0P.SemD3Glue.sourceData B) Q m c) :
    ∃ O om oc, R0P.SemSource.openingView Q = some O ∧
      m = .opening om ∧ c = .opening oc ∧
      Q.round = 26 + O.round ∧ R0FS.roundBad O.statement O.rounds om oc := by
  simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
  rcases hbad with hsem | hrest
  · rcases hsem with ⟨_, _, hlt, _, _, _⟩
    omega
  · rcases hrest with hz0 | hrest
    · rcases hz0 with ⟨_, _, hrow, _, _, _⟩
      omega
    · rcases hrest with hz1 | hopen
      · rcases hz1 with ⟨_, _, _, _, hrow, _, _, _, _⟩
        omega
      · rcases hopen with ⟨O, om, oc, hv, hm, hc, hrow, hb⟩
        exact ⟨O, om, oc, hv, hm, hc, by simpa using hrow, hb⟩

#print axioms roundBadOpen_shape

private theorem duplex_samp_zero_of_stay
    {L : Nat} {X M C : Type}
    (p : Duplex.Params M C L)
    (i : Nat) (P : FS.Prefix X M (Duplex.Chal C)) (m : M)
    (doomed : FS.Prefix X M (Duplex.Chal C) → Table (Duplex.Addr L) State → Prop)
    (T : Table (Duplex.Addr L) State)
    (hstay : ∀ a b : State, doomed (P.ext m (p.σ i a, b)) T) :
    independentMean (Duplex.samp p i P m).toProgram
      (fun w => indicator (¬ doomed (P.ext m w.2) T)) = 0 := by
  rw [Duplex.samp_mean p i P m
    (fun c : Duplex.Chal C => ¬ doomed (P.ext m c) T)]
  rw [mean_congr (fun a => mean_congr (fun b =>
    indicator_iff (iff_false_intro (fun h => h (hstay a b)))))]
  rw [indicator_false, mean_const, mean_const]

#print axioms duplex_samp_zero_of_stay

private theorem circle24_no_flip
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hmsg : ∀ y : Fin 3 → Fin 29 → WideExact, m ≠ .beforeZ0 y) :
    ∀ a b : State,
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m (p.σ 24 a, b)) T := by
  intro a b
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 24 := by dsimp [Q]; rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'; exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m (p.σ 24 a, b))) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m (p.σ 24 a) T' T hQd hnot
  obtain ⟨y, _, hm, _, _⟩ := roundBad24_shape B Q m (p.σ 24 a) hQr hbad
  exact hmsg y hm

#print axioms circle24_no_flip




/-- At the first circle row, a flip implies the first circle rejection event. -/
theorem circle_row24_D2
    {L : Nat}
    (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (y : Fin 3 → Fin 29 → WideExact)
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State, p.σ 24 s = Chal.circle (circleSample0 s)) :
    independentMean (Duplex.samp p 24 P (.beforeZ0 y)).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.beforeZ0 y) w.2) T)) ≤
      (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 24 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  have hpoint (a b : State) :
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ0 y) (p.σ 24 a, b)) T →
        z0Bad' (circleSample0 a) := by
    intro hflip
    have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
        (R0P.SemD3Glue.valuePrefix (P.ext (.beforeZ0 y) (p.σ 24 a, b))) T := hflip
    rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
    have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
      Q (.beforeZ0 y) (p.σ 24 a) T' T hQd hnot
    simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
    rcases hbad with hsem | hz0 | hz1 | hopen
    · rcases hsem with ⟨_, _, hlt, _, _, _⟩
      rw [hQr] at hlt
      omega
    · rcases hz0 with ⟨_, z, hround, _, hc, hb⟩
      rw [hQr] at hround
      rw [hσ a] at hc
      exact (Chal.circle.inj hc).symm ▸ hb
    · rcases hz1 with ⟨_, _, _, _, hround, _, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hopen with ⟨_, _, _, _, _, _, hround, _⟩
      rw [hQr] at hround
      omega
  rw [Duplex.samp_mean p 24 P (.beforeZ0 y)
    (fun c : Duplex.Chal (Chal WideExact WideExact) =>
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.beforeZ0 y) c) T)]
  calc
    mean (fun a : State => mean (fun b : State =>
        indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ0 y) (p.σ 24 a, b)) T)))
        ≤ mean (fun a : State => indicator (z0Bad' (circleSample0 a))) := by
          apply mean_mono
          intro a
          calc
            mean (fun b : State => indicator (¬
                (R0P.SemD3Glue.duplexRows B budget).doomed
                  (P.ext (.beforeZ0 y) (p.σ 24 a, b)) T))
                ≤ mean (fun _ : State => indicator (z0Bad' (circleSample0 a))) := by
                  apply mean_mono
                  intro b
                  apply indicator_mono
                  exact hpoint a b
            _ = indicator (z0Bad' (circleSample0 a)) := mean_const _
    _ ≤ (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
      simpa only [P_eq] using circleSample0_mass

#print axioms circle_row24_D2

/-- The complete row-24 bound for arbitrary messages. -/
theorem circle_row24_all_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 24)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State, p.σ 24 s = Chal.circle (circleSample0 s)) :
    independentMean (Duplex.samp p 24 P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext m w.2) T)) ≤
      (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
  cases m with
  | semantic sm =>
      have hz := duplex_samp_zero_of_stay p 24 P (.semantic sm)
        (R0P.SemD3Glue.duplexRows B budget).doomed T
        (circle24_no_flip B p budget P (.semantic sm) T' T hr hd
          (by intro y h; cases h))
      rw [hz]
      exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
        (pow_nonneg (Nat.cast_nonneg _) _)
  | beforeZ0 y => exact circle_row24_D2 B p budget P y T' T hr hd hσ
  | beforeZ1 y0 =>
      have hz := duplex_samp_zero_of_stay p 24 P (.beforeZ1 y0)
        (R0P.SemD3Glue.duplexRows B budget).doomed T
        (circle24_no_flip B p budget P (.beforeZ1 y0) T' T hr hd
          (by intro y h; cases h))
      rw [hz]
      exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
        (pow_nonneg (Nat.cast_nonneg _) _)
  | opening om =>
      have hz := duplex_samp_zero_of_stay p 24 P (.opening om)
        (R0P.SemD3Glue.duplexRows B budget).doomed T
        (circle24_no_flip B p budget P (.opening om) T' T hr hd
          (by intro y h; cases h))
      rw [hz]
      exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
        (pow_nonneg (Nat.cast_nonneg _) _)

#print axioms circle_row24_all_D2

/-- At the second circle row, a flip implies the second rejection/collision
event, using the previous circle challenge recorded in the prefix. -/
theorem circle_row25_D2
    {L : Nat}
    (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (y : Fin 3 → Fin 29 → WideExact) (y0 : Fin 29 → WideExact)
    (z0 : Point WideExact)
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 25)
    (hprev : (R0P.SemD3Glue.valuePrefix P).rounds.getLast? =
      some (.beforeZ0 y, .circle z0))
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State, p.σ 25 s = Chal.circle (circleSample1 s)) :
    independentMean (Duplex.samp p 25 P (.beforeZ1 y0)).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.beforeZ1 y0) w.2) T)) ≤
      (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 25 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'
    exact hd
  have hz0 : z0 ≠ circleFallback1 :=
    no_hit_last_circle_ne_fallback B Q y z0 hQr hprev hQd.2
  have hpoint (a b : State) :
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ1 y0) (p.σ 25 a, b)) T →
        z1Bad z0 (circleSample1 a) := by
    intro hflip
    have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
        (R0P.SemD3Glue.valuePrefix (P.ext (.beforeZ1 y0) (p.σ 25 a, b))) T := hflip
    rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
    have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
      Q (.beforeZ1 y0) (p.σ 25 a) T' T hQd hnot
    simp only [roundBad, R0P.SemD3Glue.sourceData] at hbad
    rcases hbad with hsem | hz0 | hz1 | hopen
    · rcases hsem with ⟨_, _, hlt, _, _, _⟩
      rw [hQr] at hlt
      omega
    · rcases hz0 with ⟨_, _, hround, _, _, _⟩
      rw [hQr] at hround
      omega
    · rcases hz1 with ⟨_, _, z0', z1, hround, hlast, _, hc, hb⟩
      rw [hQr] at hround
      have heq := Option.some.inj (hprev.symm.trans hlast)
      have hz : z0 = z0' := Chal.circle.inj (congrArg Prod.snd heq)
      subst z0'
      rw [hσ a] at hc
      have hc' : circleSample1 a = z1 := Chal.circle.inj hc
      rw [hc']
      exact hb
    · rcases hopen with ⟨_, _, _, _, _, _, hround, _⟩
      rw [hQr] at hround
      omega
  rw [Duplex.samp_mean p 25 P (.beforeZ1 y0)
    (fun c : Duplex.Chal (Chal WideExact WideExact) =>
      ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext (.beforeZ1 y0) c) T)]
  calc
    mean (fun a : State => mean (fun b : State =>
        indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ1 y0) (p.σ 25 a, b)) T)))
        ≤ mean (fun a : State => indicator (z1Bad z0 (circleSample1 a))) := by
          apply mean_mono
          intro a
          calc
            mean (fun b : State => indicator (¬
                (R0P.SemD3Glue.duplexRows B budget).doomed
                  (P.ext (.beforeZ1 y0) (p.σ 25 a, b)) T))
                ≤ mean (fun _ : State => indicator (z1Bad z0 (circleSample1 a))) := by
                  apply mean_mono
                  intro b
                  apply indicator_mono
                  exact hpoint a b
            _ = indicator (z1Bad z0 (circleSample1 a)) := mean_const _
    _ ≤ (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
      simpa only [P_eq] using circleSample1_mass z0 hz0

#print axioms circle_row25_D2

private theorem circle25_no_flip_of_no_previous
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 25)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hno : ¬ ∃ y : Fin 3 → Fin 29 → WideExact, ∃ z : Point WideExact,
      (R0P.SemD3Glue.valuePrefix P).rounds.getLast? =
        some (.beforeZ0 y, .circle z)) :
    ∀ a b : State,
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m (p.σ 25 a, b)) T := by
  intro a b
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 25 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'; exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m (p.σ 25 a, b))) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m (p.σ 25 a) T' T hQd hnot
  obtain ⟨y, _, z0, _, hprev, _, _, _⟩ :=
    roundBad25_shape B Q m (p.σ 25 a) hQr hbad
  exact hno ⟨y, z0, hprev⟩

#print axioms circle25_no_flip_of_no_previous

private theorem circle25_no_flip_of_wrong_message
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 25)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hmsg : ∀ y0 : Fin 29 → WideExact, m ≠ .beforeZ1 y0) :
    ∀ a b : State,
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m (p.σ 25 a, b)) T := by
  intro a b
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 25 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'; exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m (p.σ 25 a, b))) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m (p.σ 25 a) T' T hQd hnot
  obtain ⟨_, y0, _, _, _, hm, _, _⟩ :=
    roundBad25_shape B Q m (p.σ 25 a) hQr hbad
  exact hmsg y0 hm

#print axioms circle25_no_flip_of_wrong_message

/-- Every outgoing message at row 25 is bounded.  The only nonzero case is
the source's `beforeZ1` constructor when the prefix ends in its required
`beforeZ0` record. -/
theorem circle_row25_all_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 25)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State, p.σ 25 s = Chal.circle (circleSample1 s)) :
    independentMean (Duplex.samp p 25 P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext m w.2) T)) ≤
      (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 := by
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  by_cases hprev : ∃ y : Fin 3 → Fin 29 → WideExact, ∃ z : Point WideExact,
      Q.rounds.getLast? = some (.beforeZ0 y, .circle z)
  · rcases hprev with ⟨y, z0, hprev⟩
    cases m with
    | semantic sm =>
        have hstay := circle25_no_flip_of_wrong_message B p budget P (.semantic sm)
          T' T hr hd (by intro y0 h; cases h)
        rw [Duplex.samp_mean p 25 P (.semantic sm)
          (fun c : Duplex.Chal (Chal WideExact WideExact) =>
            ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.semantic sm) c) T)]
        have hzero : mean (fun a : State => mean (fun b : State =>
            indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.semantic sm) (p.σ 25 a, b)) T))) = 0 := by
          rw [mean_congr (fun a => mean_congr (fun b =>
            indicator_iff (iff_false_intro (fun h => h (hstay a b)))))]
          rw [indicator_false, mean_const, mean_const]
        rw [hzero]
        exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
          (pow_nonneg (Nat.cast_nonneg _) _)
    | beforeZ0 y0 =>
        have hstay := circle25_no_flip_of_wrong_message B p budget P (.beforeZ0 y0)
          T' T hr hd (by intro z h; cases h)
        rw [Duplex.samp_mean p 25 P (.beforeZ0 y0)
          (fun c : Duplex.Chal (Chal WideExact WideExact) =>
            ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.beforeZ0 y0) c) T)]
        have hzero : mean (fun a : State => mean (fun b : State =>
            indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.beforeZ0 y0) (p.σ 25 a, b)) T))) = 0 := by
          rw [mean_congr (fun a => mean_congr (fun b =>
            indicator_iff (iff_false_intro (fun h => h (hstay a b)))))]
          rw [indicator_false, mean_const, mean_const]
        rw [hzero]
        exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
          (pow_nonneg (Nat.cast_nonneg _) _)
    | beforeZ1 y0 => exact circle_row25_D2 B p budget P y y0 z0 T' T hr hprev hd hσ
    | opening om =>
        have hstay := circle25_no_flip_of_wrong_message B p budget P (.opening om)
          T' T hr hd (by intro y0 h; cases h)
        rw [Duplex.samp_mean p 25 P (.opening om)
          (fun c : Duplex.Chal (Chal WideExact WideExact) =>
            ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.opening om) c) T)]
        have hzero : mean (fun a : State => mean (fun b : State =>
            indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.opening om) (p.σ 25 a, b)) T))) = 0 := by
          rw [mean_congr (fun a => mean_congr (fun b =>
            indicator_iff (iff_false_intro (fun h => h (hstay a b)))))]
          rw [indicator_false, mean_const, mean_const]
        rw [hzero]
        exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
          (pow_nonneg (Nat.cast_nonneg _) _)
  · have hstay := circle25_no_flip_of_no_previous B p budget P m T' T hr hd hprev
    have hz := duplex_samp_zero_of_stay p 25 P m
      (R0P.SemD3Glue.duplexRows B budget).doomed T hstay
    rw [hz]
    exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
      (pow_nonneg (Nat.cast_nonneg _) _)

#print axioms circle_row25_all_D2

private theorem opening_no_flip_of_no_event
    {L : Nat} (B : PackBasis F)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : 26 ≤ P.round)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hno : ∀ (O : FS.Prefix (R0FS.Stmt WideExact Sfield)
        (R0FS.Msg WideExact) (R0FS.Chal WideExact))
      (om : R0FS.Msg WideExact),
      R0P.SemSource.openingView (R0P.SemD3Glue.valuePrefix P) = some O →
      m ≠ .opening om) :
    ∀ c : Duplex.Chal (Chal WideExact WideExact),
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m c) T := by
  intro c
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'; exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m c)) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m c.1 T' T hQd hnot
  obtain ⟨O, om, oc, hview, hm, _, _, _⟩ :=
    roundBadOpen_shape B Q m c.1 (by
      dsimp [Q]
      rw [R0P.SemD3Glue.valuePrefix_round]
      omega) hbad
  exact hno O om hview hm

#print axioms opening_no_flip_of_no_event

/-- At opening field rows, the parser either supplies the exact local opening
prefix used by the standalone field bound, or the flip event is empty. -/
theorem opening_field_row_all_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (j : Fin 4) (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State)
    (hr : P.round = 26 + j.val)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hσ : ∀ s : State,
      p.σ (26 + j.val) s = Chal.opening (R0C.V3.DQ.σQ j.val s)) :
    independentMean (Duplex.samp p (26 + j.val) P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext m w.2) T)) ≤
      R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 j.val := by
  cases m with
  | semantic sm =>
      have hstay := opening_no_flip_of_no_event B budget P (.semantic sm) T' T
        (by omega) hd (by intro O om hv h; cases h)
      rw [Duplex.samp_mean p (26 + j.val) P (.semantic sm)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.semantic sm) c) T)]
      have hz : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.semantic sm) (p.σ (26 + j.val) a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ _ a, b))))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg j.val
  | beforeZ0 y =>
      have hstay := opening_no_flip_of_no_event B budget P (.beforeZ0 y) T' T
        (by omega) hd (by intro O om hv h; cases h)
      rw [Duplex.samp_mean p (26 + j.val) P (.beforeZ0 y)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ0 y) c) T)]
      have hz : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ0 y) (p.σ (26 + j.val) a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ _ a, b))))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg j.val
  | beforeZ1 y =>
      have hstay := opening_no_flip_of_no_event B budget P (.beforeZ1 y) T' T
        (by omega) hd (by intro O om hv h; cases h)
      rw [Duplex.samp_mean p (26 + j.val) P (.beforeZ1 y)
        (fun c : Duplex.Chal (Chal WideExact WideExact) =>
          ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ1 y) c) T)]
      have hz : mean (fun a : State => mean (fun b : State =>
          indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
            (P.ext (.beforeZ1 y) (p.σ (26 + j.val) a, b)) T))) = 0 := by
        rw [mean_congr (fun a => mean_congr (fun b =>
          indicator_iff (iff_false_intro (fun h => h (hstay (p.σ _ a, b))))))]
        rw [indicator_false, mean_const, mean_const]
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg j.val
  | opening om =>
      cases hview : R0P.SemSource.openingView
          (R0P.SemD3Glue.valuePrefix P) with
      | none =>
          have hstay := opening_no_flip_of_no_event B budget P (.opening om) T' T
            (by omega) hd (by intro O om' hv h; rw [hview] at hv; cases hv)
          rw [Duplex.samp_mean p (26 + j.val) P (.opening om)
            (fun c : Duplex.Chal (Chal WideExact WideExact) =>
              ¬ (R0P.SemD3Glue.duplexRows B budget).doomed
                (P.ext (.opening om) c) T)]
          have hz : mean (fun a : State => mean (fun b : State =>
              indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
                (P.ext (.opening om) (p.σ (26 + j.val) a, b)) T))) = 0 := by
            rw [mean_congr (fun a => mean_congr (fun b =>
              indicator_iff (iff_false_intro (fun h => h (hstay (p.σ _ a, b))))))]
            rw [indicator_false, mean_const, mean_const]
          rw [hz]
          exact R0C.SlackDensity.epsilonSlack_nonneg
            R0C.ConcreteSlack.delta0_nonneg j.val
      | some O => exact opening_field_row_D2 B p budget P O j om T' T hr hview hd hσ

#print axioms opening_field_row_all_D2

private theorem independentMean_zero_of_pointwise_zero
    {I A O : Type} [Fintype A] (p : Program I A O)
    (f : View I A O → ℚ) (hf : ∀ w, f w = 0) : independentMean p f = 0 := by
  induction p generalizing f with
  | done o => exact hf ([], o)
  | ask i next ih =>
      simp only [independentMean]
      calc
        _ = mean (fun _ : A => (0 : ℚ)) := by
          apply mean_congr
          intro a
          exact ih a _ (fun w => hf ((i, a) :: w.1, w.2))
        _ = 0 := by simp only [mean, Finset.sum_const_zero, zero_div]

#print axioms independentMean_zero_of_pointwise_zero

private theorem round30_no_flip_of_wrong_message
    {L : Nat} (B : PackBasis F) (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State) (hr : P.round = 30)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T')
    (hmsg : ∀ om : R0FS.Msg WideExact, m ≠ .opening om) :
    ∀ c : Duplex.Chal (Chal WideExact WideExact),
      (R0P.SemD3Glue.duplexRows B budget).doomed (P.ext m c) T := by
  intro c
  by_contra hflip
  let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
    R0P.SemD3Glue.valuePrefix P
  have hQr : Q.round = 30 := by
    dsimp [Q]
    rw [R0P.SemD3Glue.valuePrefix_round, hr]
  have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
    change doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix P) T'; exact hd
  have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
      (R0P.SemD3Glue.valuePrefix (P.ext m c)) T := hflip
  rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
  have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
    Q m c.1 T' T hQd hnot
  obtain ⟨_, om, _, _, hm, _, _, _⟩ :=
    roundBadOpen_shape B Q m c.1 (by rw [hQr]; omega) hbad
  exact hmsg om hm

#print axioms round30_no_flip_of_wrong_message

/-- The final combined row uses q22 only when the opening parser applies;
all other message tags, and parser failure, leave no flip event. -/
theorem opening_q22_row30_all_D2
    {L : Nat} (B : PackBasis F)
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (budget : Nat → ℚ)
    (P : FS.Prefix (TypedContext WideExact Sfield)
      (Msg WideExact WideExact (SemMsg WideExact))
      (Duplex.Chal (Chal WideExact WideExact)))
    (m : Msg WideExact WideExact (SemMsg WideExact))
    (T' T : Table (Duplex.Addr L) State) (hr : P.round = 30)
    (hd : (R0P.SemD3Glue.duplexRows B budget).doomed P T') :
    independentMean (R0P.SemD3Glue.combinedSampler p 30 P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
        (P.ext m w.2) T)) ≤
      R0C.SlackStatement.epsilonSlack WideExact
        R0C.SlackStatement.delta0 4 := by
  cases m with
  | semantic sm =>
      have hstay := round30_no_flip_of_wrong_message B budget P (.semantic sm)
        T' T hr hd (by intro om h; cases h)
      have hz := independentMean_zero_of_pointwise_zero
        (R0P.SemD3Glue.combinedSampler p 30 P (.semantic sm)).toProgram
        (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.semantic sm) w.2) T)) (by
            intro w
            exact (indicator_iff (iff_false_intro (fun h => h (hstay w.2)))).trans indicator_false)
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg 4
  | beforeZ0 y =>
      have hstay := round30_no_flip_of_wrong_message B budget P (.beforeZ0 y)
        T' T hr hd (by intro om h; cases h)
      have hz := independentMean_zero_of_pointwise_zero
        (R0P.SemD3Glue.combinedSampler p 30 P (.beforeZ0 y)).toProgram
        (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ0 y) w.2) T)) (by
            intro w
            exact (indicator_iff (iff_false_intro (fun h => h (hstay w.2)))).trans indicator_false)
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg 4
  | beforeZ1 y =>
      have hstay := round30_no_flip_of_wrong_message B budget P (.beforeZ1 y)
        T' T hr hd (by intro om h; cases h)
      have hz := independentMean_zero_of_pointwise_zero
        (R0P.SemD3Glue.combinedSampler p 30 P (.beforeZ1 y)).toProgram
        (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
          (P.ext (.beforeZ1 y) w.2) T)) (by
            intro w
            exact (indicator_iff (iff_false_intro (fun h => h (hstay w.2)))).trans indicator_false)
      rw [hz]
      exact R0C.SlackDensity.epsilonSlack_nonneg
        R0C.ConcreteSlack.delta0_nonneg 4
  | opening om =>
      cases hview : R0P.SemSource.openingView
          (R0P.SemD3Glue.valuePrefix P) with
      | none =>
          have hstay : ∀ c : Duplex.Chal (Chal WideExact WideExact),
              (R0P.SemD3Glue.duplexRows B budget).doomed
                (P.ext (.opening om) c) T := by
            intro c
            by_contra hflip
            let Q : Prefix WideExact WideExact (TypedContext WideExact Sfield) (SemMsg WideExact) :=
              R0P.SemD3Glue.valuePrefix P
            have hQround : Q.round = 30 := by
              dsimp [Q]
              rw [R0P.SemD3Glue.valuePrefix_round, hr]
            have hQd : doomed (R0P.SemD3Glue.sourceData B) Q T' := by
              change doomed (R0P.SemD3Glue.sourceData B)
                (R0P.SemD3Glue.valuePrefix P) T'; exact hd
            have hnot : ¬ doomed (R0P.SemD3Glue.sourceData B)
                (R0P.SemD3Glue.valuePrefix (P.ext (.opening om) c)) T := hflip
            rw [R0P.SemD3Glue.valuePrefix_ext] at hnot
            have hbad := doomed_ext_roundBad (R0P.SemD3Glue.sourceData B)
              Q (.opening om) c.1 T' T hQd hnot
            obtain ⟨_, om', _, hv, hm, _, _, _⟩ :=
              roundBadOpen_shape B Q (.opening om) c.1 (by rw [hQround]; omega) hbad
            rw [hview] at hv
            cases hv
          have hz := independentMean_zero_of_pointwise_zero
            (R0P.SemD3Glue.combinedSampler p 30 P (.opening om)).toProgram
            (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B budget).doomed
              (P.ext (.opening om) w.2) T)) (by
                intro w
                exact (indicator_iff (iff_false_intro (fun h => h (hstay w.2)))).trans indicator_false)
          rw [hz]
          exact R0C.SlackDensity.epsilonSlack_nonneg
            R0C.ConcreteSlack.delta0_nonneg 4
      | some O => exact opening_q22_row_D2 B p budget P O om T' T hr hview hd

#print axioms opening_q22_row30_all_D2

/-- The authorized per-round D2 schedule: semantic candidate mass for rows
0--23, the two circle-row bounds, four opening field rows, then q22. -/
def combinedD2Budget (i : Nat) : ℚ :=
  if h : i < 24 then
    (1 + deltaQ) * ((100 * semRoundBudget (⟨i, h⟩ : Fin 24) : Nat) /
      (AspisCircleGroupOrder.P ^ 4 : ℚ))
  else if i < 26 then
    (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4
  else if i < 30 then
    R0C.SlackStatement.epsilonSlack WideExact
      R0C.SlackStatement.delta0 (i - 26)
  else
    R0C.SlackStatement.epsilonSlack WideExact
      R0C.SlackStatement.delta0 4

#print axioms combinedD2Budget

/-- Full D2 bridge for the mixed 31-round protocol.  The four sigma clauses
are the source-fixed challenge decoders for the semantic, circle, and field
rows; row 30 is the literal q22 chain and has no separate sigma decoder. -/
theorem combinedProtocol_D2
    {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
      (Chal WideExact WideExact) L)
    (msg : Pf → Nat → Msg WideExact WideExact (SemMsg WideExact))
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext WideExact Sfield) (Msg WideExact WideExact (SemMsg WideExact))
        (Duplex.Chal (Chal WideExact WideExact)) × Msg WideExact WideExact (SemMsg WideExact) ×
          Duplex.Chal (Chal WideExact WideExact))))
    (hσsem : ∀ (i : Nat) (_hi : i < 24) (s : State),
      p.σ i s = Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 24 s = Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 25 s = Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (26 + j.val) s = Chal.opening (R0C.V3.DQ.σQ j.val s)) :
    FS2.D2 (R0P.SemD3Glue.combinedProtocol B p msg decode)
      (R0P.SemD3Glue.duplexRows B combinedD2Budget) := by
  intro i P m T' T hround hi hd
  have hi31 : i < 31 := hi
  change independentMean
      (R0P.SemD3Glue.combinedSampler p i P m).toProgram
      (fun w => indicator (¬ (R0P.SemD3Glue.duplexRows B combinedD2Budget).doomed
        (P.ext m w.2) T)) ≤ combinedD2Budget i
  by_cases h24 : i < 24
  · have hsamp : R0P.SemD3Glue.combinedSampler p i P m = Duplex.samp p i P m := by
      simp only [R0P.SemD3Glue.combinedSampler, if_pos (show i < 30 by omega)]
    rw [hsamp]
    have hD := semantic_row_D2 B p combinedD2Budget i P m T' T hround h24 hd
      (hσsem i h24)
    simpa only [combinedD2Budget, dif_pos h24] using hD
  · by_cases h26 : i < 26
    · have hi24 : i = 24 ∨ i = 25 := by omega
      rcases hi24 with rfl | rfl
      · have hsamp : R0P.SemD3Glue.combinedSampler p 24 P m = Duplex.samp p 24 P m := by
          simp only [R0P.SemD3Glue.combinedSampler, if_pos (show (24 : Nat) < 30 by omega)]
        rw [hsamp]
        have hD := circle_row24_all_D2 B p combinedD2Budget P m T' T hround hd hσz0
        simpa only [combinedD2Budget, dif_neg (show ¬ (24 : Nat) < 24 by omega),
          if_pos (show (24 : Nat) < 26 by omega)] using hD
      · have hsamp : R0P.SemD3Glue.combinedSampler p 25 P m = Duplex.samp p 25 P m := by
          simp only [R0P.SemD3Glue.combinedSampler, if_pos (show (25 : Nat) < 30 by omega)]
        rw [hsamp]
        have hD := circle_row25_all_D2 B p combinedD2Budget P m T' T hround hd hσz1
        simpa only [combinedD2Budget, dif_neg (show ¬ (25 : Nat) < 24 by omega),
          if_pos (show (25 : Nat) < 26 by omega)] using hD
    · by_cases h30 : i < 30
      · have hj : i - 26 < 4 := by omega
        let j : Fin 4 := ⟨i - 26, hj⟩
        have hij : i = 26 + j.val := by dsimp [j]; omega
        rw [hij]
        have hsamp : R0P.SemD3Glue.combinedSampler p (26 + j.val) P m =
            Duplex.samp p (26 + j.val) P m := by
          simp only [R0P.SemD3Glue.combinedSampler, if_pos (show 26 + j.val < 30 by omega)]
        rw [hsamp]
        have hD := opening_field_row_all_D2 B p combinedD2Budget P j m T' T (hround.trans hij) hd
          (hσopen j)
        simpa only [combinedD2Budget, dif_neg (show ¬ 26 + j.val < 24 by omega),
          if_neg (show ¬ 26 + j.val < 26 by omega), if_pos (show 26 + j.val < 30 by omega),
          Nat.add_sub_cancel_left] using hD
      · have hi30 : i = 30 := by omega
        rw [hi30]
        have hD := opening_q22_row30_all_D2 B p combinedD2Budget P m T' T (hround.trans hi30) hd
        simpa only [combinedD2Budget, dif_neg (show ¬ (30 : Nat) < 24 by omega),
          if_neg (show ¬ (30 : Nat) < 26 by omega), if_neg (show ¬ (30 : Nat) < 30 by omega)] using hD

#print axioms combinedProtocol_D2

end
end R0P.SemSource
