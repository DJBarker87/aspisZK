import R1UnifiedSemanticContext
import R1PrefixNextLaw
import R1JointTranscriptView
import R1PrefixRecordLength

/-! A typed ordinary-prefix decoder interface. The output view is the
ordinary transcript representation associated with the parsed context. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

abbrev Completion (M Cv : Type) (L : Nat) :=
  BS (Addr L) State State × List (Addr L × Option State) ×
    (State → List State → JointTranscriptView.Output M Cv L)

def view (pub : UnifiedSampler.Public L) (ctx : UnifiedSemanticContext.Context M)
    (out : List (M × Chal Cv) × Chal Cv) : JointTranscriptView.Output M Cv L :=
  (⟨pub, TranscriptView.ordinary ctx.c1 out.1⟩, .payload ctx.message,
    TranscriptView.liftChallenge out.2)

def output (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (x : State) (as : List State) : JointTranscriptView.Output M Cv L :=
  view pub ctx (PrefixNextLaw.output p T ctx.records x as)

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) : Option (Completion M Cv L) :=
  (UnifiedSemanticContext.parse p pub.pubBytes a T).bind fun ctx =>
    if 0 < ctx.records.length ∧ ctx.records.length < 26 then
      some (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx)
    else none

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (hp : UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx)
    (hlo : 0 < ctx.records.length) (hhi : ctx.records.length < 26) :
    decode p pub a T =
      some (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx) := by
  simp [decode, hp, hlo, hhi]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own, pend, g)) :
    ∃ ctx : UnifiedSemanticContext.Context M,
      UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx ∧
      0 < ctx.records.length ∧ ctx.records.length < 26 ∧
      (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx) = (own, pend, g) := by
  unfold decode at hd
  cases hp : UnifiedSemanticContext.parse p pub.pubBytes a T with
  | none => simp [hp] at hd
  | some ctx =>
      by_cases hlo : 0 < ctx.records.length
      · by_cases hhi : ctx.records.length < 26
        · refine ⟨ctx, rfl, hlo, hhi, ?_⟩
          simp only [Option.bind_some, hlo, hhi, ↓reduceIte] at hd
          exact Option.some.inj hd
        · simp [hp, hlo, hhi] at hd
      · simp [hp, hlo] at hd

theorem output_round (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (x : State) (as : List State) :
    (output p pub T ctx x as).1.rounds.length = ctx.records.length := by
  unfold output view
  rw [TranscriptView.ordinary_length]
  change (PrefixAnswers.fromAnswers p T 0 ctx.records
    (as.take (PrefixAnswers.missing p T ctx.records).length)).length = ctx.records.length
  exact PrefixRecordLength.fromAnswers_length p T 0 ctx.records _

theorem decoded_round_bounds (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own, pend, g)) (x : State) (as : List State) :
    0 < (g x as).1.rounds.length ∧ (g x as).1.rounds.length < 26 := by
  obtain ⟨ctx, hp, hlo, hhi, heq⟩ := decode_sound p pub a T own pend g hd
  have hfun : output p pub T ctx = g := by
    have h := congrArg (fun z : Completion M Cv L => z.2.2) heq
    simpa using h
  have hr := output_round p pub T ctx x as
  rw [hfun] at hr
  exact ⟨by omega, by omega⟩

theorem follows_map (pub : UnifiedSampler.Public L)
    (ctx : UnifiedSemanticContext.Context M)
    (g : State → List State → List (M × Chal Cv) × Chal Cv)
    (tr : List (Addr L × State)) (own : BS (Addr L) State State)
    (pend : List (Addr L × Option State)) (T : Table (Addr L) State)
    (out : List (M × Chal Cv) × Chal Cv)
    (h : bfollow g tr own pend T = some out) :
    bfollow (fun x as => view pub ctx (g x as)) tr own pend T =
      some (view pub ctx out) := by
  have hm := BackgroundOutputMap.bfollow_map (view pub ctx) g tr own pend T
  rw [h] at hm
  exact hm

#print axioms decode_of_parse
#print axioms decode_sound
#print axioms output_round
#print axioms decoded_round_bounds
#print axioms follows_map

end AspisR1.UnifiedSemanticDecoder
end
