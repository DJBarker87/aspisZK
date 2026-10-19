import R1UnifiedSemanticContext
import R1ReseedSamplerLaw
import R1PrefixAnswers
import R1UnifiedSemanticDecoder

/-! A typed decoder for the single opening-reseed round after the semantic
prefix. The parsed context is the same context used by the ordinary decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedReseedDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

abbrev Completion (M Cv : Type) (L : Nat) :=
  UnifiedSemanticDecoder.Completion M Cv L

def own (p : Params M Cv L) (pub : UnifiedSampler.Public L) (a : Addr L) :
    BS (Addr L) State State :=
  ReseedSamplerLaw.own p a
    (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega))

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) : Option (Completion M Cv L) :=
  (UnifiedSemanticContext.parse p pub.pubBytes a T).bind fun ctx =>
    if ctx.records.length = 26 then
      some (own p pub a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx)
    else none

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (hp : UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx)
    (hlen : ctx.records.length = 26) :
    decode p pub a T =
      some (own p pub a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx) := by
  simp [decode, hp, hlen]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own' : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own', pend, g)) :
    ∃ ctx : UnifiedSemanticContext.Context M,
      UnifiedSemanticContext.parse p pub.pubBytes a T = some ctx ∧
      ctx.records.length = 26 ∧
      (own p pub a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx) = (own', pend, g) := by
  unfold decode at hd
  cases hp : UnifiedSemanticContext.parse p pub.pubBytes a T with
  | none => simp [hp] at hd
  | some ctx =>
      rw [hp] at hd
      simp only [Option.bind_some] at hd
      by_cases hlen : ctx.records.length = 26
      · refine ⟨ctx, rfl, hlen, ?_⟩
        simp [hlen] at hd
        rcases hd with ⟨hown, hpend, hg⟩
        cases hown
        cases hpend
        cases hg
        rfl
      · simp [hlen] at hd

theorem decoded_round (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own' : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own', pend, g)) (x : State) (as : List State) :
    (g x as).1.rounds.length = 26 := by
  obtain ⟨ctx, hp, hlen, heq⟩ := decode_sound p pub a T own' pend g hd
  have hfun : UnifiedSemanticDecoder.output p pub T ctx = g := by
    have h := congrArg (fun z : Completion M Cv L => z.2.2) heq
    simpa using h
  rw [← hfun, UnifiedSemanticDecoder.output_round]
  exact hlen

#print axioms decode_of_parse
#print axioms decode_sound
#print axioms decoded_round

end AspisR1.UnifiedReseedDecoder
end
