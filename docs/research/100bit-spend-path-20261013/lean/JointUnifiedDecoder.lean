import R1JointTranscriptView
import R0C.V3.Gen

/-! The row-32 component in the existing v3 decoder interface. The guard
requires 31 ordinary records before the recovered query. Other rounds and
the global decoder dispatch remain separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointUnifiedDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (semanticFuel openingFuel : Nat) :
    Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv) (Addr L) State State :=
  fun c T => (JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T).bind
    fun ctx => if ctx.records.length = 31 then
      some (QueryNextLaw.own p c,
        (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
        fun x as => JointTranscriptView.view pub (JointDecoder.output p T ctx x as))
    else none

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (hp : JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T = some ctx)
    (hl : ctx.records.length = 31) :
    decode p pub semanticFuel openingFuel c T =
      some (QueryNextLaw.own p c,
        (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
        fun x as => JointTranscriptView.view pub (JointDecoder.output p T ctx x as)) := by
  simp only [decode, hp, Option.bind_some, hl, ↓reduceIte]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub semanticFuel openingFuel c T = some (own, pend, g)) :
    ∃ ctx : JointContext.Context M L,
      JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T = some ctx ∧
      ctx.records.length = 31 ∧
      (QueryNextLaw.own p c,
        (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
        fun x as => JointTranscriptView.view pub (JointDecoder.output p T ctx x as)) =
        (own, pend, g) := by
  cases hp : JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T with
  | none => simp [decode, hp] at hd
  | some ctx =>
      by_cases hl : ctx.records.length = 31
      · refine ⟨ctx, rfl, hl, ?_⟩
        apply Option.some.inj
        simpa only [decode, hp, Option.bind_some, hl, ↓reduceIte] using hd
      · simp [decode, hp, hl] at hd

theorem decoded_round (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub semanticFuel openingFuel c T = some (own, pend, g))
    (x : State) (as : List State) : (g x as).1.round = 32 := by
  obtain ⟨ctx, hp, hl, hs⟩ := decode_sound p pub semanticFuel openingFuel c T own pend g hd
  cases hs
  change (JointTranscriptView.mkPrefix pub ctx.c1 ctx.queryMessage
    (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint
      (as.take (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length))).rounds.length = 32
  exact JointTranscriptView.parsed_prefix_length p pub semanticFuel openingFuel c T ctx hp hl _

#print axioms decode_of_parse
#print axioms decode_sound
#print axioms decoded_round

end AspisR1.JointUnifiedDecoder
end
