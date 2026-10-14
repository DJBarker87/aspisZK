import R1UnifiedOpeningDecoder
import R1UnifiedSemanticLaw
import R1QueryBackgroundChain

/-! Decode the query boundary after the 31-round opening prefix. This is an
interface for the existing scan result and semantic transcript view. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

abbrev Completion (M Cv : Type) (L : Nat) :=
  BS (Addr L) State (List State) × List (Addr L × Option State) ×
    (List State → List State → JointTranscriptView.Output M Cv L)

def own (p : Params M Cv L) (a : Addr L) : BS (Addr L) State (List State) :=
  .ask a fun s => QueryBackgroundChain.chainBS p 8 s [s]

def output (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (xs as : List State) : JointTranscriptView.Output M Cv L :=
  let mlen := (PrefixAnswers.missing p T ctx.records).length
  (UnifiedSemanticLaw.mkPrefix p pub T ctx (as.take mlen),
    .payload ctx.message,
    UnifiedSampler.liftQuery
      (Q22.scanOut 8 Q22.q0 (as.drop mlen) xs.tail (xs.headD default)))

theorem output_append (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (xs as bs : List State)
    (hlen : as.length = (PrefixAnswers.missing p T ctx.records).length) :
    output p pub T ctx xs (as ++ bs) =
      (UnifiedSemanticLaw.mkPrefix p pub T ctx as, .payload ctx.message,
        UnifiedSampler.liftQuery (Q22.scanOut 8 Q22.q0 bs xs.tail (xs.headD default))) := by
  dsimp only [output]
  have htake : (as ++ bs).take (PrefixAnswers.missing p T ctx.records).length = as := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdrop : (as ++ bs).drop (PrefixAnswers.missing p T ctx.records).length = bs := by
    rw [List.drop_append_of_le_length (by omega),
      List.drop_of_length_le (by omega), List.nil_append]
  rw [htake, hdrop]

theorem output_round (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (xs as : List State) :
    (output p pub T ctx xs as).1.rounds.length = ctx.records.length := by
  unfold output UnifiedSemanticLaw.mkPrefix
  rw [TranscriptView.ordinary_length]
  exact PrefixRecordLength.fromAnswers_length p T 0 ctx.records _

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) : Option (Completion M Cv L) :=
  (UnifiedOpeningDecoder.parse p pub a T).bind fun ctx =>
    if ctx.records.length = 31 then
      some (own p a, (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx)
    else none

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (hp : UnifiedOpeningDecoder.parse p pub a T = some ctx)
    (hlen : ctx.records.length = 31) :
    decode p pub a T =
      some (own p a, (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx) := by
  simp [decode, hp, hlen]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own' : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own', pend, g)) :
    ∃ ctx : UnifiedSemanticContext.Context M,
      UnifiedOpeningDecoder.parse p pub a T = some ctx ∧
      ctx.records.length = 31 ∧
      (own p a, (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        output p pub T ctx) = (own', pend, g) := by
  unfold decode at hd
  cases hp : UnifiedOpeningDecoder.parse p pub a T with
  | none => simp [hp] at hd
  | some ctx =>
    rw [hp] at hd
    simp only [Option.bind_some] at hd
    by_cases hlen : ctx.records.length = 31
    · refine ⟨ctx, rfl, hlen, ?_⟩
      simp [hlen] at hd
      rcases hd with ⟨hown, hpend, hg⟩
      cases hown
      cases hpend
      cases hg
      rfl
    · simp [hlen] at hd

theorem decoded_round_eq_31 (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own' : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own', pend, g)) (xs as : List State) :
    (g xs as).1.rounds.length = 31 := by
  obtain ⟨ctx, hp, hlen, heq⟩ := decode_sound p pub a T own' pend g hd
  have hfun : output p pub T ctx = g := by
    have h := congrArg (fun z : Completion M Cv L => z.2.2) heq
    simpa using h
  rw [← hfun]
  rw [output_round, hlen]

#print axioms output_append
#print axioms output_round
#print axioms decode_of_parse
#print axioms decode_sound
#print axioms decoded_round_eq_31

end AspisR1.UnifiedQueryDecoder
end
