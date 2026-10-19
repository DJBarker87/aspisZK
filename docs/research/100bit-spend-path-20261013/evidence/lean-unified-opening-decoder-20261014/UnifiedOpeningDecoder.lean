import R1OpeningPrefixCompletion
import R1UnifiedSemanticDecoder

/-! Decode the typed semantic context at the semantic-to-opening boundary.
This adds a row-length guard to the existing deterministic output view. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

def parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) :
    Option (UnifiedSemanticContext.Context M) :=
  (parseAbsorb a).bind fun (endpoint, label, data) =>
    (OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4 endpoint).bind
      fun (c1, rs) =>
        (IndexedMessage.read p rs.length label data).map fun m =>
          ({ c1 := c1, records := rs, message := m } : UnifiedSemanticContext.Context M)

theorem parse_of_checks (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (endpoint : State) (label : Byte) (data : Bytes)
    (c1 : State) (rs : List (Rec M)) (message : M)
    (habs : parseAbsorb a = some (endpoint, label, data))
    (htyped : OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4 endpoint =
      some (c1, rs))
    (hread : IndexedMessage.read p rs.length label data = some message) :
    parse p pub a T = some ⟨c1, rs, message⟩ := by
  simp [parse, habs, htyped, hread]

theorem parse_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (h : parse p pub a T = some ctx) :
    ∃ endpoint label data,
      parseAbsorb a = some (endpoint, label, data) ∧
      OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4 endpoint =
        some (ctx.c1, ctx.records) ∧
      IndexedMessage.read p ctx.records.length label data = some ctx.message := by
  unfold parse at h
  cases habs : parseAbsorb a with
  | none => simp [habs] at h
  | some parsed =>
    rcases parsed with ⟨endpoint, label, data⟩
    simp only [habs, Option.bind_some] at h
    cases htyped : OpeningPrefixCompletion.typed p pub.pubBytes pub.tag T 27 4 endpoint with
    | none => simp [htyped] at h
    | some recovered =>
      rcases recovered with ⟨c1, rs⟩
      simp only [htyped, Option.bind_some] at h
      cases hread : IndexedMessage.read p rs.length label data with
      | none => simp [hread] at h
      | some message =>
        simp only [hread, Option.map_some] at h
        have hctx : ({ c1 := c1, records := rs, message := message } :
            UnifiedSemanticContext.Context M) = ctx := by
          exact Option.some.inj h
        subst ctx
        exact ⟨endpoint, label, data, rfl, htyped, hread⟩

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) :
    Option (UnifiedSemanticDecoder.Completion M Cv L) :=
  (parse p pub a T).bind fun ctx =>
    if 27 ≤ ctx.records.length ∧ ctx.records.length < 31 then
      some (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx)
    else none

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State) (ctx : UnifiedSemanticContext.Context M)
    (hp : parse p pub a T = some ctx)
    (hlo : 27 ≤ ctx.records.length) (hhi : ctx.records.length < 31) :
    decode p pub a T =
      some (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx) := by
  simp [decode, hp, hlo, hhi]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own, pend, g)) :
    ∃ ctx : UnifiedSemanticContext.Context M,
      parse p pub a T = some ctx ∧
      27 ≤ ctx.records.length ∧ ctx.records.length < 31 ∧
      (QueryNextLaw.own p a,
        (PrefixAnswers.missing p T ctx.records).map fun b => (b, none),
        UnifiedSemanticDecoder.output p pub T ctx) = (own, pend, g) := by
  unfold decode at hd
  cases hp : parse p pub a T with
  | none => simp [hp] at hd
  | some ctx =>
    rw [hp] at hd
    simp only [Option.bind_some] at hd
    by_cases hlo : 27 ≤ ctx.records.length
    · by_cases hhi : ctx.records.length < 31
      · refine ⟨ctx, rfl, hlo, hhi, ?_⟩
        simp [hlo, hhi] at hd
        rcases hd with ⟨hown, hpend, hg⟩
        cases hown
        cases hpend
        cases hg
        rfl
      · simp [hlo, hhi] at hd
    · simp [hlo] at hd

theorem decoded_round_bounds (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub a T = some (own, pend, g)) (x : State) (as : List State) :
    27 ≤ (g x as).1.rounds.length ∧ (g x as).1.rounds.length < 31 := by
  obtain ⟨ctx, hp, hlo, hhi, heq⟩ := decode_sound p pub a T own pend g hd
  have hfun : UnifiedSemanticDecoder.output p pub T ctx = g := by
    have h := congrArg (fun z : UnifiedSemanticDecoder.Completion M Cv L => z.2.2) heq
    simpa using h
  have hr := UnifiedSemanticDecoder.output_round p pub T ctx x as
  rw [hfun] at hr
  omega

#print axioms parse_of_checks
#print axioms parse_sound
#print axioms decode_of_parse
#print axioms decode_sound
#print axioms decoded_round_bounds

end AspisR1.UnifiedOpeningDecoder
end
