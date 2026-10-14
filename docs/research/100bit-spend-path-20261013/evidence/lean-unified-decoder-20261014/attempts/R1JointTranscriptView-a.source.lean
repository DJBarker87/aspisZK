import R1JointDecoder
import R1JointRecoveryTotal
import R1UnifiedSamplerLaw

/-! Represent the joint completing decoder's output as the unified prefix,
message and challenge. If recovery is absent no query row is invented;
successful context parsing rules out that branch for every answer list. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointTranscriptView

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

abbrev Output (M Cv : Type) (L : Nat) :=
  UnifiedSampler.Prefix M Cv L × Message M × Challenge Cv

def prefix (pub : UnifiedSampler.Public L) (c1 : State) (qm : M)
    (completed : JointNextLaw.Completed M Cv L) : UnifiedSampler.Prefix M Cv L :=
  match completed.2 with
  | none => ⟨pub, ordinary c1 completed.1⟩
  | some (_, qr) => ⟨pub, withQuery c1 completed.1 qm qr⟩

def view (pub : UnifiedSampler.Public L) (out : JointDecoder.Output M Cv L) :
    Output M Cv L :=
  (prefix pub out.1 out.2.1 out.2.2.2.1,
    .payload out.2.2.1, liftChallenge out.2.2.2.2)

theorem view_some (pub : UnifiedSampler.Public L) (c1 : State) (qm nm : M)
    (rounds : List (M × Chal Cv)) (a : Addr L)
    (qr : AspisV8R19.Q22SamplerProgram.Result) (ch : Chal Cv) :
    view pub (c1, qm, nm, ((rounds, some (a, qr)), ch)) =
      (⟨pub, withQuery c1 rounds qm qr⟩, .payload nm, liftChallenge ch) := rfl

theorem follows_map (pub : UnifiedSampler.Public L)
    (g : State → List State → JointDecoder.Output M Cv L)
    (tr : List (Addr L × State)) (own : BS (Addr L) State State)
    (pend : List (Addr L × Option State)) (T : Table (Addr L) State)
    (out : JointDecoder.Output M Cv L)
    (h : bfollow g tr own pend T = some out) :
    bfollow (fun x as => view pub (g x as)) tr own pend T = some (view pub out) := by
  rw [BackgroundOutputMap.bfollow_map, h]
  rfl

theorem parsed_prefix_length (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (hparse : JointContext.parse p pub.pubBytes pub.tag semanticFuel openingFuel c T =
      some ctx) (hlen : ctx.records.length = 31) (as : List State) :
    (prefix pub ctx.c1 ctx.queryMessage
      (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as)).rounds.length = 32 := by
  obtain ⟨qr, hqr⟩ := JointRecoveryTotal.fromAnswers_has_query p pub.pubBytes pub.tag
    semanticFuel openingFuel c T ctx hparse as
  simp only [prefix, hqr, TranscriptView.withQuery_length]
  change (completeRounds p T _ 0 ctx.records).length + 1 = 32
  rw [completeRounds_length, hlen]

#print axioms view_some
#print axioms follows_map
#print axioms parsed_prefix_length

end AspisR1.JointTranscriptView
end
