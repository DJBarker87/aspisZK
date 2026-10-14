import R1InitialDecoder
import R1JointTranscriptView
import R0C.V3.Gen

/-! The first-round decoder presented in the shared transcript-view type.
This is a representation wrapper around the checked public initialization
parser and the existing initial sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedInitialDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

def view (pub : UnifiedSampler.Public L)
    (out : InitialDecoder.Output Cv) : JointTranscriptView.Output M Cv L :=
  (FS.emptyPrefix pub, TranscriptView.Message.initial out.1,
    TranscriptView.liftChallenge out.2)

def output (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (c1 x : State) (bs : List State) : JointTranscriptView.Output M Cv L :=
  view pub (InitialDecoder.output p c1 x bs)

def decode (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv)
      (Addr L) State State :=
  fun a T => (InitialDecoder.decode p hD pub.pubBytes a T).map
    fun (own, pend, g) => (own, pend, fun x bs => view pub (g x bs))

theorem decode_of_parse (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (c1 : State)
    (hp : PublicInitParse.parse pub.pubBytes a = some c1) :
    decode p hD pub a T = some
      (InitialSamplerLaw.own p a (PublicInitFrame.row0 p hD), [],
        fun x bs => output p pub c1 x bs) := by
  simp only [decode, InitialDecoder.decode, hp, Option.map_some]
  rfl

theorem decode_sound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p hD pub a T = some (own, pend, g)) :
    ∃ c1, PublicInitParse.parse pub.pubBytes a = some c1 ∧
      (own, pend, g) =
        (InitialSamplerLaw.own p a (PublicInitFrame.row0 p hD), [],
          fun x bs => output p pub c1 x bs) := by
  unfold decode InitialDecoder.decode at hd
  cases hp : PublicInitParse.parse pub.pubBytes a with
  | none => simp [hp] at hd
  | some c1 =>
      simp only [hp, Option.map_some] at hd
      cases hd
      exact ⟨c1, rfl, rfl⟩

theorem decoded_round (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p hD pub a T = some (own, pend, g))
    (x : State) (as : List State) : (g x as).1.round = 0 := by
  obtain ⟨c1, hp, htuple⟩ := decode_sound p hD pub a T own pend g hd
  have hg : g = fun x bs => output p pub c1 x bs := by
    cases htuple
    rfl
  rw [hg]
  rfl

theorem follows_map (pub : UnifiedSampler.Public L)
    (g : State → List State → InitialDecoder.Output Cv)
    (tr : List (Addr L × State)) (own : BS (Addr L) State State)
    (pend : List (Addr L × Option State)) (T : Table (Addr L) State)
    (out : InitialDecoder.Output Cv)
    (h : bfollow g tr own pend T = some out) :
    bfollow (fun x bs => view (M := M) pub (g x bs)) tr own pend T =
      some (view (M := M) pub out) := by
  rw [BackgroundOutputMap.bfollow_map, h]
  rfl

#print axioms decode_of_parse
#print axioms decode_sound
#print axioms decoded_round
#print axioms follows_map

end AspisR1.UnifiedInitialDecoder
end
