import AspisV8R19.R211CircleDomain
import AspisV8R19.R181SampledChordGuard

/-! The actual success/inequality premises justify the algebraic chord domain
at every CM31 circle point. No distribution or optimized inverse execution
is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R212SampledChordDomain
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open DuplexFrames SourceDuplexStep
open R165QuarticExecution (decode)
noncomputable section
local instance : DecidableEq circle.SecureCirclePoint := Classical.decEq _

 def lineValue (p q : circle.SecureCirclePoint) (x y : CM31Exact) : QM31Exact :=
    decode p.x * decode q.y - decode p.y * decode q.x +
      (decode p.y - decode q.y) * algebraMap CM31Exact QM31Exact x +
      (decode q.x - decode p.x) * algebraMap CM31Exact QM31Exact y

 theorem sampled_line_nonzero (H : Bytes → State) (s0 s1 : State)
    (p q : circle.SecureCirclePoint) (t0 t1 : transcript.Transcript)
    (h0 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s0) = .ok (.Ok p,t0))
    (h1 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s1) = .ok (.Ok q,t1))
    (hne : core.cmp.PartialEq.ne.trait_default
      circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint p q = .ok true)
    (x y : CM31Exact) (hcircle : x^2+y^2=1) : lineValue p q x y ≠ 0 := by
  obtain ⟨a,ha,hda,hp⟩ := R211CircleDomain.successful_parameter H s0 p t0 h0
  obtain ⟨b,hb,hdb,hq⟩ := R211CircleDomain.successful_parameter H s1 q t1 h1
  have hpq : p ≠ q := by
    have hcmp := R181SampledChordGuard.raw_secure_circle_point_ne p q
    rw [hne] at hcmp
    exact of_decide_eq_true (Result.ok.inj hcmp).symm
  have hpoints : SamplerCirclePolicy.point a ≠ SamplerCirclePolicy.point b := by
    intro he
    apply hpq
    rw [hp,hq,he]
  have hn := AspisV8R15.ExactTowerChord.source_policy_chord_nonzero
    a b x y hda hdb hpoints ha hb hcircle
  rw [hp,hq]
  simpa only [lineValue,R166CircleExecution.encodePoint,R165QuarticExecution.decode_encode,
    SamplerCirclePolicy.point,AspisV8R15.CircleChord.chord] using hn

#print axioms sampled_line_nonzero
end
end AspisV8R19.R212SampledChordDomain
