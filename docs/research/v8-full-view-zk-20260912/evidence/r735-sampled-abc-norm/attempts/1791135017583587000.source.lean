import AspisV8R19.R212SampledChordDomain
import AspisV8R19.R732SelectedAbcNorm

/-! Exact sampled-pair chord-coordinate norm.  This is conditional on two
successful selected circle samples and their checked inequality; it does not
identify a complete callback trace or acceptance event. -/
set_option autoImplicit false
namespace AspisV8R19.R735SampledAbcNorm
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open DuplexFrames SourceDuplexStep
open R165QuarticExecution (decode)
noncomputable section
local instance : DecidableEq circle.SecureCirclePoint := Classical.decEq _

/-- Two distinct points on a unit circle have nonzero squared chord norm,
including the vertical-chord case. -/
theorem unit_circle_pair_norm_ne_zero {F : Type*} [Field F] [NeZero (2 : F)]
    (x0 y0 x1 y1 : F) (h0 : x0^2 + y0^2 = 1) (h1 : x1^2 + y1^2 = 1)
    (hne : (x0,y0) ≠ (x1,y1)) :
    (y0-y1)^2 + (x1-x0)^2 ≠ 0 := by
  by_cases hx : x1-x0 ≠ 0
  · exact R732SelectedAbcNorm.selected_abc_norm_ne_zero x0 y0 x1 y1 h0 h1 hx
  · have hxeq : x1 = x0 := sub_eq_zero.mp (not_ne_iff.mp hx)
    intro hz
    have hy2 : (y0-y1)^2 = 0 := by simpa [hxeq] using hz
    have hyeq : y0 = y1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hy2)
    apply hne
    simp [hxeq,hyeq]

/-- Two successful actual selected secure-circle samples which pass the raw
point-inequality guard have nonzero decoded `abc` `(b,c)` norm. -/
theorem sampled_decoded_abc_norm_ne_zero
    (H : Bytes → State) (s0 s1 : State)
    (p q : circle.SecureCirclePoint) (t0 t1 : transcript.Transcript)
    (h0 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s0) = .ok (.Ok p,t0))
    (h1 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s1) = .ok (.Ok q,t1))
    (hne : core.cmp.PartialEq.ne.trait_default
      circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint p q = .ok true) :
    (decode p.y-decode q.y)^2 + (decode q.x-decode p.x)^2 ≠ 0 := by
  letI : NeZero (2 : QM31Exact) := ⟨AspisV8R15.ExactTowerChord.two_ne_zero⟩
  obtain ⟨a,ha,hda,hp⟩ := R211CircleDomain.successful_parameter H s0 p t0 h0
  obtain ⟨b,hb,hdb,hq⟩ := R211CircleDomain.successful_parameter H s1 q t1 h1
  have hpq : p ≠ q := by
    have hcmp := R181SampledChordGuard.raw_secure_circle_point_ne p q
    rw [hne] at hcmp
    exact of_decide_eq_true (Result.ok.inj hcmp).symm
  have hpolicy : SamplerCirclePolicy.point a ≠ SamplerCirclePolicy.point b := by
    intro he
    apply hpq
    rw [hp,hq,he]
  have hca := SamplerCirclePolicy.point_on_circle a hda
  have hcb := SamplerCirclePolicy.point_on_circle b hdb
  have hn := unit_circle_pair_norm_ne_zero
    (SamplerCirclePolicy.point a).1 (SamplerCirclePolicy.point a).2
    (SamplerCirclePolicy.point b).1 (SamplerCirclePolicy.point b).2 hca hcb hpolicy
  rw [hp,hq]
  simpa only [R166CircleExecution.encodePoint,R165QuarticExecution.decode_encode]
    using hn

#print axioms unit_circle_pair_norm_ne_zero
#print axioms sampled_decoded_abc_norm_ne_zero
end
end AspisV8R19.R735SampledAbcNorm
