import AspisV8R19.R178CircleOutputCanonical

/-! Actual successful selected secure-circle samples satisfy the OOD domain.
No freshness or distribution is assumed; all sampler failures remain outside
these explicitly success-conditional statements. -/
set_option autoImplicit false
namespace AspisV8R19.R211CircleDomain
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open DuplexFrames SourceDuplexStep
noncomputable section

 theorem successful_parameter (H : Bytes → State) (s : State)
    (p : circle.SecureCirclePoint) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s) = .ok (.Ok p,next)) :
    ∃ a : QM31Exact, a.im ≠ 0 ∧ 1+a^2 ≠ 0 ∧
      p = R166CircleExecution.encodePoint (SamplerCirclePolicy.point a) := by
  rw [R177CircleScheduleBridge.challenge_schedule_exact] at h
  cases hm : (SamplerCircleBridge.modelRun H 3 s).2.1 with
  | error e =>
    cases e <;> simp [R172CircleSamplerExecution.encodeOutput,
      R177CircleScheduleBridge.encodeScheduleResult,hm] at h
  | ok q =>
    have hp : p = R166CircleExecution.encodePoint q := by
      have hv := congrArg Prod.fst (Result.ok.inj h)
      simpa [R172CircleSamplerExecution.encodeOutput,
        R177CircleScheduleBridge.encodeScheduleResult,hm] using hv.symm
    obtain ⟨xs,_hlen,_hcan,haccept⟩ :=
      BoundedSamplerWrapper.successful_image _ _ _ H 3 s q hm
    obtain ⟨hout,hden,hq⟩ := SamplerCirclePolicy.accept_policy xs q haccept
    exact ⟨SamplerFieldDecode.decode xs,hout,hden,hq ▸ hp⟩

 theorem successful_domain (H : Bytes → State) (s : State)
    (p : circle.SecureCirclePoint) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s) = .ok (.Ok p,next)) :
    (R165QuarticExecution.decode p.x)^2 + (R165QuarticExecution.decode p.y)^2 = 1 ∧
      R165QuarticExecution.decode p.y ≠ 0 ∧
      R165QuarticExecution.decode p.x ≠ 1 ∧
      R165QuarticExecution.decode p.x ≠ -1 ∧
      ¬ ((R165QuarticExecution.decode p.x).im = 0 ∧
        (R165QuarticExecution.decode p.y).im = 0) := by
  obtain ⟨a,hout,hden,hp⟩ := successful_parameter H s p next h
  have ha : a ≠ 0 := by
    intro hz
    subst a
    exact hout rfl
  have hy : (SamplerCirclePolicy.point a).2 ≠ 0 := by
    change 2*a/(1+a^2) ≠ 0
    exact div_ne_zero (mul_ne_zero AspisV8R15.ExactTowerChord.two_ne_zero ha) hden
  have hc := SamplerCirclePolicy.point_on_circle a hden
  have hx1 : (SamplerCirclePolicy.point a).1 ≠ 1 := by
    intro hx
    have hz : (SamplerCirclePolicy.point a).2 ^ 2 = 0 := by
      rw [hx] at hc
      linear_combination hc
    exact hy (pow_eq_zero hz)
  have hxneg : (SamplerCirclePolicy.point a).1 ≠ -1 := by
    intro hx
    have hz : (SamplerCirclePolicy.point a).2 ^ 2 = 0 := by
      rw [hx] at hc
      linear_combination hc
    exact hy (pow_eq_zero hz)
  rw [hp]
  simp only [R166CircleExecution.encodePoint,R165QuarticExecution.decode_encode]
  exact ⟨hc,hy,hx1,hxneg,SamplerCirclePolicy.outside_point a hout⟩

#print axioms successful_parameter
#print axioms successful_domain
end
end AspisV8R19.R211CircleDomain
