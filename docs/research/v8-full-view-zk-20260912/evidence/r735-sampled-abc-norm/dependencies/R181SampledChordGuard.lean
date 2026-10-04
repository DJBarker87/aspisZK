import AspisV8R19.R178CircleOutputCanonical
import AspisV8R19.R175ChordInverseExecution

set_option autoImplicit false
namespace AspisV8R19.R181SampledChordGuard

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open DuplexFrames SourceDuplexStep

noncomputable section

local instance : DecidableEq circle.SecureCirclePoint := Classical.decEq _

theorem raw_secure_circle_point_ne (p q : circle.SecureCirclePoint) :
    core.cmp.PartialEq.ne.trait_default
      circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint p q =
      .ok (decide (p ≠ q)) := by
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    R175ChordInverseExecution.raw_secure_circle_point_eq, bind_tc_ok]

theorem sampled_chord_inverse_exact
    (H : Bytes → State) (s0 s1 : State)
    (p q : circle.SecureCirclePoint) (t0 t1 : transcript.Transcript)
    (h0 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s0) = .ok (.Ok p, t0))
    (h1 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s1) = .ok (.Ok q, t1))
    (hne : core.cmp.PartialEq.ne.trait_default
      circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint p q =
      .ok true) :
    R175ChordInverseExecution.rawChordInverse p q =
      .ok (.Ok (R164ProductExecution.encode
        ((R165QuarticExecution.decode
            (R175ChordInverseExecution.selectedCoordinates p q).1 -
          R165QuarticExecution.decode
            (R175ChordInverseExecution.selectedCoordinates p q).2)⁻¹))) := by
  have hp_can :=
    R178CircleOutputCanonical.successful_circle_canonical H s0 p t0 h0
  have hq_can :=
    R178CircleOutputCanonical.successful_circle_canonical H s1 q t1 h1
  have hpq : p ≠ q := by
    have hcmp := raw_secure_circle_point_ne p q
    rw [hne] at hcmp
    have hdec : decide (p ≠ q) = true := (Result.ok.inj hcmp).symm
    exact of_decide_eq_true hdec
  exact R175ChordInverseExecution.rawChordInverse_exact p q
    hp_can.1 hp_can.2 hq_can.1 hq_can.2 hpq

#print axioms raw_secure_circle_point_ne
#print axioms sampled_chord_inverse_exact
end
end AspisV8R19.R181SampledChordGuard
