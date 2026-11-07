import NNG_ProjectionFallback137
import NNG_LIBTerminal
import LIB_VChallenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ChallengeProjection137
open Aeneas Aeneas.Std NNG_LIBScalar

def project (fallback : Value) (c : AspisR1PublicPreparation.r1_wire.Challenges) : LIB_VCarriers.Challenges :=
  NNG_LIBArrays.projectChallenges fallback (NNG_Transport.fromT3 c)

theorem raw (fallback : Value) (c : LIB_VCarriers.Challenges) : project fallback (LIB_VCarriers.challengesRaw c)=c := by
  have native := congrArg NNG_Transport.fromT3 (NNG_LIBTerminal.lower_challenges c)
  simp only [NNG_Transport.toT3_inverse] at native
  unfold project
  rw [←native]
  exact NNG_LIBArrays.project_lower_challenges fallback c
#print axioms raw

theorem lifted (fallback : Value) (c : AspisR1PublicPreparation.r1_wire.Challenges)
    (canonical : LIB_VChallenges.Canonical c) : project fallback c=LIB_VChallenges.lift c canonical := by
  have native := LIB_VChallenges.raw_lift c canonical
  conv_lhs => rw [←native]
  exact raw fallback _
#print axioms lifted
end AspisR1.NNG_ChallengeProjection137
