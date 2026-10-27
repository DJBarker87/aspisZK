import RPu_FJq_ChallengeSlots
import RPz7_F3M_First25Challenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceChallengeMap
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIz_ConcretePack (embed)
theorem cell {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) :
    SourceLiteralTraceLift.sourceChallenge c=embed (FIp_SemanticValues.decode c.q) := rfl
theorem values {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (c : r1_wire.Challenges)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (same : cs.map SourceFull25.Call.q=BeginCalls.challengeList c++alpha.val) :
    cs.map SourceLiteralTraceLift.sourceChallenge=FJq_ChallengeSlots.values c alpha := by
  rw [FJq_ChallengeSlots.values,←same,List.map_map]
  rfl
#print axioms cell
#print axioms values
end AspisR1.FJq_SourceChallengeMap
end
