import FJq_ChallengeSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ChallengeEta
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIz_ConcretePack (embed)
theorem value (c : r1_wire.Challenges) (alpha : Array aspis_core.field.QM31 10#usize) :
    (FJq_ChallengeSlots.values c alpha).getD 14 0=embed (FIp_SemanticValues.decode c.eta) := by
  simp [FJq_ChallengeSlots.values,BeginCalls.challengeList,List.getD,List.getElem?_append,c.zc.property]
#print axioms value
end AspisR1.FJq_ChallengeEta
end
