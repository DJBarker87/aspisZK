import FJq_ChallengeSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ChallengeAlpha
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIz_ConcretePack (embed)
theorem value (c : r1_wire.Challenges) (alpha : Array aspis_core.field.QM31 10#usize)
    (i : Fin 10) :
    (FJq_ChallengeSlots.values c alpha).getD (15+i.val) 0=embed (FJn_MainPoint.point alpha i) := by
  have hi : i.val<alpha.val.length := by rw [alpha.property];exact i.isLt
  simp [FJq_ChallengeSlots.values,BeginCalls.challengeList,List.getD,List.getElem?_append,
    c.zc.property,hi,FJn_MainPoint.point]
#print axioms value
end AspisR1.FJq_ChallengeAlpha
end
