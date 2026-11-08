import NNU_CommonCuts
import NNU_CommonResume
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_CommonSelected
open Aeneas Aeneas.Std Result VTop_Stages

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (size : ck.val.length=1768)
 (success : LIBB_Tx2EnvCode.common env pub proof ck=.ok (.Ok ())) :
 ∃ p a g geo pending after afterPending,
 NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
   ck proof pub .S2 ()=.ok (.Ok (p,a)) ∧
 NID_ResumeFields.Domain p a ∧ a.next=10#usize ∧
 NHT_PacketOps.powers 29#usize p.gamma=.ok g ∧
 NJJ_Common.pending (LIBB_Tx2Reservation.reservation env) a.weights.deref=.ok (.Ok pending) ∧
 (NNH_Tx2SlotTransport.stage m env err r).op11 p.queries a.next 22#usize=.ok (.Ok geo) ∧
 (NNH_Tx2SlotTransport.stage m env err r).op6 proof p a g none geo pending 22#usize=
   .ok (.Ok (after,afterPending)) := by
 obtain ⟨p,a,g,ib,decoded,inactive,folded,geo,pending,after,afterPending,
   resume,powers,read,decode,option,merkle,geometry,init,query⟩ :=
   NNU_CommonCuts.source env pub proof ck success
 obtain ⟨fields,next⟩ := NNU_CommonResume.occurrence env pub proof ck size success p a resume
 refine ⟨p,a,g,geo,pending,after,afterPending,resume,fields,next,powers,init,?_,?_⟩
 · rw [NNU_Geometry.source];exact geometry
 · rw [NNU_Query.source m env err r proof p a g geo pending fields next powers init]
   exact query
#print axioms source
end AspisR1.NNU_CommonSelected
end
