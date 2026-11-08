import NNH_ResultPortTransport
import NNH_ReservationOkBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bFinishEdge
open Aeneas Aeneas.Std Result VTop_Stages NNH_Libraries

theorem selected (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (rep : NJC_FilledClause.reserved r = env.reservation) (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 V0 (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck = .ok (.Ok ()))
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) :
 (NNH_Tx2SlotTransport.stage m env err r).op19 v p a none =
 NLB_Parent.finish (LIBB_Tx2Reservation.reservation env) v p a none := by
 rw [NNH_ResultPortTransport.finish m env err r]
 rw [(NNH_ReservationOkBinding.source env r rep pub proof ck domain success).2]
#print axioms selected
end AspisR1.NNH_Run5bFinishEdge
end
