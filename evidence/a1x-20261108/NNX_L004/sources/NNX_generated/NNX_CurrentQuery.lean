import NNX_QueryValues
import NNX_QueryLoop
import NNV_CurrentQuerySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_CurrentQuery
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
abbrev actual (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :=
 Tx1Q_QueryBridge.leaves (NNH_CorrectConfiguration.configuration m env err r).query

theorem slots (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
 NNX_QueryValues.Slots (actual m env err r) NNH_Run5bQuerySlots.model := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor <;> rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · intro ph; rfl
 · exact NNU_QueryAccum.sum m env err r
 · exact NNU_QueryAccum.product m env err r
 · exact NNU_QueryAccum.power m env err r

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (domain : NFS_QueryInvariant.Domain p 0 10 a pending) (start : a.next.val=0) :
 verifier.candidate.query_loop (actual m env err r) proof p a scratch none geo pending 10#usize =
 verifier.candidate.query_loop NNH_Run5bQuerySlots.model proof p a scratch none geo pending 10#usize := by
 apply NNX_QueryLoop.tx1 _ NJJ_QueryOps.concrete proof p a scratch geo pending
 · intro a b d
   exact NNX_QueryValues.source _ _ (slots m env err r) proof p a scratch geo b d.power
 · exact domain
 · exact start
#print axioms slots
#print axioms source
end AspisR1.NNX_CurrentQuery
end
