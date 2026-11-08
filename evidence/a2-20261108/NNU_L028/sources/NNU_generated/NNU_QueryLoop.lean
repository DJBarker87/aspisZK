import NNU_QueryValues
import NNH_Run5bQueryDomain
import NNU_QueryInduction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NNH_Run5bQuerySlots
open NFG_QueryLoopDefs

theorem finite (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (finish : Usize) (limit : finish.val≤22) (fuel : Nat) (state : State)
 (valid : NFS_QueryLoopRoot.Valid p 10 finish.val state) :
 run (fun a b=>verifier.candidate.query_values (actual m env err r) proof p a g none geo b) finish fuel state =
 run (fun a b=>verifier.candidate.query_values model proof p a g none geo b) finish fuel state := by
 apply NNU_QueryInduction.finite _ _ (NFS_QueryLoopRoot.Valid p 10 finish.val) finish
 · intro a b domain
   exact NNU_QueryValues.source m env err r proof p a g geo b domain.power
 · intro a b after pending domain inside step
   exact NFS_QueryInvariant.step NJJ_QueryOps.concrete proof p g geo 10 finish.val
    a after b pending domain limit inside step
 · exact valid

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p 10 22 a pending)
 (start : a.next.val=10) :
 verifier.candidate.query_loop (actual m env err r) proof p a g none geo pending 22#usize =
 verifier.candidate.query_loop model proof p a g none geo pending 22#usize :=
 (NFP_Resume.tx2 _ _ _ _ _ _ _ start).symm.trans
  ((finite m env err r proof p g geo 22#usize (by decide) 12 (.Ok (a,pending)) domain).trans
   (NFP_Resume.tx2 _ _ _ _ _ _ _ start))
#print axioms finite
#print axioms source
end AspisR1.NNU_QueryLoop
end
