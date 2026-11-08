import NNU_QueryValues
import NNH_Run5bQueryDomain
import NFS_QueryLoopRoot
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
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
  cases state with
  | Err e => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish
   · simp only [run,stopped,if_true]
   · have inside : a.next.val<finish.val := Nat.lt_of_not_ge stopped
     have same := NNU_QueryValues.source m env err r proof p a g geo b valid.power
     simp only [run,stopped,if_false,same]
     cases step : verifier.candidate.query_values model proof p a g none geo b with
     | fail e => rfl
     | div => rfl
     | ok next =>
      simp only [bind_tc_ok]
      apply ih
      cases next with
      | Err e => trivial
      | Ok pair =>
       rcases pair with ⟨after,pending⟩
       exact NFS_QueryInvariant.step NJJ_QueryOps.concrete proof p g geo 10 finish.val
        a after b pending valid limit inside step

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
