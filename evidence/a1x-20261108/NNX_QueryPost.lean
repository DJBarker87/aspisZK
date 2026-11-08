import NNX_QueryLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_QueryPost
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFG_QueryLoopDefs

theorem finite (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (start : Nat) (finish : Usize) (limit : finish.val≤22)
 (fuel : Nat) (state : State) (valid : NFS_QueryLoopRoot.Valid p start finish.val state)
 (after : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (returned : run (fun a b => verifier.candidate.query_values (NFS_QueryOps.installed base)
   proof p a g none geo b) finish fuel state = .ok (.Ok (after,pending))) :
 NFS_QueryInvariant.Domain p start finish.val after pending := by
 induction fuel generalizing state with
 | zero =>
  cases state with
  | Err e => cases returned
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   simp only [run] at returned
   split at returned
   · cases core.result.Result.Ok.inj (Result.ok.inj returned)
     exact valid
   · cases returned
 | succ fuel ih =>
  cases state with
  | Err e => cases returned
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next ≥ finish
   · simp only [run,stopped,if_true] at returned
     cases core.result.Result.Ok.inj (Result.ok.inj returned)
     exact valid
   · simp only [run,stopped,if_false] at returned
     obtain ⟨next,step,tail⟩ := Port3_PushFrame.bind_success _ _ _ returned
     apply ih next ?_ tail
     cases next with
     | Err e => trivial
     | Ok pair =>
      rcases pair with ⟨a2,b2⟩
      exact NFS_QueryInvariant.step base proof p g geo start finish.val a a2 b b2 valid limit
       (Nat.lt_of_not_ge stopped) step
#print axioms finite
end AspisR1.NNX_QueryPost
end
