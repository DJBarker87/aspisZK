import NFS_QueryLoopRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_QueryPoststate
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFG_QueryLoopDefs
/-- Every successful finite run preserves the invariant on the SAME returned
pair and can return successfully only at a stopped terminal. -/
theorem finite (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry) (start : Nat)
 (finish : Usize) (limit : finish.val≤22) (fuel : Nat) (state : State)
 (valid : NFS_QueryLoopRoot.Valid p start finish.val state)
 (after : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (accepted : run (fun a b=>verifier.candidate.query_values (NFS_QueryOps.installed base)
  proof p a g none geometry b) finish fuel state=ok (.Ok (after,pending))) :
 NFS_QueryInvariant.Domain p start finish.val after pending ∧ finish.val≤after.next.val := by
 induction fuel generalizing state with
 | zero =>
  cases state with
  | Err error => cases accepted
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases halt : a.next≥finish
   · simp only [run,halt,if_true] at accepted
     cases core.result.Result.Ok.inj (Result.ok.inj accepted)
     exact ⟨valid,halt⟩
   · simp only [run,halt,if_false] at accepted
     cases accepted
 | succ fuel ih =>
  cases state with
  | Err error => cases accepted
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases halt : a.next≥finish
   · simp only [run,halt,if_true] at accepted
     cases core.result.Result.Ok.inj (Result.ok.inj accepted)
     exact ⟨valid,halt⟩
   · simp only [run,halt,if_false] at accepted
     cases childRun : verifier.candidate.query_values (NFS_QueryOps.installed base)
      proof p a g none geometry b with
     | fail error => simp only [childRun,bind_tc_fail] at accepted;cases accepted
     | div => simp only [childRun,bind_tc_div] at accepted;cases accepted
     | ok child =>
      simp only [childRun,bind_tc_ok] at accepted
      apply ih child _ accepted
      cases child with
      | Err error => trivial
      | Ok pair =>
       rcases pair with ⟨next,bnext⟩
       exact NFS_QueryInvariant.step base proof p g geometry start finish.val a next b bnext
        valid limit (Nat.lt_of_not_ge halt) childRun
/-- The real ten-step TX1 loop supplies both its final invariant and next=10;
no accepted-finish or independently selected output state is assumed. -/
theorem tx1 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a after : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
 (b pending : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p 0 10 a b)
 (start : a.next.val=0)
 (accepted : verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 10#usize=ok (.Ok (after,pending))) :
 NFS_QueryInvariant.Domain p 0 10 after pending ∧ after.next.val=10 := by
 rw [←NFP_Resume.tx1 (NFS_QueryOps.installed base) proof p a g geometry b start] at accepted
 have result := finite base proof p g geometry 0 10#usize (by decide) 10 (.Ok (a,b)) domain after pending accepted
 exact ⟨result.1,Nat.le_antisymm result.1.upper result.2⟩
#print axioms finite
#print axioms tx1
end AspisR1.NGC_QueryPoststate
end
