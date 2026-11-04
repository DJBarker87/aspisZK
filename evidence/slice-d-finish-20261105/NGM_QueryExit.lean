import NGM_NGC_QueryPoststate
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_QueryExit
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- The same accepted twelve-query run supplies the final invariant and
next=22. The accepted run is the caller's actual query-loop observation. -/
theorem tx2 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (b pending : verifier.BatchedWeights)
 (domain : NFS_QueryInvariant.Domain p 10 22 a b) (start : a.next.val=10)
 (accepted : verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 22#usize=ok (.Ok (after,pending))) :
 NFS_QueryInvariant.Domain p 10 22 after pending ∧ after.next.val=22 := by
 rw [←NFP_Resume.tx2 (NFS_QueryOps.installed base) proof p a g geometry b start] at accepted
 have result := NGC_QueryPoststate.finite base proof p g geometry 10 22#usize
  (by decide) 12 (.Ok (a,b)) domain after pending accepted
 exact ⟨result.1,Nat.le_antisymm result.1.upper result.2⟩
#print axioms tx2
end AspisR1.NGM_QueryExit
end
