import R1Z.PV_RJN_NodeReject
import R1Z.PV_RunJoin_PublishSkeleton57
set_option autoImplicit false
namespace R1Z.PV_RJN_NodeRangeWitness
open Aeneas Aeneas.Std ProverRwFull
/-- The explicit range precondition excludes precisely the substituted query
shape used in the obstruction; no sufficiency claim is made. -/
theorem excluded : ¬PV_RunJoin_PublishSkeleton57.QueryRange PV_RJN_NodeReject.badQueries := by
  intro range
  have member : (262144#u32) ∈ PV_RJN_NodeReject.badQueries.val := by
    change (262144#u32) ∈ List.ofFn (fun _ : Fin (22#usize).val => (262144#u32))
    exact List.mem_ofFn.mpr ⟨⟨0,by decide⟩,rfl⟩
  have bad := range (262144#u32) member
  exact Nat.lt_irrefl 262144 bad
#print axioms excluded
end R1Z.PV_RJN_NodeRangeWitness
