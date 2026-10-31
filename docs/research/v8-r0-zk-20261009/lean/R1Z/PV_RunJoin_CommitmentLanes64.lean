import R1Z.PV_RunJoin_SliceCopy64
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CommitmentLanes64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

def values : host_commitment.CommitmentTime → List Usize
  | .C1 => [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,
      8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize,
      16#usize,17#usize,18#usize,19#usize,20#usize,21#usize,22#usize,23#usize,
      24#usize,25#usize,28#usize]
  | .C2 => [26#usize,27#usize]

theorem source (time : host_commitment.CommitmentTime) :
    Post (fun status => match status with | .Err _ => True | .Ok lanes => lanes.val=values time)
      (host_commitment.commitment_lanes time) := by
  cases time <;> unfold host_commitment.commitment_lanes
  all_goals
    apply PV_RunJoin_ResultPost41.bind
    intro status
    cases status with
    | Err e => trivial
    | Ok lanes =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry]
      apply PV_RunJoin_PostEquation60.bind
      intro copied hcopy
      have hc := PV_RunJoin_SliceCopy64.value _ _ _ _ hcopy
      rw [hc]
      rfl

theorem complete (time : host_commitment.CommitmentTime) (lanes : alloc.vec.Vec Usize)
    (success : host_commitment.commitment_lanes time=ok (.Ok lanes)) :
    lanes.length≤29 ∧ ∀ lane∈lanes.val,lane.val<29 := by
  have hv := PV_RunJoin_ResultPost41.success _ _ (.Ok lanes) (source time) success
  have length : lanes.length=lanes.val.length := rfl
  rw [length,hv]
  cases time <;> constructor
  · decide
  · intro lane member
    simp only [values,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · decide
  · intro lane member
    simp only [values,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl|rfl <;> decide

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_CommitmentLanes64
