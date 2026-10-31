import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_PostBind63
import R1Z.ProverRwSuccessHeapSource
set_option autoImplicit false
namespace R1Z.PV_RunJoin_VectorSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41

theorem list_resize {T : Type} (xs : List T) (n : Nat) (x : T) :
    (xs.resize n x).length=n := by
  simp only [List.resize,List.length_append,List.length_take,List.length_replicate]
  omega

theorem resize {T : Type} (clone : core.clone.Clone T) (v : alloc.vec.Vec T)
    (n : Usize) (value : T) :
    Post (fun next => next.length=n.val) (alloc.vec.Vec.resize clone v n value) := by
  unfold alloc.vec.Vec.resize
  split
  · change (v.val.resize n.val value).length=n.val
    exact list_resize v.val n.val value
  · apply PV_RunJoin_ResultPost41.bind
    intro copied
    change (v.val.resize n.val copied).length=n.val
    exact list_resize v.val n.val copied

variable [ExternalTypes] [ExternalFuns]
theorem filled {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T) :
    Post (fun status => match status with | .Err _ => True | .Ok v => v.length=n.val)
      (ProverRwSuccessHeapSource.aspis_core.r0.heap.filled copy n value) := by
  unfold ProverRwSuccessHeapSource.aspis_core.r0.heap.filled
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨r,out⟩
  apply PV_RunJoin_ResultPost41.bind
  intro mapped
  cases mapped with
  | Err e => trivial
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_PostBind63.guarded _ _ _ _ (resize copy.cloneInst out n value)
    intro next hlen
    exact hlen

#print axioms list_resize
#print axioms resize
#print axioms filled
end R1Z.PV_RunJoin_VectorSize64
