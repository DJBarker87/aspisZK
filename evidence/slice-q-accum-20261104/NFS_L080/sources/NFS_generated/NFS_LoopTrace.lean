import NFS_LoopTraceDefs
import NFS_QueryLoopRoot
import NFP_QueryTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_LoopTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts NFP_TraceTypes NFG_QueryLoopDefs
open NFS_LoopTraceDefs

theorem erase_fixed (base : Ops) :
 NFP_ObserverErasure.erase (NFS_QueryOps.installed base)=NFS_QueryOps.installed base := rfl

theorem source (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (qPlace gPlace start : Nat)
 (finish : Usize) (limit : finish.val≤22)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (fuel : Nat) (state : State) (valid : NFS_QueryLoopRoot.Valid p start finish.val state) :
 NFS_LoopTraceDefs.run (fun a b=>NFS_QueryValuesPacket.run base proof p a g geometry b qPlace gPlace) finish fuel state =
 NFS_LoopTraceDefs.run (fun a b=>NFP_QueryTrace.run (NFS_QueryOps.installed base) proof p a g geometry b) finish fuel state := by
 apply NFS_LoopTraceDefs.compare _ _ (NFS_QueryLoopRoot.Valid p start finish.val) finish ?_ ?_ fuel state valid
 · intro a b input inside
   exact NFS_QueryValuesPacket.source base proof p a g geometry b qPlace gPlace canonical
    (NFS_QueryInvariant.active p start finish.val a b input limit inside)
 · intro a b next input inside h
   have actual := (NFP_QueryTrace.erased (NFS_QueryOps.installed base) proof p a g geometry b).symm.trans h
   rw [erase_fixed] at actual
   cases next with
   | Err error => trivial
   | Ok pair =>
    rcases pair with ⟨after,pending⟩
    exact NFS_QueryInvariant.step base proof p g geometry start finish.val a after b pending input limit inside actual
#print axioms erase_fixed
#print axioms source
end AspisR1.NFS_LoopTrace
end
