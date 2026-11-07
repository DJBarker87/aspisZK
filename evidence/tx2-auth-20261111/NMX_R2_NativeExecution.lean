import NMX_R2_StdOps
import NMX_R2_Semantics
import NMX_R2_Observation
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeExecution
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Independent reached std allocation decisions. Lane allocation belongs to
its complete child observation; no allocator internals or stopped heap exists. -/
structure Allocations where
 clone : Bool
 master : Bool
 checkpoint : Bool
 snapshot : Bool

def box {A : Type} (aborts : Bool) (owner : Nat)
 (decoded : core.result.Result A PE) : RSL.Obs (Except RSL.ProgramError (Box A)) :=
 match decoded with
 | .Err e => ⟨.ret (.error (NMX_R2_Carrier.error e)),[]⟩
 | .Ok value => if aborts then ⟨.abort,[]⟩ else ⟨.ret (.ok ⟨owner,value⟩),[]⟩

/-- Native helper calls at the source commands, using concrete std slots.
This operational definition is WIP until all command packets are checked;
it is not a row root and supplies no child packet by definition. -/
def command (owners : Owners) (alloc : Allocations) (failure : Error)
 (lane : NMX_R2_RawChildren.LaneNative) (registry : NMX_R2_RawChildren.RegistryNative)
 (env : RSL.Env) : {A : Type} → Command A → RSL.Obs (Except RSL.ProgramError A) :=
 fun {_} cmd =>
 let std := NMX_R2_StdOps.install env alloc.clone failure
 match cmd with
 | .raw r => NMX_R2_ResultRelation.rawObs r
 | .readonlyBuffer a => NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_readonly_buffer a)
 | .checkpointGuard a program writable => NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_verifier_checkpoint std a program writable)
 | .readonlyAccount a expected => NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_readonly_account (NGL_ReadonlyModel.install std) a expected)
 | .distinct accounts => NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_distinct_accounts (NGL_ReadonlyModel.install std) accounts)
 | .data a => NMX_R2_ObserveResult.observe id (r1_pool_adapter.owned.OwnedAccount.data std a)
 | .key a => NMX_R2_ResultRelation.rawObs (r1_pool_adapter.owned.OwnedAccount.impl.key a)
 | .toBytes key => NMX_R2_ResultRelation.rawObs (std.op39 key)
 | .fromBytes bytes => NMX_R2_ResultRelation.rawObs (std.op37 bytes)
 | .asRef key => NMX_R2_ResultRelation.rawObs (std.op40 key)
 | .master bytes => box alloc.master owners.master (NMX_MasterValue.decoded bytes)
 | .checkpoint bytes => box alloc.checkpoint owners.checkpoint (NMX_CheckpointValue.decoded bytes)
 | .lane bytes => lane bytes env
 | .registry verifier pool ma m r e slot => registry ⟨verifier,pool,ma,m,r,e,slot⟩ env
 | .pda seeds program =>
   let reply := env.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program)
   ⟨.ret (match reply with
    | none => .error .invalidAccountData
    | some key => .ok (NMX_R2_InverseBytes.fromKey key)),
    [.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program) reply]⟩
 | .snapshot payload => if alloc.snapshot then ⟨.abort,[]⟩
   else ⟨.ret (.ok ⟨owners.snapshot,payload⟩),[]⟩

/-- Chronological execution: an error or stop has no suffix calls or state. -/
def run (owners : Owners) (alloc : Allocations) (failure : Error)
 (lane : NMX_R2_RawChildren.LaneNative) (registry : NMX_R2_RawChildren.RegistryNative)
 (env : RSL.Env) : Program Auth → RSL.Obs (Except RSL.ProgramError RSL.Authenticated)
 | .ret value => ⟨.ret (.ok (NMX_R2_Carrier.auth value)),[]⟩
 | .reject error => ⟨.ret (.error (NMX_R2_Carrier.error error)),[]⟩
 | .stop (.failed _) => ⟨.abort,[]⟩
 | .stop .diverged => ⟨.diverge,[]⟩
 | .step cmd next => NMX_R2_Observation.rustBind
   (command owners alloc failure lane registry env cmd)
   (fun reply => run owners alloc failure lane registry env (next reply))
end NMX_R2_NativeExecution
end
