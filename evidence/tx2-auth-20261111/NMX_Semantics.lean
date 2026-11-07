import NMX_RawChildren
import NMX_ResultRelation
import NMX_MasterValue
import NMX_CheckpointValue
import NMX_LeafInstall
import NMX_InverseBytes
set_option autoImplicit false
noncomputable section
namespace NMX_Semantics
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Decoder rejection precedes allocation. The independent abort arm is at
this precise Box site; no stopped post-world or cleanup is introduced. -/
def boxed {A : Type} (owner : Nat) (decoded : core.result.Result A PE) : RSL.RS (Box A) :=
 match decoded with
 | .Err e => RSL.RS.throw (NMX_Carrier.error e)
 | .Ok value => RSL.RS.bind (RSL.RS.lift RSL.Spec.alloc)
   (fun _ => RSL.RS.pure ⟨owner,value⟩)

/-- Dictionary-free operational interpretation of source occurrences. CLOSED child
carrier theorems and raw217/234 packets must be installed by the consumer;
this definition alone is not source/native or row credit. -/
def command (owners : Owners)
 (lane : NMX_RawChildren.LaneNative) (registry : NMX_RawChildren.RegistryNative) :
 {B : Type} → Command B → RSL.RS B :=
 fun {_} cmd => match cmd with
 | .raw r => NMX_ResultRelation.raw r
 | .readonlyBuffer a => RSL.RS.ofExcept (RSL.readonlyBuffer (NMX_Carrier.account a))
 | .checkpointGuard a program writable =>
   RSL.RS.ofExcept (RSL.verifierCheckpoint (NMX_Carrier.account a) (NMX_Carrier.key program) writable)
 | .readonlyAccount a owner =>
   RSL.RS.ofExcept (RSL.readonlyAccount (NMX_Carrier.account a) (NMX_Carrier.key owner))
 | .distinct accounts =>
   RSL.RS.ofExcept (RSL.requireDistinct (accounts.val.map NMX_Carrier.account))
 | .data a => match a.bytes with
   | .Ok v => RSL.RS.pure v.deref
   | .Err e => RSL.RS.throw (NMX_Carrier.error e)
 | .key a => RSL.RS.pure a.key
 | .toBytes key => RSL.RS.pure key
 | .fromBytes bytes => RSL.RS.pure bytes
 | .asRef key => RSL.RS.pure (Array.to_slice key)
 | .master bytes => boxed owners.master (NMX_MasterValue.decoded bytes)
 | .checkpoint bytes => boxed owners.checkpoint (NMX_CheckpointValue.decoded bytes)
 | .lane bytes => fun env o => o = lane bytes env
 | .registry verifier pool ma m r e slot =>
   fun env o => o = registry ⟨verifier,pool,ma,m,r,e,slot⟩ env
 | .pda seeds program => fun env o =>
   let reply := env.pda (seeds.val.map NMX_Carrier.bytes) (NMX_Carrier.key program)
   o = ⟨.ret (match reply with
    | none => .error .invalidAccountData
    | some key => .ok (NMX_InverseBytes.fromKey key)),
    [.pda (seeds.val.map NMX_Carrier.bytes) (NMX_Carrier.key program) reply]⟩
 | .snapshot payload => RSL.RS.bind (RSL.RS.lift RSL.Spec.alloc)
   (fun _ => RSL.RS.pure ⟨owners.snapshot,payload⟩)

/-- Final payload conversion happens only on the actual returned Auth value;
all intermediate owners and full child replies remain typed in the program. -/
def denote (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) : Program Auth → RSL.RS RSL.Authenticated
 | .ret a => RSL.RS.pure (NMX_Carrier.auth a)
 | .reject e => RSL.RS.throw (NMX_Carrier.error e)
 | .stop (.failed _) => fun _ o => o = ⟨.abort,[]⟩
 | .stop .diverged => fun _ o => o = ⟨.diverge,[]⟩
 | .step cmd next => RSL.RS.bind (command owners lane registry cmd)
   (fun reply => denote owners lane registry (next reply))
end NMX_Semantics
end
