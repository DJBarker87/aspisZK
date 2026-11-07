import NMX_SourceProgram
import NLM_Auth233
set_option autoImplicit false
noncomputable section
namespace NMX_SourceModel
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program
structure Owners where
 master : Nat
 checkpoint : Nat
 lane : Nat
 snapshot : Nat
/-- Nominal ownership annotation of the normal allocation path. Actual
allocator stops are handled by a separate full command packet, not this value
model. No nominal owner is asserted to be a native pointer. -/
def boxResult {A : Type} (owner : Nat) :
 Result (core.result.Result A PE) → Result (core.result.Result (Box A) PE)
 | .ok (.Ok a) => .ok (.Ok ⟨owner,a⟩)
 | .ok (.Err e) => .ok (.Err e)
 | .fail e => .fail e
 | .div => .div

def returned {W E A : Type} (w : W) (es : List E) :
 Result (core.result.Result A PE) → End W E A
 | .ok r => .returned r w es
 | .fail e => .stopped es (.failed e)
 | .div => .stopped es .diverged

def rawResult {A : Type} : Result A → Result (core.result.Result A PE)
 | .ok a => .ok (.Ok a)
 | .fail e => .fail e
 | .div => .div

def source {W : Type} (ops : Ops) (owners : Owners) : Handler W NLM_Auth233.Event :=
 fun {_} cmd before => match cmd with
 | .raw r => returned before [] (rawResult r)
 | .readonlyBuffer a =>
   let r := r1_pool_adapter.owned.require_readonly_buffer a
   returned before [.readonlyBuffer a r] r
 | .checkpointGuard a program writable =>
   let r := r1_pool_adapter.owned.require_verifier_checkpoint ops a program writable
   returned before [.checkpointGuard a program writable r] r
 | .readonlyAccount a owner =>
   let r := r1_pool_adapter.owned.require_readonly_account ops a owner
   returned before [.readonlyAccount a owner r] r
 | .distinct accounts =>
   let r := r1_pool_adapter.owned.require_distinct_accounts ops accounts
   returned before [.distinct accounts r] r
 | .data a =>
   let r := r1_pool_adapter.owned.OwnedAccount.data ops a
   returned before [.data a r] r
 | .key a =>
   let r := r1_pool_adapter.owned.OwnedAccount.impl.key a
   returned before [.key a r] (rawResult r)
 | .toBytes key =>
   let r := ops.op39 key
   returned before [.toBytes key r] (rawResult r)
 | .fromBytes bytes =>
   let r := ops.op37 bytes
   returned before [.fromBytes bytes r] (rawResult r)
 | .asRef key =>
   let r := ops.op40 key
   returned before [.asRef key r] (rawResult r)
 | .master bytes =>
   let r := ops.op48 bytes
   returned before [.decodeMaster bytes r] (boxResult owners.master r)
 | .checkpoint bytes =>
   let r := ops.op49 bytes
   returned before [.decodeCheckpoint bytes r] (boxResult owners.checkpoint r)
 | .lane bytes =>
   let r := ops.op50 bytes
   returned before [.decodeLane bytes r] (boxResult owners.lane r)
 | .pda seeds program =>
   let r := ops.op38 seeds program
   let mapped := do
     let reply ← r
     match reply with
     | .Ok key => ok (.Ok key)
     | .Err _ => ok (.Err .InvalidAccountData)
   returned before [.pda seeds program r] mapped
 | .registry verifier pool ma m registry entry slot =>
   let r := r1_pool_adapter.owned.authenticate_invariant_release_registry ops
     verifier pool ma m registry entry slot
   returned before [.registry verifier pool ma m registry entry slot r] r
 | .snapshot payload => .returned (.Ok ⟨owners.snapshot,payload⟩) before []
end NMX_SourceModel
end
