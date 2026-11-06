import NKY_BoxPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxCarrier
open Aeneas Aeneas.Std Result
open NKY_BoxAction

def erase {T : Type} : core.result.Result (Owned T) PE → core.result.Result T PE
 | .Ok box => .Ok box.value
 | .Err e => .Err e
/-- Scalar native pointer observation at the Box::new source site; payload
identity is deliberately absent and must come from all NKP field windows. -/
def Owner {T : Type} (allocated : Nat) : core.result.Result (Owned T) PE → Prop
 | .Ok box => box.owner=allocated
 | .Err _ => True

structure CheckpointCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (out : core.result.Result (Owned NJQ_Carrier.CC) PE) (allocated : Nat) : Prop where
 decoder : NJQ_CheckpointTotal.Cut bytes raw
 fields : NKP_BoxCuts.CheckpointReturned (NJQ_Carrier.checkpoint_result raw) (erase out)
 owner : Owner allocated out

structure MasterCut (bytes : Slice U8)
 (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (out : core.result.Result (Owned NJQ_Carrier.CM) PE) (allocated : Nat) : Prop where
 decoder : NJQ_MasterTotal.Cut bytes raw
 fields : NKP_BoxCuts.MasterReturned (NJQ_Carrier.master_result raw) (erase out)
 owner : Owner allocated out

/-- Native post-cut summary returns the ACTUAL owned carrier from that
invocation. It does not construct a replacement owner or infer bytes from it.
The allocation action is interpreted at the original source site via the
existing Allocator item and includes every outcome. -/
def native {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation)
 (out : core.result.Result (Owned T) PE) :
 Result (core.result.Result (Owned T) PE × S) :=
 match out with
 | .Err e => ok (.Err e,s)
 | .Ok box => do
  let post ← a.allocate s bytes
  match r with
  | .Err _ => fail .panic
  | .Ok _ => ok (.Ok box,post)

theorem association {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (out : core.result.Result (Owned T) PE) (owner : Owner allocated out) :
 native a s bytes r out=run a s bytes r allocated (ok (erase out)) := by
 cases out with
 | Err e => rfl
 | Ok box =>
  have same : (⟨allocated,box.value⟩ : Owned T)=box := by
   cases box
   cases owner
   rfl
  simp only [native,run,erase,newBox,bind_tc_ok]
  cases ha:a.allocate s bytes <;> cases r <;> simp [ha,same]
#print axioms association
end AspisR1.NKY_BoxCarrier
end
