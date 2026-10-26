import BEg_Terminal
import BEf_Count
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

def rejected (parts : Parts) : Code (core.result.Result Unit Unit) :=
  .read parts (fun _ => .done (.Err ()))

def accepted (parts : Parts) : Code (core.result.Result Unit Unit) :=
  .read parts (fun _ => .done (.Ok ()))

/-- A positive-query rejecting example, with a real state transition retained
before canonical error erasure. This is interpreter non-vacuity only. -/
theorem rejection (parts : Parts) (digest : Digest) (n : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .ok digest))
      (rejected parts) n before = (.ok (.Err ()),n+1,before++[⟨parts,.ok digest⟩]) ∧
    BEf_Carrier.run (BEf_Count.call (fun _ => .ok digest))
      (BEg_Terminal.terminal (rejected parts)) n before =
      (.fail .panic,n+1,before++[⟨parts,.ok digest⟩]) := by
  exact ⟨rfl,rfl⟩

/-- Accepted output is retained, not collapsed into the rejection observation. -/
theorem success (parts : Parts) (digest : Digest) (n : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .ok digest))
      (BEg_Terminal.terminal (accepted parts)) n before =
      (.ok (.Ok ()),n+1,before++[⟨parts,.ok digest⟩]) := rfl

/-- A syscall can fail after changing the carrier; its attempt remains. -/
theorem failed_read (parts : Parts) (n : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .fail .panic))
      (BEg_Terminal.terminal (accepted parts)) n before =
      (.fail .panic,n+1,before++[⟨parts,.fail .panic⟩]) := rfl

#print axioms rejection
#print axioms success
#print axioms failed_read
end AspisR1.BEg_Nonvacuity
end
