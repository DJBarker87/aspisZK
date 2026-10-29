import R1Z.PV_OWND_InitialCheck
import R1Z.PV_OWND_InitialSuccess
import R1Z.PV_OWND_InitialNull
import R1Z.PV_OWND_InitialFailure
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialProgram
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Allocator construction, full-Link stores, scalar checks and cleanup on one
world. Its unproved native counter-array association remains explicit. -/
def program {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S)
 (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : PV_OWND_InitialCheck.CheckError → E) (owner : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → Bytes) :
 Action S X E (Buffer Link) :=
 bind (PV_OWND_InitialRun.construct prim owner oom payload)
  (PV_OWND_InitialCheck.finish dealloc error)
attribute [local irreducible] program
end R1Z.PV_OWND_InitialProgram
