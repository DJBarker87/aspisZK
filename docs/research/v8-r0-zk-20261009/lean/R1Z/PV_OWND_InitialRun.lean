import R1Z.PV_OWND_InitialIdentity
import R1Z.PV_OWND_ActualBytes
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialRun
open PV_OWN_Operations PV_OWN_Link PV_OWN_Heap PV_OWNC_Vector PV_W_Threading
/-- Stores do not call the allocator and retain its actual post-state and Extra.
The source checks following these stores are deliberately separate. -/
def stores {S X E : Type} (t : Token) (owner : Nat) (payload : Nat → Link → PV_OWN_Bytes.Bytes) : Action S X E (Buffer Link) := fun w=>
 let b:=PV_OWND_ActualBytes.initialized w.memory t owner payload
 ⟨.ok b,{w with memory:=b.memory},[]⟩
/-- Default OOM dispatch is retained as an explicit handler, not a successful
allocation premise. The null branch executes before any Link store. -/
def construct {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (owner : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → PV_OWN_Bytes.Bytes) : Action S X E (Buffer Link) :=
 bind (allocate prim ⟨1016,2⟩ owner) fun t=>
 match t with
 | none => oom
 | some t => stores t owner payload
attribute [local irreducible] stores construct
end R1Z.PV_OWND_InitialRun
