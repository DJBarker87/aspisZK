import R1Z.PV_OWND_InitialRun
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialFailure
open PV_OWN_Operations PV_OWN_Link PV_OWN_Heap PV_OWNC_Vector PV_W_Threading PV_OWND_InitialRun

theorem failed {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (owner : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → PV_OWN_Bytes.Bytes) (w : State S X) (s : S) (e : E)
 (h:prim ⟨1016,2⟩ w.allocator=(.fail e,s)) :
 construct prim owner oom payload w = ⟨.fail e,{w with allocator:=s},[(w,.allocate 1016 2)]⟩ := by
 simp only [construct,bind,allocate,emit,h]

theorem diverged {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (owner : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → PV_OWN_Bytes.Bytes) (w : State S X) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.div,s)) :
 construct prim owner oom payload w = ⟨.div,{w with allocator:=s},[(w,.allocate 1016 2)]⟩ := by
 simp only [construct,bind,allocate,emit,h]
#print axioms failed
#print axioms diverged
end R1Z.PV_OWND_InitialFailure
