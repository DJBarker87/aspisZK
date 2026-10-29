import R1Z.PV_OWND_InitialRun
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialNull
open PV_OWN_Operations PV_OWN_Link PV_OWN_Heap PV_OWNC_Vector PV_W_Threading PV_OWND_InitialRun

theorem complete {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (owner : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → PV_OWN_Bytes.Bytes) (w : State S X) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok none,s)) :
 construct prim owner oom payload w =
 let after:= {w with allocator:=s}
 ⟨(oom after).outcome,(oom after).world,[(w,.allocate 1016 2)]++(oom after).calls⟩ := by
 simp only [construct,PV_W_Threading.bind,allocate,emit,h]
#print axioms complete
end R1Z.PV_OWND_InitialNull
