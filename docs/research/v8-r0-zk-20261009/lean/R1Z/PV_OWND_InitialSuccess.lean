import R1Z.PV_OWND_InitialRun
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialSuccess
open PV_OWN_Operations PV_OWN_Link PV_OWN_Heap PV_OWNC_Vector PV_W_Threading PV_OWND_InitialRun

theorem complete {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (owner p : Nat)
 (oom : Action S X E (Buffer Link)) (w : State S X) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s)) :
 construct prim owner oom w =
 let a:=allocate prim ⟨1016,2⟩ owner w
 let b:=PV_OWND_InitialBytes.initialized a.world.memory ⟨p,w.memory.generations p+1⟩ owner
 ⟨.ok b,{a.world with memory:=b.memory},[(w,.allocate 1016 2)]⟩ := by
 simp only [construct,bind,allocate,emit,h,stores,List.append_nil]
#print axioms complete
end R1Z.PV_OWND_InitialSuccess
