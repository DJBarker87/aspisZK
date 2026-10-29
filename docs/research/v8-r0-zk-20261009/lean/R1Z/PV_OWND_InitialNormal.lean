import R1Z.PV_OWND_InitialProgram
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialNormal
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes

theorem complete {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S)
 (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : PV_OWND_InitialCheck.CheckError → E) (owner p : Nat)
 (oom : Action S X E (Buffer Link)) (payload : Nat → Link → Bytes) (w : State S X) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (checked:PV_OWND_InitialCheck.checks (PV_OWND_ActualBytes.initialized
  (allocate prim ⟨1016,2⟩ owner w).world.memory ⟨p,w.memory.generations p+1⟩ owner payload)=.ok ()) :
 PV_OWND_InitialProgram.program prim dealloc error owner oom payload w=
 let a:=allocate prim ⟨1016,2⟩ owner w
 let b:=PV_OWND_ActualBytes.initialized a.world.memory ⟨p,w.memory.generations p+1⟩ owner payload
 ⟨.ok b,{a.world with memory:=b.memory},[(w,.allocate 1016 2)]⟩ := by
 unfold PV_OWND_InitialProgram.program
 rw [PV_W_Threading.bind,PV_OWND_InitialSuccess.complete prim owner p oom payload w s h]
 simp only [PV_OWND_InitialCheck.finish,checked,lift,List.append_nil]
#print axioms complete
end R1Z.PV_OWND_InitialNormal
