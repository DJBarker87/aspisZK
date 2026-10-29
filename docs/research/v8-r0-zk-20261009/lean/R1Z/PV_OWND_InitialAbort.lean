import R1Z.PV_OWND_InitialProgram
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialAbort
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Default abort has no unwind suffix. This is a handler model law; its native
runtime identity is retained under rdea-1. -/
theorem null_abort {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S)
 (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : PV_OWND_InitialCheck.CheckError → E) (owner : Nat)
 (payload : Nat → Link → Bytes) (w : State S X) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok none,s)) :
 PV_OWND_InitialProgram.program prim dealloc error owner (lift .div) payload w=
 ⟨.div,{w with allocator:=s},[(w,.allocate 1016 2)]⟩ := by
 unfold PV_OWND_InitialProgram.program
 rw [bind,PV_OWND_InitialNull.complete prim owner (lift .div) payload w s h]
 simp only [lift,List.append_nil]
#print axioms null_abort
end R1Z.PV_OWND_InitialAbort
