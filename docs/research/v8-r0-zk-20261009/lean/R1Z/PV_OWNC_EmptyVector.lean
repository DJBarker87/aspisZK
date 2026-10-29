import R1Z.PV_OWNC_CursorVector
set_option autoImplicit false
namespace R1Z.PV_OWNC_EmptyVector
open PV_OWNC_Vector PV_OWN_Heap PV_OWN_View
/-- A newly allocated destination starts at len0. Initialized spare bytes are
not asserted; the allocator outcome and fresh owner are supplied by the
retained runtime allocation instance, before this theorem applies. -/
theorem initialized {T : Type} (k : Codec T) (m : Memory) (t : Token)
 (owner cap : Nat) (c : Cell) (values : Nat → T)
 (owned:Writable m owner t c) (size:c.size=cap*k.width)
 (align:c.alignment=k.alignment) :
 PV_OWNC_Vector.Valid k ⟨m,t,owner,c,0,cap,values⟩ := by
 refine ⟨owned,size,align,Nat.zero_le _,?_⟩
 intro i hi
 omega
#print axioms initialized
end R1Z.PV_OWNC_EmptyVector
