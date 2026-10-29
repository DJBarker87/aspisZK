import R1Z.PV_OWNC_GuardTransfer
set_option autoImplicit false
namespace R1Z.PV_OWNC_GuardValid
open PV_OWNB_Cursor PV_OWNC_GuardState PV_OWN_Heap PV_OWN_Operations
/-- Moving a guard changes owner only: both active-byte intervals survive. -/
theorem valid (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (dst : Nat)
 (empty:q.memory.slots dst=none) (distinct:dst≠q.owner) :
 PV_OWNB_Cursor.Valid (handoff q dst) := by
 have owned:=PV_OWNC_GuardTransfer.owned q h dst empty distinct
 unfold PV_OWNB_Cursor.Valid at h ⊢
 refine ⟨⟨owned,h.1.2⟩,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
  h.2.2.2.2.2.1,?_,?_⟩
 · intro i lo hi
   exact h.2.2.2.2.2.2.1 i lo hi
 · intro i hi
   exact h.2.2.2.2.2.2.2 i hi
#print axioms valid
end R1Z.PV_OWNC_GuardValid
