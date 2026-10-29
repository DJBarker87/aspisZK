import R1Z.PV_OWNC_SourceIterator
set_option autoImplicit false
namespace R1Z.PV_OWNC_ReadPointer
open PV_OWNB_Cursor PV_OWNC_SourceIterator
/-- In-bounds pointer arithmetic for the deployed non-ZST read. -/
theorem in_bounds (q : Cursor) (h:Valid q) (more:q.read<q.length) :
 (header q).buf≤(header q).ptr ∧
 (header q).ptr+8≤(header q).endPtr ∧
 (header q).endPtr≤(header q).buf+q.capacity*8 := by
 unfold Valid at h
 simp only [header]
 omega

theorem advance_pointer (q : Cursor) :
 (header (advance q)).ptr=(header q).ptr+8 := by
 simp only [header,advance]
 omega
#print axioms in_bounds
#print axioms advance_pointer
end R1Z.PV_OWNC_ReadPointer
