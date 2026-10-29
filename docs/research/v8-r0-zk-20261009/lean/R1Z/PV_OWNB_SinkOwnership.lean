import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_SinkOwnership
open PV_OWNB_Cursor PV_OWN_Heap
theorem owned (q : Cursor) (v : PV_OWN_Link.Link) (h:PV_OWNB_Cursor.Valid q) :
 Writable (sink q v).memory q.owner q.token (sink q v).cell := by
 unfold PV_OWNB_Cursor.Valid at h
 unfold sink
 exact ⟨⟨⟨put_same _ _ _,h.1.1.1.2.1,h.1.1.1.2.2⟩,h.1.1.2.1,h.1.1.2.2⟩,h.1.2⟩
theorem generation (q : Cursor) (v : PV_OWN_Link.Link) :
 (sink q v).memory.generations=q.memory.generations ∧ (sink q v).token=q.token := by
 unfold sink
 exact ⟨rfl,rfl⟩
#print axioms owned
#print axioms generation
end R1Z.PV_OWNB_SinkOwnership
