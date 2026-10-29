import R1Z.PV_OWNC_PushFold
set_option autoImplicit false
namespace R1Z.PV_OWNC_LinkPush
open PV_OWNC_Vector PV_OWN_Link
/-- All 72 forest pushes fit after reserve selects cap254 and len64. This
proves initialized byte ownership for arbitrary full-Link values, not just
endpoint-only links. The reserve-to-this-carrier bridge is still required. -/
theorem forest (b : Buffer Link) (xs : List Link)
 (h:Valid PV_OWNB_LinkCodec.codec b) (len:b.length=64)
 (cap:b.capacity=254) (count:xs.length=72) :
 Valid PV_OWNB_LinkCodec.codec (PV_OWNC_PushFold.append PV_OWNB_LinkCodec.codec b xs) ∧
 (PV_OWNC_PushFold.append PV_OWNB_LinkCodec.codec b xs).length=136 ∧
 (PV_OWNC_PushFold.append PV_OWNB_LinkCodec.codec b xs).capacity=254 := by
 refine ⟨PV_OWNC_PushFold.valid _ b xs h (by omega) ?_,?_,?_⟩
 · intro x i z hi
   exact PV_OWNB_LinkBound.bounded x i z hi
 · rw [PV_OWNC_PushFold.length,len,count]
 · rw [PV_OWNC_PushFold.capacity,cap]
#print axioms forest
end R1Z.PV_OWNC_LinkPush
