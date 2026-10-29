import R1Z.PV_OWNC_PushBytes
set_option autoImplicit false
namespace R1Z.PV_OWNC_PushOwned
open PV_OWNC_Vector PV_OWN_Heap PV_OWN_View
/-- Non-growing push changes no allocation slot, identity or generation. -/
theorem writable {T : Type} (k : Codec T) (b : Buffer T) (v : T)
 (actual : PV_OWN_Bytes.Bytes) (h:Valid k b) :
 Writable (push k b v actual).memory b.owner b.token (push k b v actual).cell := by
 unfold Valid at h
 unfold push
 exact ⟨⟨⟨put_same _ _ _,h.1.1.1.2.1,h.1.1.1.2.2⟩,h.1.1.2.1,h.1.1.2.2⟩,h.1.2⟩

theorem identity {T : Type} (k : Codec T) (b : Buffer T) (v : T)
 (actual : PV_OWN_Bytes.Bytes) :
 (push k b v actual).token=b.token ∧
 (push k b v actual).memory.generations=b.memory.generations ∧
 (push k b v actual).memory.slots=b.memory.slots := ⟨rfl,rfl,rfl⟩
#print axioms writable
#print axioms identity
end R1Z.PV_OWNC_PushOwned
