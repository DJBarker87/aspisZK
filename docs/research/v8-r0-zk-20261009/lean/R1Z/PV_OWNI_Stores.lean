import R1Z.PV_OWNI_EmptyVec
import R1Z.PV_OWNC_PushFold
set_option autoImplicit false
namespace R1Z.PV_OWNI_Stores
open PV_OWN_Heap PV_OWNC_Vector PV_OWNI_EntryBytes
/-- Every tuple store precedes its length publication; bounded prefixes cannot
reach Vec::push's cold reserve branch. No field operation is evaluated here. -/
theorem complete (m : Memory) (p owner capacity : Nat) (xs : List Entry)
 (loans:NoLoans m (PV_OWNI_EmptyVec.token m p)) (count:xs.length=capacity) :
 Valid codec (PV_OWNC_PushFold.append codec (PV_OWNI_EmptyVec.buffer m p owner capacity) xs) ∧
 (PV_OWNC_PushFold.append codec (PV_OWNI_EmptyVec.buffer m p owner capacity) xs).length=capacity ∧
 (PV_OWNC_PushFold.append codec (PV_OWNI_EmptyVec.buffer m p owner capacity) xs).capacity=capacity := by
 refine ⟨PV_OWNC_PushFold.valid codec _ xs (PV_OWNI_EmptyVec.valid m p owner capacity loans) ?_
   bounded,?_,?_⟩
 · change 0+xs.length≤capacity
   omega
 · rw [PV_OWNC_PushFold.length]
   change 0+xs.length=capacity
   omega
 · exact PV_OWNC_PushFold.capacity codec _ xs

#print axioms complete
end R1Z.PV_OWNI_Stores
