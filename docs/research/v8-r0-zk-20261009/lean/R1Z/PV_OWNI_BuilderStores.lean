import R1Z.PV_OWNI_Stores
import R1Z.PV_OWNI_BuildTotal
set_option autoImplicit false
namespace R1Z.PV_OWNI_BuilderStores
open PV_OWN_Heap PV_OWNC_Vector PV_OWNI_RawOps
/-- The encoding argument is an explicit remaining typed/numeric carrier
association, not an assumed value-law or successful builder hypothesis. -/
theorem initialized (encode : Nat × Q → PV_OWNI_EntryBytes.Entry)
 (point : List Q) (width trailing suffix p owner : Nat) (m : Memory)
 (loans:NoLoans m (PV_OWNI_EmptyVec.token m p)) :
 Valid PV_OWNI_EntryBytes.codec
  (PV_OWNC_PushFold.append PV_OWNI_EntryBytes.codec
   (PV_OWNI_EmptyVec.buffer m p owner (2^width))
   ((PV_OWNI_BuildTotal.entries point width trailing suffix).map encode)) ∧
 (PV_OWNC_PushFold.append PV_OWNI_EntryBytes.codec
   (PV_OWNI_EmptyVec.buffer m p owner (2^width))
   ((PV_OWNI_BuildTotal.entries point width trailing suffix).map encode)).length=2^width := by
 have h:=PV_OWNI_Stores.complete m p owner (2^width)
  ((PV_OWNI_BuildTotal.entries point width trailing suffix).map encode) loans
  (by rw [List.length_map,PV_OWNI_BuildTotal.cardinality])
 exact ⟨h.1,h.2.1⟩
#print axioms initialized
end R1Z.PV_OWNI_BuilderStores
