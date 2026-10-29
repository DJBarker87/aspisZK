import R1Z.PV_OWNI_NumericBytes
import R1Z.PV_OWNI_BuilderStores
import R1Z.PV_OWNI_ScannedResult
set_option autoImplicit false
namespace R1Z.PV_OWNI_InitializedResult
open PV_OWN_Heap PV_OWNC_Vector PV_OWNI_RawOps PV_OWNI_Scanner
/-- Actual numeric tuple encoding replaces BuilderStores' arbitrary encoder.
Runtime freshness/alignment and source-to-byte ABI remain named boundaries. -/
theorem initialized (point : List Q) (p owner : Nat) (m : Memory)
 (loans:NoLoans m (PV_OWNI_EmptyVec.token m p)) :
 Valid PV_OWNI_EntryBytes.codec
  (PV_OWNC_PushFold.append PV_OWNI_EntryBytes.codec
   (PV_OWNI_EmptyVec.buffer m p owner (2^width point))
   ((PV_OWNI_BuildTotal.entries point (width point) (trailing point) (suffix point)).map
    PV_OWNI_NumericBytes.encode)) :=
 (PV_OWNI_BuilderStores.initialized PV_OWNI_NumericBytes.encode point _ _ _ p owner m loans).1

#print axioms initialized
end R1Z.PV_OWNI_InitializedResult
