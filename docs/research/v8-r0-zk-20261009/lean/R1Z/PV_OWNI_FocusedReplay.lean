import R1Z.PV_OWNI_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWNI_FocusedReplay
open Aeneas Aeneas.Std Result PV_OWN_Heap PV_OWNI_RawOps PV_OWNI_Scanner
/-- Focused composition of raw value Result and initialized ownership. This
is not the missing concrete dense/public protocol consuming law. -/
theorem value_and_memory (point column : List Q) (len:point.length=10)
 (m : Memory) (p owner : Nat) (loans:NoLoans m (PV_OWNI_EmptyVec.token m p)) :
 PV_OWNI_RawConsumer.source point column (width point) (trailing point) (suffix point)=
 ok (PV_OWNI_RawConsumer.value point column (width point) (trailing point) (suffix point)) ∧
 PV_OWNC_Vector.Valid PV_OWNI_EntryBytes.codec
  (PV_OWNC_PushFold.append PV_OWNI_EntryBytes.codec
   (PV_OWNI_EmptyVec.buffer m p owner (2^width point))
   ((PV_OWNI_BuildTotal.entries point (width point) (trailing point) (suffix point)).map
    PV_OWNI_NumericBytes.encode)) :=
 ⟨PV_OWNI_ScannedResult.result point column len,
  PV_OWNI_InitializedResult.initialized point p owner m loans⟩
#print axioms value_and_memory
end R1Z.PV_OWNI_FocusedReplay
