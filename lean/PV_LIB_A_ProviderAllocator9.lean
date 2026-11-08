import PV_LIB_A_ValueDestruct9
import PV_THR2_Packet218ReturnData
set_option autoImplicit false
namespace PV_LIB_A_ProviderAllocator9
open PV_STX2_Syntax PV_STX2_Store PV_LIB_A_TypedDestruct

/-- Exact allocator already produced by the provider's source218 theorem.
No equality of activation counters or final stores is requested. -/
theorem source218_allocator : PV_THR2_Packet218ReturnData.allocator =
    PV_LIB_A_AllocatorProvenance.globalValue := rfl

/-- The provider's exact THREE-field Arc representation, imported by name.
The old pointer/allocator values are not replaced by a restated bare pointer. -/
theorem source315_allocator {W : Type} (base : Carrier W Data) (ptr : Data) :
    PV_LIB_A_AllocatorProvenance.arcAllocator (PV_THR2_KeyValues.carrier base)
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator) =
      some PV_LIB_A_AllocatorProvenance.globalType := rfl

theorem source315_glue {W : Type} (base : Carrier W Data) (payload ptr : Data) :
    PV_LIB_A_AllocatorProvenance.arcGlue (PV_THR2_KeyValues.carrier base)
      (PV_LIB_A_TypedBindingFacts.arcType payload)
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator) =
      some (.call (fnPtr 405 ⟨[.atom "Erased"],
        [payload,PV_LIB_A_AllocatorProvenance.globalType],[],[]⟩)) := by
  -- The Arc kind differs across typed cohorts; field2 does not.
  have same : PV_LIB_A_AllocatorProvenance.arcAllocator (PV_THR2_KeyValues.carrier base)
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator) =
    PV_LIB_A_AllocatorProvenance.arcAllocator (PV_THR2_KeyValues.carrier base)
      (PV_LIB_A_AllocatorProvenance.constructed payload ptr .null) := rfl
  simpa only [PV_LIB_A_AllocatorProvenance.arcGlue,same] using
    PV_LIB_A_AllocatorProvenance.source_glue base payload ptr .null

#print axioms source218_allocator
#print axioms source315_allocator
#print axioms source315_glue
end PV_LIB_A_ProviderAllocator9
