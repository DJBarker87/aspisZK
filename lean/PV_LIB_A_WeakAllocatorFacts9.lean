import PV_LIB_A_WeakOwnerFree9
import PV_LIB_A_ProviderAllocator9
import PV_STX2_TypedReferences
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakAllocatorFacts9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_LIB_A_WeakOwnerFree9

theorem direct (C : Carrier OWNER Data) (s : Store Data) (w : OWNER) :
    allocator C s w PV_LIB_A_AllocatorProvenance.globalType
      PV_THR2_Packet218ReturnData.allocator = some () := rfl

/-- The implicit weak guard uses &A, not an invented owned allocator value.
The actual pointer and source read discharge both type and value recognition. -/
theorem borrowed (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (region reference : Data) (p : Address)
    (pointer : C.dereference w reference = some p)
    (source : readAddress C s p = some PV_THR2_Packet218ReturnData.allocator) :
    allocator C s w (.object [("Ref",.array
      [region,PV_LIB_A_AllocatorProvenance.globalType,.atom "Shared"])]) reference = some () := by
  unfold allocator
  change (C.dereference w reference).bind _ = _
  rw [pointer]
  change (readAddress C s p).bind _ = _
  rw [source]
  rfl

/-- Dereference of the guard's source reference reads Arc.alloc at field2.
The source Arc representation is the provider's definition, imported by name. -/
theorem guard_from_arc (base : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (region ptr : Data) (a i : Nat)
    (source : s.cells ⟨a,i,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator)) :
    allocator (PV_STX2_TypedReferences.carrier (PV_THR2_KeyValues.carrier base)) s w
      (.object [("Ref",.array [region,PV_LIB_A_AllocatorProvenance.globalType,.atom "Shared"])])
      (PV_STX2_TypedReferences.reference ⟨a,i,[2]⟩ .null) = some () := by
  apply borrowed (p := ⟨a,i,[2]⟩)
  · exact PV_STX2_TypedReferences.dereference (PV_THR2_KeyValues.carrier base) w _ _
  · change (s.cells ⟨a,i,[]⟩).bind _ = _
    rw [source]
    rfl

#print axioms direct
#print axioms borrowed
#print axioms guard_from_arc
end PV_LIB_A_WeakAllocatorFacts9
