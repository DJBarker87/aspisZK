import PV_LIB_A_WeakAllocatorFacts9
import PV_THR2_OwnInitExactReturnedCases
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardCaller9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine

/-- The existing source315 Arc on the ACTUAL original carrier stack supplies
drop_slow's borrowed Global allocator. This is an internal source read lemma;
caller reachability of the root is still composed from provider results. -/
theorem allocator (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (region ptr : Data) (a i : Nat)
    (source : s.cells ⟨a,i,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator)) :
    PV_LIB_A_WeakOwnerFree9.allocator (PV_THR2_OwnInitExactReturnedCases.carrier C b) s w
      (.object [("Ref",.array [region,PV_LIB_A_AllocatorProvenance.globalType,.atom "Shared"])])
      (PV_STX2_TypedReferences.reference ⟨a,i,[2]⟩ .null) = some () := by
  apply PV_LIB_A_WeakAllocatorFacts9.borrowed (p := ⟨a,i,[2]⟩)
  · rfl
  · change (s.cells ⟨a,i,[]⟩).bind _ = _
    rw [source]
    rfl

#print axioms allocator
end PV_LIB_A_WeakGuardCaller9
