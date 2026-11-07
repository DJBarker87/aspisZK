import PV_THR2_PacketMetadata76Store
set_option autoImplicit false
namespace PV_THR2_PacketMetadata76Frame
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Actual13129 moves only25/13/23 and writes27; foreign roots and Arc17
remain on the complete Store. No hypotheses about values. -/
def prepared (s : Store Data) (a : Nat) (v : Data) :=
  write (write (write (write s ⟨a,25,[]⟩ none) ⟨a,13,[]⟩ none) ⟨a,23,[]⟩ none) ⟨a,27,[]⟩ (some v)
theorem frame (s : Store Data) (a : Nat) (v : Data) (p : Address) (other : p.activation ≠ a) :
    (prepared s a v).cells p = s.cells p := by
  simp only [prepared,write,
    show ∀ i, p ≠ (⟨a,i,[]⟩ : Address) from fun i h => other (congrArg Address.activation h),if_false]
#print axioms frame
end PV_THR2_PacketMetadata76Frame
