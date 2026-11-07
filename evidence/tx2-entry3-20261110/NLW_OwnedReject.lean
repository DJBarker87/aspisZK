import NLE_OwnedFold
set_option autoImplicit false
noncomputable section
namespace NLW_OwnedReject
open Aeneas Aeneas.Std Result AdapterRw
/-- Complete first source prefix: wrong account count rejects before any
child, allocation, SDK read or error-map/emit suffix. Ops is never inspected. -/
theorem count (ops : Ops) (s : NLE_Owned.State)
 (guard : (Slice.len s.frame.accounts != 7#usize)=true) :
 NLE_Owned.G ops s=⟨.ok (.Err .InvalidInstructionData),[]⟩ := by
 unfold NLE_Owned.G
 simp only [guard,↓reduceIte]
 rfl
#print count
#print axioms count
end NLW_OwnedReject
