import KNA_Frame
set_option autoImplicit false
namespace KNA_Halves04
open KMX_CopyMeaning KMY_WindowComposition
/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, 640≤j → j<720 → actual j=expected j)
 (right : ∀ j, 720≤j → j<800 → actual j=expected j) :
 ∀ j, 640≤j → j<800 → actual j=expected j := by
 intro j lower upper
 by_cases h : j<720
 · exact left j lower h
 · exact right j (by omega) upper
#print axioms result
end KNA_Halves04
