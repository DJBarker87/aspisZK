import KNA_Frame
set_option autoImplicit false
namespace KNA_Halves00
open KMX_CopyMeaning KMY_WindowComposition
/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, 0≤j → j<80 → actual j=expected j)
 (right : ∀ j, 80≤j → j<160 → actual j=expected j) :
 ∀ j, 0≤j → j<160 → actual j=expected j := by
 intro j lower upper
 by_cases h : j<80
 · exact left j lower h
 · exact right j (by omega) upper
#print axioms result
end KNA_Halves00
