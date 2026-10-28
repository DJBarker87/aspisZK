import KNA_Frame
set_option autoImplicit false
namespace KNA_Halves05
open KMX_CopyMeaning KMY_WindowComposition
/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, 800≤j → j<880 → actual j=expected j)
 (right : ∀ j, 880≤j → j<960 → actual j=expected j) :
 ∀ j, 800≤j → j<960 → actual j=expected j := by
 intro j lower upper
 by_cases h : j<880
 · exact left j lower h
 · exact right j (by omega) upper
#print axioms result
end KNA_Halves05
