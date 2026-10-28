import KNA_Frame
set_option autoImplicit false
namespace KNA_Halves10
open KMX_CopyMeaning KMY_WindowComposition
/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, 1600≤j → j<1668 → actual j=expected j)
 (right : ∀ j, 1668≤j → j<1736 → actual j=expected j) :
 ∀ j, 1600≤j → j<1736 → actual j=expected j := by
 intro j lower upper
 by_cases h : j<1668
 · exact left j lower h
 · exact right j (by omega) upper
#print axioms result
end KNA_Halves10
