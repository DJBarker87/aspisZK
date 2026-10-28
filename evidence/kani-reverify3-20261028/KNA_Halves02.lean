import KNA_Frame
set_option autoImplicit false
namespace KNA_Halves02
open KMX_CopyMeaning KMY_WindowComposition
/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, 320≤j → j<400 → actual j=expected j)
 (right : ∀ j, 400≤j → j<480 → actual j=expected j) :
 ∀ j, 320≤j → j<480 → actual j=expected j := by
 intro j lower upper
 by_cases h : j<400
 · exact left j lower h
 · exact right j (by omega) upper
#print axioms result
end KNA_Halves02
