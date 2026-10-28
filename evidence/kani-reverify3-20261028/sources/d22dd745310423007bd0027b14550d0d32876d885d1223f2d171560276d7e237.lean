import KMZ_Growth
set_option autoImplicit false
namespace KNA_Frame
open KMX_CopyMeaning KMY_WindowComposition
/-- A pointwise heap frame is the runtime interface; no allocation is inferred. -/
theorem result (before source after : Nat → Nat) (len size : Nat)
 (prefix : ∀ j, j<len → after j=before j)
 (tail : ∀ j, len≤j → j<len+size → after j=source (j-len)) :
 ∀ j, j<len+size → after j=(if j<len then before j else source (j-len)) := by
 intro j bound
 by_cases h : j<len
 · simpa only [if_pos h] using prefix j h
 · simpa only [if_neg h] using tail j (by omega) bound
#print axioms result
end KNA_Frame
