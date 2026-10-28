import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPm_K004
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (len cap next j : Nat)
 (limit : len≤1704) (live : len≤cap) (growth : cap≤next) (bound : j<len+32) :
 len+32≤1736 ∧ window source (loop before garbage 0 (min cap next)) len 32 j =
 (if j<len then before j else source (j-len)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source len cap next 32 j live growth bound
#print axioms result
end KMZ_LPm_K004
