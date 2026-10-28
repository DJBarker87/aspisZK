import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPi_K012
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (len cap next j : Nat)
 (limit : len≤1720) (live : len≤cap) (growth : cap≤next) (bound : j<len+16) :
 len+16≤1736 ∧ window source (loop before garbage 0 (min cap next)) len 16 j =
 (if j<len then before j else source (j-len)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source len cap next 16 j live growth bound
#print axioms result
end KMZ_LPi_K012
