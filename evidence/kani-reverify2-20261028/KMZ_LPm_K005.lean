import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPm_K005
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (len cap next j : Nat)
 (limit : len≤1732) (live : len≤cap) (growth : cap≤next) (bound : j<len+4) :
 len+4≤1736 ∧ window source (loop before garbage 0 (min cap next)) len 4 j =
 (if j<len then before j else source (j-len)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source len cap next 4 j live growth bound
#print axioms result
end KMZ_LPm_K005
