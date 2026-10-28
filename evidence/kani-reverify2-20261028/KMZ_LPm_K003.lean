import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPm_K003
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (i cap next j : Nat)
 (idx : i<64) (live : 712+16*i≤cap) (growth : cap≤next) (bound : j<712+16*i+16) :
 712+16*i+16≤1736 ∧ window source (loop before garbage 0 (min cap next)) (712+16*i) 16 j =
 (if j<712+16*i then before j else source (j-(712+16*i))) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source _ cap next 16 j live growth bound
#print axioms result
end KMZ_LPm_K003
