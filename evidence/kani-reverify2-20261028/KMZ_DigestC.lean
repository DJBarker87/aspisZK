import KMZ_Growth
set_option autoImplicit false
namespace KMZ_DigestC
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<80+32) :
 window source (loop before garbage 0 (min 96 192)) 80 32 j =
 if j<80 then before j else source (j-80) :=
 KMZ_Growth.append_after_growth before garbage source 80 96 192 32 j (by omega) (by omega) bound
#print axioms result
end KMZ_DigestC
