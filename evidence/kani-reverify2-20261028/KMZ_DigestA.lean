import KMZ_Growth
set_option autoImplicit false
namespace KMZ_DigestA
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<16+32) :
 window source (loop before garbage 0 (min 16 48)) 16 32 j =
 if j<16 then before j else source (j-16) :=
 KMZ_Growth.append_after_growth before garbage source 16 16 48 32 j (by omega) (by omega) bound
#print axioms result
end KMZ_DigestA
