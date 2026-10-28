import KMZ_Growth
set_option autoImplicit false
namespace KMZ_DigestB
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<48+32) :
 window source (loop before garbage 0 (min 48 96)) 48 32 j =
 if j<48 then before j else source (j-48) :=
 KMZ_Growth.append_after_growth before garbage source 48 48 96 32 j (by omega) (by omega) bound
#print axioms result
end KMZ_DigestB
