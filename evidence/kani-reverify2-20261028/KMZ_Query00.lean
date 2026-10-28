import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query00
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<64+4) :
 window source (loop before garbage 0 (min 64 128)) 64 4 j =
 if j<64 then before j else source (j-64) :=
 KMZ_Growth.append_after_growth before garbage source 64 64 128 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query00
