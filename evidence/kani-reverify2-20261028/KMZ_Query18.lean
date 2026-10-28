import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query18
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<136+4) :
 window source (loop before garbage 0 (min 256 256)) 136 4 j =
 if j<136 then before j else source (j-136) :=
 KMZ_Growth.append_after_growth before garbage source 136 256 256 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query18
