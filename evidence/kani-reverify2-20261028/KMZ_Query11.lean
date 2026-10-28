import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query11
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<108+4) :
 window source (loop before garbage 0 (min 128 128)) 108 4 j =
 if j<108 then before j else source (j-108) :=
 KMZ_Growth.append_after_growth before garbage source 108 128 128 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query11
