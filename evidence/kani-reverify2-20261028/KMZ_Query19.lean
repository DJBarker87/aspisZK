import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query19
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<140+4) :
 window source (loop before garbage 0 (min 256 256)) 140 4 j =
 if j<140 then before j else source (j-140) :=
 KMZ_Growth.append_after_growth before garbage source 140 256 256 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query19
