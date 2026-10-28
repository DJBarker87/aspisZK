import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query06
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<88+4) :
 window source (loop before garbage 0 (min 128 128)) 88 4 j =
 if j<88 then before j else source (j-88) :=
 KMZ_Growth.append_after_growth before garbage source 88 128 128 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query06
