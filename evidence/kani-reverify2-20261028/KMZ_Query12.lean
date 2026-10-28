import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Query12
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<112+4) :
 window source (loop before garbage 0 (min 128 128)) 112 4 j =
 if j<112 then before j else source (j-112) :=
 KMZ_Growth.append_after_growth before garbage source 112 128 128 4 j (by omega) (by omega) bound
#print axioms result
end KMZ_Query12
