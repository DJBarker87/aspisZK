import KMZ_Growth
set_option autoImplicit false
namespace KMZ_RootA
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<0+32) :
 window source (loop before garbage 0 (min 0 32)) 0 32 j =
 if j<0 then before j else source (j-0) :=
 KMZ_Growth.append_after_growth before garbage source 0 0 32 32 j (by omega) (by omega) bound
#print axioms result
end KMZ_RootA
