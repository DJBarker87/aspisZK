import KMZ_Growth
set_option autoImplicit false
namespace KMZ_RootB
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<32+32) :
 window source (loop before garbage 0 (min 32 64)) 32 32 j =
 if j<32 then before j else source (j-32) :=
 KMZ_Growth.append_after_growth before garbage source 32 32 64 32 j (by omega) (by omega) bound
#print axioms result
end KMZ_RootB
