import KMZ_Growth
set_option autoImplicit false
namespace KMZ_IteratorInterior
open KMX_CopyMeaning KMY_WindowComposition
theorem result (i : Nat) (interior : i<63) : i<64 ∧ 64-(i+1)=63-i := by omega
#print axioms result
end KMZ_IteratorInterior
