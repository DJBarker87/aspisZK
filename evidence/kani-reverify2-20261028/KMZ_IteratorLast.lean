import KMZ_Growth
set_option autoImplicit false
namespace KMZ_IteratorLast
open KMX_CopyMeaning KMY_WindowComposition
theorem result (i : Nat) (last : i=63) : 64-i=1 ∧ 64-(i+1)=0 := by omega
#print axioms result
end KMZ_IteratorLast
