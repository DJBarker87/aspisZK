import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Body01
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (j : Nat) (range : 160≤j ∧ j<320) :
 loop before garbage 0 (min 1736 3472) j = before j :=
 KMY_VectorComposition.growth_retains before garbage 1736 3472 j (by omega) (by omega)
#print axioms result
end KMZ_Body01
