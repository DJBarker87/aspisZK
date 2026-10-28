import KMZ_Growth
set_option autoImplicit false
namespace KMZ_TypedExterior
open KMX_CopyMeaning KMY_WindowComposition
theorem result {α : Type} (raw before : Nat → α) (j : Nat) (outside : j=0 ∨ 65≤j) :
 loop raw before 1 64 j = before j :=
 copy_frame raw before 1 64 j (by omega)
#print axioms result
end KMZ_TypedExterior
