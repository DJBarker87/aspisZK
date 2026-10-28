import KMZ_Growth
set_option autoImplicit false
namespace KMZ_TypedInside
open KMX_CopyMeaning KMY_WindowComposition
theorem result {α : Type} (raw before : Nat → α) (j : Nat) (bound : j<64) :
 loop raw before 0 64 j = raw j := by
 rw [copy_prefix, if_pos bound]
#print axioms result
end KMZ_TypedInside
