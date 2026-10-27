import JGc_TX2_HashBytes
set_option autoImplicit false
namespace AspisR1.JGc_TX2_HashBytes
theorem append (xs ys : List Nat) : bytes (xs++ys)=bytes xs++bytes ys := List.map_append _ _ _
#print axioms append
end AspisR1.JGc_TX2_HashBytes
