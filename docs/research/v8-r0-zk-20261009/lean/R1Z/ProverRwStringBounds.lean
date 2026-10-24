import Aeneas
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace R1Z.ProverRwStringBounds

theorem burn : ".burn".toByteArray.size ≤ U32.max := by
  rw [String.size_toByteArray]
  change 5 ≤ U32.max
  norm_num [U32.max,U32.numBits]

theorem digit : "0".toByteArray.size ≤ U32.max := by
  rw [String.size_toByteArray]
  change 1 ≤ U32.max
  norm_num [U32.max,U32.numBits]

#print axioms burn
#print axioms digit
end R1Z.ProverRwStringBounds
