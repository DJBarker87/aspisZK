import Aeneas
open Aeneas Aeneas.Std
namespace AspisR1.CuSavingsGeometryString
theorem short_error_string : "IndexOutOfRange".toByteArray.size ≤ U32.max := by
  norm_num [U32.max,U32.numBits,UScalar.max,UScalarTy.numBits]
  decide
#print axioms short_error_string
end AspisR1.CuSavingsGeometryString
