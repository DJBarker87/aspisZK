import R1Z.PV_CBL_FallbackConstantMatrix
import R1Z.PV_CBL_FallbackArrayRead
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockConstantRead05
set_option autoImplicit false
theorem source : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 5#usize =
    ok PV_CBL_FallbackConstantMatrix.q5 := by
  simp [Array.index_usize,Array.getElem?_Usize_eq,PV_CBL_FallbackConstantMatrix.matrix]
#print axioms source
end R1Z.PV_CBL_BlockConstantRead05
