import R1Z.PV_CB3_StagedSource
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedLoadInspect
open Aeneas Aeneas.Std
#print core.num.U32.from_le_bytes

theorem byte_bound (x : U8) : x.val < 256 := by
  simpa only [UScalar.bv_toNat] using x.bv.isLt
#print axioms byte_bound
end R1Z.PV_CB3_StagedLoadInspect
