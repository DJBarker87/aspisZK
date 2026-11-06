import NKU_HeaderValue
import NJU_FieldScalar
set_option autoImplicit false
namespace NKU_HeaderSize
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Small closed parameter arithmetic only:744+16*64, not a recurrence. -/
theorem size : CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant transport.Variant.S2)=ok 1768#usize := by
 have product : 16#usize * 64#usize = ok 1024#usize := by
  apply NJU_FieldScalar.eq_of_value
  simpa using UScalar.mul_spec (x:=16#usize) (y:=64#usize) (by scalar_tac)
 have sum : 744#usize + 1024#usize = ok 1768#usize := by
  apply NJU_FieldScalar.eq_of_value
  simpa using UScalar.add_spec (x:=744#usize) (y:=1024#usize) (by scalar_tac)
 unfold CheckpointBytes4Ops.checkpointSize CheckpointBytes4Ops.finalLen NIL_Carriers.variant
 simp only [bind_tc_ok,product,sum]
#print axioms size
end NKU_HeaderSize
