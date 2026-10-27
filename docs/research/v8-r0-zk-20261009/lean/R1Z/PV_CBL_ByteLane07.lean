import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane07
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[28]! b.val[29]! b.val[30]! b.val[31]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane7 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane7
  rw [PV_CBL_ArrayReadValue.read b 28#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 29#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 30#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 31#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane07
