import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane09
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[36]! b.val[37]! b.val[38]! b.val[39]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane9 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane9
  rw [PV_CBL_ArrayReadValue.read b 36#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 37#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 38#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 39#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane09
