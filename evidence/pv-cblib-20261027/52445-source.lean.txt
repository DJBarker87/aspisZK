import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane13
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[52]! b.val[53]! b.val[54]! b.val[55]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane13 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane13
  rw [PV_CBL_ArrayReadValue.read b 52#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 53#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 54#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 55#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane13
