import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane01
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[4]! b.val[5]! b.val[6]! b.val[7]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane1 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane1
  rw [PV_CBL_ArrayReadValue.read b 4#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 5#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 6#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 7#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane01
