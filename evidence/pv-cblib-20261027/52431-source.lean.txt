import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane00
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[0]! b.val[1]! b.val[2]! b.val[3]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane0 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane0
  rw [PV_CBL_ArrayReadValue.read b 0#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 1#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 2#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 3#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane00
