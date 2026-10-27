import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane04
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[16]! b.val[17]! b.val[18]! b.val[19]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane4 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane4
  rw [PV_CBL_ArrayReadValue.read b 16#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 17#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 18#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 19#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane04
