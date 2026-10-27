import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane02
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[8]! b.val[9]! b.val[10]! b.val[11]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane2 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane2
  rw [PV_CBL_ArrayReadValue.read b 8#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 9#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 10#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 11#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane02
