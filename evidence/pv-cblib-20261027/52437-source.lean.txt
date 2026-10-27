import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane05
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[20]! b.val[21]! b.val[22]! b.val[23]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane5 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane5
  rw [PV_CBL_ArrayReadValue.read b 20#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 21#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 22#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 23#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane05
