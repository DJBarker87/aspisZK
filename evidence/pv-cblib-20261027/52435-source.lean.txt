import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane03
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[12]! b.val[13]! b.val[14]! b.val[15]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane3 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane3
  rw [PV_CBL_ArrayReadValue.read b 12#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 13#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 14#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 15#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane03
