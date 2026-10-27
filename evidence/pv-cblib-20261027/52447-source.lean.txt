import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane15
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[60]! b.val[61]! b.val[62]! b.val[63]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane15 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane15
  rw [PV_CBL_ArrayReadValue.read b 60#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 61#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 62#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 63#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane15
