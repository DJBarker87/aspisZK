import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane06
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[24]! b.val[25]! b.val[26]! b.val[27]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane6 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane6
  rw [PV_CBL_ArrayReadValue.read b 24#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 25#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 26#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 27#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane06
