import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane12
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[48]! b.val[49]! b.val[50]! b.val[51]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane12 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane12
  rw [PV_CBL_ArrayReadValue.read b 48#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 49#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 50#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 51#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane12
