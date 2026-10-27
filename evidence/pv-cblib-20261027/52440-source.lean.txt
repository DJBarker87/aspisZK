import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane08
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[32]! b.val[33]! b.val[34]! b.val[35]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane8 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane8
  rw [PV_CBL_ArrayReadValue.read b 32#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 33#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 34#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 35#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane08
