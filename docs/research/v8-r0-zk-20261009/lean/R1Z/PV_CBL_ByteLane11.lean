import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane11
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[44]! b.val[45]! b.val[46]! b.val[47]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane11 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane11
  rw [PV_CBL_ArrayReadValue.read b 44#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 45#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 46#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 47#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane11
