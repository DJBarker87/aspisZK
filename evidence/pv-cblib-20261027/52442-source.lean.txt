import R1Z.PV_CBL_ByteLoadSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteLane10
set_option autoImplicit false
def value (b : Array U8 64#usize) : U32 :=
  PV_CBL_ByteCodecValue.load b.val[40]! b.val[41]! b.val[42]! b.val[43]!
theorem source (b : Array U8 64#usize) :
    PV_CBL_ShaBytes.sha_load_lane10 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load_lane10
  rw [PV_CBL_ArrayReadValue.read b 40#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 41#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 42#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read b 43#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ByteLoadSource.source]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteLane10
