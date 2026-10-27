import R1Z.PV_CBL_FinalSoft
import R1Z.PV_CBL_ByteStoreRead
import R1Z.PV_CBL_ByteStoreValue
import R1Z.PV_CBL_ArrayReadValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestBytesValue
set_option autoImplicit false
def value (state : Array U32 8#usize) : Array U8 32#usize :=
  Array.make 32#usize [PV_CBL_ByteStoreValue.byte state.val[0]! 0,PV_CBL_ByteStoreValue.byte state.val[0]! 1,PV_CBL_ByteStoreValue.byte state.val[0]! 2,PV_CBL_ByteStoreValue.byte state.val[0]! 3,PV_CBL_ByteStoreValue.byte state.val[1]! 0,PV_CBL_ByteStoreValue.byte state.val[1]! 1,PV_CBL_ByteStoreValue.byte state.val[1]! 2,PV_CBL_ByteStoreValue.byte state.val[1]! 3,PV_CBL_ByteStoreValue.byte state.val[2]! 0,PV_CBL_ByteStoreValue.byte state.val[2]! 1,PV_CBL_ByteStoreValue.byte state.val[2]! 2,PV_CBL_ByteStoreValue.byte state.val[2]! 3,PV_CBL_ByteStoreValue.byte state.val[3]! 0,PV_CBL_ByteStoreValue.byte state.val[3]! 1,PV_CBL_ByteStoreValue.byte state.val[3]! 2,PV_CBL_ByteStoreValue.byte state.val[3]! 3,PV_CBL_ByteStoreValue.byte state.val[4]! 0,PV_CBL_ByteStoreValue.byte state.val[4]! 1,PV_CBL_ByteStoreValue.byte state.val[4]! 2,PV_CBL_ByteStoreValue.byte state.val[4]! 3,PV_CBL_ByteStoreValue.byte state.val[5]! 0,PV_CBL_ByteStoreValue.byte state.val[5]! 1,PV_CBL_ByteStoreValue.byte state.val[5]! 2,PV_CBL_ByteStoreValue.byte state.val[5]! 3,PV_CBL_ByteStoreValue.byte state.val[6]! 0,PV_CBL_ByteStoreValue.byte state.val[6]! 1,PV_CBL_ByteStoreValue.byte state.val[6]! 2,PV_CBL_ByteStoreValue.byte state.val[6]! 3,PV_CBL_ByteStoreValue.byte state.val[7]! 0,PV_CBL_ByteStoreValue.byte state.val[7]! 1,PV_CBL_ByteStoreValue.byte state.val[7]! 2,PV_CBL_ByteStoreValue.byte state.val[7]! 3]
theorem source (state : Array U32 8#usize) :
    PV_CBL_FinalSoft.sha_digest32 state = ok (value state) := by
  unfold PV_CBL_FinalSoft.sha_digest32
  simp only [PV_CBL_ArrayReadValue.read state 0#usize (by decide),PV_CBL_ArrayReadValue.read state 1#usize (by decide),PV_CBL_ArrayReadValue.read state 2#usize (by decide),PV_CBL_ArrayReadValue.read state 3#usize (by decide),PV_CBL_ArrayReadValue.read state 4#usize (by decide),PV_CBL_ArrayReadValue.read state 5#usize (by decide),PV_CBL_ArrayReadValue.read state 6#usize (by decide),PV_CBL_ArrayReadValue.read state 7#usize (by decide),
    PV_CBL_ByteCodecValue.store_source,PV_CBL_ByteStoreRead.read0,PV_CBL_ByteStoreRead.read1,
    PV_CBL_ByteStoreRead.read2,PV_CBL_ByteStoreRead.read3,bind_tc_ok]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_DigestBytesValue
