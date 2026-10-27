import R1Z.PV_CBL_FinalSoft
import R1Z.PV_CBL_SoftByteSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftByteExtracted
set_option autoImplicit false
theorem bridge (state : Array U32 8#usize) (block : Array U8 64#usize) :
    PV_CBL_FinalSoft.sha_compress_byte_owned state block =
      PV_CBL_SoftByteSource.reference state block := rfl
theorem source (state : Array U32 8#usize) (block : Array U8 64#usize) :
    PV_CBL_FinalSoft.sha_compress_byte_owned state block = ok (PV_CBL_SoftByteSource.value state block) := by
  rw [bridge,PV_CBL_SoftByteSource.source]
#print axioms bridge
#print axioms source
end R1Z.PV_CBL_SoftByteExtracted
