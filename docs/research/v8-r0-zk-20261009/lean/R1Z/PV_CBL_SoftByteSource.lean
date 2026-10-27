import R1Z.PV_CBL_ByteWordsSource
import R1Z.PV_CBL_SoftBlockSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftByteSource
set_option autoImplicit false
def reference (state : Array U32 8#usize) (block : Array U8 64#usize) :
    Result (Array U32 8#usize) := do
  let words ← PV_CBL_ShaBytes.sha_load64 block
  PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state words
def value (state : Array U32 8#usize) (block : Array U8 64#usize) : Array U32 8#usize :=
  PV_CBL_FallbackStateCodec.encode (PV_CBL_SoftBlockSource.value
    (PV_CBL_FallbackStateCodec.decode state) (PV_CBL_ByteWordsSource.value block))
/-- Composition of the complete extracted byte decoder and extracted scalar block.
The enclosing native iterator/loan and dispatcher associations are separate. -/
theorem source (state : Array U32 8#usize) (block : Array U8 64#usize) :
    reference state block = ok (value state block) := by
  rw [reference,PV_CBL_ByteWordsSource.source,bind_tc_ok,PV_CBL_SoftBlockSource.source]
  rfl
#print axioms reference
#print axioms value
#print axioms source
end R1Z.PV_CBL_SoftByteSource
