import R1Z.PV_CBL_BlockGraph
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockValue
set_option autoImplicit false
/-- Complete output composition of the extracted owned Rust soft block.
The value graph has all sixteen groups, schedule recurrence, constants and
feed-forward; no native dispatcher or byte-buffer wrapper is substituted. -/
theorem source (state : Array U32 8#usize) (input : Array U32 16#usize) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state input =
      ok (PV_CBL_FallbackStateCodec.encode
        (PV_CBL_BlockGraph.value (PV_CBL_FallbackStateCodec.decode state) input)) := by
  calc
    _ = PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block
        (PV_CBL_FallbackStateCodec.encode (PV_CBL_FallbackStateCodec.decode state)) input := by
      rw [PV_CBL_FallbackStateCodec.encode_decode]
    _ = _ := (PV_CBL_BlockGraph.source _ input).trans (PV_CBL_BlockGraph.graph_value _ input)
#print axioms source
end R1Z.PV_CBL_BlockValue
