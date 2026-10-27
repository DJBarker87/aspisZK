import R1Z.PV_CBL_BlockValue
import R1Z.PV_CBL_CanonicalStage00
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftBlockSource
open PV_CBL_FallbackScalar
set_option autoImplicit false
/-- Conventional four-round SHA steps, scheduled in sixteen groups. -/
def value (state : State) (input : Array U32 16#usize) : State :=
  PV_CBL_CanonicalStage00.value state state
    (PV_CBL_BlockGraph.group0 input) (PV_CBL_BlockGraph.group1 input)
    (PV_CBL_BlockGraph.group2 input) (PV_CBL_BlockGraph.group3 input)
theorem graph_value (state : State) (input : Array U32 16#usize) :
    PV_CBL_BlockGraph.value state input = value state input :=
  PV_CBL_CanonicalStage00.source_value state state _ _ _ _
theorem source (state : Array U32 8#usize) (input : Array U32 16#usize) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state input =
      ok (PV_CBL_FallbackStateCodec.encode (value (PV_CBL_FallbackStateCodec.decode state) input)) := by
  rw [PV_CBL_BlockValue.source,graph_value]
#print axioms value
#print axioms graph_value
#print axioms source
end R1Z.PV_CBL_SoftBlockSource
