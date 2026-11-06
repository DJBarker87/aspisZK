import NLE_Length
import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NLM_EncoderExtent
open Aeneas Aeneas.Std AdapterRw
/-- The actual op22 output carrier, not an independently selected public
slice, supplies the native public-byte extent at its entered continuation. -/
theorem returned (ops : Ops)
 (statement : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
 (bytes : Array U8 1880#usize)
 (_entered : ops.op22 statement=.ok (.Ok bytes)) :
 bytes.to_slice.val.length=1880 := NLE_Length.public_extent bytes
#print returned
#print axioms returned
end NLM_EncoderExtent
