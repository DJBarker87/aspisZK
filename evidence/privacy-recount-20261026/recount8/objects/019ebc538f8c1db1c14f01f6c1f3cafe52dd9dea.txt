import PV_B3P_ByteEncode226
import PV_B3P_ByteProject226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.public_bytes
  (source : reference226.Source) :
  Result (core.result.Result ((Array (Array Std.U8 64#usize) 23#usize) ×
    Std.Usize) aspis_core.state_only_prefix.r0.Error)
  := do
  let op ← reference226.project source
  reference226.encode_owned op

end PV_B3P_226
#print axioms PV_B3P_226.reference226.public_bytes
