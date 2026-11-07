import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_314
open RSL PCM PCM.Computation
abbrev Args := Bytes
/-- Frozen real callee: decode_pool_v1_pair_forest_terminal_request_v1; map all errors to InvalidInstructionData. Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child (Bytes) Request
def Ref (decoder : Decoder) (a : Args) : Computation Request := do
  let value ← decoder.call a
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation Request) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_314
