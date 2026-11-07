import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_337
open RSL PCM PCM.Computation
abbrev Encoder := Child TerminalResult Bytes
/-- Encoder Err maps to exactly Custom(0x4153202d); its by-value output has no
heap allocation. The Box site is reached only after encoder success. -/
def Ref (encoder : Encoder) (a : TerminalResult) : Computation Bytes := do
  let bytes ← mapError (fun _ => .custom 0x4153202d) (encoder.call a)
  alloc
  Computation.pure bytes
def RowSpec (encoder : Encoder) (impl : TerminalResult → State → Env → Observation Bytes) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref encoder) impl
end PCM_POOL_337
