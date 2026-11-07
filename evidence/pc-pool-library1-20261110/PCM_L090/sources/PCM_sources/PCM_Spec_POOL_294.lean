import PCM_Carriers
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM_POOL_294
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × Marker
structure Children where
  encode : Child Marker Bytes
  canonicalNullifier : Marker → B32
  address : Child (B32 × B32 × B32) (B32 × B32)
  classify : Child (B32 × AccountInfo) Preparation

def Ref (C : Children) (a : Args) : Computation PlannedMarker := do
  let (program,account,marker) := a
  let encoded ← mapError (fun _ => .custom 0x41532025) (C.encode.call marker)
  let (expected,seed) ← C.address.call (program,marker.pool,C.canonicalNullifier marker)
  check (account.key != expected || account.key == marker.pool) (.custom 0x41532024)
  let prep ← C.classify.call (program,account)
  Computation.pure ⟨prep,seed,encoded⟩
def RowSpec (C : Children) (impl : Args → State → Env → Observation PlannedMarker) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_294
