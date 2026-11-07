import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_326
open RSL PCM PCM.Computation
abbrev Args := LaneState × UInt8 × Digest
structure Children where
  append : Child (Tree × Digest × List Digest) (Tree × Append)
  encode : Child (LaneState × List Digest) Bytes
/-- Deployed deposit-invariant-audit OFF: native generic append then two
Box sites, with the first allocation preceding a later encoder rejection. -/
def Ref (C : Children) (a : Args) : Computation (Append × Bytes) := do
  let (lane,laneId,leaf) := a
  let (tree,append) ← mapError (fun _ => .custom 0x41532003) (C.append.call (lane.tree,leaf,EMPTY_ROOTS))
  alloc
  let nextLane : LaneState := ⟨lane.bump,lane.master,laneId,tree⟩
  let image ← mapError (fun _ => .custom 0x41532003) (C.encode.call (nextLane,EMPTY_ROOTS))
  alloc
  Computation.pure (append,image)
def RowSpec (C : Children) (impl : Args → State → Env → Observation (Append × Bytes)) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_326
