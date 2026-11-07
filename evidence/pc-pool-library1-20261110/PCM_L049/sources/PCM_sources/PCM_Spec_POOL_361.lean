import PCM_Carriers
import PCM_SdkOps
set_option autoImplicit false
namespace PCM_POOL_361
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × List Bytes × AccountInfo × AccountInfo × AccountInfo × PlannedMarker × PCM.Rent
structure Children where
  seedString : Child B32 String
  createWithSeed : Child (AccountInfo × AccountInfo × AccountInfo × String × AccountInfo × Nat × B32 × List Bytes × PCM.Rent) Unit
  recheck : Child (B32 × AccountInfo) Preparation
  rentExempt : PCM.Rent → UInt64 → Nat → Bool

def Ref (C : Children) (a : Args) : Computation PlannedMarker := do
  let (program,master,seeds,marker,payer,system,planned,rent) := a
  if planned.preparation == .createOrAllocateSystemOwned then
    let seed ← C.seedString.call planned.seed
    C.createWithSeed.call (payer,marker,master,seed,system,256,program,seeds,rent)
  let prep ← C.recheck.call (program,marker)
  check (prep != .programOwnedZeroed) (.custom 0x41532025)
  let lamports ← readLamports marker
  check (!C.rentExempt rent lamports 256) (.custom 0x41532025)
  Computation.pure planned

def RowSpec (C : Children) (impl : Args → State → Env → Observation PlannedMarker) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_361
