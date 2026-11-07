import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_358
open RSL PCM PCM.Computation
abbrev Args := AccountInfo × AccountInfo × AccountInfo × Nat × B32 × List Bytes
structure Children where
  rentGet : Child Unit PCM.Rent
  withRent : Child (Args × PCM.Rent) Unit
/-- Rent::get is reached before the with-rent helper. No successful CPI,
rent exemption, system semantics, or runtime borrow frame is assumed. -/
def Ref (C : Children) (a : Args) : Computation Unit := do
  let rent ← C.rentGet.call ()
  C.withRent.call (a,rent)
def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_358
