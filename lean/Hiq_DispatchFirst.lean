import Hiq_DispatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchFirst
open Aeneas Aeneas.Std Result Hiq_DispatchSource

theorem source {Account : Type} (ops : Ops Account) (id : Key) (accounts : Slice Account) (data : Slice U8)
    (first : Hiq_ReleaseRoute.stage1 data) :
    r1_pool_adapter.process ops id accounts data = ops.first id accounts data := by
  classical
  rcases first with h | h
  all_goals simp [Array.make,r1_pool_adapter.process,firstByte,copied,h,eqU8]
  all_goals rfl

#print axioms source
end AspisR1.Hiq_DispatchFirst
end
