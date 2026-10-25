import Hiq_DispatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchAdmitted
open Aeneas Aeneas.Std Result
open Hiq_DispatchSource
attribute [local instance] Classical.propDecidable

theorem exact (data : Slice U8) :
    pool_route.admitted data = ok (decide (Hiq_ReleaseRoute.stage1 data ∨ Hiq_ReleaseRoute.asq8 data)) := by
  classical
  by_cases a : data.val = [3#u8,10#u8]
  · simp [Array.make,Array.to_slice,lift,pool_route.admitted,eqU8,starts,Hiq_ReleaseRoute.stage1,Hiq_ReleaseRoute.asq8,a]
  by_cases b : data.val = [3#u8,11#u8]
  · simp [Array.make,Array.to_slice,lift,pool_route.admitted,eqU8,starts,Hiq_ReleaseRoute.stage1,Hiq_ReleaseRoute.asq8,a,b]
  · simp [Array.make,Array.to_slice,lift,pool_route.admitted,eqU8,starts,Hiq_ReleaseRoute.stage1,Hiq_ReleaseRoute.asq8,a,b]

#print axioms exact
end AspisR1.Hiq_DispatchAdmitted
end
