import Hiq_DispatchSource
import Hiq_RouteHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchSecond
open Aeneas Aeneas.Std Result Hiq_DispatchSource

theorem disjoint (data : Slice U8) (second : Hiq_ReleaseRoute.asq8 data) : ¬ Hiq_ReleaseRoute.stage1 data := by
  intro first
  have heads := (Hiq_RouteHead.second_head data second).symm.trans (Hiq_RouteHead.first_head data first)
  exact (by decide : (65#u8) ≠ 3#u8) (Option.some.inj heads)

theorem source {Account : Type} (ops : Ops Account) (id : Key) (accounts : Slice Account) (data : Slice U8)
    (second : Hiq_ReleaseRoute.asq8 data) :
    r1_pool_adapter.process ops id accounts data = ops.second id accounts data := by
  classical
  have head := Hiq_RouteHead.second_head data second
  have no := disjoint data second
  have no10 : data.val ≠ [3#u8,10#u8] := fun h => no (Or.inl h)
  have no11 : data.val ≠ [3#u8,11#u8] := fun h => no (Or.inr h)
  simp only [r1_pool_adapter.process,firstByte,head,copied,bind_tc_ok]
  change (do
    let b ← eqU8 data (Array.make 2#usize [3#u8,10#u8])
    if b then ops.first id accounts data else do
      let b1 ← eqU8 data (Array.make 2#usize [3#u8,11#u8])
      if b1 then ops.first id accounts data else ops.second id accounts data) = ops.second id accounts data
  simp [eqU8,Array.make,no10,no11]

#print axioms disjoint
#print axioms source
end AspisR1.Hiq_DispatchSecond
end
