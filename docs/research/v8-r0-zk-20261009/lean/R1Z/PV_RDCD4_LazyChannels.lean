import R1Z.PV_RDCD4_LazyCell
import R1Z.PV_RDCD3_RangeLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyChannels
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell
/-- The two source for-loops own and return the complete nested channel array. -/
def row (left right : List (List M)) (sums : Sums) (component : Nat) : Result Sums :=
  PV_RDCD3_RangeLoop.source (fun s channel => cell left right s component channel) ⟨0,3⟩ sums

def nine (left right : List (List M)) (sums : Sums) : Result Sums :=
  PV_RDCD3_RangeLoop.source (fun s component => row left right s component) ⟨0,3⟩ sums

theorem row_unroll (left right : List (List M)) (sums : Sums) (component : Nat) :
    row left right sums component = (do
      let s ← cell left right sums component 0
      let s ← cell left right s component 1
      cell left right s component 2) := by
  rw [row,PV_RDCD3_RangeLoop.complete _ 3 0 3 sums (by omega)]
  simp only [PV_RDCD3_RangeFold.ordered,bind_tc_ok,bind_ok]

theorem nine_unroll (left right : List (List M)) (sums : Sums) :
    nine left right sums = (do
      let s ← row left right sums 0
      let s ← row left right s 1
      row left right s 2) := by
  rw [nine,PV_RDCD3_RangeLoop.complete _ 3 0 3 sums (by omega)]
  simp only [PV_RDCD3_RangeFold.ordered,bind_tc_ok,bind_ok]
#print axioms row_unroll
#print axioms nine_unroll
end R1Z.PV_RDCD4_LazyChannels
