import NKU_State
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderSlots
open Aeneas Aeneas.Std
def set (s : NKU.State) (next : U8) («end» : Usize) : NKU.State :=
 {s with decoded := {s.decoded with next := some next,endAt := some «end»}}
theorem same (s : NKU.State) (next : U8) («end» : Usize)
 (hn : s.decoded.next=some next) (he : s.decoded.endAt=some «end») :
 set s next «end»=s := by
 cases s with
 | mk frame phase decoded reader iterator owned returned history =>
  cases decoded
  simp_all [set]
#print axioms same
end NKU_HeaderSlots
