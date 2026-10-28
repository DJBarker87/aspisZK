import R1Z.PV_AL_RangeStep
import R1Z.PV_AL_RangeLists
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_RangeInvariant
set_option autoImplicit false

theorem capacity (v : Slice U8) (out : alloc.vec.Vec U8) (lo : Nat) (i last : Usize)
    (hl : last.val ≤ v.val.length) (hi : i.val < last.val) (hlo : lo ≤ i.val)
    (hp : out.val=PV_AL_RangeLists.segment v.val lo i.val) :
    out.val.length < Usize.max := by
  rw [hp,PV_AL_RangeLists.length v.val lo i.val hlo (by omega)]
  have := v.property
  omega

theorem advance (v : Slice U8) (out next : alloc.vec.Vec U8) (lo : Nat) (i : Usize)
    (hlo : lo ≤ i.val) (hi : i.val < v.val.length)
    (hp : out.val=PV_AL_RangeLists.segment v.val lo i.val)
    (hn : next.val=out.val++[v.val[i.val]]) :
    next.val=PV_AL_RangeLists.segment v.val lo (i.val+1) := by
  rw [hn,hp]
  exact PV_AL_RangeLists.advance v.val lo i.val hlo hi

#print axioms capacity
#print axioms advance
end R1Z.PV_AL_RangeInvariant
