import R1Z.PV_AL_PopStep
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_PopPrefix
set_option autoImplicit false

theorem length {T : Type} (v : Slice T) (out : alloc.vec.Vec T) (i last : Usize)
    (hi : i.val<last.val) (hl : last.val≤v.val.length)
    (hp : out.val=v.val.take i.val) : out.val.length<Usize.max := by
  rw [hp,List.length_take,Nat.min_eq_left (by omega)]
  have := v.property
  omega

theorem advance {T : Type} (v : Slice T) (out next : alloc.vec.Vec T) (i : Usize)
    (hi : i.val<v.val.length) (hp : out.val=v.val.take i.val)
    (hn : next.val=out.val++[v.val[i.val]]) : next.val=v.val.take (i.val+1) := by
  rw [hn,hp]
  exact (List.take_succ_eq_append_getElem hi).symm
#print axioms length
#print axioms advance
end R1Z.PV_AL_PopPrefix
