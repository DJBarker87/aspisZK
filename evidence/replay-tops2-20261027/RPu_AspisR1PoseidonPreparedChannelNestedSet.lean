import RPu_AspisR1PoseidonPreparedChannelArraySet

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelNestedSet
open Aeneas.Std
abbrev U64 := UScalar UScalarTy.U64
abbrev Sums := Array (Array U64 3#usize) 3#usize
open AspisR1PoseidonPreparedChannelArraySet

theorem cell_nested_set (a : Sums) (component channel c j : Usize)
    (row : Array U64 3#usize) (updated : U64)
    (hcomp : component.val < 3) (hchannel : channel.val < 3)
    (hc : c.val < 3) (hj : j.val < 3)
    (hrow : row = at3 a component hcomp) :
    at3 (at3 (a.set component (row.set channel updated)) c hc) j hj =
      if c.val = component.val then
        if j.val = channel.val then updated else at3 (at3 a component hcomp) j hj
      else at3 (at3 a c hc) j hj := by
  have houterSet := at3_set a component c (row.set channel updated) hcomp hc
  rw [houterSet]
  by_cases houter : c.val = component.val
  · simp only [if_pos houter]
    have hinnerSet := at3_set row channel j updated hchannel hj
    rw [hinnerSet]
    by_cases hinner : j.val = channel.val
    · simp only [if_pos hinner]
    · simp only [if_neg hinner, hrow]
  · simp only [if_neg houter]

#print axioms cell_nested_set
end AspisR1PoseidonPreparedChannelNestedSet
