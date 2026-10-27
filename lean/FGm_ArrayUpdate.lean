import FGm_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_ArrayUpdate
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode value)

theorem set_value {N : Usize} (a : Array NE N) (i : Usize)
    (hi : i.val<a.val.length) (z : NE) (j : Nat) :
    value (Aeneas.Std.Array.set a i z) j=if i.val=j then decode z else value a j := by
  simp only [value,Aeneas.Std.Array.set,List.getElem?_set]
  split
  · rename_i h
    simp only [h,if_pos hi,Option.map_some,Option.getD_some]
  · rfl

theorem back_value {N : Usize} (a : Array NE N) (i : Usize)
    (old : NE) (back : NE → Array NE N)
    (run : Array.index_mut_usize a i=ok (old,back)) (z : NE) (j : Nat) :
    value (back z) j=if i.val=j then decode z else value a j := by
  unfold Array.index_mut_usize at run
  obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := congrArg Prod.snd (Result.ok.inj run)
  have backEq : back=Aeneas.Std.Array.set a i := same.symm
  rw [backEq]
  apply set_value
  unfold Array.index_usize at hx
  split at hx
  · cases hx
  · rename_i v hv
    change a.val[i.val]?=some v at hv
    exact (List.getElem_of_getElem? hv).choose

#print axioms set_value
#print axioms back_value
end AspisR1.FGm_ArrayUpdate
end
