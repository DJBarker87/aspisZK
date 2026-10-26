import F3K_QueryWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryIndex
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge

theorem drop_index {α : Type} {n : Usize} (a : Array α n) (i : Usize) (v : α)
    (h : Array.index_usize a i=ok v) : a.val.drop i.val=v::a.val.drop (i.val+1) := by
  unfold Array.index_usize at h
  split at h
  · cases h
  · rename_i x hx
    cases Result.ok.inj h
    change a.val[i.val]?=some x at hx
    exact List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hx).1

theorem drop_decoded (a : Array (Array U8 32#usize) 8#usize) (i : Usize)
    (v : Array U8 32#usize) (h : Array.index_usize a i=ok v) :
    (a.val.map decodeState).drop i.val=decodeState v::(a.val.map decodeState).drop (i.val+1) := by
  rw [← List.map_drop,drop_index a i v h,List.map_cons,List.map_drop]

#print axioms drop_index
#print axioms drop_decoded
end AspisR1.F3K_QueryIndex
end
