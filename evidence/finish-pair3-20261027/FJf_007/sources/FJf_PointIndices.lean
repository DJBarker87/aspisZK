import FJf_ArraySlots
import FJc_ReadSlot
set_option autoImplicit false
namespace AspisR1.FJf_PointIndices
open Aeneas Aeneas.Std Result

def tau (d : Nat) : Nat := ([3,4,2,0,1] : List Nat)[d]?.getD 0

theorem tau_read (d t : Usize) (run : Array.index_usize FIn_WeightsExtract.TAU d=ok t) :
    d.val<5 ∧ t.val≤4 ∧ t.val=tau d.val := by
  have hs := FJc_ReadSlot.slot _ _ _ run
  have hm := List.mem_of_getElem? hs
  change t∈([3#usize,4#usize,2#usize,0#usize,1#usize] : List Usize) at hm
  have hd := (List.getElem_of_getElem? hs).choose
  have hb : t.val≤4 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨hd,hb,?_⟩
  have hv := congrArg (Option.map UScalar.val) hs
  change Option.map UScalar.val
    (([3#usize,4#usize,2#usize,0#usize,1#usize] : List Usize)[d.val]?)=some t.val at hv
  have hmap : ([3#usize,4#usize,2#usize,0#usize,1#usize] : List Usize).map UScalar.val=
      [3,4,2,0,1] := rfl
  rw [←List.getElem?_map,hmap] at hv
  simp only [tau,hv,Option.getD_some]

#print axioms tau_read
end AspisR1.FJf_PointIndices
