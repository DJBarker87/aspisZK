import R1Z.PV_RDB2F_Iterator
import R1Z.PV_RDB2D_SHAModel
namespace R1Z.PV_RDB2F_ArrayHandles
open Aeneas Aeneas.Std Result PV_RDB2F_Iterator
set_option autoImplicit false

theorem restore_total (q : Words) (i : Usize) (x : U32) (h : i.val<8) :
    restore q ⟨i⟩ x=ok (q.set i x) := PV_CBL_ArrayStep.write q i x h

theorem retained_length (q : Words) (i : Usize) (x : U32) :
    (q.set i x).val.length=8 := (q.set i x).property

theorem readback (q : Words) (i : Usize) (x : U32) (h : i.val<8) :
    (q.set i x).val[i.val]?=some x := by
  simp [Array.set,List.getElem?_set,h,q.property]

theorem frame (q : Words) (i j : Usize) (x : U32) (ne : j.val≠i.val) :
    (q.set i x).val[j.val]?=q.val[j.val]? := by
  simp [Array.set,List.getElem?_set,ne,Ne.symm ne]

theorem restore_then_read (q : Words) (i : Usize) (x : U32) (h : i.val<8) :
    (do let current ← restore q ⟨i⟩ x; Array.index_usize current i)=ok x := by
  rw [restore_total q i x h]
  simp only [bind_tc_ok,Array.index_usize,Array.getElem?_Usize_eq,readback q i x h]

#print axioms restore_total
#print axioms retained_length
#print axioms readback
#print axioms frame
#print axioms restore_then_read
end R1Z.PV_RDB2F_ArrayHandles
