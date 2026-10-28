import R1Z.PV_RDB2_Pointer

/-! Complete checked-index interface for the deployed index-loop helper.
The native slice-index failure is represented by Aeneas's arrayOutOfBounds;
the loop guard proves that it is not reached, for every admitted iteration. -/
namespace R1Z.PV_RDB2_Index
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_Pointer

def index (values : Slice U32) (i : Usize) : Result U32 :=
  if h : i.val < values.val.length then ok values.val[i.val]
  else fail .arrayOutOfBounds

theorem index_complete (values : Slice U32) (i : Usize) :
    index values i = Slice.index_usize values i := by
  simp only [index,Slice.index_usize,Slice.getElem?_Usize_eq]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem h]
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]

theorem guarded (values : Slice U32) (i : Usize)
    (h : i.val < values.val.length) :
    index values i = ok values.val[i.val] := dif_pos h

theorem rejected (values : Slice U32) (i : Usize)
    (h : values.val.length ≤ i.val) :
    index values i = fail .arrayOutOfBounds := dif_neg (by omega)

/-- Read and word-copy semantics at a valid shared M31 location. The complete
returned storage is preserved; the copied word has no reference identity. -/
def readCopy (c : Cursor) : Result (U32 × Slice U32) :=
  if h : c.position < c.values.val.length then
    ok (c.values.val[c.position],c.values)
  else fail .undef

theorem read_copy_complete (c : Cursor) (i : Usize)
    (hi : i.val = c.position) (h : c.position < c.values.val.length) :
    readCopy c = (do let word ← Slice.index_usize c.values i; ok (word,c.values)) := by
  rw [← index_complete,guarded c.values i (by omega)]
  simp only [readCopy,h,↓reduceDIte,hi]
  rfl

theorem increment_bound (values : Slice U32) (i : Usize)
    (h : i.val < values.val.length) : i.val+1 ≤ Usize.max := by
  have := Slice.length_ineq values
  omega

#print axioms index_complete
#print axioms guarded
#print axioms rejected
#print axioms read_copy_complete
#print axioms increment_bound
end R1Z.PV_RDB2_Index
