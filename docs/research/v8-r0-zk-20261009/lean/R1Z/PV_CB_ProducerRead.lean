import R1Z.PV_CB_ProducerCell
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerRead
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerCell

theorem slice_mem {A : Type} (values : Slice A) (index : Usize) (value : A)
    (read : Slice.index_usize values index = ok value) : value ∈ values.val := by
  unfold Slice.index_usize at read
  rw [Slice.getElem?_Usize_eq] at read
  cases found : values.val[index.val]? with
  | none => rw [found] at read; cases read
  | some element =>
    rw [found] at read
    cases read
    exact List.mem_of_getElem? found

theorem vec_mem {A : Type} (values : alloc.vec.Vec A) (index : Usize) (value : A)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice A) values index = ok value) :
    value ∈ values.val := by
  rw [alloc.vec.Vec.index_slice_index] at read
  unfold alloc.vec.Vec.index_usize at read
  change (match values.val[index.val]? with | none => fail .arrayOutOfBounds | some x => ok x) = ok value at read
  cases found : values.val[index.val]? with
  | none => rw [found] at read; cases read
  | some element =>
    rw [found] at read
    cases read
    exact List.mem_of_getElem? found

theorem array_mem {A : Type} {N : Usize} (values : Array A N) (index : Usize) (value : A)
    (read : Array.index_usize values index = ok value) : value ∈ values.val := by
  unfold Array.index_usize at read
  rw [Array.getElem?_Usize_eq] at read
  cases found : values.val[index.val]? with
  | none => rw [found] at read; cases read
  | some element =>
    rw [found] at read
    cases read
    exact List.mem_of_getElem? found

#print axioms array_mem
/-- Plain input list invariant implies the extracted read invariant. -/
theorem reads (columns : Slice V)
    (valid : ∀ vector ∈ columns.val, ∀ word ∈ vector.val, Valid word) : Reads columns := by
  intro column vector hc row word hr
  exact valid vector (slice_mem columns column vector hc) word (vec_mem vector row word hr)
#print axioms slice_mem
#print axioms vec_mem
#print axioms reads
end R1Z.PV_CB_ProducerRead
