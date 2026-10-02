import AspisV8R19.R306BatchReverseStepExecution

/-! Error order for the unchanged generated reverse bodies, evaluated against
the pinned executable Aeneas library. No caller invariant or whole Rust
standard-library correspondence is assumed or concluded. -/
set_option autoImplicit false
namespace AspisV8R19.R313BatchReverseIndexErrors
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open R306BatchReverseStepExecution
open AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm
noncomputable section

theorem prefix_index_error (xs : Slice U32) (px ox : alloc.vec.Vec U32)
    (iter : ReverseRange) (ix : U32)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hp : px.val[(Usize.wrapping_sub (Usize.wrapping_sub iter.iter.end 1#usize)
      1#usize).val]? = none) :
    batch_loop2.body xs px iter ix ox = .fail .arrayOutOfBounds := by
  simp only [batch_loop2.body, reverse_next_step iter hstep, bind_tc_ok,
    lift, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, hp, bind_tc_fail]

theorem output_index_error (xs : Slice U32) (px ox : alloc.vec.Vec U32)
    (iter : ReverseRange) (x p : M31Exact)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hp : px.val[(Usize.wrapping_sub (Usize.wrapping_sub iter.iter.end 1#usize)
      1#usize).val]? = some (encodeBase p))
    (ho : ox.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]? = none) :
    batch_loop2.body xs px iter (encodeBase x) ox = .fail .arrayOutOfBounds := by
  simp only [batch_loop2.body, reverse_next_step iter hstep, bind_tc_ok,
    lift, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, hp, R250PrivateBaseExecution.mul_encoded,
    alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
    alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq, ho, bind_tc_fail]

theorem input_index_error (xs : Slice U32) (px ox : alloc.vec.Vec U32)
    (iter : ReverseRange) (x p : M31Exact)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hp : px.val[(Usize.wrapping_sub (Usize.wrapping_sub iter.iter.end 1#usize)
      1#usize).val]? = some (encodeBase p))
    (ho : (Usize.wrapping_sub iter.iter.end 1#usize).val < ox.length)
    (hv : xs.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]? = none) :
    batch_loop2.body xs px iter (encodeBase x) ox = .fail .arrayOutOfBounds := by
  obtain ⟨⟨old, back⟩, hb, _, _⟩ := spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec ox
      (Usize.wrapping_sub iter.iter.end 1#usize) ho)
  simp only [batch_loop2.body, reverse_next_step iter hstep, bind_tc_ok,
    lift, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    alloc.vec.Vec.getElem?_Nat_eq, hp, R250PrivateBaseExecution.mul_encoded,
    alloc.vec.Vec.index_mut_slice_index, hb, Slice.index_usize,
    Slice.getElem?_Usize_eq, hv, bind_tc_fail]

#print axioms prefix_index_error
#print axioms output_index_error
#print axioms input_index_error
end
end AspisV8R19.R313BatchReverseIndexErrors
