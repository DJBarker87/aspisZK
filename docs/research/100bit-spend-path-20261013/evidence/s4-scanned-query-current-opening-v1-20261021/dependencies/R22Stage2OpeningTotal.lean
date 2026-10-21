import R22Stage2LeafTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2

/-- Complete emitted opening accessor: checked multiplication/addition and
range indexing all succeed from the opening index and proof length. -/
theorem r22_opening_total (proof : Slice U8) (index : Usize)
    (hi : index.val < 22) (hlen : 28359 ≤ proof.val.length) :
    ∃ out, verifier.candidate.opening proof index = ok out ∧ out.length = 832 := by
  have hm : proof.val.length ≤ Usize.max := proof.property
  have hoff := AspisR1.R22Stage2ControlBounds.compact_opening index.val hi
  obtain ⟨stride,hs,hsv⟩ := AspisR1.R22Stage2ControlBounds.mul_total index 832#usize
    (by change index.val*832 ≤ Usize.max; omega)
  change stride.val = index.val*832 at hsv
  obtain ⟨startPos,hstart,hstartv⟩ := AspisR1.R22Stage2ControlBounds.add_total 10055#usize stride
    (by change 10055+stride.val ≤ Usize.max; omega)
  change startPos.val = 10055+stride.val at hstartv
  obtain ⟨endPos,hend,hendv⟩ := AspisR1.R22Stage2ControlBounds.add_total startPos 832#usize
    (by change startPos.val+832 ≤ Usize.max; omega)
  change endPos.val = startPos.val+832 at hendv
  obtain ⟨out,hout,_,houtlen⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨startPos,endPos⟩ proof
      (by change startPos.val ≤ endPos.val; omega)
      (by change endPos.val ≤ proof.val.length; omega))
  refine ⟨out,?_,?_⟩
  · simp only [verifier.candidate.opening,r22_compact_OPENING_total,
      r22_compact_OFF_OPENINGS_total,bind_tc_ok,hs,hstart,hend,
      Slice.index_SliceIndexRangeUsizeSliceInst]
    exact hout
  · change out.length = endPos.val-startPos.val at houtlen
    omega

#print axioms r22_opening_total
end AspisR1Stage2
