import R22Stage2OpeningTotal

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4OpeningBytesFromCurrentV1

theorem opening_slice_exact (proof : Slice U8) (index : Usize)
    (hi : index.val < 22) (hlen : 28359 ≤ proof.val.length) :
    ∃ q, AspisR1Stage2.verifier.candidate.opening proof index = .ok q ∧
      q.val = proof.val.slice (10055 + index.val * 832)
        (10055 + index.val * 832 + 832) := by
  have hm : proof.val.length ≤ Usize.max := proof.property
  have hoff := AspisR1.R22Stage2ControlBounds.compact_opening index.val hi
  have hmulBound : index.val * 832 ≤ Usize.max := by omega
  obtain ⟨stride, hs, hsv⟩ :=
    AspisR1.R22Stage2ControlBounds.mul_total index 832#usize hmulBound
  change stride.val = index.val * 832 at hsv
  have haddBound : 10055 + stride.val ≤ Usize.max := by omega
  obtain ⟨startPos, hstart, hstartv⟩ :=
    AspisR1.R22Stage2ControlBounds.add_total 10055#usize stride haddBound
  change startPos.val = 10055 + stride.val at hstartv
  have hendBound : startPos.val + 832 ≤ Usize.max := by omega
  obtain ⟨endPos, hend, hendv⟩ :=
    AspisR1.R22Stage2ControlBounds.add_total startPos 832#usize hendBound
  change endPos.val = startPos.val + 832 at hendv
  obtain ⟨s, hslice, hcontents, _hlen⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨startPos, endPos⟩ proof
      (by change startPos.val ≤ endPos.val; omega)
      (by change endPos.val ≤ proof.val.length; omega))
  have hsource : AspisR1Stage2.verifier.candidate.opening proof index = .ok s := by
    simp only [AspisR1Stage2.verifier.candidate.opening,
      AspisR1Stage2.r22_compact_OPENING_total,
      AspisR1Stage2.r22_compact_OFF_OPENINGS_total,
      bind_tc_ok, hs, hstart, hend,
      Slice.index_SliceIndexRangeUsizeSliceInst]
    exact hslice
  have hstartEq : startPos.val = 10055 + index.val * 832 := by omega
  have hendEq : endPos.val = 10055 + index.val * 832 + 832 := by omega
  have hspan : endPos.val - startPos.val = 832 := by omega
  have hbytes : s.val = proof.val.slice
      (10055 + index.val * 832) (10055 + index.val * 832 + 832) := by
    change s.val = List.extract proof.val startPos.val endPos.val at hcontents
    rw [hstartEq, hendEq] at hcontents
    simpa [List.extract_eq_take_drop, List.slice, hspan] using hcontents
  exact ⟨s, hsource, hbytes⟩

#print axioms opening_slice_exact
end AspisR1S4OpeningBytesFromCurrentV1
