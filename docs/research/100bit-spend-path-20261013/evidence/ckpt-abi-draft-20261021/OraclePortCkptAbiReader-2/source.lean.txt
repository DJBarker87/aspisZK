import R22Stage2ReaderTotal

/-! Exact bytes for the emitted Reader.raw body with explicit unwrap-on-Ok.
The concrete debug-bearing unwrap identification remains outside this theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbiReader
open AspisR1Stage2

/-- Total checked range read, including its exact bytes and unchanged backing
slice. This strengthens the existing cursor-only contract without assuming
that successful reads happen to decode the desired model value. -/
theorem raw_total_exact (r : verifier.Reader) (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ b, unwrap (.Ok b) = ok b)
    (bounds : r.at.val + N.val ≤ r.bytes.val.length) :
    ∃ b out, verifier.Reader.rawWithUnwrap N unwrap r = ok (b,out) ∧
      b.val = (r.bytes.val.drop r.at.val).take N.val ∧
      out.at.val = r.at.val + N.val ∧ out.bytes = r.bytes := by
  have maxLen : r.bytes.val.length ≤ Usize.max := r.bytes.property
  obtain ⟨endPos,he,hv⟩ := AspisR1.R22Stage2ControlBounds.add_total r.at N (by omega)
  let range : core.ops.range.Range Usize := ⟨r.at,endPos⟩
  obtain ⟨s,hs,hcontents,hlen⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec range r.bytes
      (by change r.at.val ≤ endPos.val; omega)
      (by change endPos.val ≤ r.bytes.val.length; omega))
  have hsize : s.length = N.val := by
    change s.val.length = N.val
    change s.val.length = endPos.val-r.at.val at hlen
    omega
  unfold verifier.Reader.rawWithUnwrap
  rw [he]
  simp only [bind_tc_ok]
  rw [Slice.index_SliceIndexRangeUsizeSliceInst]
  change ∃ b out, (do
    let s1 ← core.slice.index.SliceIndexRangeUsizeSlice.index range r.bytes
    let z ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s1
    let b ← unwrap z
    ok (b, { r with «at» := endPos })) = ok (b,out) ∧
      b.val = (r.bytes.val.drop r.at.val).take N.val ∧
      out.at.val = r.at.val + N.val ∧ out.bytes = r.bytes
  rw [hs]
  simp only [bind_tc_ok,core.array.TryFromArrayCopySlice.try_from,hsize,↓reduceDIte]
  rw [unwrap_ok]
  refine ⟨_,_,rfl,?_,hv,rfl⟩
  change s.val = (r.bytes.val.drop r.at.val).take N.val
  change s.val = r.bytes.val.extract r.at.val endPos.val at hcontents
  rw [hcontents,List.extract_eq_drop_take]
  congr 1
  omega

#print axioms raw_total_exact
end AspisR1.OraclePortCkptAbiReader
