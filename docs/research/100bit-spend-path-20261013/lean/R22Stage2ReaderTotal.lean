import R22Stage2LocalBodies
import R22Stage2ControlBounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2

/-- The emitted Reader.raw body with only its debug-bearing unwrap boundary
made explicit. The concrete emitted debug instance depends on the nonstandard
Formatter axiom, so its connection is deliberately not asserted here. -/
def verifier.Reader.rawWithUnwrap (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (self : verifier.Reader) : Result (Array U8 N × verifier.Reader) := do
  let i ← self.at + N
  let s ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) self.bytes
    { start := self.at, «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← unwrap r
  ok (b, { self with «at» := i })

/-- Total under an explicit unwrap-on-Ok contract and cursor/end bound.
This is a backend-parametric theorem, not concrete Reader.raw totality. -/
theorem r22_reader_raw_total (r : verifier.Reader) (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ b, unwrap (.Ok b) = ok b)
    (h : r.at.val+N.val ≤ r.bytes.val.length) :
    ∃ bytes out, verifier.Reader.rawWithUnwrap N unwrap r = ok (bytes,out) ∧
      out.at.val = r.at.val+N.val ∧ out.bytes = r.bytes := by
  have hm : r.bytes.val.length ≤ Usize.max := r.bytes.property
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
  have hconv : s.length = N.val := hsize
  unfold verifier.Reader.rawWithUnwrap
  rw [he]
  simp only [bind_tc_ok]
  rw [Slice.index_SliceIndexRangeUsizeSliceInst]
  change ∃ bytes out, (do
    let s1 ← core.slice.index.SliceIndexRangeUsizeSlice.index range r.bytes
    let z ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s1
    let b ← unwrap z
    ok (b, { r with «at» := endPos })) = ok (bytes,out) ∧
      out.at.val = r.at.val+N.val ∧ out.bytes = r.bytes
  rw [hs]
  simp only [bind_tc_ok,core.array.TryFromArrayCopySlice.try_from,hconv,↓reduceDIte]
  rw [unwrap_ok]
  exact ⟨_,_,rfl,hv,rfl⟩

#print axioms r22_reader_raw_total
end AspisR1Stage2
