import PSem_Slices
import FJl_ScalarWindow
set_option autoImplicit false
namespace AspisR1.FJl_SliceCopy
open Aeneas Aeneas.Std Result
/-- Successful fixed-size copy retains all the SAME slice bytes. -/
theorem bytes {n : Usize} (s : Slice U8) (a : Array U8 n)
    (run : core.array.TryFromArrayCopySlice.try_from n core.marker.CopyU8 s=ok (.Ok a)) : a.val=s.val := by
  unfold core.array.TryFromArrayCopySlice.try_from at run
  split at run
  · cases core.result.Result.Ok.inj (Result.ok.inj run)
    rfl
  · cases run
/-- The actual scalar byte array is exactly the selected four-byte window. -/
theorem scalar (q : Array U8 608#usize) (slot term : Usize) (v : U32)
    (run : JFr_TX2_ScalarRead.read q slot term=ok v) :
    ∃ a : Array U8 4#usize,
      a.val=(q.val.drop (slot.val*120+term.val*4)).take 4 ∧
      FIp_DotDecode.field.M31.from_le_bytes a=ok (some v) := by
  obtain ⟨start,stop,s,a,hs,he,hr,hc,hd,hv⟩ := FJl_ScalarWindow.reached q slot term v run
  have range := PSem_Slices.range_bytes (Array.to_slice q) s start stop hr
  have width : stop.val-start.val=4 := by omega
  refine ⟨a,?_,hd⟩
  rw [bytes s a hc,range,width,hs]
  rfl
#print axioms bytes
#print axioms scalar
end AspisR1.FJl_SliceCopy
