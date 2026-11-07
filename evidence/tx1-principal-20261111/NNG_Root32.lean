import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_Root32
open Aeneas Aeneas.Std Result NNG_verify_finish

def copy (s : Slice U8) : Result (Array U8 32#usize) := do
  let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s
  core.result.Result.unwrap core.fmt.DebugTryFromSliceError r

def value (s : Slice U8) (h : s.val.length = 32) : Array U8 32#usize := ⟨s.val,h⟩

/-- Exact standard success arm, byte-for-byte; no allocator or whole-buffer
normalization is involved in copying this fixed 32-byte value. -/
theorem returned (s : Slice U8) (h : s.val.length = 32) :
    copy s = .ok (value s h) := by
  unfold copy core.array.TryFromArrayCopySlice.try_from
  have len : s.length = (32#usize).val := h
  rw [dif_pos len]
  rfl
#print axioms returned

/-- The unwrap panic on every other length is retained, not excluded by the
standard interpretation. Parent geometry may prove this arm unreachable. -/
theorem rejected (s : Slice U8) (h : s.val.length ≠ 32) :
    copy s = .fail .panic := by
  unfold copy core.array.TryFromArrayCopySlice.try_from
  have len : s.length ≠ (32#usize).val := h
  rw [dif_neg len]
  rfl
#print axioms rejected
end AspisR1.NNG_Root32
