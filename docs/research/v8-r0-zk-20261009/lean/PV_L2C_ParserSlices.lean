import PV_L2C_CanonicalParser
set_option autoImplicit false
namespace PV_L2C_ParserSlices
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71
#print core.slice.index.SliceIndexRangeUsizeSlice.index

def slice {n : Usize} (a : Array U8 n) : Slice U8 :=
  ⟨a.val,by have := a.property; scalar_tac⟩

theorem copy_array {n : Usize} (a : Array U8 n) :
    core.array.TryFromArrayCopySlice.try_from n core.marker.CopyU8 (slice a)=ok (.Ok a) := by
  simp [core.array.TryFromArrayCopySlice.try_from,slice,a.property]
#print axioms copy_array
end PV_L2C_ParserSlices
