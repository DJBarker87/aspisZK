import RPz7_Tx1Q_Execution
set_option autoImplicit false
namespace AspisR1.FJp_RootBinding
open Aeneas Aeneas.Std Result
/-- Output provenance retained by the original accepted TX1 constructor. -/
def Holds (proof : Slice U8) (root : Array U8 32#usize) : Prop :=
  ∃ view,core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
    core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root)
end AspisR1.FJp_RootBinding
