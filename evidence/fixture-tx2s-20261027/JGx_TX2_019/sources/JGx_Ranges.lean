import JFw_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Ranges
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFw_Frames.window

theorem source (start stop : Usize) (ordered : start.val≤stop.val) (bound : stop.val≤57607) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=start,«end»:=stop}=
        ok (JFw_Frames.window start.val (stop.val-start.val)) :=
  JFw_Range.read start stop ordered bound
#print axioms source

theorem inactive : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7495#usize,«end»:=7527#usize}=ok (JFw_Frames.window 7495 32) :=
  source 7495#usize 7527#usize (by decide) (by decide)
#print axioms inactive

theorem round0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7527#usize,«end»:=7751#usize}=ok (JFw_Frames.window 7527 224) :=
  source 7527#usize 7751#usize (by decide) (by decide)
#print axioms round0

theorem round1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7783#usize,«end»:=8007#usize}=ok (JFw_Frames.window 7783 224) :=
  source 7783#usize 8007#usize (by decide) (by decide)
#print axioms round1

theorem final_message : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=8007#usize,«end»:=10055#usize}=ok (JFw_Frames.window 8007 2048) :=
  source 8007#usize 10055#usize (by decide) (by decide)
#print axioms final_message
end AspisR1.JGx_Ranges
end
