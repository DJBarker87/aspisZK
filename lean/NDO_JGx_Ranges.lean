import NDO_JFw_Range
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
  by
    have h := source 7495#usize 7527#usize (by decide) (by decide)
    simpa only [show (7495#usize).val=7495 from rfl,show (7527#usize).val=7527 from rfl,Nat.reduceSub] using h
#print axioms inactive

theorem round0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7527#usize,«end»:=7751#usize}=ok (JFw_Frames.window 7527 224) :=
  by
    have h := source 7527#usize 7751#usize (by decide) (by decide)
    simpa only [show (7527#usize).val=7527 from rfl,show (7751#usize).val=7751 from rfl,Nat.reduceSub] using h
#print axioms round0

theorem round1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7783#usize,«end»:=8007#usize}=ok (JFw_Frames.window 7783 224) :=
  by
    have h := source 7783#usize 8007#usize (by decide) (by decide)
    simpa only [show (7783#usize).val=7783 from rfl,show (8007#usize).val=8007 from rfl,Nat.reduceSub] using h
#print axioms round1

theorem final_message : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=8007#usize,«end»:=10055#usize}=ok (JFw_Frames.window 8007 2048) :=
  by
    have h := source 8007#usize 10055#usize (by decide) (by decide)
    simpa only [show (8007#usize).val=8007 from rfl,show (10055#usize).val=10055 from rfl,Nat.reduceSub] using h
#print axioms final_message
end AspisR1.JGx_Ranges
end
