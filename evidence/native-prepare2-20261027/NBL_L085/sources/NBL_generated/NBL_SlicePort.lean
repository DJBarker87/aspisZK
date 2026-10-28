import PoolS2_Ranges
set_option autoImplicit false
namespace AspisR1.NBL_SlicePort
open Aeneas Aeneas.Std Result

def segment (bs : Slice U8) (lo hi : Usize) : Slice U8 :=
  ⟨(bs.val.drop lo.val).take (hi.val-lo.val),by
    exact Nat.le_trans (List.length_take_le' _ _) (Nat.le_trans (by simp) bs.property)⟩

theorem source (bs : Slice U8) (lo hi : Usize)
    (ordered : lo.val≤hi.val) (within : hi.val≤bs.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bs {start:=lo,«end»:=hi}=ok (segment bs lo hi) := by
  obtain ⟨out,call⟩ := PoolS2_Ranges.selected_exists bs lo hi ordered within
  have bytes := (PoolS2_Ranges.selected_exact bs out lo hi ordered within call).1
  have same : out=segment bs lo hi := Subtype.ext bytes
  simpa only [same] using call

theorem length (bs : Slice U8) (lo hi : Usize)
    (ordered : lo.val≤hi.val) (within : hi.val≤bs.val.length) :
    (segment bs lo hi).val.length=hi.val-lo.val :=
  (PoolS2_Ranges.selected_exact bs _ lo hi ordered within (source bs lo hi ordered within)).2

theorem empty (bs : Slice U8) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bs {«end»:=0#usize}=ok (⟨[],by simp⟩ : Slice U8) := by
  obtain ⟨out,call,bytes,len⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      ({«end»:=0#usize} : core.ops.range.RangeTo Usize) bs (by simp))
  have same : out=(⟨[],by simp⟩ : Slice U8) := by
    apply Subtype.ext
    simpa only [List.slice,List.drop_zero,Nat.sub_zero,List.take_zero] using bytes
  simpa only [same] using call

#print axioms source
#print axioms length
#print axioms empty
end AspisR1.NBL_SlicePort
