import RPt_JFo_PrefixRead
import NDO_JFo_SuffixRead
set_option autoImplicit false
namespace AspisR1.JFo_RangeEnds
open Aeneas Aeneas.Std Result WP

theorem trailing_eq (bytes : Slice U8) (start stop : Usize)
    (bound : start.val≤stop.val) (size : stop.val=bytes.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=start} =
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop} := by
  have left : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=start} ⦃ out => out.val=bytes.val.drop start.val ⦄ := by
    unfold core.slice.index.Slice.index
    step* <;> simp_all [List.slice]
  have right : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop} ⦃ out => out.val=bytes.val.drop start.val ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    simp_all [List.slice,List.take_of_length_le,List.length_drop]
  obtain ⟨l,hl,vl⟩ := WP.spec_imp_exists left
  obtain ⟨r,hr,vr⟩ := WP.spec_imp_exists right
  have same : l=r := Subtype.ext (vl.trans vr.symm)
  rw [hl,hr,same]

theorem suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
    JFx_NativeBytes.checkpoint {start:=1736#usize}=ok (JFq_Range.segment 1736 32 (by decide)) := by
  rw [trailing_eq JFx_NativeBytes.checkpoint 1736#usize 1768#usize (by decide)
    JFx_NativeBytes.checkpointBytes_length.symm]
  have read := JFq_Range.read 1736#usize 1768#usize (by decide) (by decide)
  simp only [show (1736#usize).val=1736 from rfl,show (1768#usize).val=1768 from rfl,Nat.reduceSub] at read
  exact read

theorem leading : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JFx_NativeBytes.checkpoint {«end»:=1736#usize}=ok (JFq_Range.segment 0 1736 (by decide)) := by
  apply JFo_PrefixRead.source
  · change 1736≤JFx_NativeBytes.checkpoint.val.length
    have size : JFx_NativeBytes.checkpoint.val.length=1768 := JFx_NativeBytes.checkpointBytes_length
    omega
  · simp only [JFq_Range.segment,List.drop_zero,show (1736#usize).val=1736 from rfl]

#print axioms trailing_eq
#print axioms suffix
#print axioms leading
end AspisR1.JFo_RangeEnds
