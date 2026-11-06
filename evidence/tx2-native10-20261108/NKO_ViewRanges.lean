import NKO_Offsets
import NJU_ViewWindows
set_option autoImplicit false
namespace NKO_ViewRanges
open Aeneas Aeneas.Std Result AspisR1
/-- Normalize the small layout arithmetic symbolically before applying the
range lemmas, avoiding recursive reduction of large unary subtractions. -/
theorem diff0 : (7751#usize).val-(7527#usize).val=224 := by
 change 7751-7527=224
 omega
theorem diff1 : (8007#usize).val-(7783#usize).val=224 := by
 change 8007-7783=224
 omega
theorem diffFinal : (10055#usize).val-(8007#usize).val=2048 := by
 change 10055-8007=2048
 omega

theorem val0 : (7527#usize).val=7527 := by scalar_tac
theorem val1 : (7783#usize).val=7783 := by scalar_tac
theorem valFinal : (8007#usize).val=8007 := by scalar_tac

theorem round0 (proof selected : Slice U8)
 (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7527#usize,«end»:=7751#usize}=ok selected) :
 selected.val=(proof.val.drop 7527).take 224 := by
 have value := PSem_Slices.range_bytes proof selected 7527#usize 7751#usize call
 rw [diff0,val0] at value
 exact value

theorem round1 (proof selected : Slice U8)
 (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7783#usize,«end»:=8007#usize}=ok selected) :
 selected.val=(proof.val.drop 7783).take 224 := by
 have value := PSem_Slices.range_bytes proof selected 7783#usize 8007#usize call
 rw [diff1,val1] at value
 exact value

theorem final_message (proof selected : Slice U8)
 (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=8007#usize,«end»:=10055#usize}=ok selected) :
 selected.val=(proof.val.drop 8007).take 2048 ∧ selected.val.length=2048 := by
 have value := PSem_Slices.range_bytes proof selected 8007#usize 10055#usize call
 have size := PSem_Slices.range_length proof selected 8007#usize 10055#usize call
 rw [diffFinal,valFinal] at value
 rw [diffFinal] at size
 exact ⟨value,size⟩
#print axioms val0
#print axioms val1
#print axioms valFinal
#print axioms diff0
#print axioms diff1
#print axioms diffFinal
#print axioms round0
#print axioms round1
#print axioms final_message
end NKO_ViewRanges
