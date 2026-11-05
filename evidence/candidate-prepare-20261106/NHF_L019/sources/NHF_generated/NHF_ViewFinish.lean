import NHF_ViewDecoder
import NGV_ByteWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_ViewFinish
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1 NHF_ViewCut NGV_ByteWindow

def root (proof : Slice U8) (size : 10055 ≤ proof.val.length) : Array U8 32#usize :=
 ⟨(select proof 7751 32).val,by
   have h:=select_length proof 7751 32 (by omega)
   simpa only [UScalar.ofNatCore_val_eq] using h⟩

def value (proof semantic y1 : Slice U8) (inactive : E) (size : 10055 ≤ proof.val.length) : verifier.View :=
 ⟨.S2,semantic,y1,inactive,select proof 7527 224,some (root proof size),
  select proof 7783 224,select proof 8007 2048,select proof 0 0⟩

theorem array_conversion (proof : Slice U8) (size : 10055 ≤ proof.val.length) :
 core.array.TryFromSharedArraySlice.try_from 32#usize (select proof 7751 32) =
 ok (.Ok (root proof size)) := by
 unfold core.array.TryFromSharedArraySlice.try_from
 have h : Slice.len (select proof 7751 32)=32#usize :=
   UScalar.eq_of_val_eq (select_length proof 7751 32 (by omega))
 rw [dif_pos h]
 rfl

theorem empty_read (proof : Slice U8) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   proof {«end»:=0#usize} = ok (select proof 0 0) := by
 simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
   core.slice.index.SliceIndexRangeToUsizeSlice.index]
 rw [if_pos (show (0#usize).val≤proof.length by change 0≤_;omega)]
 rfl

/-- Every borrowed returned field and array conversion on the original proof;
no decoding success or output-field equality is a premise. -/
theorem result (proof semantic y1 : Slice U8) (inactive : E)
 (size : 10055 ≤ proof.val.length) :
 finish proof semantic y1 inactive = ok (.Ok (value proof semantic y1 inactive size)) := by
 unfold finish range
 rw [read proof 7527#usize 7751#usize (by change 7527≤7751 ∧ 7751≤_;omega),bind_tc_ok]
 rw [read proof 7751#usize 7783#usize (by change 7751≤7783 ∧ 7783≤_;omega),bind_tc_ok]
 norm_num only [UScalar.ofNatCore_val_eq]
 rw [array_conversion proof size,bind_tc_ok]
 simp only [core.result.Result.unwrap,bind_tc_ok]
 rw [read proof 7783#usize 8007#usize (by change 7783≤8007 ∧ 8007≤_;omega),bind_tc_ok]
 rw [read proof 8007#usize 10055#usize (by change 8007≤10055 ∧ 10055≤_;omega),bind_tc_ok]
 rw [empty_read,bind_tc_ok]
 rfl
#print axioms array_conversion
#print axioms empty_read
#print axioms result
end AspisR1.NHF_ViewFinish
end
