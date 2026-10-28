import NDO_JFv_ZeroDecode
import RPz7_PAln_Offsets
import NDO_JFw_Range
set_option autoImplicit false
namespace AspisR1.JFv_View
open Aeneas Aeneas.Std Result
open AspisR1SelectedWideViewV1
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem inactive : ∃ value, viewFromBytes (JFw_Frames.window 7495 32) = ok (some value) := by
  have zero : (JFw_Frames.window 7495 32).val = List.replicate 32 0#u8 := by
    have selected := JFz_Scan01.b00_selected
    have zeros : JFz_Scan01.b00 = List.replicate 32 0#u8 := rfl
    simpa only [JFw_Frames.window] using selected.trans zeros
  obtain ⟨value,parsed⟩ := JFv_ZeroDecode.parser (JFw_Frames.window 7495 32) zero
  refine ⟨parserCarrier value,?_⟩
  simp only [viewFromBytes,parsed,bind_tc_ok,Option.map_some]

theorem array (input : Slice U8) (length : input.length=32) :
    ∃ root : Array U8 32#usize,
      core.array.TryFromSharedArraySlice.try_from 32#usize input = ok (.Ok root) := by
  let root : Array U8 32#usize := ⟨input.val,length⟩
  refine ⟨root,?_⟩
  have size : Slice.len input=32#usize := by
    apply UScalar.eq_of_val_eq
    exact length
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos size]

def emptySlice : Slice U8 := ⟨[],by simp⟩

theorem empty : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JFx_NativeBytes.proof {«end»:=0#usize} = ok emptySlice := by
  simp only [Slice.index_SliceIndexRangeToUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
  rw [if_pos (by scalar_tac : (0#usize).val ≤ JFx_NativeBytes.proof.length)]
  rfl

theorem selected (semantic y1 : Slice U8) : ∃ view,
    verifier.candidate.wide_view JFx_NativeBytes.proof semantic y1=ok (.Ok view) := by
  obtain ⟨inactive,parsed⟩ := inactive
  obtain ⟨root,rootRead⟩ := array (JFw_Frames.window 7751 32)
    (JFw_Frames.window_length 7751 32 (by decide))
  obtain ⟨o0,o1,o2,o3,o4,o5⟩ := PAln_Offsets.offsets
  have r0 := JFw_Range.read 7495#usize 7527#usize (by decide) (by decide)
  have r1 := JFw_Range.read 7527#usize 7751#usize (by decide) (by decide)
  have r2 := JFw_Range.read 7751#usize 7783#usize (by decide) (by decide)
  have r3 := JFw_Range.read 7783#usize 8007#usize (by decide) (by decide)
  have r4 := JFw_Range.read 8007#usize 10055#usize (by decide) (by decide)
  simp only [show (7495#usize).val=7495 from rfl,show (7527#usize).val=7527 from rfl,
    show (7751#usize).val=7751 from rfl,show (7783#usize).val=7783 from rfl,
    show (8007#usize).val=8007 from rfl,show (10055#usize).val=10055 from rfl,Nat.reduceSub] at r0 r1 r2 r3 r4
  unfold verifier.candidate.wide_view
  rw [o0,o1]
  simp only [bind_tc_ok]
  rw [r0,bind_tc_ok,parsed,bind_tc_ok]
  simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [o2,bind_tc_ok,r1,bind_tc_ok,o3,bind_tc_ok,r2,bind_tc_ok,rootRead,bind_tc_ok]
  simp only [core.result.Result.unwrap,bind_tc_ok]
  rw [o4,bind_tc_ok,r3,bind_tc_ok,o5,bind_tc_ok,r4,bind_tc_ok,empty,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem current (semantic y1 : Slice U8) : ∃ view,
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof semantic y1=ok (.Ok view) := by
  obtain ⟨view,accepted⟩ := selected semantic y1
  exact ⟨AspisR1CurrentCaller.InstalledPreparation.selectedView view,by
    simp only [AspisR1CurrentCaller.InstalledPreparation.sourceView,accepted,bind_tc_ok]⟩

#print axioms inactive
#print axioms array
#print axioms empty
#print axioms selected
#print axioms current
end AspisR1.JFv_View
