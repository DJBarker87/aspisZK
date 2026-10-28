import NDO_JFv_View
import NDO_JGe_Roots
set_option autoImplicit false
namespace AspisR1.JGe_View
open Aeneas Aeneas.Std Result
open AspisR1SelectedWideViewV1
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

def folded : Array U8 32#usize :=
  ⟨(JFw_Frames.window 7751 32).val,JFw_Frames.window_length 7751 32 (by decide)⟩

theorem selected (semantic y1 : Slice U8) : ∃ view,
    verifier.candidate.wide_view JFx_NativeBytes.proof semantic y1=ok (.Ok view) ∧
    view.variant=.S2 ∧ view.folded_root=some folded ∧
    view.round0=JFw_Frames.window 7527 224 ∧
    view.round1=JFw_Frames.window 7783 224 ∧
    view.final_message=JFw_Frames.window 8007 2048 ∧ view.y1=y1 := by
  obtain ⟨inactive,parsed⟩ := JFv_View.inactive
  have rootRead : core.array.TryFromSharedArraySlice.try_from 32#usize
      (JFw_Frames.window 7751 32)=ok (.Ok folded) := by
    have size : Slice.len (JFw_Frames.window 7751 32)=32#usize := by
      apply UScalar.eq_of_val_eq
      exact JFw_Frames.window_length 7751 32 (by decide)
    unfold core.array.TryFromSharedArraySlice.try_from
    rw [dif_pos size]
    rfl
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
  rw [o4,bind_tc_ok,r3,bind_tc_ok,o5,bind_tc_ok,r4,bind_tc_ok,JFv_View.empty,bind_tc_ok]
  exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms selected
end AspisR1.JGe_View
