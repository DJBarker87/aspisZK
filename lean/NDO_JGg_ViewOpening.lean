import NDO_JGe_View
import NDO_JGg_InactiveBytes
import NDO_JGg_Opening27
import NDO_JGg_Opening29
import NDO_JGg_Opening30
import NDO_JGg_Opening31
set_option autoImplicit false
namespace AspisR1.JGg_ViewOpening
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation OriginalSerializerInstallation
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem windows (off n m : Nat) :
    (JFw_Frames.window off n).val ++ (JFw_Frames.window (off+n) m).val=
      (JFw_Frames.window off (n+m)).val := by
  simp only [JFw_Frames.window,List.take_add,List.drop_drop,Nat.add_comm]
#print axioms windows

theorem source (semantic : Slice U8) : ∃ view,
    sourceView JFx_NativeBytes.proof semantic JGe_Payload27.value=ok (.Ok view) ∧
    view.variant=.S2 ∧ view.y1=JGg_Opening27.payload ∧
    view.round0=JGg_Opening29.payload ∧ view.folded_root=some JGe_View.folded ∧
    JGe_View.folded.val ++ view.round1.val=JGg_Opening30.payload.val ∧
    view.final_message=JGg_Opening31.payload ∧
    sourceBytes (retainedView view).inactive=ok (Array.repeat 32#usize 0#u8) := by
  obtain ⟨view,call,variant,root,round0,round1,finalMessage,y1⟩ := JGe_View.selected semantic JGe_Payload27.value
  have current : sourceView JFx_NativeBytes.proof semantic JGe_Payload27.value=ok (.Ok (selectedView view)) := by
    simp only [sourceView,call,bind_tc_ok]
  have currentVariant : (selectedView view).variant=.S2 := by
    simp only [selectedView,variant]
  refine ⟨selectedView view,current,currentVariant,y1,round0,root,?_,finalMessage,JGg_InactiveBytes.source _ _ _ current⟩
  change JGe_View.folded.val ++ view.round1.val=JGg_Opening30.payload.val
  rw [round1]
  exact windows 7751 32 224
#print axioms source
end AspisR1.JGg_ViewOpening
