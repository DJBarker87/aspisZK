import NDO_JGe_View
set_option autoImplicit false
namespace AspisR1.JGe_CurrentView
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation

def Fields (view : verifier.View) : Prop :=
  view.folded_root=some JGe_View.folded ∧
  view.round0=JFw_Frames.window 7527 224 ∧
  view.round1=JFw_Frames.window 7783 224 ∧
  view.final_message=JFw_Frames.window 8007 2048

theorem source (semantic y1 : Slice U8) : ∃ view,
    sourceView JFx_NativeBytes.proof semantic y1=ok (.Ok view) ∧ Fields view := by
  obtain ⟨view,call,variant,root,round0,round1,finalMessage,first⟩ := JGe_View.selected semantic y1
  refine ⟨selectedView view,?_,root,round0,round1,finalMessage⟩
  simp only [sourceView,call,bind_tc_ok]
#print axioms source
end AspisR1.JGe_CurrentView
