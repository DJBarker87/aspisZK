import NLT_NativeWindows
set_option autoImplicit false
noncomputable section
namespace NLT_QuestionStep
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Different encoded reply seeds have no effect on a native cut. Every
native field comes from that cut's decoded arguments and local input record.
Compatibility will be derived from the ONE ordered invocation, not assumed
as an extra caller-domain clause. -/
theorem source (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (e : Event)
 (entered : e∈(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events)
 (recorded : Event) (input : NLT_NativeWindows.Input recorded)
 (same : NLT_NativeWindows.question recorded=NLT_NativeWindows.question e)
 (compatible : NLT_NativeWindows.Compatible f recorded input) :
 NLT_NativeWindows.window H d hash recorded input=e := by
 cases e <;> cases recorded <;> cases same
 all_goals
  have realized:=NLT_NativeWindows.interpreted H d hash f _ input compatible
  have installed:=NLT_Interpreted.step f H d pub proof ck hash len _ entered
   (NLT_NativeWindows.projectedInput _ input)
  exact realized.trans installed
set_option pp.proofs false
#print source
#print axioms source
end NLT_QuestionStep
