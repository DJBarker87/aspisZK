import LIBB_CommonReservation
set_option autoImplicit false
noncomputable section
namespace LIBB_RecordReservation
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Runtime representation clause at one reached occurrence, not an
own-input domain or a success premise. Unreached calls impose no clause. -/
def Bound (r : NP6_StdModel.Reservation) : (e : Event) → NLT_NativeWindows.Input e → Prop
 | .resume ..,input => NJC_FilledClause.reserved input=NJC_FilledClause.reserved r
 | .pending ..,input => NJC_FilledClause.reserved input=NJC_FilledClause.reserved r
 | .finish ..,input => NJC_FilledClause.reserved input.1=NJC_FilledClause.reserved r
 | _,_ => True

def frame (r : NP6_StdModel.Reservation) : (e : Event) → NLT_NativeWindows.Input e → NLT_Interpreted.Uninstalled
 | .resume ..,input => ⟨input,r,r,NLT_FrameFromCuts.unusedLocations⟩
 | .pending ..,input => ⟨r,input,r,NLT_FrameFromCuts.unusedLocations⟩
 | .finish ..,input => ⟨r,r,input.1,input.2⟩
 | _,_ => ⟨r,r,r,NLT_FrameFromCuts.unusedLocations⟩

theorem compatible (r : NP6_StdModel.Reservation) (e : Event) (input : NLT_NativeWindows.Input e) :
 NLT_NativeWindows.Compatible (frame r e input) e input := by
 cases e <;> first | exact True.intro | rfl | exact ⟨rfl,rfl⟩

theorem tags (r : NP6_StdModel.Reservation) (e : Event) (input : NLT_NativeWindows.Input e)
 (bound : Bound r e input) :
 NJC_FilledClause.reserved (frame r e input).resume=NJC_FilledClause.reserved r ∧
 NJC_FilledClause.reserved (frame r e input).pending=NJC_FilledClause.reserved r ∧
 NJC_FilledClause.reserved (frame r e input).finish=NJC_FilledClause.reserved r := by
 cases e <;> first
 | exact ⟨rfl,rfl,rfl⟩
 | exact ⟨bound,rfl,rfl⟩
 | exact ⟨rfl,bound,rfl⟩
 | exact ⟨rfl,rfl,bound⟩

/-- The closed same-occurrence step with tag-only reservation binding and
its actual ABI locations. Every child domain comes from Interpreted.step. -/
theorem step (r : NP6_StdModel.Reservation) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (e : Event)
 (entered : e∈(run r r (NLP_NativeMerkle.action H) (NLB_Parent.finish r)
  d pub proof ck hash none).events)
 (recorded : Event) (input : NLT_NativeWindows.Input recorded)
 (question : NLT_NativeWindows.question recorded=NLT_NativeWindows.question e)
 (bound : Bound r recorded input) :
 NLT_NativeWindows.window H d hash recorded input=e := by
 let f:=frame r recorded input
 have t:=tags r recorded input bound
 have same:=LIBB_CommonReservation.observed f.resume r f.pending r f.finish r
  (NLP_NativeMerkle.action H) t.1 t.2.1 t.2.2
 have reached : e∈(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
  rw [same]
  exact entered
 exact NLT_QuestionStep.source f H d pub proof ck hash len e reached recorded input question
  (compatible r recorded input)
#print axioms compatible
#print axioms tags
#print axioms step
end LIBB_RecordReservation
end
