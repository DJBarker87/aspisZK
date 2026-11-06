import NLT_RecordFrames
import NLT_NativeFacts
set_option autoImplicit false
noncomputable section
namespace NLT_QueryInstalled
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
def argsOf : Event → Option NKE_QueryInput.Args
 | .query pr p a g geo pending _ => some ⟨pr,p,a,g,geo,pending⟩
 | _ => none
/-- Logical input/owned-return projection of the reviewed C07 native family.
Native pointer/capacity/live-region observations stay in the pinned P6 cuts;
no address equality is used as a payload proof here. -/
def Law : (e : Event) → NLT_NativeWindows.Input e → Prop
 | .query pr p a g geo pending _,input =>
   let before : NKE_QueryInput.Args:=⟨pr,p,a,g,geo,pending⟩
   NLB_Parent.queryArgs before input.observation=before ∧
   NKO_QueryReturnG.G (NKE_QueryReturn.observed
    (NKE_QueryInput.child (NLB_Parent.queryArgs before input.observation)))=
    NJJ_Common.query pr p a g none geo pending 22#usize ∧
   ∀ reply,NJR_Cuts.queryReturn reply (NKE_QueryReturn.G reply)
 | _,_ => True
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (r : Occurrence H d hash) (atRecord : r∈records) : Law r.entered r.input := by
 have arguments:=NLT_RecordFrames.parent H d pub proof ck hash len result records native r atRecord
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case query pr p a g geo pending reply =>
  have same:=congrArg argsOf arguments
  have frame : NLB_Parent.queryArgs (⟨pr,p,a,g,geo,pending⟩ : NKE_QueryInput.Args) input.observation=
   (⟨pr,p,a,g,geo,pending⟩ : NKE_QueryInput.Args) := Option.some.inj same
  refine ⟨frame,?_,fun reply=>NKE_QueryReturn.cut reply⟩
  rw [frame]
  exact NKO_QueryReturnG.retained_return _
set_option pp.proofs false
#print installed
#print axioms installed
end NLT_QueryInstalled
