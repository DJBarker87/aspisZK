import NLT_Subcuts
set_option autoImplicit false
noncomputable section
namespace NLT_NativeWindows
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NLB_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Event := NJU_CommonObserved.Event
/-- Native per-call cut inputs. Allocator replies and finish ABI fields are
selected AT THEIR OWN occurrence, not passed as three global flags. Selection
alone does not assert that an allocation occurred: rejected child prefixes may
never reach their reserve site. The full child G retains that distinction. -/
def Input : Event → Type
 | .resume .. => NP6_StdModel.Reservation
 | .pending .. => NP6_StdModel.Reservation
 | .finish .. => NP6_StdModel.Reservation × NIW_AlignFinishComposed.Locations
 | .query pr p a g geo pending _ => NLT_ParentCuts.Query ⟨pr,p,a,g,geo,pending⟩
 | _ => PUnit
/-- Concrete local G, independent of a global allocator/ABI/window dictionary.
Only the encoded arguments are used; the encoded reply is never consumed. -/
def window (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (e : Event) (input : Input e) : Event :=
 match e with
 | .resume ck proof pub _ => .resume ck proof pub
   (NLB_ResumePacket.action NLP_ResumeInstall.native input d ck proof pub hash)
 | .powers gamma _ => .powers gamma (NHT_PacketOps.powers 29#usize gamma)
 | .inactive bytes _ => .inactive bytes (NJC_ClosedCalls.inactive bytes)
 | .merkle proof p folded _ => .merkle proof p folded (NLP_NativeMerkle.action H d proof p folded 1#usize hash)
 | .geometry queries next _ => .geometry queries next (NJC_ClosedCalls.geometry queries next 22#usize)
 | .pending weights _ => .pending weights (NKE_CommonNative.pendingG input weights)
 | .query pr p a g geo pending _ =>
   let before : NKE_QueryInput.Args:=⟨pr,p,a,g,geo,pending⟩
   let args:=queryArgs before input.observation
   .query args.proof args.prepared args.accumulator args.powers args.geometry args.pending
    (NKO_QueryReturnG.G (NKE_QueryReturn.observed (NKE_QueryInput.child args)))
 | .flush pending weights _ => .flush pending weights (ok (NLB_NativeFlush.G pending weights))
 | .finish v p a _ => .finish v p a (NHT_ResultPort.action (NJF_FinishObserved.G input.1 input.2 v p a).1)
/-- This projection keeps the complete native resume history, including the
conditional filled/reserve occurrence. It creates no ghost allocation on an
early reject. Its argument fields are the actual parent cut fields. -/
def resumeRun {X : Type} (d : aspis_core.digest.Digest32 X) (ck proof pub : Slice U8)
 (hash : X) (r : NP6_StdModel.Reservation) :=
 NKU_ParentFold.G (NJC_ResumeCalls.digest d) hash (NKU.initial ⟨ck,proof,pub,r⟩)
/-- Compatibility is an auxiliary proof interface only. The future root must
derive it from one actual trace's source order, never accept it as a premise. -/
def Compatible (f : NLT_Interpreted.Uninstalled) : (e : Event) → Input e → Prop
 | .resume ..,r => r=f.resume
 | .pending ..,r => r=f.pending
 | .finish ..,x => x.1=f.finish ∧ x.2=f.locations
 | _,_ => True
def projectedInput (e : Event) (input : Input e) : NLT_Interpreted.Input e :=
 match e with
 | .query .. => input
 | _ => PUnit.unit
/-- Exact connection to the predecessor interpreted windows, preserving every
reply arm. The compatibility hypothesis is explicitly NOT a root clause. -/
theorem interpreted (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (f : NLT_Interpreted.Uninstalled) (e : Event) (input : Input e) (same : Compatible f e input) :
 window H d hash e input=NLT_Interpreted.window f H d hash e (projectedInput e input) := by
 cases e with
 | resume ck proof pub reply => change input=f.resume at same;subst input;rfl
 | pending weights reply => change input=f.pending at same;subst input;rfl
 | finish v p a reply =>
   change input.1=f.finish ∧ input.2=f.locations at same
   change Event.finish v p a (NHT_ResultPort.action (NJF_FinishObserved.G input.1 input.2 v p a).1)=_
   rw [same.1,same.2]
   rfl
 | powers gamma reply => rfl
 | inactive bytes reply => rfl
 | merkle pr p folded reply => rfl
 | geometry queries next reply => rfl
 | query pr p a g geo pending reply => rfl
 | flush pending weights reply => rfl
set_option pp.proofs false
#print interpreted
#print axioms interpreted
end NLT_NativeWindows
