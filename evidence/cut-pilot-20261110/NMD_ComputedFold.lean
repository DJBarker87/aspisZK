import NMD_CandidateFold
set_option autoImplicit false
noncomputable section
namespace NMD_ComputedFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064 NMD_CutState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Complete-outcome G fold. The one selected child reply can be resolved or
independently stopped; no returned Result is fabricated for the latter. -/
def run {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash) :
 End H s.frame.args × List (Event Ambient X) :=
 match NLE_ParseInstall.parse s.frame.args.proof with
 | .fail e => (.parseFail e,[.parse s.frame (.fail e)])
 | .div => (.parseDiv,[.parse s.frame .div])
 | .ok (.Err e) => (.parseReject e,[.parse s.frame (.ok (.Err e))])
 | .ok (.Ok v) => (.common (pick v),[.parse s.frame (.ok (.Ok v)),.marker s.frame,.commonEnter s.frame])
/-- Only the child reached at this SAME successful parse is instantiated. -/
def ChildAt {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash) : Prop :=
 ∀ v,NLE_ParseInstall.parse s.frame.args.proof=.ok (.Ok v) →
 NLT_CompleteRoot.Native H s.frame.args.digest s.frame.args.publicBytes s.frame.args.proof
  s.frame.args.checkpoint s.frame.args.hash (pick v)

theorem transcription {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash)
 (child : ChildAt H s pick) :
 Invocation H s.frame (run H s pick).1 (run H s pick).2 := by
 unfold run
 cases parsed : NLE_ParseInstall.parse s.frame.args.proof with
 | fail e => exact .fail e parsed
 | div => exact .div parsed
 | ok reply =>
  cases reply with
  | Err e => exact .reject e parsed
  | Ok v => exact .common v parsed (pick v) (child v parsed)

def Selected {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash) :
 End H s.frame.args → Prop
 | .common out => ∀ v,NLE_ParseInstall.parse s.frame.args.proof=.ok (.Ok v) → out=pick v
 | _ => True
/-- Literal equality to NLW's full transcription at the selected native child.
This is stronger than just a trace projection and retains every stopped arm. -/
theorem same_fold {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash)
 (outcome : End H s.frame.args) (events : List (Event Ambient X))
 (native : Invocation H s.frame outcome events) (selected : Selected H s pick outcome) :
 (outcome,events)=run H s pick := by
 cases native with
 | fail e parsed => simp only [run,parsed]
 | div parsed => simp only [run,parsed]
 | reject e parsed => simp only [run,parsed]
 | common v parsed out child =>
  have eq : out=pick v := selected v parsed
  subst out
  simp only [run,parsed]
/-- The merged corrected candidate discharges the child RowSpec, including
C04 stop prefixes. Native segment production remains a separate obligation. -/
theorem fold {Ambient X Physical : Type} (H : Bytes → State)
 (s : Parent Ambient X Physical)
 (pick : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash)
 (child : ChildAt H s pick)
 (publicBound : s.frame.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.frame.args.checkpoint s.frame.args.proof) :
 Law H s.frame.args (run H s pick).1 ∧
 (run H s pick).2=chronology H s.frame (run H s pick).1 := by
 apply NMD_CandidateFold.fold H s publicBound root0
 exact (NMD_SegmentFold.transcription H s _ _).mpr (transcription H s pick child)
#print transcription
#print same_fold
#print fold
#print axioms transcription
#print axioms same_fold
#print axioms fold
end NMD_ComputedFold
