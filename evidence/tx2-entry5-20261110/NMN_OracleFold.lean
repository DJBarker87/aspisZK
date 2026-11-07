import NMN_Relation
import NMD_ComputedFold
set_option autoImplicit false
noncomputable section
namespace NMN_OracleFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev ParserReply := Result (core.result.Result transport.Variant verifier.Error)
/-- G is quantified over the FULL parser reply and FULL common outcome.
Child law is deliberately absent here, as required by (bl)(2). -/
def run {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (parsed : ParserReply)
 (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash) :
 End H s.args × List (Event Ambient X) :=
 match parsed with
 | .fail e => (.parseFail e,[.parse s (.fail e)])
 | .div => (.parseDiv,[.parse s .div])
 | .ok (.Err e) => (.parseReject e,[.parse s (.ok (.Err e))])
 | .ok (.Ok v) => (.common (common v),[.parse s (.ok (.Ok v)),.marker s,.commonEnter s])
/-- Substitute the closed parser at its recorded SAME argument. -/
theorem transcription {Ambient X Physical : Type} (H : Bytes → State)
 (s : NMD_CutState.Parent Ambient X Physical)
 (common : transport.Variant → NLT_CompleteRoot.End H s.frame.args.digest s.frame.args.hash) :
 run H s.frame (NLE_ParseInstall.parse s.frame.args.proof) common =
 NMD_ComputedFold.run H s common := rfl
/-- Every actual branch of the native G has the matching source constructor.
The child clause is an execution relation at the SAME args, not success. -/
theorem installed {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (parsed : ParserReply)
 (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash)
 (parseLaw : parsed=NLE_ParseInstall.parse s.args.proof)
 (child : ∀ v,parsed=.ok (.Ok v) → NLT_CompleteRoot.Native H s.args.digest
  s.args.publicBytes s.args.proof s.args.checkpoint s.args.hash (common v)) :
 Invocation H s (run H s parsed common).1 (run H s parsed common).2 := by
 subst parsed
 unfold run
 cases p : NLE_ParseInstall.parse s.args.proof with
 | fail e => exact .fail e p
 | div => exact .div p
 | ok reply =>
  cases reply with
  | Err e => exact .reject e p
  | Ok v => exact .common v p (common v) (child v p)
/-- Discharges the complete child law with ledger24 CLOSED roots after G
argument association; no free child RowSpec remains. -/
theorem composed {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : NMK_Domain.Caller s.args) (parsed : ParserReply)
 (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash)
 (parseLaw : parsed=NLE_ParseInstall.parse s.args.proof)
 (child : ∀ v,parsed=.ok (.Ok v) → NLT_CompleteRoot.Native H s.args.digest
  s.args.publicBytes s.args.proof s.args.checkpoint s.args.hash (common v)) :
 Law H s.args (run H s parsed common).1 ∧
 (run H s parsed common).2=chronology H s (run H s parsed common).1 :=
 (NMN_Relation.composition H s domain).1 _ _ (installed H s parsed common parseLaw child)
#print run
#print transcription
#print installed
#print composed
#print axioms transcription
#print axioms installed
#print axioms composed
end NMN_OracleFold
