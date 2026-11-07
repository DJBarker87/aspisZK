import NLW_RowSpec_065
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLW_Full064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Reply := core.result.Result Unit verifier.Error
structure Args (X : Type) where
 digest : aspis_core.digest.Digest32 X
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
 hash : X
structure Frame (Ambient X : Type) where
 args : Args X
 world : NLM_PacketTypes.World Ambient
/-- Native independent abort is a distinct outcome. There is no invented
common Result or parent return after it. Generic/partial backend is retained. -/
inductive End (H : Bytes → State) {X : Type} (args : Args X) where
 | parseFail (error : Aeneas.Std.Error)
 | parseDiv
 | parseReject (error : verifier.Error)
 | common (outcome : NLT_CompleteRoot.End H args.digest args.hash)
inductive Event (Ambient X : Type) where
 | parse (before : Frame Ambient X)
   (reply : Result (core.result.Result transport.Variant verifier.Error))
 | marker (before : Frame Ambient X)
 | commonEnter (before : Frame Ambient X)
def ChildBridge (H : Bytes → State) : Prop :=
 ∀ {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X),
 proof.val.length=57607 → pub.val.length≤1880 → NLP_InputDomain.Root0 ck proof →
 NLW_RowSpec_065.RowSpec_065 H d pub proof ck hash
/-- Reviewed call-boundary interpretation,including the complete stopped
child. Full physical Frame decoder/contract binding remains a review item. -/
inductive Invocation {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X) :
 End H s.args → List (Event Ambient X) → Prop where
 | fail (e : Aeneas.Std.Error) (parsed : NLE_ParseInstall.parse s.args.proof=.fail e) :
   Invocation H s (.parseFail e) [.parse s (.fail e)]
 | div (parsed : NLE_ParseInstall.parse s.args.proof=.div) :
   Invocation H s .parseDiv [.parse s .div]
 | reject (e : verifier.Error) (parsed : NLE_ParseInstall.parse s.args.proof=.ok (.Err e)) :
   Invocation H s (.parseReject e) [.parse s (.ok (.Err e))]
 | common (v : transport.Variant) (parsed : NLE_ParseInstall.parse s.args.proof=.ok (.Ok v))
   (outcome : NLT_CompleteRoot.End H s.args.digest s.args.hash)
   (child : NLT_CompleteRoot.Native H s.args.digest s.args.publicBytes s.args.proof
    s.args.checkpoint s.args.hash outcome) :
   Invocation H s (.common outcome) [.parse s (.ok (.Ok v)),.marker s,.commonEnter s]
#print ChildBridge
#print Invocation
end NLW_Full064
